use std::{borrow::Cow, fmt, io, rc::Rc};

use anyhow::anyhow;
use rustc_hash::FxHashMap;

use crate::{
    ast::{BinOp, Expr, ExprKind, Ident, Literal, Stmt, StmtKind, Term, UnOp},
    error::LoxError,
    parser,
    span::Span,
};

#[derive(Default)]
pub struct Environment<'scope> {
    table: SymbolTable<'scope>,
}

#[derive(Debug, Clone, PartialEq)]
/// represents runtime value
pub enum Rt<'s> {
    Literal(Literal<'s>),
}
impl<'s> Rt<'s> {
    pub fn truthy(&self) -> bool {
        match self {
            Rt::Literal(l) => l.truthy(),
        }
    }
}
impl<'s> fmt::Display for Rt<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rt::Literal(l) => l.fmt(f),
        }
    }
}

#[derive(Default)]
pub struct SymbolTable<'scope> {
    env: FxHashMap<Ident<'scope>, Rt<'scope>>,
    enclosing: Option<Box<SymbolTable<'scope>>>,
}

impl<'s> Environment<'s> {
    pub fn new() -> Self {
        let table = SymbolTable::new();
        Environment { table }
    }

    pub fn define(&mut self, ident: Ident<'s>, expr: Rt<'s>) {
        tracing::info!("define {ident} = {expr:?}");
        self.table.define(ident, expr);
    }

    pub fn assign(&mut self, ident: Ident<'s>, expr: Rt<'s>) -> Result<(), LoxError<'s>> {
        self.table.assign(ident, expr)
    }

    pub fn lookup<'a>(&'a self, ident: &Ident<'a>) -> Option<&Rt<'s>> {
        self.table.lookup(ident)
    }

    /// creates a nested/scoped environment that is used while executing a block statement.
    pub fn nest_scope<'a>(&mut self) -> Result<(), LoxError<'a>> {
        let current_table = std::mem::take(&mut self.table);
        self.table = SymbolTable {
            enclosing: Some(Box::new(current_table)),
            ..Default::default()
        };
        Ok(())
    }

    pub fn exit_scope<'a>(&mut self) -> Result<(), LoxError<'a>> {
        assert!(self.table.enclosing.is_some());
        self.table = *self.table.enclosing.take().unwrap();
        Ok(())
    }
}

impl<'s> SymbolTable<'s> {
    pub fn new() -> Self {
        let env = FxHashMap::default();
        let enclosing = None;
        SymbolTable { env, enclosing }
    }

    pub fn define(&mut self, ident: Ident<'s>, expr: Rt<'s>) {
        self.env.insert(ident, expr);
    }

    pub fn assign(&mut self, ident: Ident<'s>, expr: Rt<'s>) -> Result<(), LoxError<'s>> {
        if self.env.get(&ident).is_some() {
            self.define(ident, expr);
        } else {
            match &mut self.enclosing {
                Some(e) => {
                    e.assign(ident, expr)?;
                }
                None => return Err(LoxError::Other(anyhow!("undefined variable"))),
            }
        }

        Ok(())
    }

    pub fn lookup<'a>(&'a self, ident: &Ident<'a>) -> Option<&Rt<'s>> {
        self.env
            .get(ident)
            .or_else(|| self.enclosing.as_ref().and_then(|t| t.lookup(ident)))
    }
}

pub struct Interpreter<'a, 's: 'a, W: io::Write> {
    writer: &'s mut W,
    env: Environment<'a>,
}

impl<'a, 's, W: io::Write> Interpreter<'a, 's, W> {
    pub fn new(writer: &'s mut W) -> Self {
        let env = Environment::new();
        Interpreter { writer, env }
    }

    fn error(&self, message: String, span: Span) -> LoxError<'a> {
        let message = Cow::Owned(message);
        LoxError::SyntaxError { message, span }
    }

    pub fn execute(&mut self, line: &'a str) -> Result<(), LoxError<'a>> {
        let stmts = parser::parse(line).into_iter().map(Rc::new);
        for stmt in stmts {
            if let Err(e) = self.stmt(stmt) {
                writeln!(self.writer, "{e}").unwrap();
                return Err(LoxError::Other(anyhow!("runtime error")));
            }
        }

        self.writer.flush().unwrap();

        Ok(())
    }

    fn stmt(&mut self, stmt: Rc<Stmt<'a>>) -> Result<(), LoxError<'a>> {
        match &stmt.kind {
            StmtKind::Expr(ref expr) => {
                self.expr(expr)?;
            }
            StmtKind::Print(ref expr) => {
                let literal = self.expr(expr)?;
                tracing::debug!("print {literal}");
                writeln!(self.writer, "{literal}").unwrap();
            }
            StmtKind::DeclVar { name, initializer } => {
                self.env.define(name.clone(), self.expr(initializer)?)
            }
            StmtKind::Assign { name, expr } => {
                if self.env.lookup(name).is_none() {
                    let message = format!("undefined variable {name}");
                    return Err(self.error(message, stmt.span));
                }

                self.env.assign(name.clone(), self.expr(expr)?)?
            }
            StmtKind::Block(stmts) => {
                self.env.nest_scope()?;
                for stmt in stmts {
                    self.stmt(stmt.clone())?;
                }
                self.env.exit_scope()?;
            }
            StmtKind::If {
                condition,
                then_branch,
                else_branch,
            } => match self.expr(condition)? {
                cond @ (Rt::Literal(Literal::True) | Rt::Literal(Literal::False)) => {
                    if cond.truthy() {
                        self.stmt(then_branch.clone())?;
                    } else if let Some(else_branch) = else_branch {
                        self.stmt(else_branch.clone())?;
                    }
                }
                _ => {
                    let message =
                        String::from("condition of if statement is not evaluated to boolean");
                    return Err(self.error(message, stmt.span));
                }
            },
            StmtKind::While { condition, stmt } => {
                while self.expr(condition)?.truthy() {
                    self.stmt(stmt.clone())?;
                }
            }
            _ => unimplemented!()
        }

        Ok(())
    }

    fn expr(&self, expr: &Expr<'a>) -> Result<Rt<'a>, LoxError<'a>> {
        match &expr.kind {
            ExprKind::Term(term) => Ok(self.term(term)?),
            ExprKind::Unary(op, expr) => match expr.kind {
                ExprKind::Term(Term::Literal(literal)) => {
                    let lit = self
                        .apply_unary(*op, Rt::Literal(literal))
                        .map_err(|e| self.error(e, expr.span))?;

                    Ok(lit)
                }
                _ => {
                    // reduct non-literal expr then apply unary operation
                    let lit = self.expr(expr)?;
                    let lit = self
                        .apply_unary(*op, lit)
                        .map_err(|e| self.error(e, expr.span))?;

                    Ok(lit)
                }
            },
            ExprKind::Binary(op, box lhs, box rhs) => {
                let lhs = self.expr(lhs)?;
                let rhs = self.expr(rhs)?;

                match lhs {
                    Rt::Literal(Literal::String(lhv)) if *op == BinOp::Plus => {
                        let Rt::Literal(Literal::String(rhv)) = rhs else {
                            return Err(self.error("incomparable operation".into(), expr.span));
                        };

                        let s = format!("{lhv}{rhv}");
                        // FIXME: hold static string or cow
                        Ok(Rt::Literal(Literal::String(s.leak())))
                    }
                    Rt::Literal(Literal::Integer(lhv)) => {
                        let Rt::Literal(Literal::Integer(rhv)) = rhs else {
                            return Err(self.error("incomparable operation".into(), expr.span));
                        };

                        let v = match op {
                            BinOp::Plus => Literal::Integer(lhv + rhv),
                            BinOp::Minus => Literal::Integer(lhv - rhv),
                            BinOp::Mul => Literal::Integer(lhv * rhv),
                            BinOp::Div => Literal::Integer(lhv / rhv),
                            BinOp::Eq => Literal::from(lhv == rhv),
                            BinOp::Neq => Literal::from(lhv != rhv),
                            BinOp::Lt => Literal::from(lhv < rhv),
                            BinOp::Leq => Literal::from(lhv <= rhv),
                            BinOp::Gt => Literal::from(lhv > rhv),
                            BinOp::Geq => Literal::from(lhv >= rhv),
                            _ => return Err(self.error("incomparable operation".into(), expr.span)),
                        };

                        Ok(Rt::Literal(v))
                    }
                    Rt::Literal(Literal::Float(lhv)) => {
                        let Rt::Literal(Literal::Float(rhv)) = rhs else {
                            return Err(self.error("incomparable operation".into(), expr.span));
                        };

                        let v = match op {
                            BinOp::Plus => Literal::Float(lhv + rhv),
                            BinOp::Minus => Literal::Float(lhv - rhv),
                            BinOp::Mul => Literal::Float(lhv * rhv),
                            BinOp::Div => Literal::Float(lhv / rhv),
                            BinOp::Eq => Literal::from(lhv == rhv),
                            BinOp::Neq => Literal::from(lhv != rhv),
                            BinOp::Lt => Literal::from(lhv < rhv),
                            BinOp::Leq => Literal::from(lhv <= rhv),
                            BinOp::Gt => Literal::from(lhv > rhv),
                            BinOp::Geq => Literal::from(lhv >= rhv),
                            _ => return Err(self.error("incomparable operation".into(), expr.span)),
                        };

                        Ok(Rt::Literal(v))
                    }
                    _ => {
                        let v = match op {
                            BinOp::And => Literal::from(lhs.truthy() && rhs.truthy()),
                            BinOp::Or => Literal::from(lhs.truthy() || rhs.truthy()),
                            _ => return Err(self.error("unsupported operation".into(), expr.span)),
                        };

                        Ok(Rt::Literal(v))
                    }
                }
            }
        }
    }

    fn term(&self, term: &Term<'a>) -> Result<Rt<'a>, LoxError<'a>> {
        match &term {
            Term::Literal(lit) => Ok(Rt::Literal(*lit)),
            Term::Grouped(box expr) => Ok(self.expr(expr)?),
            Term::Ident(ident) => {
                let Some(value) = self.env.lookup(ident) else {
                    // TODO: give a span
                    return Err(
                        self.error(format!("undefined identifier `{ident}`"), Span::new(0, 0))
                    );
                };

                Ok(value.clone())
            }
        }
    }

    fn apply_unary(&self, op: UnOp, v: Rt<'a>) -> Result<Rt<'a>, String> {
        let v = match v {
            Rt::Literal(Literal::True) if op == UnOp::Not => Literal::False,
            Rt::Literal(Literal::False) if op == UnOp::Not => Literal::True,
            Rt::Literal(Literal::Integer(n)) if op == UnOp::Minus => Literal::Integer(-n),
            Rt::Literal(Literal::Float(n)) if op == UnOp::Minus => Literal::Float(-n),
            _ => return Err(format!("cannot apply operation `{op}` to `{v}`")),
        };

        Ok(Rt::Literal(v))
    }
}

#[cfg(test)]
mod tests {
    use std::io::BufWriter;

    use super::*;
    use crate::parser::Parser;

    fn assert_redex(program: &str, expected: Literal) {
        let mut stdout = BufWriter::new(Vec::new());
        let expr = Parser::new(program).parse::<Expr>().unwrap();
        let reducted = Interpreter::new(&mut stdout).expr(&expr).unwrap();
        assert_eq!(reducted, Rt::Literal(expected))
    }

    fn assert_stmt(program: &str, expected: &str) {
        let mut stdout = BufWriter::new(Vec::new());
        Interpreter::new(&mut stdout).execute(program).unwrap();
        let output = String::from_utf8(stdout.into_inner().unwrap()).unwrap();
        assert_eq!(output.trim(), expected.to_string());
    }

    #[test]
    fn unary_redex() {
        assert_redex("!true", Literal::False);
        assert_redex("!!true", Literal::True);
        assert_redex("!!false", Literal::False);

        assert_redex("-10", Literal::Integer(-10));
    }

    #[test]
    fn binary_redex() {
        assert_redex("1 + 2 * 3", Literal::Integer(7));
        assert_redex("(1 + 2) * 3", Literal::Integer(9));
        assert_redex("2 * 2 + 3", Literal::Integer(7));
        assert_redex("2 * (2 + 3)", Literal::Integer(10));
        assert_redex("2 * 3 + 3 * 4", Literal::Integer(18));
        assert_redex("true and true", Literal::True);
        assert_redex("true and false", Literal::False);
        assert_redex("false or true", Literal::True);
        assert_redex("false or false", Literal::False);
        assert_redex("true and nil", Literal::False);
        assert_redex(r#""hello, " + "world""#, Literal::String("hello, world"));
    }

    #[test]
    fn interpret() {
        assert_stmt("1 + 2;", "");
        assert_stmt("print 1 + 2;", "3");
        assert_stmt(r#"print "1 + 2";"#, "1 + 2");
        assert_stmt(r#"print "Hello, " + "World";"#, "Hello, World");
        assert_stmt("var x = 10; print x;", "10");
    }

    #[test]
    fn interpret_block() {
        assert_stmt(
            r#"
            var x = 10;
            {
                var x = 20;
                print x;

                {
                    x = 30;
                    print x;
                }

                print x;
            }
            print x;
        "#,
            "20\n30\n30\n10",
        );
    }

    #[test]
    fn interpret_if_stmt() {
        assert_stmt(r#"if(true) { print 10; } else { print 0; }"#, "10");
        assert_stmt(r#"if(false) { print 10; } else { print 0; }"#, "0");
    }

    #[test]
    fn interpret_while_stmt() {
        assert_stmt("var x = 3; while(x > 0) { x = x - 1; print x; }", "2\n1\n0");
    }
}
