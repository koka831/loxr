use std::{borrow::Cow, fmt, io, rc::Rc};

use anyhow::anyhow;
use rustc_hash::FxHashMap;

use crate::{
    ast::{BinOp, Expr, ExprKind, Fn, Ident, Literal, Stmt, StmtKind, Term, UnOp},
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
    // function ptr
    Fn(Rc<Fn<'s>>),
    Void,
}
impl<'s> Rt<'s> {
    pub fn truthy(&self) -> bool {
        match self {
            Rt::Literal(l) => l.truthy(),
            Rt::Fn(..) => false,
            Rt::Void => false,
        }
    }
}
impl<'s> fmt::Display for Rt<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rt::Literal(l) => l.fmt(f),
            Rt::Fn(fun) => fun.fmt(f),
            Rt::Void => write!(f, "void"),
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
        tracing::info!("define {ident} = {expr}");
        self.table.define(ident, expr);
    }

    pub fn assign(&mut self, ident: Ident<'s>, expr: Rt<'s>) -> Result<(), LoxError<'s>> {
        tracing::info!("assign {ident} = {expr}");
        self.table.assign(ident, expr)
    }

    pub fn lookup<'a>(&'a self, ident: &Ident<'a>) -> Option<&Rt<'s>> {
        tracing::debug!("look up {ident}");
        self.table.lookup(ident)
    }

    /// creates a nested/scoped environment that is used while executing a block statement.
    pub fn nest_scope<'a>(&mut self) -> Result<(), LoxError<'a>> {
        tracing::info!("create an nested block");
        let current_table = std::mem::take(&mut self.table);
        self.table = SymbolTable {
            enclosing: Some(Box::new(current_table)),
            ..Default::default()
        };
        Ok(())
    }

    pub fn exit_scope<'a>(&mut self) -> Result<(), LoxError<'a>> {
        tracing::info!("exit an nested block");
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
    // TODO: hold current cursor (span)
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
        let stmts = parser::parse(line)?.into_iter().map(Rc::new);
        for stmt in stmts {
            if let Err(e) = self.stmt(stmt) {
                writeln!(self.writer, "{e}").unwrap();
                self.writer.flush().unwrap();
                return Err(e);
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
                let evaluated = self.expr(initializer)?;
                self.env.define(name.clone(), evaluated)
            }
            StmtKind::DefFun(fun) => {
                self.env
                    .define(fun.name.clone(), Rt::Fn(Rc::new(fun.clone())));
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
            StmtKind::For {
                init,
                test,
                after,
                body,
            } => {
                self.env.nest_scope()?;
                self.stmt(Rc::clone(init))?;
                loop {
                    self.env.nest_scope()?;
                    if let Some(test) = test {
                        if !self.expr(test)?.truthy() {
                            self.env.exit_scope()?;
                            break;
                        }

                        self.stmt(Rc::clone(body))?;

                        if let Some(after) = after {
                            self.expr(&Rc::clone(after))?;
                        }
                    }
                    self.env.exit_scope()?;
                }

                self.env.exit_scope()?;
            }
            StmtKind::Return(expr) => {
                let rt = match expr {
                    Some(expr) => self.expr(expr)?,
                    None => Rt::Void,
                };
                // HACK: use Result::Err to exit and return value
                return Err(LoxError::_Return(rt));
            }
        }

        Ok(())
    }

    fn expr(&mut self, expr: &Expr<'a>) -> Result<Rt<'a>, LoxError<'a>> {
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
            ExprKind::Assign { name, expr } => {
                if self.env.lookup(name).is_none() {
                    let message = format!("undefined variable {name}");
                    return Err(self.error(message, expr.span));
                }

                let evaluated = self.expr(expr)?;
                self.env.assign(name.clone(), evaluated.clone())?;
                Ok(evaluated)
            }
        }
    }

    fn term(&mut self, term: &Term<'a>) -> Result<Rt<'a>, LoxError<'a>> {
        match &term {
            Term::Literal(lit) => Ok(Rt::Literal(*lit)),
            Term::Grouped(box expr) => Ok(self.expr(expr)?),
            Term::Ident(ident) => {
                let Some(value) = self.env.lookup(ident) else {
                    // TODO: give a span
                    let message = format!("undefined identifier `{ident}`");
                    return Err(self.error(message, Span::new(0, 0)));
                };

                Ok(value.clone())
            }
            Term::FnCall { callee, arguments } => {
                let Some(Rt::Fn(func)) = self.env.lookup(callee) else {
                    let message = format!("undefined function `{callee}`");
                    return Err(self.error(message, Span::new(0, 0)));
                };

                let param_len = func.params.len();
                let arg_len = arguments.len();
                if param_len != arg_len {
                    let message = format!("arity mismatch: expect {param_len}, given {arg_len}");
                    return Err(self.error(message, Span::new(0, 0)));
                }

                // todo avoid clone
                let params = func.params.clone();
                let body = func.body.clone();

                self.env.nest_scope()?;
                for i in 0..param_len {
                    let expr = self.expr(&arguments[i])?;
                    tracing::info!("argument[{i}] = {expr}");
                    self.env.define(params[i].clone(), expr);
                }
                for stmt in &body {
                    if let Err(LoxError::_Return(rt)) = self.stmt(Rc::clone(stmt)) {
                        tracing::info!("return {callee} with {rt}");
                        self.env.exit_scope()?;
                        return Ok(rt);
                    }
                }
                self.env.exit_scope()?;

                Ok(Rt::Literal(Literal::Nil))
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

    macro_rules! assert_interpret {
        ($program:literal, $expected:literal $(,)*) => {
            let mut stdout = BufWriter::new(Vec::new());
            Interpreter::new(&mut stdout).execute($program).unwrap();
            let output = String::from_utf8(stdout.into_inner().unwrap()).unwrap();
            assert_eq!(output.trim(), $expected.to_string());
        };
    }

    macro_rules! assert_interpret_err {
        // use `$cond` to compare an inner value of `Cow`
        ($program:literal, $expected:pat if $cond:expr) => {
            let mut stdout = BufWriter::new(Vec::new());
            match Interpreter::new(&mut stdout).execute($program).unwrap_err() {
                $expected if $cond => {}
                e => panic!("unexpected error {e:?}"),
            }
        };
        ($program:literal, $expected:expr $(,)*) => {
            let mut stdout = BufWriter::new(Vec::new());
            match Interpreter::new(&mut stdout).execute($program).unwrap_err() {
                $expected => {}
                e => panic!("unexpected error {e:?}"),
            }
        };
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
        assert_interpret!("1 + 2;", "");
        assert_interpret!("print 1 + 2;", "3");
        assert_interpret!(r#"print "1 + 2";"#, "1 + 2");
        assert_interpret!(r#"print "Hello, " + "World";"#, "Hello, World");
        assert_interpret!("var x = 10; print x;", "10");
    }

    #[test]
    fn interpret_block() {
        assert_interpret!(
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
        assert_interpret!(r#"if(true) { print 10; } else { print 0; }"#, "10");
        assert_interpret!(r#"if(false) { print 10; } else { print 0; }"#, "0");
    }

    #[test]
    fn interpret_while_stmt() {
        assert_interpret!("var x = 3; while(x > 0) { x = x - 1; print x; }", "2\n1\n0");
    }

    #[test]
    fn interpret_for_stmt() {
        assert_interpret!(
            "for (var i = 0; i < 5; i = i + 1) { print i; }",
            "0\n1\n2\n3\n4",
        );
    }

    #[test]
    fn interpret_fn_call() {
        assert_interpret!(
            r#"
fun add(a, b) { return a + b; }
print add(1, 2);"#,
            "3",
        );
        assert_interpret!(
            r#"
fun fib(n) {
  if (n <= 1) return n;
  return fib(n - 2) + fib(n - 1);
}

for (var i = 0; i < 10; i = i + 1) {
  print fib(i);
}"#,
            "0\n1\n1\n2\n3\n5\n8\n13\n21\n34"
        );
        assert_interpret_err!(
            r#"a();"#,
            LoxError::SyntaxError { message, .. } if message == "undefined function `a`"
        );
        assert_interpret_err!(
            "fun foo(a, b) { print a + b; } foo(1, 2, 3);",
            LoxError::SyntaxError { message, .. } if message == "arity mismatch: expect 2, given 3"
        );
    }
}
