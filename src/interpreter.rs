use std::{borrow::Cow, io};

use rustc_hash::FxHashMap;

use crate::{
    ast::{BinOp, Expr, ExprKind, Ident, Literal, Stmt, StmtKind, Term, UnOp},
    error::LoxError,
    parser::Parser,
    span::Span,
};

#[derive(Default)]
pub struct Environment<'scope> {
    env: FxHashMap<Ident<'scope>, Expr<'scope>>,
}

impl<'s> Environment<'s> {
    pub fn new() -> Self {
        let env = FxHashMap::default();
        Environment { env }
    }

    #[tracing::instrument(skip(self))]
    pub fn define(&mut self, ident: Ident<'s>, expr: Expr<'s>) {
        self.env.insert(ident, expr);
    }

    pub fn lookup<'a>(&'a self, ident: &Ident<'a>) -> Option<&Expr<'s>> {
        self.env.get(ident)
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
        let stmt = Parser::new(line).parse()?;
        self.stmt(stmt)
    }

    fn stmt(&mut self, stmt: Stmt<'a>) -> Result<(), LoxError<'a>> {
        match stmt.kind {
            StmtKind::Expr(ref expr) => {
                self.expr(expr)?;
            }
            StmtKind::Print(ref expr) => {
                let literal = self.expr(expr)?;
                writeln!(self.writer, "{literal}").unwrap();
            }
            StmtKind::Local { name, initializer } => self.env.define(name, initializer),
        }

        self.writer.flush().unwrap();

        Ok(())
    }

    fn expr(&self, expr: &Expr<'a>) -> Result<Literal<'a>, LoxError<'a>> {
        match &expr.kind {
            ExprKind::Term(term) => Ok(self.term(term)?),
            ExprKind::Unary(op, expr) => match expr.kind {
                ExprKind::Term(Term::Literal(literal)) => {
                    let lit = self
                        .apply_unary(*op, literal)
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
                    Literal::String(lhv) if *op == BinOp::Plus => {
                        let Literal::String(rhv) = rhs else {
                            return Err(self.error("uncompatitive operation".into(), expr.span));
                        };

                        let s = format!("{lhv}{rhv}");
                        // FIXME: hold static string or cow
                        Ok(Literal::String(s.leak()))
                    }
                    Literal::Integer(lhv) => {
                        let Literal::Integer(rhv) = rhs else {
                            return Err(self.error("uncompatitive operation".into(), expr.span));
                        };

                        match op {
                            BinOp::Plus => Ok(Literal::Integer(lhv + rhv)),
                            BinOp::Minus => Ok(Literal::Integer(lhv - rhv)),
                            BinOp::Mul => Ok(Literal::Integer(lhv * rhv)),
                            BinOp::Div => Ok(Literal::Integer(lhv / rhv)),
                            BinOp::Eq => Ok(Literal::from_boolean(lhv == rhv)),
                            BinOp::Neq => Ok(Literal::from_boolean(lhv != rhv)),
                            BinOp::Lt => Ok(Literal::from_boolean(lhv < rhv)),
                            BinOp::Leq => Ok(Literal::from_boolean(lhv <= rhv)),
                            BinOp::Gt => Ok(Literal::from_boolean(lhv > rhv)),
                            BinOp::Geq => Ok(Literal::from_boolean(lhv >= rhv)),
                        }
                    }
                    Literal::Float(lhv) => {
                        let Literal::Float(rhv) = rhs else {
                            return Err(self.error("uncompatitive operation".into(), expr.span));
                        };

                        match op {
                            BinOp::Plus => Ok(Literal::Float(lhv + rhv)),
                            BinOp::Minus => Ok(Literal::Float(lhv - rhv)),
                            BinOp::Mul => Ok(Literal::Float(lhv * rhv)),
                            BinOp::Div => Ok(Literal::Float(lhv / rhv)),
                            BinOp::Eq => Ok(Literal::from_boolean(lhv == rhv)),
                            BinOp::Neq => Ok(Literal::from_boolean(lhv != rhv)),
                            BinOp::Lt => Ok(Literal::from_boolean(lhv < rhv)),
                            BinOp::Leq => Ok(Literal::from_boolean(lhv <= rhv)),
                            BinOp::Gt => Ok(Literal::from_boolean(lhv > rhv)),
                            BinOp::Geq => Ok(Literal::from_boolean(lhv >= rhv)),
                        }
                    }
                    _ => Err(self.error("unsupported operation".into(), expr.span)),
                }
            }
        }
    }

    fn term(&self, term: &Term<'a>) -> Result<Literal<'a>, LoxError<'a>> {
        match &term {
            Term::Literal(lit) => Ok(*lit),
            Term::Grouped(box expr) => Ok(self.expr(expr)?),
            Term::Ident(ident) => {
                let Some(value) = self.env.lookup(ident) else {
                    // TODO: give a span
                    return Err(
                        self.error(format!("undefined identifier `{ident}`"), Span::new(0, 0))
                    );
                };

                Ok(self.expr(value)?)
            }
        }
    }

    fn apply_unary(&self, op: UnOp, lit: Literal<'a>) -> Result<Literal<'a>, String> {
        match lit {
            Literal::True if op == UnOp::Not => Ok(Literal::False),
            Literal::False if op == UnOp::Not => Ok(Literal::True),
            Literal::Integer(n) if op == UnOp::Minus => Ok(Literal::Integer(-n)),
            Literal::Float(n) if op == UnOp::Minus => Ok(Literal::Float(-n)),
            _ => Err(format!("cannot apply operation `{op}` to `{lit}`")),
        }
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
        assert_eq!(reducted, expected)
    }

    fn assert_stmt(program: &str, expected: &str) {
        let mut stdout = BufWriter::new(Vec::new());
        let stmt = Parser::new(program).parse::<Stmt>().unwrap();
        Interpreter::new(&mut stdout).stmt(stmt).unwrap();
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
        assert_redex(r#""hello, " + "world""#, Literal::String("hello, world"));
    }

    #[test]
    fn interpret_stmt() {
        assert_stmt("1 + 2;", "");
        assert_stmt("print 1 + 2;", "3");
        assert_stmt(r#"print "1 + 2";"#, "1 + 2");
        assert_stmt(r#"print "Hello, " + "World";"#, "Hello, World");
    }
}
