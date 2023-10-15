use std::borrow::Cow;

use crate::{
    ast::{BinOp, Expr, ExprKind, Literal, UnOp},
    error::LoxError,
    span::Span,
};

#[derive(Default)]
pub struct Interpreter {}

impl Interpreter {
    pub fn new() -> Self {
        Interpreter {}
    }

    fn error<'a>(&self, message: String, span: Span) -> LoxError<'a> {
        let message = Cow::Owned(message);
        LoxError::SyntaxError { message, span }
    }

    pub fn expr<'a>(&self, expr: &Expr<'a>) -> Result<Literal<'a>, LoxError<'a>> {
        match &expr.kind {
            ExprKind::Grouped(box expr) => Ok(self.expr(expr)?),
            ExprKind::Literal(lit) => Ok(*lit),
            ExprKind::Unary(op, expr) => match expr.kind {
                ExprKind::Literal(literal) => {
                    let lit = self
                        .reduct_unary(*op, literal)
                        .map_err(|e| self.error(e, expr.span))?;

                    Ok(lit)
                }
                _ => {
                    // reduct non-literal expr then apply unary operation
                    let lit = self.expr(expr)?;
                    let lit = self
                        .reduct_unary(*op, lit)
                        .map_err(|e| self.error(e, expr.span))?;

                    Ok(lit)
                }
            },
            ExprKind::Binary(op, box lhs, box rhs) => {
                let lhs = self.expr(lhs)?;
                let rhs = self.expr(rhs)?;

                match op {
                    BinOp::Plus => match lhs {
                        Literal::String(lhv) => {
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

                            Ok(Literal::Integer(lhv + rhv))
                        }
                        _ => {
                            todo!()
                        }
                    },
                    _ => todo!(),
                }
            }
        }
    }

    fn reduct_unary<'a>(&self, op: UnOp, lit: Literal<'a>) -> Result<Literal<'a>, String> {
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
    use super::*;
    use crate::parser::Parser;

    fn assert_redex(program: &str, expected: Literal) {
        let expr = Parser::new(program).parse::<Expr>().unwrap();
        let reducted = Interpreter::new().expr(&expr).unwrap();
        assert_eq!(reducted, expected)
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
        assert_redex("1 + 2 + 3", Literal::Integer(6));
        assert_redex(r#""hello, " + "world""#, Literal::String("hello, world"));
    }
}
