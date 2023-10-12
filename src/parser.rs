use std::iter::Peekable;

use crate::{
    ast::{
        Compare, Comparison, EqOp, Equality, Expr, ExprKind, Factor, FactorOp, Literal, NumberKind,
        Primary, Term, TermOp, UnOp, Unary, UnaryKind,
    },
    error::{LexError, LoxError},
    lexer::Lexer,
    span::Span,
    token::{self, Token, TokenKind},
};

type ParseResult<'s, T> = std::result::Result<T, LoxError<'s>>;

pub trait Parse<'a>: Sized {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self>;
}

struct TokenStream<'ast> {
    tokens: Peekable<Lexer<'ast>>,
    peeked: Option<Result<Token<'ast>, LexError>>,
    current_span: Span,
}

impl<'a> TokenStream<'a> {
    fn new(lexer: Lexer<'a>) -> Self {
        let mut tokens = lexer.peekable();
        let peeked = tokens.next();
        let current_span = match peeked {
            Some(Ok(ref token)) => token.span,
            _ => Span::new(0, 0),
        };

        TokenStream {
            tokens,
            peeked,
            current_span,
        }
    }

    fn peek(&self) -> Option<&Result<Token<'a>, LexError>> {
        self.peeked.as_ref()
    }

    fn next(&mut self) -> Option<Result<Token<'a>, LexError>> {
        let next = self.peeked.take().or_else(|| self.tokens.next());
        if let Some(Ok(ref token)) = next {
            self.current_span = token.span;
        }

        self.peeked = self.tokens.next();
        next
    }
}

pub struct Parser<'a> {
    tokens: TokenStream<'a>,
}

impl<'a> Parser<'a> {
    pub fn new(source: &'a str) -> Parser<'a> {
        let tokens = TokenStream::new(Lexer::new(source));
        Parser { tokens }
    }

    pub fn parse<P: Parse<'a>>(&mut self) -> ParseResult<'a, P> {
        Parse::<'a>::parse(self)
    }

    fn unexpected_token<T>(&self, token: &Token<'a>) -> ParseResult<'a, T> {
        let token = token.clone();
        Err(LoxError::UnexpectedToken { token })
    }

    fn peek(&self) -> ParseResult<'a, &Token<'a>> {
        match self.tokens.peek() {
            Some(Ok(ref token)) => Ok(token),
            Some(Err(e)) => Err(LoxError::from(*e)),
            None => Err(LoxError::UnexpectedEOF),
        }
    }

    fn next(&mut self) -> ParseResult<'a, Token<'a>> {
        match self.tokens.next() {
            Some(Ok(token)) => Ok(token),
            Some(Err(e)) => Err(e.into()),
            None => Err(LoxError::UnexpectedEOF),
        }
    }

    /// consume the next token iff token == `expected`.
    fn eat(&mut self, expected: TokenKind<'a>) -> ParseResult<'a, Token<'a>> {
        match self.next() {
            Ok(token) if token.kind == expected => Ok(token),
            Ok(ref actual) => self.unexpected_token(actual),
            Err(e) => Err(e),
        }
    }

    fn eat_matches<F>(&mut self, matcher: F) -> ParseResult<'a, Token<'a>>
    where
        F: Fn(&Token<'a>) -> bool,
    {
        let token = self.peek()?;
        if matcher(token) {
            let token = self.next()?;
            Ok(token)
        } else {
            self.unexpected_token(token)
        }
    }
}

impl<'a> Parse<'a> for Literal<'a> {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self> {
        let token = parser.peek()?;
        let lit = match token.kind {
            TokenKind::Number(ref kind) => {
                let kind = match kind {
                    token::NumberKind::Float(f) => NumberKind::Float(*f),
                    token::NumberKind::Integer(i) => NumberKind::Integer(*i),
                };
                Literal::Number(kind)
            }
            TokenKind::String(str) => Literal::String(str),
            TokenKind::True => Literal::True,
            TokenKind::False => Literal::False,
            TokenKind::Nil => Literal::Nil,
            _ => return parser.unexpected_token(token),
        };

        parser.next()?;
        Ok(lit)
    }
}

impl<'a> Parse<'a> for Primary<'a> {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self> {
        let token = parser.peek()?;
        let lexed = if token.kind == TokenKind::LParen {
            let expr = parser.parse()?;
            parser.eat(TokenKind::RParen)?;

            Primary::Grouped(Box::new(expr))
        } else {
            let literal = parser.parse()?;

            Primary::Literal(literal)
        };

        Ok(lexed)
    }
}

impl<'a> Parse<'a> for Unary<'a> {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self> {
        let token = parser.peek()?;
        let span = token.span;
        // FIXME: when op = None
        let kind = if matches!(token.kind, TokenKind::Bang | TokenKind::Minus) {
            let op = parser.next()?;
            let op = match op.kind {
                TokenKind::Bang => Some(UnOp::Not),
                TokenKind::Minus => Some(UnOp::Minus),
                _ => None,
            };

            let unary = Box::new(parser.parse()?);
            UnaryKind::UnOp { op, unary }
        } else {
            let primary = parser.parse()?;
            UnaryKind::Primary(primary)
        };

        let span = span.with_hi(parser.tokens.current_span.hi());
        Ok(Unary { kind, span })
    }
}

impl<'a> Parse<'a> for Factor<'a> {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self> {
        let lhs = parser.parse()?;

        let token = parser.peek()?;
        let span = token.span;
        let rhs = if matches!(token.kind, TokenKind::Slash | TokenKind::Star) {
            let op = parser.next()?;
            let op = match op.kind {
                TokenKind::Slash => FactorOp::Div,
                TokenKind::Star => FactorOp::Mul,
                _ => return parser.unexpected_token(&op),
            };

            let rhs = parser.parse()?;
            Some((op, rhs))
        } else {
            None
        };

        let span = span.with_hi(parser.tokens.current_span.hi());
        Ok(Factor { lhs, rhs, span })
    }
}

impl<'a> Parse<'a> for Term<'a> {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self> {
        let lhs = parser.parse()?;
        let token = parser.peek()?;
        let span = token.span;
        let rhs = if matches!(token.kind, TokenKind::Plus | TokenKind::Minus) {
            let op = parser.next()?;
            let op = match op.kind {
                TokenKind::Plus => TermOp::Plus,
                TokenKind::Minus => TermOp::Minus,
                _ => unreachable!(),
            };

            let rhs = parser.parse()?;
            Some((op, rhs))
        } else {
            None
        };

        let span = span.with_hi(parser.tokens.current_span.hi());
        Ok(Term { lhs, rhs, span })
    }
}

impl<'a> Parse<'a> for Comparison<'a> {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self> {
        let lhs = parser.parse()?;
        let token = parser.peek()?;
        let span = token.span;
        let rhs = if matches!(
            token.kind,
            TokenKind::Lt | TokenKind::Leq | TokenKind::Gt | TokenKind::Geq
        ) {
            let op = parser.next()?;
            let op = match op.kind {
                TokenKind::Lt => Compare::Lt,
                TokenKind::Leq => Compare::Leq,
                TokenKind::Gt => Compare::Gt,
                TokenKind::Geq => Compare::Geq,
                _ => unreachable!(),
            };
            let rhs = parser.parse()?;
            Some((op, rhs))
        } else {
            None
        };

        let span = span.with_hi(parser.tokens.current_span.hi());
        Ok(Comparison { lhs, rhs, span })
    }
}

impl<'a> Parse<'a> for Equality<'a> {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self> {
        let lhs = parser.parse()?;
        let token = parser.peek()?;
        let span = token.span;
        let rhs = if matches!(token.kind, TokenKind::EqEq | TokenKind::BangEq) {
            let op = parser.next()?;
            let op = match op.kind {
                TokenKind::EqEq => EqOp::Eq,
                TokenKind::BangEq => EqOp::Neq,
                _ => unreachable!(),
            };
            let rhs = parser.parse()?;
            Some((op, rhs))
        } else {
            None
        };

        let span = span.with_hi(parser.tokens.current_span.hi());
        Ok(Equality { lhs, rhs, span })
    }
}

impl<'a> Parse<'a> for Expr<'a> {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self> {
        if let equality = parser.parse::<Equality>()? {
            let span = equality.span;
            let kind = ExprKind::Equality(equality);
            return Ok(Expr { kind, span });
        }

        todo!()
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::NumberKind;

    use super::*;
    use std::fmt;

    fn assert_parse<'a, P>(source: &'a str, expect: P)
    where
        P: Parse<'a> + PartialEq + fmt::Debug,
    {
        let parsed = Parser::new(source).parse::<P>().unwrap();
        assert_eq!(parsed, expect);
    }

    #[test]
    fn parse_literal() {
        assert_parse("12", Literal::Number(NumberKind::Integer(12)));
        assert_parse("12.3", Literal::Number(NumberKind::Float(12.3)));
        assert_parse(r#""string""#, Literal::String("string"));
        assert_parse("true", Literal::True);
        assert_parse("false", Literal::False);
        assert_parse("nil", Literal::Nil);

        match Parser::new("null").parse::<Literal>().unwrap_err() {
            LoxError::UnexpectedToken { .. } => {}
            e => panic!("raises unexpected error: {e:?}"),
        }
    }

    #[test]
    fn parse_primary() {
        assert_parse(
            "123",
            Primary::Literal(Literal::Number(NumberKind::Integer(123))),
        );
        assert_parse(
            "12.3",
            Primary::Literal(Literal::Number(NumberKind::Float(12.3))),
        );

        // FIXME
        assert_parse(
            "(123)",
            Primary::Literal(Literal::Number(NumberKind::Float(12.3))),
        );
    }

    #[test]
    fn parse_unary() {
        assert_parse(
            "123",
            Unary {
                kind: UnaryKind::Primary(Primary::Literal(Literal::Number(NumberKind::Integer(
                    123,
                )))),
                span: Span::new(0, 3),
            },
        );

        assert_parse(
            "-123",
            Unary {
                kind: UnaryKind::UnOp {
                    op: Some(UnOp::Minus),
                    unary: Box::new(Unary {
                        kind: UnaryKind::Primary(Primary::Literal(Literal::Number(
                            NumberKind::Integer(123),
                        ))),
                        span: Span::new(1, 4),
                    }),
                },
                span: Span::new(0, 4),
            },
        );
    }
}
