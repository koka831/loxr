use std::iter::Peekable;

use crate::{
    ast::{BinOp, Expr, ExprKind, Literal, UnOp},
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
        let lit = match &token.kind {
            TokenKind::Number(ref kind) => match kind {
                token::NumberKind::Float(f) => Literal::Float(*f),
                token::NumberKind::Integer(i) => Literal::Integer(*i),
            },
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

impl<'a> Parse<'a> for UnOp {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self> {
        let token = parser.peek()?;
        let op = match token.kind {
            TokenKind::Minus => UnOp::Minus,
            TokenKind::Bang => UnOp::Not,
            _ => return parser.unexpected_token(token),
        };

        parser.next()?;
        Ok(op)
    }
}

impl<'a> Parse<'a> for BinOp {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self> {
        use TokenKind::*;

        let token = parser.peek()?;
        let op = match token.kind {
            BangEq => BinOp::Neq,
            EqEq => BinOp::Eq,
            Gt => BinOp::Gt,
            Geq => BinOp::Geq,
            Lt => BinOp::Lt,
            Leq => BinOp::Leq,
            Minus => BinOp::Minus,
            Plus => BinOp::Plus,
            Slash => BinOp::Div,
            Star => BinOp::Mul,
            _ => return parser.unexpected_token(token),
        };

        parser.next()?;
        Ok(op)
    }
}

impl<'a> Parse<'a> for Expr<'a> {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self> {
        let token = parser.peek()?;
        let span = token.span;

        let kind = match token.kind {
            TokenKind::Bang | TokenKind::Minus => {
                let op = parser.parse()?;
                let expr = parser.parse()?;
                ExprKind::Unary(op, Box::new(expr))
            }
            TokenKind::LParen => {
                parser.next()?;
                let expr = parser.parse()?;
                parser.eat(TokenKind::RParen)?;

                ExprKind::Grouped(Box::new(expr))
            }
            _ => {
                let literal = parser.parse()?;
                ExprKind::Literal(literal)
            }
        };

        let span = span.with_hi(parser.tokens.current_span.hi());
        let expr = Expr { kind, span };

        // If the following token is BinOp, perform parsing of rhs as `ExprKind::Binary`.
        if let Ok(op) = parser.parse() {
            let rhs = parser.parse()?;

            let kind = ExprKind::Binary(op, Box::new(expr), Box::new(rhs));
            let span = span.with_hi(parser.tokens.current_span.hi());

            Ok(Expr { kind, span })
        } else {
            Ok(expr)
        }
    }
}

#[cfg(test)]
mod tests {
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
        assert_parse("12", Literal::Integer(12));
        assert_parse("12.3", Literal::Float(12.3));
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
    fn parse_literal_expr() {
        assert_parse(
            "12",
            Expr {
                kind: ExprKind::Literal(Literal::Integer(12)),
                span: Span::new(0, 2),
            },
        );
        assert_parse(
            "true",
            Expr {
                kind: ExprKind::Literal(Literal::True),
                span: Span::new(0, 4),
            },
        );

        match Parser::new("null").parse::<Expr>().unwrap_err() {
            LoxError::UnexpectedToken { .. } => {}
            e => panic!("raises unexpected error: {e:?}"),
        }
    }

    #[test]
    fn parse_unary_expr() {
        assert_parse(
            "!true",
            Expr {
                kind: ExprKind::Unary(
                    UnOp::Not,
                    Box::new(Expr {
                        kind: ExprKind::Literal(Literal::True),
                        span: Span::new(1, 5),
                    }),
                ),
                span: Span::new(0, 5),
            },
        );

        assert_parse(
            "!!true",
            Expr {
                kind: ExprKind::Unary(
                    UnOp::Not,
                    Box::new(Expr {
                        kind: ExprKind::Unary(
                            UnOp::Not,
                            Box::new(Expr {
                                kind: ExprKind::Literal(Literal::True),
                                span: Span::new(2, 6),
                            }),
                        ),
                        span: Span::new(1, 6),
                    }),
                ),
                span: Span::new(0, 6),
            },
        );
    }

    #[test]
    fn parse_binary_expr() {
        use super::ExprKind::*;
        use super::Literal::*;
        assert_parse(
            "42 == true",
            Expr {
                kind: ExprKind::Binary(
                    BinOp::Eq,
                    Box::new(Expr {
                        kind: ExprKind::Literal(Integer(42)),
                        span: Span::new(0, 2),
                    }),
                    Box::new(Expr {
                        kind: ExprKind::Literal(True),
                        span: Span::new(6, 10),
                    }),
                ),
                span: Span::new(0, 10),
            },
        );

        assert_parse(
            "1 + 2 * 3",
            Expr {
                kind: ExprKind::Binary(
                    BinOp::Plus,
                    Box::new(Expr {
                        kind: ExprKind::Literal(Integer(1)),
                        span: Span { base: 0, len: 1 },
                    }),
                    Box::new(Expr {
                        kind: ExprKind::Binary(
                            BinOp::Mul,
                            Box::new(Expr {
                                kind: ExprKind::Literal(Integer(2)),
                                span: Span { base: 4, len: 1 },
                            }),
                            Box::new(Expr {
                                kind: ExprKind::Literal(Integer(3)),
                                span: Span { base: 8, len: 1 },
                            }),
                        ),
                        span: Span { base: 4, len: 5 },
                    }),
                ),
                span: Span { base: 0, len: 9 },
            },
        );

        assert_parse(
            "(1 + 2) * 3",
            Expr {
                kind: ExprKind::Binary(
                    BinOp::Mul,
                    Box::new(Expr {
                        kind: Grouped(Box::new(Expr {
                            kind: Binary(
                                BinOp::Plus,
                                Box::new(Expr {
                                    kind: Literal(Integer(1)),
                                    span: Span { base: 1, len: 1 },
                                }),
                                Box::new(Expr {
                                    kind: Literal(Integer(2)),
                                    span: Span { base: 5, len: 1 },
                                }),
                            ),
                            span: Span { base: 1, len: 5 },
                        })),
                        span: Span { base: 0, len: 6 },
                    }),
                    Box::new(Expr {
                        kind: Literal(Integer(3)),
                        span: Span { base: 10, len: 1 },
                    }),
                ),
                span: Span { base: 0, len: 11 },
            },
        );
    }
}
