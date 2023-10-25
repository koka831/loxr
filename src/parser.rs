use std::iter::Peekable;

use crate::{
    ast::{BinOp, Expr, ExprKind, Ident, Literal, Stmt, StmtKind, Term, UnOp},
    error::{LexError, LoxError},
    lexer::Lexer,
    span::Span,
    token::{self, Token, TokenKind},
};

type ParseResult<'s, T> = std::result::Result<T, LoxError<'s>>;

pub fn parse(source: &str) -> Vec<Stmt<'_>> {
    let mut parser = Parser::new(source);
    let mut stmts = Vec::new();
    while let Ok(stmt) = parser.parse() {
        stmts.push(stmt);
    }

    stmts
}

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

    fn unexpected_token<T>(&self, token: &Token<'a>, message: &'a str) -> ParseResult<'a, T> {
        let token = token.clone();
        Err(LoxError::UnexpectedToken { message, token })
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
    #[tracing::instrument(skip(self))]
    fn eat(&mut self, expected: TokenKind<'a>) -> ParseResult<'a, Token<'a>> {
        let token = self.peek();
        match token {
            Ok(token) if token.kind == expected => {
                let token = self.next()?;
                Ok(token)
            }
            Ok(actual) => self.unexpected_token(actual, "expect matching tokenkind"),
            Err(e) => Err(e),
        }
    }

    fn current_span(&self) -> Span {
        self.tokens.current_span
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
            _ => return parser.unexpected_token(token, "expect a literal"),
        };

        parser.next()?;
        Ok(lit)
    }
}

impl<'a> Parse<'a> for Ident<'a> {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self> {
        let token = parser.next()?;
        match token.kind {
            TokenKind::Ident(name) => Ok(Ident(name)),
            _ => parser.unexpected_token(&token, "expect an identifier"),
        }
    }
}

impl<'a> Parse<'a> for UnOp {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self> {
        let token = parser.peek()?;
        let op = match token.kind {
            TokenKind::Minus => UnOp::Minus,
            TokenKind::Bang => UnOp::Not,
            _ => return parser.unexpected_token(token, "expect unary operator"),
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
            And => BinOp::And,
            Or => BinOp::Or,
            _ => return parser.unexpected_token(token, "expect binary operator"),
        };

        parser.next()?;
        Ok(op)
    }
}

impl<'a> Parse<'a> for Term<'a> {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self> {
        let token = parser.peek()?;
        let term = match token.kind {
            TokenKind::LParen => {
                parser.next()?;
                let expr = parser.parse()?;
                parser.eat(TokenKind::RParen)?;

                Term::Grouped(Box::new(expr))
            }
            TokenKind::Ident(_) => Term::Ident(parser.parse()?),
            _ => {
                let literal = parser.parse()?;
                Term::Literal(literal)
            }
        };

        Ok(term)
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
            _ => {
                let term = parser.parse()?;
                ExprKind::Term(term)
            }
        };

        let span = span.to(parser.current_span());
        let expr = Expr { kind, span };

        // If the following token is BinOp, perform parsing of rhs as `ExprKind::Binary`.
        if let Ok(op) = parser.parse() {
            // When encountering a high-priority operator, parse elements that do not contain the
            // operator or are indivisible in order to construct the parse tree.
            if matches!(op, BinOp::Mul | BinOp::Div) {
                let term_span = parser.peek()?.span;
                let rhs = Expr {
                    kind: ExprKind::Term(parser.parse()?),
                    span: term_span.to(parser.current_span()),
                };

                let lhs = Expr {
                    kind: ExprKind::Binary(op, Box::new(expr), Box::new(rhs)),
                    span: span.to(parser.current_span()),
                };

                if let Ok(op) = parser.parse() {
                    let rhs = parser.parse()?;

                    Ok(Expr {
                        kind: ExprKind::Binary(op, Box::new(lhs), Box::new(rhs)),
                        span: span.to(parser.current_span()),
                    })
                } else {
                    Ok(lhs)
                }
            } else {
                let rhs = parser.parse()?;
                let kind = ExprKind::Binary(op, Box::new(expr), Box::new(rhs));
                let span = span.to(parser.current_span());

                Ok(Expr { kind, span })
            }
        } else {
            Ok(expr)
        }
    }
}

impl<'a> Parse<'a> for Stmt<'a> {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self> {
        let token = parser.peek()?;
        let span = token.span;

        let kind = match token.kind {
            TokenKind::Print => {
                parser.eat(TokenKind::Print)?;
                let expr = parser.parse::<Expr>()?;

                StmtKind::Print(expr)
            }
            TokenKind::Var => {
                parser.eat(TokenKind::Var)?;
                let name = parser.parse()?;
                let initializer = if parser.eat(TokenKind::Eq).is_ok() {
                    parser.parse()?
                } else {
                    Expr::nil()
                };

                StmtKind::DeclVar { name, initializer }
            }
            // ident = expr ; (re-assignment)
            TokenKind::Ident(_) => {
                let name = parser.parse()?;
                parser.eat(TokenKind::Eq)?;
                let expr = parser.parse()?;

                StmtKind::Assign { name, expr }
            }
            TokenKind::LBrace => {
                parser.eat(TokenKind::LBrace)?;
                let mut stmts = Vec::new();

                while parser.peek()?.kind != TokenKind::RBrace {
                    let stmt = parser.parse()?;
                    stmts.push(stmt);
                }

                parser.eat(TokenKind::RBrace)?;

                // block does not end with `;`
                let span = span.to(parser.current_span());
                let kind = StmtKind::Block(stmts);
                return Ok(Stmt { kind, span });
            }
            TokenKind::If => {
                parser.eat(TokenKind::If)?;
                parser.eat(TokenKind::LParen)?;
                let condition = parser.parse()?;
                parser.eat(TokenKind::RParen)?;

                let then_branch = Box::new(parser.parse()?);
                let else_branch = if parser.eat(TokenKind::Else).is_ok() {
                    Some(Box::new(parser.parse()?))
                } else {
                    None
                };
                let span = span.to(parser.current_span());

                return Ok(Stmt {
                    kind: StmtKind::If {
                        condition,
                        then_branch,
                        else_branch,
                    },
                    span,
                });
            }
            _ => {
                let expr = parser.parse::<Expr>()?;

                StmtKind::Expr(expr)
            }
        };

        parser.eat(TokenKind::Semicolon)?;
        let span = span.to(parser.current_span());

        Ok(Stmt { kind, span })
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
                kind: ExprKind::Term(Term::Literal(Literal::Integer(12))),
                span: Span::new(0, 2),
            },
        );
        assert_parse(
            "true",
            Expr {
                kind: ExprKind::Term(Term::Literal(Literal::True)),
                span: Span::new(0, 4),
            },
        );
    }

    #[test]
    fn parse_unary_expr() {
        assert_parse(
            "!true",
            Expr {
                kind: ExprKind::Unary(
                    UnOp::Not,
                    Box::new(Expr {
                        kind: ExprKind::Term(Term::Literal(Literal::True)),
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
                                kind: ExprKind::Term(Term::Literal(Literal::True)),
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
        use super::Literal::*;

        assert_parse(
            "42 == true",
            Expr {
                kind: ExprKind::Binary(
                    BinOp::Eq,
                    Box::new(Expr {
                        kind: ExprKind::Term(Term::Literal(Integer(42))),
                        span: Span::new(0, 2),
                    }),
                    Box::new(Expr {
                        kind: ExprKind::Term(Term::Literal(True)),
                        span: Span::new(6, 10),
                    }),
                ),
                span: Span::new(0, 10),
            },
        );

        assert_parse(
            "true and true",
            Expr {
                kind: ExprKind::Binary(
                    BinOp::And,
                    Box::new(Expr {
                        kind: ExprKind::Term(Term::Literal(Literal::True)),
                        span: Span::new(0, 4),
                    }),
                    Box::new(Expr {
                        kind: ExprKind::Term(Term::Literal(Literal::True)),
                        span: Span::new(9, 13),
                    }),
                ),
                span: Span::new(0, 13),
            },
        );

        assert_parse(
            "1 + 2 * 3",
            Expr {
                kind: ExprKind::Binary(
                    BinOp::Plus,
                    Box::new(Expr {
                        kind: ExprKind::Term(Term::Literal(Integer(1))),
                        span: Span { base: 0, len: 1 },
                    }),
                    Box::new(Expr {
                        kind: ExprKind::Binary(
                            BinOp::Mul,
                            Box::new(Expr {
                                kind: ExprKind::Term(Term::Literal(Integer(2))),
                                span: Span { base: 4, len: 1 },
                            }),
                            Box::new(Expr {
                                kind: ExprKind::Term(Term::Literal(Integer(3))),
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
            "1 * 2 + 3",
            Expr {
                kind: ExprKind::Binary(
                    BinOp::Plus,
                    Box::new(Expr {
                        kind: ExprKind::Binary(
                            BinOp::Mul,
                            Box::new(Expr {
                                kind: ExprKind::Term(Term::Literal(Integer(1))),
                                span: Span { base: 0, len: 1 },
                            }),
                            Box::new(Expr {
                                kind: ExprKind::Term(Term::Literal(Integer(2))),
                                span: Span { base: 4, len: 1 },
                            }),
                        ),
                        span: Span { base: 0, len: 5 },
                    }),
                    Box::new(Expr {
                        kind: ExprKind::Term(Term::Literal(Integer(3))),
                        span: Span { base: 8, len: 1 },
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
                        kind: ExprKind::Term(Term::Grouped(Box::new(Expr {
                            kind: ExprKind::Binary(
                                BinOp::Plus,
                                Box::new(Expr {
                                    kind: ExprKind::Term(Term::Literal(Integer(1))),
                                    span: Span { base: 1, len: 1 },
                                }),
                                Box::new(Expr {
                                    kind: ExprKind::Term(Term::Literal(Integer(2))),
                                    span: Span { base: 5, len: 1 },
                                }),
                            ),
                            span: Span { base: 1, len: 5 },
                        }))),
                        span: Span { base: 0, len: 7 },
                    }),
                    Box::new(Expr {
                        kind: ExprKind::Term(Term::Literal(Integer(3))),
                        span: Span { base: 10, len: 1 },
                    }),
                ),
                span: Span { base: 0, len: 11 },
            },
        );
    }

    #[test]
    fn parse_stmt() {
        assert_parse(
            "1 + 2;",
            Stmt {
                kind: StmtKind::Expr(Expr {
                    kind: ExprKind::Binary(
                        BinOp::Plus,
                        Box::new(Expr {
                            kind: ExprKind::Term(Term::Literal(Literal::Integer(1))),
                            span: Span::new(0, 1),
                        }),
                        Box::new(Expr {
                            kind: ExprKind::Term(Term::Literal(Literal::Integer(2))),
                            span: Span::new(4, 5),
                        }),
                    ),
                    span: Span::new(0, 5),
                }),
                span: Span::new(0, 6),
            },
        );
        assert_parse(
            r#"print "hi";"#,
            Stmt {
                kind: StmtKind::Print(Expr {
                    kind: ExprKind::Term(Term::Literal(Literal::String("hi"))),
                    span: Span::new(6, 10),
                }),
                span: Span::new(0, 11),
            },
        );
        assert_parse(
            "print x;",
            Stmt {
                kind: StmtKind::Print(Expr {
                    kind: ExprKind::Term(Term::Ident(Ident("x"))),
                    span: Span::new(6, 7),
                }),
                span: Span::new(0, 8),
            },
        );
    }

    #[test]
    fn parse_variable_decl() {
        assert_parse(
            "var x1_foobar;",
            Stmt {
                kind: StmtKind::DeclVar {
                    name: Ident("x1_foobar"),
                    initializer: Expr::nil(),
                },
                span: Span::new(0, 14),
            },
        );
        assert_parse(
            "var x = 10;",
            Stmt {
                kind: StmtKind::DeclVar {
                    name: Ident("x"),
                    initializer: Expr {
                        kind: ExprKind::Term(Term::Literal(Literal::Integer(10))),
                        span: Span::new(8, 10),
                    },
                },
                span: Span::new(0, 11),
            },
        );
        assert_parse(
            "x = 10;",
            Stmt {
                kind: StmtKind::Assign {
                    name: Ident("x"),
                    expr: Expr {
                        kind: ExprKind::Term(Term::Literal(Literal::Integer(10))),
                        span: Span::new(4, 6),
                    },
                },
                span: Span::new(0, 7),
            },
        );
    }

    #[test]
    fn parse_block() {
        assert_parse(
            "{}",
            Stmt {
                kind: StmtKind::Block(vec![]),
                span: Span::new(0, 2),
            },
        );
        assert_parse(
            "{ var x = 10; }",
            Stmt {
                kind: StmtKind::Block(vec![Stmt {
                    kind: StmtKind::DeclVar {
                        name: Ident("x"),
                        initializer: Expr {
                            kind: ExprKind::Term(Term::Literal(Literal::Integer(10))),
                            span: Span::new(10, 12),
                        },
                    },
                    span: Span::new(2, 13),
                }]),
                span: Span::new(0, 15),
            },
        );
        assert_parse(
            "{ var x = 10; print x; }",
            Stmt {
                kind: StmtKind::Block(vec![
                    Stmt {
                        kind: StmtKind::DeclVar {
                            name: Ident("x"),
                            initializer: Expr {
                                kind: ExprKind::Term(Term::Literal(Literal::Integer(10))),
                                span: Span::new(10, 12),
                            },
                        },
                        span: Span::new(2, 13),
                    },
                    Stmt {
                        kind: StmtKind::Print(Expr {
                            kind: ExprKind::Term(Term::Ident(Ident("x"))),
                            span: Span::new(20, 21),
                        }),
                        span: Span::new(14, 22),
                    },
                ]),
                span: Span::new(0, 24),
            },
        );
    }

    #[test]
    fn parse_if_stmt() {
        assert_parse(
            "if(true) print 10;",
            Stmt {
                kind: StmtKind::If {
                    condition: Expr {
                        kind: ExprKind::Term(Term::Literal(Literal::True)),
                        span: Span::new(3, 7),
                    },
                    then_branch: Box::new(Stmt {
                        kind: StmtKind::Print(Expr {
                            kind: ExprKind::Term(Term::Literal(Literal::Integer(10))),
                            span: Span::new(15, 17),
                        }),
                        span: Span::new(9, 18),
                    }),
                    else_branch: None,
                },
                span: Span::new(0, 18),
            },
        );
        assert_parse(
            "if(10 != 42) {
                print false;
            } else {
                print true;
            }",
            Stmt {
                kind: StmtKind::If {
                    condition: Expr {
                        kind: ExprKind::Binary(
                            BinOp::Neq,
                            Box::new(Expr {
                                kind: ExprKind::Term(Term::Literal(Literal::Integer(10))),
                                span: Span { base: 3, len: 2 },
                            }),
                            Box::new(Expr {
                                kind: ExprKind::Term(Term::Literal(Literal::Integer(42))),
                                span: Span { base: 9, len: 2 },
                            }),
                        ),
                        span: Span { base: 3, len: 8 },
                    },
                    then_branch: Box::new(Stmt {
                        kind: StmtKind::Block(vec![Stmt {
                            kind: StmtKind::Print(Expr {
                                kind: ExprKind::Term(Term::Literal(Literal::False)),
                                span: Span { base: 37, len: 5 },
                            }),
                            span: Span { base: 31, len: 12 },
                        }]),
                        span: Span { base: 13, len: 44 },
                    }),
                    else_branch: Some(Box::new(Stmt {
                        kind: StmtKind::Block(vec![Stmt {
                            kind: StmtKind::Print(Expr {
                                kind: ExprKind::Term(Term::Literal(Literal::True)),
                                span: Span { base: 87, len: 4 },
                            }),
                            span: Span { base: 81, len: 11 },
                        }]),
                        span: Span { base: 63, len: 43 },
                    })),
                },
                span: Span { base: 0, len: 106 },
            },
        );
    }
}
