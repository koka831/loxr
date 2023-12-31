use std::iter::Peekable;
use std::rc::Rc;

use crate::ast::{
    BinOp, ClassDecl, Expr, ExprKind, FnCall, FunDecl, Ident, Literal, Stmt, StmtKind, Term, UnOp,
};
use crate::error::{LexError, LoxError};
use crate::lexer::Lexer;
use crate::span::Span;
use crate::token::{self, Token, TokenKind};

type ParseResult<T> = std::result::Result<T, LoxError>;

pub fn parse(source: &str) -> Result<Vec<Stmt>, LoxError> {
    let mut parser = Parser::new(source);
    let mut stmts = Vec::new();
    while !parser.eof() {
        let stmt = parser.parse()?;
        stmts.push(stmt);
    }

    Ok(stmts)
}

pub trait Parse<'a>: Sized {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<Self>;
}

struct TokenStream<'a> {
    tokens: Peekable<Lexer<'a>>,
    peeked: Option<Result<Token, LexError>>,
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

    fn peek(&self) -> Option<&Result<Token, LexError>> {
        self.peeked.as_ref()
    }

    fn next(&mut self) -> Option<Result<Token, LexError>> {
        let next = self.peeked.take().or_else(|| self.tokens.next());
        if let Some(Ok(ref token)) = next {
            self.current_span = token.span;
        }

        self.peeked = self.tokens.next();
        next
    }

    fn eof(&self) -> bool {
        self.peek().is_none()
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

    pub fn parse<P: Parse<'a>>(&mut self) -> ParseResult<P> {
        Parse::<'a>::parse(self)
    }

    pub fn eof(&self) -> bool {
        self.tokens.eof()
    }

    fn unexpected_token<T>(&self, token: &Token, expect: String) -> ParseResult<T> {
        let actual = token.clone();
        Err(LoxError::UnexpectedToken { expect, actual })
    }

    fn peek(&self) -> ParseResult<&Token> {
        match self.tokens.peek() {
            Some(Ok(ref token)) => {
                tracing::debug!("peeked token: {token}");
                Ok(token)
            }
            Some(Err(e)) => Err(LoxError::from(*e)),
            None => Err(LoxError::UnexpectedEOF),
        }
    }

    fn next(&mut self) -> ParseResult<Token> {
        match self.tokens.next() {
            Some(Ok(token)) => {
                tracing::debug!("next token: {token}");
                Ok(token)
            }
            Some(Err(e)) => Err(e.into()),
            None => Err(LoxError::UnexpectedEOF),
        }
    }

    /// consume the next token iff token == `expected`.
    #[tracing::instrument(skip(self))]
    fn eat(&mut self, expected: TokenKind) -> ParseResult<Token> {
        let token = self.peek();
        match token {
            Ok(token) if token.kind == expected => {
                let token = self.next()?;
                tracing::info!("eat token `{token}`");
                Ok(token)
            }
            Ok(actual) => self.unexpected_token(actual, format!("`{expected}`")),
            Err(e) => Err(e),
        }
    }

    fn current_span(&self) -> Span {
        self.tokens.current_span
    }
}

impl<'a> Parse<'a> for Literal {
    #[tracing::instrument(name = "Parse<Literal>", skip(parser))]
    fn parse(parser: &mut Parser<'a>) -> ParseResult<Self> {
        let token = parser.peek()?;
        let lit = match &token.kind {
            TokenKind::Number(ref kind) => match kind {
                token::NumberKind::Float(f) => Literal::Float(*f),
                token::NumberKind::Integer(i) => Literal::Integer(*i),
            },
            TokenKind::String(str) => Literal::String(str.to_string()),
            TokenKind::True => Literal::True,
            TokenKind::False => Literal::False,
            TokenKind::Nil => Literal::Nil,
            _ => return parser.unexpected_token(token, "literal".into()),
        };

        parser.next()?;
        tracing::info!("parsed literal `{lit}`");
        Ok(lit)
    }
}

impl<'a> Parse<'a> for Ident {
    #[tracing::instrument(name = "Parse<Ident>", skip(parser))]
    fn parse(parser: &mut Parser<'a>) -> ParseResult<Self> {
        let token = parser.next()?;
        match token.kind {
            TokenKind::Ident(name) => {
                tracing::info!("parsed ident `{name}`");
                Ok(Ident(name))
            }
            _ => parser.unexpected_token(&token, "an identifier".into()),
        }
    }
}

impl<'a> Parse<'a> for UnOp {
    #[tracing::instrument(name = "Parse<UnOp>", skip(parser))]
    fn parse(parser: &mut Parser<'a>) -> ParseResult<Self> {
        let token = parser.peek()?;
        let op = match token.kind {
            TokenKind::Minus => UnOp::Minus,
            TokenKind::Bang => UnOp::Not,
            _ => return parser.unexpected_token(token, "unary operator".into()),
        };

        parser.next()?;
        tracing::info!("parsed unary operator `{op}`");
        Ok(op)
    }
}

impl<'a> Parse<'a> for BinOp {
    #[tracing::instrument(name = "Parse<BinOp>", skip(parser))]
    fn parse(parser: &mut Parser<'a>) -> ParseResult<Self> {
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
            _ => return parser.unexpected_token(token, "binary operator".to_string()),
        };

        parser.next()?;
        tracing::info!("parsed binary operator `{op}`");
        Ok(op)
    }
}

impl<'a> Parse<'a> for Term {
    #[tracing::instrument(name = "Parse<Term>", skip(parser))]
    fn parse(parser: &mut Parser<'a>) -> ParseResult<Self> {
        let token = parser.peek()?;
        let term = match token.kind {
            TokenKind::LParen => {
                parser.next()?;
                let expr = parser.parse()?;
                parser.eat(TokenKind::RParen)?;

                Term::Grouped(Box::new(expr))
            }
            TokenKind::Ident(_) => {
                let ident = parser.parse()?;
                if parser.eat(TokenKind::LParen).is_ok() {
                    let mut arguments = Vec::new();
                    while parser.eat(TokenKind::RParen).is_err() {
                        let argument = parser.parse()?;
                        arguments.push(argument);

                        if parser.eat(TokenKind::Comma).is_ok() {}
                    }

                    Term::FnCall(FnCall {
                        callee: ident,
                        arguments,
                    })
                } else {
                    Term::Ident(ident)
                }
            }
            _ => {
                let literal = parser.parse()?;
                Term::Literal(literal)
            }
        };

        tracing::info!("parsed term `{term}`");
        Ok(term)
    }
}

impl<'a> Parse<'a> for Expr {
    #[tracing::instrument(name = "Parse<Expr>", skip(parser))]
    fn parse(parser: &mut Parser<'a>) -> ParseResult<Self> {
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
                let term_span = span.to(parser.current_span());

                if let Term::Ident(ref ident) = term {
                    if parser.eat(TokenKind::Eq).is_ok() {
                        let expr = Box::new(parser.parse()?);
                        let kind = ExprKind::Assign {
                            name: ident.clone(),
                            expr,
                        };

                        let span = span.to(parser.current_span());
                        let expr = Expr { kind, span };
                        tracing::info!("parsed expr `{expr}`");

                        return Ok(expr);
                    } else if parser.eat(TokenKind::Dot).is_ok() {
                        let field = parser.parse()?;
                        ExprKind::Get(
                            Box::new(Expr {
                                kind: ExprKind::Term(term),
                                span: term_span,
                            }),
                            field,
                        )
                    } else {
                        ExprKind::Term(term)
                    }
                } else {
                    ExprKind::Term(term)
                }
            }
        };

        let span = span.to(parser.current_span());
        let expr = Expr { kind, span };

        // If the following token is BinOp, perform parsing of rhs as `ExprKind::Binary`.
        if let Ok(op) = parser.parse() {
            // When encountering a high-priority operator, parse elements that do not contain the
            // operator or are indivisible in order to construct the parse tree.
            match op {
                BinOp::Mul | BinOp::Div => {
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

                        let expr = Expr {
                            kind: ExprKind::Binary(op, Box::new(lhs), Box::new(rhs)),
                            span: span.to(parser.current_span()),
                        };
                        tracing::info!("parsed expr `{expr}`");
                        Ok(expr)
                    } else {
                        tracing::info!("parsed expr `{lhs}`");
                        Ok(lhs)
                    }
                }
                _ => {
                    let rhs = parser.parse()?;
                    let kind = ExprKind::Binary(op, Box::new(expr), Box::new(rhs));
                    let span = span.to(parser.current_span());

                    let expr = Expr { kind, span };
                    tracing::info!("parsed expr `{expr}`");
                    Ok(expr)
                }
            }
        } else if parser.eat(TokenKind::Dot).is_ok() {
            let field = parser.parse()?;
            let expr = Expr {
                kind: ExprKind::Get(Box::new(expr), field),
                span: span.to(parser.current_span()),
            };

            Ok(expr)
        } else {
            tracing::info!("parsed expr `{expr}`");
            Ok(expr)
        }
    }
}

impl<'a> Parse<'a> for ClassDecl {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<Self> {
        parser.eat(TokenKind::Class)?;
        let name = parser.parse()?;
        parser.eat(TokenKind::LBrace)?;
        let mut methods = Vec::new();
        while parser.eat(TokenKind::RBrace).is_err() {
            let method = parser.parse()?;
            methods.push(method);
        }

        Ok(ClassDecl { name, methods })
    }
}

// parse function declaration without `fun` prefix keyword
impl<'a> Parse<'a> for FunDecl {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<Self> {
        let name = parser.parse()?;
        // parse parameters
        parser.eat(TokenKind::LParen)?;
        let mut params = Vec::new();
        while parser.eat(TokenKind::RParen).is_err() {
            let param = parser.parse()?;
            params.push(param);

            if parser.eat(TokenKind::Comma).is_ok() {}
        }

        // parse body
        let body = match parser.parse()? {
            Stmt {
                kind: StmtKind::Block(block),
                ..
            } => block,
            stmt => {
                let message = format!("function body must be a block: `{stmt}`");
                let span = stmt.span;
                return Err(LoxError::SyntaxError { message, span });
            }
        };

        Ok(FunDecl { name, params, body })
    }
}

impl<'a> Parse<'a> for Stmt {
    #[tracing::instrument(name = "Parse<Stmt>", skip(parser))]
    fn parse(parser: &mut Parser<'a>) -> ParseResult<Self> {
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
                    Rc::new(parser.parse()?)
                } else {
                    Rc::new(Expr::nil())
                };

                StmtKind::VarDecl { name, initializer }
            }
            TokenKind::Class => {
                let class = parser.parse()?;
                let stmt = Stmt {
                    kind: StmtKind::ClassDecl(class),
                    span: span.to(parser.current_span()),
                };

                tracing::info!("parsed statement `{stmt}`");
                return Ok(stmt);
            }
            TokenKind::Fun => {
                parser.eat(TokenKind::Fun)?;
                let fun = parser.parse()?;
                let stmt = Stmt {
                    kind: StmtKind::FunDecl(fun),
                    span: span.to(parser.current_span()),
                };

                tracing::info!("parsed statement `{stmt}`");
                return Ok(stmt);
            }
            TokenKind::LBrace => {
                parser.eat(TokenKind::LBrace)?;
                let mut stmts = Vec::new();

                while parser.peek()?.kind != TokenKind::RBrace {
                    let stmt = parser.parse()?;
                    stmts.push(Rc::new(stmt));
                }

                parser.eat(TokenKind::RBrace)?;

                // block does not end with `;`
                let span = span.to(parser.current_span());
                let kind = StmtKind::Block(stmts);
                let stmt = Stmt { kind, span };
                tracing::info!("parsed statement `{stmt}`");
                return Ok(stmt);
            }
            TokenKind::If => {
                parser.eat(TokenKind::If)?;
                parser.eat(TokenKind::LParen)?;
                let condition = parser.parse()?;
                parser.eat(TokenKind::RParen)?;

                let then_branch = Rc::new(parser.parse()?);
                let else_branch = if parser.eat(TokenKind::Else).is_ok() {
                    Some(Rc::new(parser.parse()?))
                } else {
                    None
                };
                let span = span.to(parser.current_span());

                let stmt = Stmt {
                    kind: StmtKind::If {
                        condition,
                        then_branch,
                        else_branch,
                    },
                    span,
                };
                tracing::info!("parsed statement `{stmt}`");
                return Ok(stmt);
            }
            TokenKind::While => {
                parser.eat(TokenKind::While)?;
                parser.eat(TokenKind::LParen)?;
                let condition = parser.parse()?;
                parser.eat(TokenKind::RParen)?;

                let stmt = Rc::new(parser.parse()?);

                let stmt = Stmt {
                    kind: StmtKind::While { condition, stmt },
                    span: span.to(parser.current_span()),
                };
                tracing::info!("parsed statement `{stmt}`");
                return Ok(stmt);
            }
            TokenKind::For => {
                tracing::debug!("parse for statement");
                parser.eat(TokenKind::For)?;
                parser.eat(TokenKind::LParen)?;

                let init = match parser.parse()? {
                    stmt @ Stmt {
                        kind: StmtKind::VarDecl { .. } | StmtKind::Expr(..),
                        ..
                    } => Rc::new(stmt),
                    stmt => {
                        tracing::warn!("unexpected stmt kind in init section of for statement");
                        return Err(LoxError::SyntaxError {
                            message: "unexpected statement".to_string(),
                            span: stmt.span,
                        });
                    }
                };
                let token = parser.peek()?;
                let test = if token.kind != TokenKind::RParen {
                    tracing::debug!("parsing for:test section");
                    Some(Rc::new(parser.parse()?))
                } else {
                    None
                };
                let after = if parser.eat(TokenKind::Semicolon).is_ok() {
                    tracing::debug!("parsing for:after section");
                    Some(Rc::new(parser.parse()?))
                } else {
                    None
                };
                parser.eat(TokenKind::RParen)?;

                let body = Rc::new(parser.parse()?);

                let stmt = Stmt {
                    kind: StmtKind::For {
                        init,
                        test,
                        after,
                        body,
                    },
                    span: span.to(parser.current_span()),
                };
                tracing::info!("parsed statement `{stmt}`");
                return Ok(stmt);
            }
            TokenKind::Return => {
                parser.eat(TokenKind::Return)?;
                let expr = if parser.eat(TokenKind::Semicolon).is_ok() {
                    None
                } else {
                    let expr = Rc::new(parser.parse()?);
                    parser.eat(TokenKind::Semicolon)?;

                    Some(expr)
                };

                let kind = StmtKind::Return(expr);
                let span = span.to(parser.current_span());
                let stmt = Stmt { kind, span };
                tracing::info!("parsed statement `{stmt}`");

                return Ok(stmt);
            }
            _ => {
                let expr = parser.parse::<Expr>()?;
                if let ExprKind::Get(box expr, field) = expr.kind {
                    parser.eat(TokenKind::Eq)?;
                    let rhs = parser.parse()?;

                    StmtKind::SetField {
                        callee: Box::new(expr),
                        field,
                        expr: Box::new(rhs),
                    }
                } else {
                    StmtKind::Expr(expr)
                }
            }
        };

        parser.eat(TokenKind::Semicolon)?;

        let span = span.to(parser.current_span());
        let stmt = Stmt { kind, span };
        tracing::info!("parsed statement `{stmt}`");

        Ok(stmt)
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::ClassDecl;

    use super::*;
    use std::assert_matches::assert_matches;
    use std::fmt;

    fn assert_parse<'a, P>(source: &'a str, expect: P)
    where
        P: Parse<'a> + PartialEq + fmt::Debug,
    {
        let parsed = Parser::new(source).parse::<P>().unwrap();
        assert_eq!(parsed, expect);
    }

    macro_rules! assert_parse {
        ($source:literal, $expect:pat if $target:expr => $cond:pat $(,)*) => {
            let parsed = Parser::new($source).parse().unwrap();
            assert_matches!(
                parsed,
                $expect if match $target {
                    $cond => true ,
                    _ => panic!()
                }
            );
        };
        // use `cond` for comparing `Rc`
        ($source:literal, $expect:pat if $cond:expr $(,)*) => {
            let parsed = Parser::new($source).parse().unwrap();
            assert_matches!(parsed, $expect if $cond);
        };
        ($source:literal, $expect:pat $(,)*) => {
            let parsed = Parser::new($source).parse().unwrap();
            assert_matches!(parsed, $expect);
        };
    }

    macro_rules! assert_parse_err {
        ($source:literal, $ty:ty, $expect:pat) => {
            match Parser::new($source).parse::<$ty>().unwrap_err() {
                $expect => {}
                e => panic!("raises unexpected error: {e:?}"),
            }
        };
    }

    #[test]
    fn parse_literal() {
        assert_parse!("12", Literal::Integer(12));
        assert_parse!("12.3", Literal::Float(..));
        assert_parse(r#""string""#, Literal::String("string".into()));
        assert_parse!("true", Literal::True);
        assert_parse!("false", Literal::False);
        assert_parse!("nil", Literal::Nil);

        assert_parse_err!("null", Literal, LoxError::UnexpectedToken { .. });
    }

    #[test]
    fn parse_fncall_term() {
        assert_parse!(
            "fn()",
            Term::FnCall(FnCall {
                callee: Ident(..),
                arguments
            }) if arguments == vec![]
        );
        assert_parse!(
            "add(1, 2)",
            Term::FnCall(FnCall {
                callee: Ident(..),
                arguments,
            }) if arguments == vec![
                Expr {
                    kind: ExprKind::Term(Term::Literal(Literal::Integer(1))),
                    span: Span { base: 4, len: 1 },
                },
                Expr {
                    kind: ExprKind::Term(Term::Literal(Literal::Integer(2))),
                    span: Span { base: 7, len: 1 },
                }
            ]
        );
        assert_parse!("x(a,)", Term::FnCall { .. });
        assert_parse!("x()()", Term::FnCall { .. });

        assert_parse_err!("x(,)", Term, LoxError::UnexpectedToken { .. });
        assert_parse_err!("x(a,,)", Term, LoxError::UnexpectedToken { .. });
    }

    #[test]
    fn parse_term_expr() {
        assert_parse!(
            "12",
            Expr {
                kind: ExprKind::Term(Term::Literal(Literal::Integer(12))),
                span: Span { base: 0, len: 2 },
            },
        );
        assert_parse!(
            "true",
            Expr {
                kind: ExprKind::Term(Term::Literal(Literal::True)),
                span: Span { base: 0, len: 4 },
            },
        );
        assert_parse!(
            "x()",
            Expr {
                kind: ExprKind::Term(Term::FnCall { .. }),
                ..
            }
        );
    }

    #[test]
    fn parse_getter_expr() {
        assert_parse(
            "x.y",
            Expr {
                kind: ExprKind::Get(
                    Box::new(Expr {
                        kind: ExprKind::Term(Term::Ident(Ident("x".into()))),
                        span: Span { base: 0, len: 1 },
                    }),
                    Ident("y".into()),
                ),
                span: Span { base: 0, len: 3 },
            },
        );

        assert_parse(
            "foo().bar",
            Expr {
                kind: ExprKind::Get(
                    Box::new(Expr {
                        kind: ExprKind::Term(Term::FnCall(FnCall {
                            callee: Ident("foo".into()),
                            arguments: vec![],
                        })),
                        span: Span { base: 0, len: 5 },
                    }),
                    Ident("bar".into()),
                ),
                span: Span { base: 0, len: 9 },
            },
        );
    }

    #[test]
    fn parse_unary_expr() {
        assert_parse!(
            "!true",
            Expr {
                kind: ExprKind::Unary(
                    UnOp::Not,
                    box Expr {
                        kind: ExprKind::Term(Term::Literal(Literal::True)),
                        span: Span { base: 1, len: 4 },
                    },
                ),
                span: Span { base: 0, len: 5 },
            },
        );

        assert_parse!(
            "!!true",
            Expr {
                kind: ExprKind::Unary(
                    UnOp::Not,
                    box Expr {
                        kind: ExprKind::Unary(
                            UnOp::Not,
                            box Expr {
                                kind: ExprKind::Term(Term::Literal(Literal::True)),
                                span: Span { base: 2, len: 4 },
                            },
                        ),
                        span: Span { base: 1, len: 5 },
                    },
                ),
                span: Span { base: 0, len: 6 },
            },
        );
    }

    #[test]
    fn parse_assignment_expr() {
        assert_parse!(
            "x = 10",
            Expr {
                kind: ExprKind::Assign {
                    name: Ident(..),
                    expr: box Expr {
                        kind: ExprKind::Term(Term::Literal(Literal::Integer(10))),
                        ..
                    }
                },
                ..
            }
        );
    }

    #[test]
    fn parse_binary_expr() {
        use super::Literal::*;

        assert_parse!(
            "42 == true",
            Expr {
                kind: ExprKind::Binary(
                    BinOp::Eq,
                    box Expr {
                        kind: ExprKind::Term(Term::Literal(Integer(42))),
                        span: Span { base: 0, len: 2 },
                    },
                    box Expr {
                        kind: ExprKind::Term(Term::Literal(True)),
                        span: Span { base: 6, len: 4 },
                    },
                ),
                span: Span { base: 0, len: 10 },
            },
        );

        assert_parse!(
            "true and true",
            Expr {
                kind: ExprKind::Binary(
                    BinOp::And,
                    box Expr {
                        kind: ExprKind::Term(Term::Literal(Literal::True)),
                        ..
                    },
                    box Expr {
                        kind: ExprKind::Term(Term::Literal(Literal::True)),
                        ..
                    },
                ),
                ..
            },
        );

        assert_parse!(
            "1 + 2 * 3",
            Expr {
                kind: ExprKind::Binary(
                    BinOp::Plus,
                    box Expr {
                        kind: ExprKind::Term(Term::Literal(Integer(1))),
                        ..
                    },
                    box Expr {
                        kind: ExprKind::Binary(
                            BinOp::Mul,
                            box Expr {
                                kind: ExprKind::Term(Term::Literal(Integer(2))),
                                ..
                            },
                            box Expr {
                                kind: ExprKind::Term(Term::Literal(Integer(3))),
                                ..
                            },
                        ),
                        ..
                    },
                ),
                ..
            },
        );

        assert_parse!(
            "1 * 2 + 3",
            Expr {
                kind: ExprKind::Binary(
                    BinOp::Plus,
                    box Expr {
                        kind: ExprKind::Binary(
                            BinOp::Mul,
                            box Expr {
                                kind: ExprKind::Term(Term::Literal(Integer(1))),
                                ..
                            },
                            box Expr {
                                kind: ExprKind::Term(Term::Literal(Integer(2))),
                                ..
                            },
                        ),
                        ..
                    },
                    box Expr {
                        kind: ExprKind::Term(Term::Literal(Integer(3))),
                        ..
                    },
                ),
                ..
            },
        );

        assert_parse!(
            "(1 + 2) * 3",
            Expr {
                kind: ExprKind::Binary(
                    BinOp::Mul,
                    box Expr {
                        kind: ExprKind::Term(Term::Grouped(box Expr {
                            kind: ExprKind::Binary(
                                BinOp::Plus,
                                box Expr {
                                    kind: ExprKind::Term(Term::Literal(Integer(1))),
                                    ..
                                },
                                box Expr {
                                    kind: ExprKind::Term(Term::Literal(Integer(2))),
                                    ..
                                },
                            ),
                            ..
                        })),
                        ..
                    },
                    box Expr {
                        kind: ExprKind::Term(Term::Literal(Integer(3))),
                        ..
                    },
                ),
                span: Span { base: 0, len: 11 },
            },
        );
    }

    #[test]
    fn parse_stmt() {
        assert_parse!(
            "1 + 2;",
            Stmt {
                kind: StmtKind::Expr(Expr {
                    kind: ExprKind::Binary(
                        BinOp::Plus,
                        box Expr {
                            kind: ExprKind::Term(Term::Literal(Literal::Integer(1))),
                            ..
                        },
                        box Expr {
                            kind: ExprKind::Term(Term::Literal(Literal::Integer(2))),
                            ..
                        },
                    ),
                    ..
                }),
                ..
            },
        );
        assert_parse!(
            r#"print "hi";"#,
            Stmt {
                kind: StmtKind::Print(Expr {
                    kind: ExprKind::Term(Term::Literal(Literal::String(..))),
                    ..
                }),
                ..
            },
        );
        assert_parse!(
            "print x;",
            Stmt {
                kind: StmtKind::Print(Expr {
                    kind: ExprKind::Term(Term::Ident(Ident(..))),
                    ..
                }),
                ..
            },
        );
    }

    #[test]
    fn parse_variable_decl() {
        assert_parse!(
            "var x1_0;",
            Stmt {
                kind: StmtKind::VarDecl { name: Ident(name), initializer },
                ..
            } if &name == "x1_0" && *initializer == Expr::nil()
        );
        assert_parse!(
            "var x = 10;",
            Stmt {
                kind: StmtKind::VarDecl { name: Ident(..), initializer },
                ..
            } if *initializer => Expr {
                kind: ExprKind::Term(Term::Literal(Literal::Integer(10))),
                ..
            }
        );
        assert_parse!(
            "x = 10;",
            Stmt {
                kind: StmtKind::Expr(Expr {
                    kind: ExprKind::Assign { expr, .. },
                    ..
                }),
                ..
            } if *expr => Expr {
                kind: ExprKind::Term(Term::Literal(Literal::Integer(10))),
                ..
            }
        );
    }

    #[test]
    fn parse_block() {
        assert_parse!(
            "{}",
            Stmt { kind: StmtKind::Block(block), .. } if block.is_empty()
        );
        assert_parse(
            "{ var x = 10; }",
            Stmt {
                kind: StmtKind::Block(vec![Stmt {
                    kind: StmtKind::VarDecl {
                        name: Ident("x".into()),
                        initializer: Expr {
                            kind: ExprKind::Term(Term::Literal(Literal::Integer(10))),
                            span: Span::new(10, 12),
                        }
                        .into(),
                    },
                    span: Span::new(2, 13),
                }
                .into()]),
                span: Span::new(0, 15),
            },
        );
        assert_parse(
            "{ var x = 10; print x; }",
            Stmt {
                kind: StmtKind::Block(vec![
                    Stmt {
                        kind: StmtKind::VarDecl {
                            name: Ident("x".into()),
                            initializer: Expr {
                                kind: ExprKind::Term(Term::Literal(Literal::Integer(10))),
                                span: Span::new(10, 12),
                            }
                            .into(),
                        },
                        span: Span::new(2, 13),
                    }
                    .into(),
                    Stmt {
                        kind: StmtKind::Print(Expr {
                            kind: ExprKind::Term(Term::Ident(Ident("x".into()))),
                            span: Span::new(20, 21),
                        }),
                        span: Span::new(14, 22),
                    }
                    .into(),
                ]),
                span: Span::new(0, 24),
            },
        );
    }

    #[test]
    fn parse_if_stmt() {
        assert_parse!(
            "if(true) print 10;",
            Stmt {
                kind: StmtKind::If {
                    condition: Expr {
                        kind: ExprKind::Term(Term::Literal(Literal::True)),
                        ..
                    },
                    then_branch,
                    else_branch: None,
                },
                ..
            } if *then_branch => Stmt {
                    kind: StmtKind::Print(Expr {
                    kind: ExprKind::Term(Term::Literal(Literal::Integer(10))),
                    ..
                }),
                ..
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
                        }
                        .into()]),
                        span: Span { base: 13, len: 44 },
                    })
                    .into(),
                    else_branch: Some(
                        Box::new(Stmt {
                            kind: StmtKind::Block(vec![Stmt {
                                kind: StmtKind::Print(Expr {
                                    kind: ExprKind::Term(Term::Literal(Literal::True)),
                                    span: Span { base: 87, len: 4 },
                                }),
                                span: Span { base: 81, len: 11 },
                            }
                            .into()]),
                            span: Span { base: 63, len: 43 },
                        })
                        .into(),
                    ),
                },
                span: Span { base: 0, len: 106 },
            },
        );
    }

    #[test]
    fn parse_while_stmt() {
        assert_parse!(
            "while (true) print 10;",
            Stmt {
                kind: StmtKind::While {
                    condition: Expr {
                        kind: ExprKind::Term(Term::Literal(Literal::True)),
                        ..
                    },
                    stmt,
                },
            ..
            } if *stmt => Stmt {
                kind: StmtKind::Print(Expr {
                    kind: ExprKind::Term(Term::Literal(Literal::Integer(10))),
                    ..
                }),
                ..
            }
        );
    }

    #[test]
    fn parse_deffun_stmt() {
        assert_parse!(
            "fun x(){}",
            Stmt {
                kind: StmtKind::FunDecl(FunDecl { name, params, .. }),
                ..
            } if name == Ident("x".into()) && params.is_empty()
        );
        assert_parse!(
            "fun add(a, b) { print a + b; }",
            Stmt {
                kind: StmtKind::FunDecl(FunDecl { name, params, .. }),
                ..
            } if name == Ident("add".into()) && params == vec![Ident("a".into()), Ident("b".into())]
        );
        assert_parse_err!(
            "fun add(a, b) print a + b;",
            Stmt,
            LoxError::SyntaxError { .. }
        );
    }

    #[test]
    fn parse_return_stmt() {
        assert_parse!(
            "return;",
            Stmt {
                kind: StmtKind::Return(None),
                ..
            }
        );

        assert_parse!(
            "return 42;",
            Stmt {
                kind: StmtKind::Return(expr),
                ..
            } if expr == Some(
                Rc::new(
                    Expr {
                        kind: ExprKind::Term(Term::Literal(Literal::Integer(42))),
                        span: Span::new(7, 9),
                    },
                )
            )
        );
    }

    #[test]
    fn parse_class_decl() {
        assert_parse(
            r#"
class Breakfast {
  cook() {
    print "Eggs a-fryin'!";
  }

  serve(who) {
    print "Enjoy your breakfast";
  }
}
            "#,
            ClassDecl {
                name: Ident("Breakfast".to_string()),
                methods: vec![
                    FunDecl {
                        name: Ident("cook".to_string()),
                        params: vec![],
                        body: vec![Rc::new(Stmt {
                            kind: StmtKind::Print(Expr {
                                kind: ExprKind::Term(Term::Literal(Literal::String(
                                    "Eggs a-fryin'!".to_string(),
                                ))),
                                span: Span::new(40, 56),
                            }),
                            span: Span::new(34, 57),
                        })],
                    },
                    FunDecl {
                        name: Ident("serve".to_string()),
                        params: vec![Ident("who".to_string())],
                        body: vec![Rc::new(Stmt {
                            kind: StmtKind::Print(Expr {
                                kind: ExprKind::Term(Term::Literal(Literal::String(
                                    "Enjoy your breakfast".to_string(),
                                ))),
                                span: Span::new(88, 110),
                            }),
                            span: Span::new(82, 111),
                        })],
                    },
                ],
            },
        );
    }
}
