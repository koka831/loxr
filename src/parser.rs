use std::iter::Peekable;

use crate::{
    ast::{BinOp, Binary, Expr, Literal, NumberKind, UnOp, Unary},
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

impl<'a> Parse<'a> for BinOp {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self> {
        use TokenKind::*;

        let token = parser.peek()?;
        let op = match token.kind {
            EqEq => BinOp::Equal,
            BangEq => BinOp::NotEqual,
            Lt => BinOp::Lt,
            LtEq => BinOp::Leq,
            Gt => BinOp::Gt,
            GtEq => BinOp::Geq,
            Plus => BinOp::Plus,
            Minus => BinOp::Minus,
            Star => BinOp::Mul,
            Slash => BinOp::Div,
            _ => return parser.unexpected_token(token),
        };

        parser.next()?;
        Ok(op)
    }
}

impl<'a> Parse<'a> for Binary<'a> {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self> {
        let lhs = parser.parse()?;
        let op = parser.parse()?;
        let rhs = parser.parse()?;

        Ok(Binary {
            lhs: Box::new(lhs),
            op,
            rhs: Box::new(rhs),
        })
    }
}

impl<'a> Parse<'a> for UnOp {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self> {
        let token = parser.peek()?;
        let op = match token.kind {
            TokenKind::Bang => UnOp::Not,
            TokenKind::Minus => UnOp::Minus,
            _ => return parser.unexpected_token(token),
        };

        parser.next()?;
        Ok(op)
    }
}

impl<'a> Parse<'a> for Unary<'a> {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self> {
        let op = parser.parse()?;
        let rhs = parser.parse()?;
        Ok(Unary {
            op,
            rhs: Box::new(rhs),
        })
    }
}

impl<'a> Parse<'a> for Expr<'a> {
    fn parse(parser: &mut Parser<'a>) -> ParseResult<'a, Self> {
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
}
