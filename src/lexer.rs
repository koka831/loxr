use std::{iter::Peekable, str::CharIndices};

use crate::{
    error::LexError,
    span::{BytePos, Span},
    token::{NumberKind, Token, TokenKind},
};

type Lexed<'s> = Option<Token<'s>>;
type LexResult<'s> = std::result::Result<Lexed<'s>, LexError>;

pub struct Lexer<'source> {
    source: &'source str,
    chars: Peekable<CharIndices<'source>>,
    pos: BytePos,
}

impl<'s> Lexer<'s> {
    pub fn new(source: &str) -> Lexer<'_> {
        Lexer {
            source,
            chars: source.char_indices().peekable(),
            pos: 0,
        }
    }

    #[tracing::instrument(skip(self))]
    pub fn lex(&mut self) -> LexResult<'s> {
        tracing::debug!("current cursor: {}", self.pos);

        while self.eat_ws()? {}

        if let Some(lexed) = self.lex_number()? {
            return Ok(Some(lexed));
        }

        if let Some(lexed) = self.lex_str()? {
            return Ok(Some(lexed));
        }

        if let Some(lexed) = self.lex_symbol()? {
            return Ok(Some(lexed));
        }

        if let Some(lexed) = self.lex_ident()? {
            return Ok(Some(lexed));
        }

        Ok(None)
    }

    fn next(&mut self) -> Option<(usize, char)> {
        let next = self.chars.next();
        if next.is_some() {
            self.pos += 1;
        }

        next
    }

    fn peek(&mut self) -> Option<&(usize, char)> {
        self.chars.peek()
    }

    #[tracing::instrument(skip(self))]
    fn lex_str(&mut self) -> LexResult<'s> {
        let Some(from) = self.eat_char('"') else {
            return Ok(None);
        };

        self.eat_while(|c| c != '"');

        if self.eat_char('"').is_none() {
            let span = Span::new(from, self.pos);
            return Err(LexError::UnterminatedString(span));
        };

        Ok(Some(Token {
            // current pos is at the closing `"`
            kind: TokenKind::String(&self.source[from + 1..self.pos - 1]),
            // includes surrounding `"`
            span: Span::new(from, self.pos),
        }))
    }

    #[tracing::instrument(skip(self))]
    fn lex_number(&mut self) -> LexResult<'s> {
        let pos = self.pos;

        match self.eat_number() {
            Ok(Some(integral)) => {
                if self.eat_str(".").is_none() {
                    let kind = TokenKind::Number(NumberKind::Integer(integral));
                    let span = Span::new(pos, self.pos);
                    return Ok(Some(Token { kind, span }));
                }

                // given literal contains fractional part
                let Ok(Some(_)) = self.eat_number() else {
                    return Err(LexError::InvalidNumber(Span::new(pos, self.pos)));
                };

                let span = Span::new(pos, self.pos);
                let float = self.source[pos..self.pos]
                    .parse()
                    .map_err(|_| LexError::InvalidNumber(span))?;
                let kind = TokenKind::Number(NumberKind::Float(float));
                Ok(Some(Token { kind, span }))
            }
            Ok(None) => Ok(None),
            Err(e) => Err(e),
        }
    }

    #[tracing::instrument(skip(self))]
    fn eat_number(&mut self) -> Result<Option<i32>, LexError> {
        let is_integer = |c: char| c.is_ascii_digit();
        let Some(from) = self.eat_matches(is_integer) else {
            return Ok(None);
        };

        let num_str = match self.eat_while(is_integer) {
            Some(len) => &self.source[from..=from + len],
            // met EOF
            None => &self.source[from..],
        };

        let span = Span::from_len(from, num_str.len());
        let num = num_str.parse().map_err(|_| LexError::InvalidNumber(span))?;
        Ok(Some(num))
    }

    #[tracing::instrument(skip(self))]
    fn lex_symbol(&mut self) -> LexResult<'s> {
        use TokenKind::*;

        let pos = self.pos;
        let Some((_, c)) = self.peek() else {
            return Ok(None);
        };

        let token = match c {
            '(' => LParen,
            ')' => RParen,
            '{' => LBrace,
            '}' => RBrace,
            ',' => Comma,
            '.' => Dot,
            '-' => Minus,
            '+' => Plus,
            ';' => Semicolon,
            '*' => Star,
            '/' => Slash,
            '=' => {
                self.next();

                let token = match self.eat_char('=') {
                    Some(_) => EqEq,
                    _ => Eq,
                };

                let span = Span::from_len(pos, self.pos - pos);
                let token = Token::new(token, span);

                return Ok(Some(token));
            }
            '!' => {
                self.next();

                let token = match self.eat_char('=') {
                    Some(_) => BangEq,
                    _ => Bang,
                };

                let span = Span::from_len(pos, self.pos - pos);
                let token = Token::new(token, span);

                return Ok(Some(token));
            }
            '<' => {
                self.next();

                let token = match self.eat_char('=') {
                    Some(_) => Leq,
                    _ => Lt,
                };

                let span = Span::from_len(pos, self.pos - pos);
                let token = Token::new(token, span);

                return Ok(Some(token));
            }
            '>' => {
                self.next();

                let token = match self.eat_char('=') {
                    Some(_) => Geq,
                    _ => Gt,
                };

                let span = Span::from_len(pos, self.pos - pos);
                let token = Token::new(token, span);

                return Ok(Some(token));
            }
            _ => {
                // it's not a symbol, identifier maybe.
                return Ok(None);
            }
        };

        // consume peeked cursor
        self.next();

        let span = Span::from_len(pos, self.pos - pos);
        let token = Token::new(token, span);

        Ok(Some(token))
    }

    #[tracing::instrument(skip(self))]
    fn lex_ident(&mut self) -> LexResult<'s> {
        use TokenKind::*;

        let pos = self.pos;
        // ident must not start with number
        let first_char = |c: char| c.is_ascii_alphabetic() || c == '_';
        if self.eat_matches(first_char).is_none() {
            return Ok(None);
        };
        self.eat_while(|c| c.is_ascii_alphanumeric() || c == '_');

        let ident_str = &self.source[pos..self.pos];
        let span = Span::new(pos, self.pos);

        let kind = match ident_str {
            "and" => And,
            "class" => Class,
            "else" => Else,
            "false" => False,
            "fun" => Fun,
            "for" => For,
            "if" => If,
            "nil" => Nil,
            "or" => Or,
            "print" => Print,
            "return" => Return,
            "super" => Super,
            "true" => True,
            "var" => Var,
            "while" => While,
            _ => Ident(ident_str),
        };

        Ok(Some(Token { kind, span }))
    }

    // if `peek`ed character == `want`, consume the character and return its position
    fn eat_char(&mut self, want: char) -> Option<usize> {
        self.eat_matches(|c| c == want)
    }

    fn eat_matches<F: Fn(char) -> bool>(&mut self, matcher: F) -> Option<usize> {
        match self.peek() {
            Some((pos, c)) if matcher(*c) => {
                let pos = *pos;
                self.next();
                Some(pos)
            }
            _ => None,
        }
    }

    /// Consume the iterator while the given condition `cond` is satisfied.
    /// Once the condition is no longer satisfied, return consumed byte length.
    fn eat_while<F: Fn(char) -> bool>(&mut self, cond: F) -> Option<usize> {
        let pos = self.pos;
        while self.eat_matches(&cond).is_some() {}
        Some(self.pos - pos)
    }

    /// consume source if the source starts with the given pat, return consumed byte length
    fn eat_str(&mut self, pat: &str) -> Option<usize> {
        let len = pat.len();
        if self.source[self.pos..].starts_with(pat) {
            self.chars.nth(len - 1);
            self.pos += len;
            Some(len)
        } else {
            None
        }
    }

    fn eat_ws(&mut self) -> Result<bool, LexError> {
        Ok(self.eat_matches(char::is_whitespace).is_some() || self.eat_line_comment())
    }

    fn eat_line_comment(&mut self) -> bool {
        if self.eat_str("//").is_none() {
            return false;
        }

        while let Some((_, c)) = self.next() {
            if c == '\n' {
                break;
            }
        }

        true
    }
}

impl<'s> Iterator for Lexer<'s> {
    type Item = Result<Token<'s>, LexError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.lex().transpose()
    }
}

#[cfg(test)]
mod test_lex {
    use super::*;
    use crate::token::{NumberKind, TokenKind::*};

    fn lex(source: &str) -> Result<Vec<Token<'_>>, LexError> {
        Lexer::new(source).collect()
    }

    macro_rules! assert_lex {
        ($source:expr, $expect:expr $(,)*) => {
            let lexed = lex($source)
                .unwrap()
                .iter()
                .map(|t| t.kind.clone())
                .collect::<Vec<_>>();
            assert_eq!(lexed, $expect);
        };
    }

    macro_rules! assert_lex_error {
        // $errkind: LexErrorKind
        ($input:expr, $errkind:pat) => {
            match lex($input).unwrap_err() {
                $errkind => { /* ok */ }
                e => panic!("did not match to error kind : {}", e),
            }
        };
    }

    #[test]
    fn lex_symbol() {
        let lexed = lex(";").unwrap();
        assert_eq!(lexed[0].kind, Semicolon);
        assert_eq!(lexed[0].span, Span::new(0, 1));
        assert_lex!("! != =", vec![Bang, BangEq, Eq]);
        assert_lex!("== = ===", vec![EqEq, Eq, EqEq, Eq]);
        assert_lex!(
            "(()){}",
            vec![LParen, LParen, RParen, RParen, LBrace, RBrace],
        );
        assert_lex!(
            "!*+-/=<> <= ==",
            vec![Bang, Star, Plus, Minus, Slash, Eq, Lt, Gt, Leq, EqEq],
        );
    }

    #[test]
    fn lex_string() {
        let lexed = lex(r#""hello""#).unwrap();
        assert_eq!(lexed[0].kind, String("hello"));
        assert_eq!(lexed[0].span, Span::new(0, 7));

        // unterminated string
        assert_lex_error!(r#""abc"#, LexError::UnterminatedString(..));

        // accepts multiline string
        assert_eq!(lex(r#""xxx\nxxx""#).unwrap()[0].kind, String("xxx\\nxxx"));
    }

    #[test]
    fn lex_number() {
        let lexed = lex("12345").unwrap();
        assert_eq!(lexed[0].kind, Number(NumberKind::Integer(12345)));
        assert_eq!(lexed[0].span, Span::new(0, 5));

        assert_eq!(
            lex("123.45").unwrap()[0].kind,
            Number(NumberKind::Float(123.45))
        );
        assert_eq!(lex("123.45").unwrap()[0].span, Span::new(0, 6));
        assert_lex_error!("123.", LexError::InvalidNumber(..));
        assert_lex_error!("123.a", LexError::InvalidNumber(..));
    }

    #[test]
    fn lex_ident() {
        let lexed = lex("foo").unwrap();
        assert_eq!(lexed[0].kind, Ident("foo"));
        assert_eq!(lexed[0].span, Span::new(0, 3));

        assert_lex!(
            "and class else false fun for if nil or print return super true var while",
            vec![
                And, Class, Else, False, Fun, For, If, Nil, Or, Print, Return, Super, True, Var,
                While
            ],
        );
    }

    #[test]
    fn lex_stmt() {
        assert_lex!(r#"print "hi";"#, vec![Print, String("hi"), Semicolon]);
    }
}
