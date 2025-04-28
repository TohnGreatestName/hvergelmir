mod keyword;
use std::{iter::Peekable, str::Chars};

use keyword::{try_keyword, Keyword};
use snafu::Snafu;

/// A character position, line and column,
/// in a source file.
#[derive(Debug, Clone, Copy)]
pub struct CharPosition {
    line: usize,
    col: usize,
}

impl CharPosition {
    pub fn new(col: usize, line: usize) -> Self {
        Self { line, col }
    }
}

/// A span, in a file.
#[derive(Debug)]
pub struct Span {
    start: CharPosition,
    end: CharPosition,
}
impl Span {
    pub fn new(start: CharPosition, end: CharPosition) -> Self {
        Self { start, end }
    }
}

/// A parsed token, from the lexer.
#[derive(Debug)]
pub struct Token {
    value: TokenType,
    span: Span,
}

pub struct CharStream<'a> {
    chars: Peekable<Chars<'a>>,
    current_position: CharPosition,
    last_pop: CharPosition,
}
#[derive(Clone, Copy)]
pub enum SkipWhitespace {
    No,
    Yes
}
impl SkipWhitespace {
    pub fn skip(&self) -> bool {
        matches!(self, SkipWhitespace::Yes)
    }
}
impl<'a> CharStream<'a> {
    pub fn new(s: &'a str) -> Self {
        Self {
            chars: s.chars().peekable(),
            current_position: CharPosition::new(0, 0),
            last_pop: CharPosition::new(0, 0),
        }
    }

    pub fn peek(&mut self, ws: SkipWhitespace) -> Option<char> {
        let c = loop {
            let c = *self.chars.peek()?;
            if c.is_whitespace() && ws.skip() {
                self.chars.next(); // swallow it
            }
            if c == '\n' {
                self.current_position.line += 1;
            } else {
                self.current_position.col += 1;
            }
            if c.is_whitespace() && ws.skip() {
                continue;
            } else {
                self.current_position.col -= 1;
                break c;
            }
        };
        Some(c)
    }

    pub fn next(&mut self, ws: SkipWhitespace) -> Option<char> {
        let p = self.peek(ws)?;
        self.chars.next();
        self.current_position.col += 1;
        Some(p)
    }


    pub fn next_one_matches(&mut self, ws: SkipWhitespace, f: impl Fn(char) -> bool) -> Option<char> {
        if self.peek(ws).map(f) == Some(true) {
            self.next(ws)
        } else {
            None
        }
    }

    pub fn next_one_is(&mut self, c: char) -> bool {
        self.next_one_matches(SkipWhitespace::Yes, |v| v == c).is_some()
    }

    pub fn pop_span(&mut self) -> Span {
        let s = Span::new(self.last_pop, self.current_position);
        self.last_pop = self.current_position;
        s
    }

    pub fn make_token(&mut self, t: TokenType) -> Token {
        Token {
            value: t,
            span: self.pop_span(),
        }
    }
}
#[derive(Debug)]
pub enum TokenType {
    Dot,
    Multiply,
    Divide,
    Add,
    Subtract,
    Colon,
    EqualsAssign,
    EqualsCompare,
    LessThan,
    LessThanOrEqualTo,
    GreaterThan,
    GreaterThanOrEqualTo,
    LeftParenthesis,
    RightParenthesis,
    LeftSquareBracket,
    RightSquareBracket,
    LeftCurlyBracket,
    RightCurlyBracket,
    Arrow,
    Keyword(Keyword),
    // TODO: Probably intern these. Ha.
    Identifier(String),
    String(String),
    //
}

#[derive(Debug, Snafu)]
pub enum LexerError {
    #[snafu(display("Unexpected end of file at {position:?}."))]
    UnexpectedEndOfFile { position: CharPosition },
    #[snafu(display("Unclosed quote at {span:?}."))]
    UnclosedQuote { span: Span },
}

pub fn lexer(mut char_stream: CharStream) -> Result<Vec<Token>, LexerError> {
    let mut tokens = vec![];
    while let Some(next_peek) = char_stream.next(SkipWhitespace::Yes) {
        let ty = match next_peek {
            '.' => TokenType::Dot,
            '*' => TokenType::Multiply,
            '/' => TokenType::Divide,
            '+' => TokenType::Add,
            '-' => {
                if char_stream.next_one_is('>') {
                    TokenType::Arrow
                } else {
                    TokenType::Subtract
                }
            }
            ':' => TokenType::Colon,
            '=' => {
                if char_stream.next_one_is('=') {
                    TokenType::EqualsCompare
                } else {
                    TokenType::EqualsAssign
                }
            }
            '<' => {
                if char_stream.next_one_is('=') {
                    TokenType::LessThanOrEqualTo
                } else {
                    TokenType::LessThan
                }
            }
            '>' => {
                if char_stream.next_one_is('=') {
                    TokenType::GreaterThanOrEqualTo
                } else {
                    TokenType::GreaterThan
                }
            }
            '(' => TokenType::LeftParenthesis,
            ')' => TokenType::RightParenthesis,
            '[' => TokenType::LeftSquareBracket,
            ']' => TokenType::RightSquareBracket,
            '{' => TokenType::LeftCurlyBracket,
            '}' => TokenType::RightCurlyBracket,
            '"' => {
                let mut s = String::new();
                while !char_stream.next_one_is('"') {
                    s.push(
                        char_stream
                            .next(SkipWhitespace::No)
                            .ok_or_else(|| LexerError::UnclosedQuote {
                                span: char_stream.pop_span(),
                            })?,
                    );
                }
                TokenType::String(s)
            }
            v if v.is_alphabetic() => {
                let mut s = v.to_string();
                while let Some(next_char) = char_stream.next_one_matches(SkipWhitespace::No, |v| v.is_alphanumeric()) {
                    s.push(next_char);
                }
                println!("S: {:?}", s);
                if let Some(kw) = try_keyword(&s) {
                    TokenType::Keyword(kw)
                } else {
                    TokenType::Identifier(s)
                }
            }
            _ => {
                return Err(LexerError::UnexpectedEndOfFile {
                    position: char_stream.current_position,
                })
            }
        };
        tokens.push(char_stream.make_token(ty));
    }
    Ok(tokens)
}

#[cfg(test)]
mod tests {
    use crate::lexer::{keyword::Keyword, SkipWhitespace, TokenType};

    use super::{lexer, CharStream};

    #[test]
    fn char_stream_test() {
        let mut s = CharStream::new(
            "{ g  b 
}  ",
        );
        assert_eq!(s.next(SkipWhitespace::Yes), Some('{'));
        assert_eq!(s.next(SkipWhitespace::Yes), Some('g'));
        assert_eq!(s.next(SkipWhitespace::Yes), Some('b'));
        assert_eq!(s.next(SkipWhitespace::Yes), Some('}'));
        let span = s.pop_span();
        assert_eq!(span.start.col, 0);
        assert_eq!(span.start.line, 0);
        assert_eq!(span.end.col, 8);
        assert_eq!(span.end.line, 1);
    }

    #[test]
    fn lexer_test() {
        let lexed = lexer(CharStream::new(" hello -> [  four ] ")).unwrap();
        let mut iter = lexed.iter();
        let TokenType::Identifier(ref i) = iter.next().unwrap().value else {
            panic!()
        };
        assert_eq!(i, "hello");
        assert!(matches!(iter.next().unwrap().value, TokenType::Arrow));
        assert!(matches!(iter.next().unwrap().value, TokenType::LeftSquareBracket));
        let TokenType::Identifier(ref i) = iter.next().unwrap().value else {
            panic!()
        };
        assert_eq!(i, "four");
        assert!(matches!(iter.next().unwrap().value, TokenType::RightSquareBracket));
    }

    #[test]
    fn lexer_test_2() {
        let lexed = lexer(CharStream::new("func epic(number: int32) -> int64 { \"hello\" }")).unwrap();
        let mut iter = lexed.iter();


        assert!(matches!(iter.next().unwrap().value, TokenType::Keyword(Keyword::Function)));
        let TokenType::Identifier(ref i) = iter.next().unwrap().value else {
            panic!()
        };
        assert_eq!(i, "epic");
        assert!(matches!(iter.next().unwrap().value, TokenType::LeftParenthesis));
        let TokenType::Identifier(ref i) = iter.next().unwrap().value else {
            panic!()
        };
        assert_eq!(i, "number");
        assert!(matches!(iter.next().unwrap().value, TokenType::Colon));
        let TokenType::Identifier(ref i) = iter.next().unwrap().value else {
            panic!()
        };
        assert_eq!(i, "int32");
        assert!(matches!(iter.next().unwrap().value, TokenType::RightParenthesis));
        assert!(matches!(iter.next().unwrap().value, TokenType::Arrow));

        let TokenType::Identifier(ref i) = iter.next().unwrap().value else {
            panic!()
        };
        assert_eq!(i, "int64");

        assert!(matches!(iter.next().unwrap().value, TokenType::LeftCurlyBracket));
        let TokenType::String(ref i) = iter.next().unwrap().value else {
            panic!()
        };
        assert_eq!(i, "hello");
        assert!(matches!(iter.next().unwrap().value, TokenType::RightCurlyBracket));

    }
}
