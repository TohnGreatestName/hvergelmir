pub mod keyword;
pub mod token_types;
use std::{iter::Peekable, str::Chars};

use enum_downcast::{EnumDowncast, IntoVariant};
use keyword::{try_keyword, Keyword};
use snafu::Snafu;
use string_interner::{symbol::SymbolU32, DefaultStringInterner};
use token_types::{
    Add, Arrow, Colon, Divide, Dot, EqualsAssign, EqualsCompare, GreaterThan, GreaterThanOrEqualTo,
    Identifier, LeftCurlyBracket, LeftParenthesis, LeftSquareBracket, LessThan, LessThanOrEqualTo,
    Multiply, Number, RightCurlyBracket, RightParenthesis, RightSquareBracket, StringToken, Subtract,
    TokenValue,
};

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
#[derive(Debug, Clone, Copy)]
pub struct Span {
    pub start: CharPosition,
    pub end: CharPosition,
}
impl Span {
    pub fn new(start: CharPosition, end: CharPosition) -> Self {
        Self { start, end }
    }
}

/// A parsed token, from the lexer.
#[derive(Debug, Clone, Copy)]
pub struct GenericToken {
    value: TokenValue,
    span: Span,
}

impl GenericToken {
    pub fn value(&self) -> &TokenValue {
        &self.value
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn make_concrete<T>(self) -> Result<Token<T>, Self> where TokenValue: IntoVariant<T> {
        self.value
            .enum_downcast::<T>()
            .map(|v| Token {
                value: v,
                span: self.span,
            })
            .map_err(|e| GenericToken {
                value: e,
                span: self.span,
            })
    }
}

#[derive(Debug)]
pub struct Token<T> {
    value: T,
    span: Span,
}

impl<T> Token<T> {
    pub fn value(self) -> T {
        self.value
    }
    pub fn value_ref(&self) -> &T {
        &self.value
    }
}

pub struct CharStream<'a> {
    chars: Peekable<Chars<'a>>,
    current_position: CharPosition,
    last_pop: CharPosition,
}
#[derive(Clone, Copy)]
pub enum SkipWhitespace {
    No,
    Yes,
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

    pub fn next_one_matches(
        &mut self,
        ws: SkipWhitespace,
        f: impl Fn(char) -> bool,
    ) -> Option<char> {
        if self.peek(ws).map(f) == Some(true) {
            self.next(ws)
        } else {
            None
        }
    }

    pub fn next_one_is(&mut self, c: char) -> bool {
        self.next_one_matches(SkipWhitespace::Yes, |v| v == c)
            .is_some()
    }

    pub fn pop_span(&mut self) -> Span {
        let s = Span::new(self.last_pop, self.current_position);
        self.last_pop = self.current_position;
        s
    }

    pub fn make_token(&mut self, t: TokenValue) -> GenericToken {
        GenericToken {
            value: t,
            span: self.pop_span(),
        }
    }
}

#[derive(Debug, Snafu)]
pub enum LexerError {
    #[snafu(display("Unexpected end of file at {position:?}."))]
    UnexpectedEndOfFile { position: CharPosition },
    #[snafu(display("Unclosed quote at {span:?}."))]
    UnclosedQuote { span: Span },
}

pub fn lexer(
    mut char_stream: CharStream,
    symbol_table: &mut DefaultStringInterner,
) -> Result<Vec<GenericToken>, LexerError> {
    let mut tokens = vec![];
    while let Some(next_peek) = char_stream.next(SkipWhitespace::Yes) {
        let ty = match next_peek {
            '.' => TokenValue::Dot(Dot),
            '*' => TokenValue::Multiply(Multiply),
            '/' => TokenValue::Divide(Divide),
            '+' => TokenValue::Add(Add),
            '-' => {
                if char_stream.next_one_is('>') {
                    TokenValue::Arrow(Arrow)
                } else {
                    TokenValue::Subtract(Subtract)
                }
            }
            ':' => TokenValue::Colon(Colon),
            '=' => {
                if char_stream.next_one_is('=') {
                    TokenValue::EqualsCompare(EqualsCompare)
                } else {
                    TokenValue::EqualsAssign(EqualsAssign)
                }
            }
            '<' => {
                if char_stream.next_one_is('=') {
                    TokenValue::LessThanOrEqualTo(LessThanOrEqualTo)
                } else {
                    TokenValue::LessThan(LessThan)
                }
            }
            '>' => {
                if char_stream.next_one_is('=') {
                    TokenValue::GreaterThanOrEqualTo(GreaterThanOrEqualTo)
                } else {
                    TokenValue::GreaterThan(GreaterThan)
                }
            }
            '(' => TokenValue::LeftParenthesis(LeftParenthesis),
            ')' => TokenValue::RightParenthesis(RightParenthesis),
            '[' => TokenValue::LeftSquareBracket(LeftSquareBracket),
            ']' => TokenValue::RightSquareBracket(RightSquareBracket),
            '{' => TokenValue::LeftCurlyBracket(LeftCurlyBracket),
            '}' => TokenValue::RightCurlyBracket(RightCurlyBracket),
            '"' => {
                let mut s = String::new();
                while !char_stream.next_one_is('"') {
                    s.push(char_stream.next(SkipWhitespace::No).ok_or_else(|| {
                        LexerError::UnclosedQuote {
                            span: char_stream.pop_span(),
                        }
                    })?);
                }
                TokenValue::StringToken(StringToken {
                    symbol: symbol_table.get_or_intern(s),
                })
            }
            v if v.is_alphabetic() => {
                let mut s = v.to_string();
                while let Some(next_char) =
                    char_stream.next_one_matches(SkipWhitespace::No, |v| v.is_alphanumeric())
                {
                    s.push(next_char);
                }
                println!("S: {:?}", s);
                if let Some(kw) = try_keyword(&s) {
                    TokenValue::Keyword(kw)
                } else {
                    TokenValue::Identifier(Identifier {
                        symbol: symbol_table.get_or_intern(s),
                    })
                }
            }
            v if v.is_numeric() => {
                let mut s = v.to_string();
                let mut has_decimal = false;
                while let Some(next_char) = char_stream.next_one_matches(SkipWhitespace::No, |v| v.is_numeric() || v == '.') {
                    if next_char == '.' {
                        if has_decimal {
                            break; // Stop if a second decimal point is encountered
                        }
                        has_decimal = true;
                    }
                    s.push(next_char);
                }
                let value = if has_decimal {
                    let parts: Vec<&str> = s.split('.').collect();
                    let integer_part = parts[0].parse::<i64>().unwrap();
                    let fractional_part = parts[1];
                    let exponent = fractional_part.len() as i64;
                    let mantissa = format!("{}{}", integer_part, fractional_part).parse::<i64>().unwrap();
                    (mantissa, -exponent)
                } else {
                    (s.parse::<i64>().unwrap(), 0)
                };
                TokenValue::Number(Number { value })
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
    use string_interner::{DefaultStringInterner, StringInterner};

    use crate::lexer::{keyword::Keyword, token_types::TokenValue, SkipWhitespace, Token};

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
        let mut interner = DefaultStringInterner::new();
        let lexed = lexer(CharStream::new(" hello -> [  four ] "), &mut interner).unwrap();
        let mut iter = lexed.iter();
        let TokenValue::Identifier(ref i) = iter.next().unwrap().value else {
            panic!()
        };
        assert_eq!(interner.resolve(i.symbol).unwrap(), "hello");
        assert!(matches!(iter.next().unwrap().value, TokenValue::Arrow(_)));
        assert!(matches!(
            iter.next().unwrap().value,
            TokenValue::LeftSquareBracket(_)
        ));
        let TokenValue::Identifier(ref i) = iter.next().unwrap().value else {
            panic!()
        };
        assert_eq!(interner.resolve(i.symbol).unwrap(), "four");
        assert!(matches!(
            iter.next().unwrap().value,
            TokenValue::RightSquareBracket(_)
        ));
    }

    #[test]
    fn lexer_test_2() {
        let mut interner = DefaultStringInterner::new();
        let lexed = lexer(
            CharStream::new("func epic(number: int32) -> int64 { \"hello\" }"),
            &mut interner,
        )
        .unwrap();
        let mut iter = lexed.iter();

        assert!(matches!(
            iter.next().unwrap().value,
            TokenValue::Keyword(Keyword::Function)
        ));
        let TokenValue::Identifier(ref i) = iter.next().unwrap().value else {
            panic!()
        };
        assert_eq!(interner.resolve(i.symbol).unwrap(), "epic");
        assert!(matches!(
            iter.next().unwrap().value,
            TokenValue::LeftParenthesis(_)
        ));
        let TokenValue::Identifier(ref i) = iter.next().unwrap().value else {
            panic!()
        };
        assert_eq!(interner.resolve(i.symbol).unwrap(), "number");
        assert!(matches!(iter.next().unwrap().value, TokenValue::Colon(_)));
        let TokenValue::Identifier(ref i) = iter.next().unwrap().value else {
            panic!()
        };
        assert_eq!(interner.resolve(i.symbol).unwrap(), "int32");
        assert!(matches!(
            iter.next().unwrap().value,
            TokenValue::RightParenthesis(_)
        ));
        assert!(matches!(iter.next().unwrap().value, TokenValue::Arrow(_)));

        let TokenValue::Identifier(ref i) = iter.next().unwrap().value else {
            panic!()
        };
        assert_eq!(interner.resolve(i.symbol).unwrap(), "int64");

        assert!(matches!(
            iter.next().unwrap().value,
            TokenValue::LeftCurlyBracket(_)
        ));
        let TokenValue::StringToken(ref i) = iter.next().unwrap().value else {
            panic!()
        };
        assert_eq!(interner.resolve(i.symbol).unwrap(), "hello");
        assert!(matches!(
            iter.next().unwrap().value,
            TokenValue::RightCurlyBracket(_)
        ));
    }
}
