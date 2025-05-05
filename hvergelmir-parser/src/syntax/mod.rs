pub mod ast;
use std::convert::identity;

use enum_downcast::IntoVariant;
use snafu::{whatever, ResultExt, Snafu, Whatever};
use stream::{TokenStream, TokenStreamError};

use crate::lexer::{keyword::Keyword, token_types::TokenValue, Token};

mod stream;

/// The overall context passed down the parser, immutably.
pub struct ParsingContext {}

#[derive(Debug, Snafu, Clone)]
pub enum ParseError {
    
    TokenStreamError {
        #[snafu(source)]
        source: TokenStreamError
    },
    WrongKeyword {
        expected: Keyword,
        found: Keyword,
    },
}


impl TryInto<TokenStreamError> for ParseError {
    type Error = Self;

    fn try_into(self) -> Result<TokenStreamError, Self> {
        match self {
            ParseError::TokenStreamError { source } => Ok(source),
            s => Err(s),
        }
    }
}
impl From<TokenStreamError> for ParseError {
    fn from(value: TokenStreamError) -> Self {
        Self::TokenStreamError { source: value }
    }
}
pub trait Parseable: Sized {
    fn parse(c: &ParsingContext, token_stream: &mut TokenStream) -> Result<Self, ParseError>;
}

impl<T> Parseable for Token<T>
where
    TokenValue: IntoVariant<T>,
{
    fn parse(c: &ParsingContext, token_stream: &mut TokenStream) -> Result<Self, ParseError> {
        Ok(token_stream.next_as::<T>()?)
    }
}

#[cfg(test)]
mod tests {
    use snafu::{whatever, FromString, ResultExt, Whatever};
    use string_interner::DefaultStringInterner;

    use crate::{
        lexer::{
            lexer,
            token_types::{Arrow, Dot, Identifier},
            CharStream, Token,
        },
        parse_one_of,
    };

    use super::{stream::TokenStream, ParseError, Parseable};

    #[derive(Debug)]
    pub struct IdentifierThenArrow {
        ident: Token<Identifier>,
        arrow: Token<Arrow>,
    }

    impl Parseable for IdentifierThenArrow {
        fn parse(
            c: &super::ParsingContext,
            token_stream: &mut super::stream::TokenStream,
        ) -> Result<Self, ParseError> {
            let ident = token_stream.next_as::<Identifier>()?;
            token_stream.stack_entry_mut().ambiguous = false;
            let a = token_stream.next_as::<Arrow>()?;
            Ok(Self { ident, arrow: a })
        }
    }

    #[test]
    pub fn ident_parse_test() {
        let mut symbols = DefaultStringInterner::new();
        let binding = lexer(CharStream::new("hello->"), &mut symbols).unwrap();
        let mut v = TokenStream::new(&binding, symbols);

        let mut output = v
            .parse::<IdentifierThenArrow>(&super::ParsingContext {})
            .unwrap();
        assert_eq!(
            v.symbols().resolve(output.ident.value().symbol),
            Some("hello")
        );
    }
    #[test]
    pub fn one_of_parse_test() {
        let mut symbols = DefaultStringInterner::new();
        let binding = lexer(CharStream::new("["), &mut symbols).unwrap();
        let mut v = TokenStream::new(&binding, symbols);
        let ctx = super::ParsingContext {};
    }
}
