use enum_downcast::IntoVariant;
use snafu::{Snafu, Whatever};
use string_interner::DefaultStringInterner;

use crate::lexer::{
    lexer, token_types::{Arrow, TokenValue}, CharPosition, CharStream, GenericToken, LexerError, Token
};

use super::{ParseError, Parseable, ParsingContext};

pub struct ParseStackEntry {
    pub position: usize,
    pub ambiguous: bool,
}
impl Default for ParseStackEntry {
    fn default() -> Self {
        Self::new(0)
    }
}
impl ParseStackEntry {
    pub fn new(p: usize) -> Self {
        Self {
            position: p,
            ambiguous: true,
        }
    }
}

/// A peekable stream of tokens.
///
/// TODO: Perhaps merge with [`crate::lexer::CharStream`]?
pub struct TokenStream<'a> {
    tokens: &'a [GenericToken],
    symbol_table: DefaultStringInterner,
    /// The position stack, for parsing.
    position_stack: Vec<ParseStackEntry>,
}

#[derive(Snafu, Debug, Clone)]
pub enum TokenStreamError {
    #[snafu(display("Unexpected EOF encountered after {position:?}"))]
    UnexpectedEOF { position: Option<CharPosition> },
    #[snafu(display("Unexpected token encountered: {token:?}"))]
    UnexpectedToken { token: GenericToken },
}

pub trait ResultExt<T, E> {
    /// Turns an `EOF` error into an Option, ignoring all
    /// other error types.
    fn coalesce_eof(self) -> impl ResultExt<Option<T>, E>;
}

impl<T, E: TryInto<TokenStreamError> + Clone> ResultExt<T, E> for Result<T, E> {
    fn coalesce_eof(self) -> Result<Option<T>, E> {
        match self {
            Ok(v) => Ok(Some(v)),
            Err(e) => match e.clone().try_into() {
                Ok(TokenStreamError::UnexpectedEOF { .. }) => Ok(None),
                _ => Err(e),
            },
        }
    }
}



pub type TokenStreamResult<T> = Result<T, TokenStreamError>;


impl<'a> TokenStream<'a> {

    pub fn new(tokens: &'a [GenericToken], symbol_table: DefaultStringInterner) -> Self {
        Self {
            tokens,
            position_stack: vec![ParseStackEntry::default()],
            symbol_table,
        }
    }

    pub fn unambiguous(&mut self) {
        self.stack_entry_mut().ambiguous = false;
    }
    
    pub fn symbols(&self) -> &DefaultStringInterner {
        &self.symbol_table
    }

    pub fn stack_entry_mut(&mut self) -> &mut ParseStackEntry {
        self.position_stack
            .last_mut()
            .expect("Should always be a position on the stack.")
    }
    pub fn stack_entry(&self) -> &ParseStackEntry {
        self.position_stack
            .last()
            .expect("Should always be a position on the stack.")
    }

    pub fn position_mut(&mut self) -> &mut usize {
        &mut self.stack_entry_mut().position
    }
    pub fn position(&self) -> usize {
        self.stack_entry().position
    }

    pub fn last_token(&self) -> TokenStreamResult<GenericToken> {
        if self.position() == 0 {
            return Err(TokenStreamError::UnexpectedEOF { position: None });
        } else {
            match self.tokens.get(self.position() - 1) {
                Some(t) => Ok(*t),
                None => return Err(TokenStreamError::UnexpectedEOF { position: None }),
            }
        }
    }

    pub fn peek(&self) -> TokenStreamResult<GenericToken> {
        match self.tokens.get(self.position()).copied() {
            Some(t) => Ok(t),
            None => {
                return Err(TokenStreamError::UnexpectedEOF {
                    position: Some(self.last_token()?.span().end),
                })
            }
        }
    }

    pub fn peek_as<T>(&self) -> TokenStreamResult<Token<T>>
    where
        TokenValue: IntoVariant<T>,
    {
        self.peek()?.make_concrete::<T>().map_err(|e| TokenStreamError::UnexpectedToken { token: e })
    }

    /// FIXME: distinguish between EOF and invalid token
    pub fn next_as<T>(&mut self) -> TokenStreamResult<Token<T>>
    where
        TokenValue: IntoVariant<T>,
    {
        let v = self.peek_as::<T>()?;
        self.advance();
        Ok(v)
    }

    pub fn next(&mut self) -> TokenStreamResult<GenericToken> {
        let t = self.peek()?;
        self.advance();
        Ok(t)
    }

    pub fn advance(&mut self) {
        *self.position_mut() += 1;
    }

    pub fn push_stack(&mut self) {
        let p = self.position();
        self.position_stack.push(ParseStackEntry::new(p));
    }

    pub fn pop_stack(&mut self, advance: bool) {
        let v = self.position_stack.pop();
        assert!(
            !self.position_stack.is_empty(),
            "Emptied the position stack!"
        );;
        if advance {
            *self.position_mut() = v.unwrap().position;
        }
    }
    pub fn parse<T: Parseable>(&mut self, c: &ParsingContext) -> Result<T, ParseError> {
        self.push_stack();
        match T::parse(c, self) {
            Ok(v) => {
                self.pop_stack(true);
                Ok(v)
            }
            Err(e) => Err(e), // up to caller to handle.
        }
    }

    pub fn parse_one<T: Parseable>(&mut self, c: &ParsingContext) -> Result<T, ParseError> {
        match self.parse(c) {
            Ok(v) => Ok(v),
            Err(e) => {
                self.pop_stack(false);
                Err(e)
            }
        }
    }
}
#[macro_export]
macro_rules! parse_one_of {
    ($ts:expr, $ctx:expr, $(
        [$node:ty : $ident:ident] => $block:block
    ),*) => {

        'pblk: {
            let mut errors_list = vec![];
            let initial_position = $ts.position();
            $(
                let val = $ts.parse::<$node>($ctx);
                match val {
                    Err(e) => {
                        if !$ts.stack_entry().ambiguous {
                            break 'pblk Err(e);
                        } else {
                            errors_list.push(($ts.position() - initial_position, e));
                            $ts.pop_stack(false);
                        }
                    },
                    Ok($ident) => {
                        break 'pblk ($block);
                    }
                }
            )*

            errors_list.sort_by(|a, b| a.0.cmp(&b.0));
            break 'pblk Err(errors_list.pop().unwrap().1);
        }

    };
}
