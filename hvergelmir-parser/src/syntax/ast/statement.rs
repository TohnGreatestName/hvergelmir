use crate::{lexer::{keyword::Keyword, token_types::{EqualsAssign, Identifier}, Token}, parse_one_of, syntax::{stream::TokenStream, ParseError, Parseable, ParsingContext}};

use super::expr::Expr;

#[derive(Debug)]
pub enum Statement {
    VariableDeclaration(VariableDeclaration)
}

impl Parseable for Statement {
    fn parse(c: &ParsingContext, token_stream: &mut TokenStream) -> Result<Self, ParseError> {
        parse_one_of!(token_stream, c,
            [VariableDeclaration : vdecl] => {
                Ok(Statement::VariableDeclaration(vdecl))
            }
        )
    }
}

#[derive(Debug)]
pub struct VariableDeclaration {
    let_token: Token<Keyword>,
    name: Token<Identifier>,
    equals_token: Token<EqualsAssign>,
    value: Box<Expr>,
}

impl Parseable for VariableDeclaration {
    fn parse(c: &ParsingContext, token_stream: &mut TokenStream) -> Result<Self, ParseError> {
        let let_token = token_stream.next_as::<Keyword>()?;
        if *let_token.value_ref() != Keyword::Let {
            return Err(ParseError::WrongKeyword {
                expected: Keyword::Let,
                found: *let_token.value_ref(),
            });
        }

        token_stream.stack_entry_mut().ambiguous = false;
        let name = token_stream.next_as::<Identifier>()?;
        let equals_token = token_stream.next_as::<EqualsAssign>()?;
        let value = token_stream.parse_one(c)?;
        Ok(VariableDeclaration {
            let_token,
            name,
            equals_token,
            value: Box::new(value),
        })
    }
}