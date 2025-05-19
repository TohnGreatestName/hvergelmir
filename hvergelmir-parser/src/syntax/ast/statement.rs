use snafu::ResultExt;

use crate::{
    lexer::{
        keyword::Keyword,
        token_types::{EqualsAssign, Identifier},
        Token,
    },
    parse_one_of,
    syntax::{stream::TokenStream, ParseError, ParseErrorType, Parseable, ParsingContext, TokenStreamSnafu},
};

use super::expr::Expr;

#[derive(Debug)]
pub enum Statement {
    VariableDeclaration(VariableDeclaration),
    Assignment(Assignment),
    Return(ReturnStatement)
}

impl Parseable for Statement {
    fn parse(c: &ParsingContext, token_stream: &mut TokenStream) -> Result<Self, ParseError> {
        parse_one_of!(token_stream, c,
            [VariableDeclaration : vdecl] => {
                Ok(Statement::VariableDeclaration(vdecl))
            },
            [ReturnStatement : rtrn] => {
                Ok(Statement::Return(rtrn))
            },
            [Assignment : assign] => {
                Ok(Statement::Assignment(assign))
            }
        )
    }
}

#[derive(Debug)]
pub struct ReturnStatement {
    pub return_token: Token<Keyword>,
    pub value: Box<Expr>,
}

impl Parseable for ReturnStatement {
    fn parse(c: &ParsingContext, token_stream: &mut TokenStream) -> Result<Self, ParseError> {

        let return_token = token_stream
            .next_as::<Keyword>()?
            .map(|v| v.require(Keyword::Return))?;
        token_stream.unambiguous();
        
        let value = Box::new(token_stream.parse_one::<Expr>(c)?);
        Ok(Self {
            return_token,
            value,
        })
    }
}

#[derive(Debug)]
pub struct VariableDeclaration {
    pub let_token: Token<Keyword>,
    pub name: Token<Identifier>,
    pub equals_token: Token<EqualsAssign>,
    pub value: Box<Expr>,
}

impl Parseable for VariableDeclaration {
    fn parse(c: &ParsingContext, token_stream: &mut TokenStream) -> Result<Self, ParseError> {
        let let_token = token_stream.next_as::<Keyword>()?;
        if *let_token.value_ref() != Keyword::Let {
            return Err(ParseError::new::<Self>(ParseErrorType::WrongKeyword {
                expected: Keyword::Let,
                found: *let_token.value_ref(),
            }));
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

#[derive(Debug)]
pub struct Assignment {
    pub name: Token<Identifier>,
    pub equals_token: Token<EqualsAssign>,
    pub value: Box<Expr>,
}

impl Parseable for Assignment {
    fn parse(c: &ParsingContext, token_stream: &mut TokenStream) -> Result<Self, ParseError> {
        
        let name = token_stream.next_as::<Identifier>()?;
        let equals_token = token_stream.next_as::<EqualsAssign>()?;
        token_stream.stack_entry_mut().ambiguous = false;
        let value = token_stream.parse_one(c)?;
        Ok(Assignment {
            name,
            equals_token,
            value: Box::new(value),
        })
    }
}
