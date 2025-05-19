use crate::{lexer::{keyword::Keyword, token_types::{Arrow, Colon, Identifier, LeftCurlyBracket, LeftParenthesis, RightCurlyBracket, RightParenthesis}, Token}, syntax::{stream::{self, TokenStream}, Parseable, ParsingContext}};

use super::statement::Statement;
use enum_downcast::EnumDowncast;
use stream::ResultExt;

#[derive(Debug)]
pub struct File {
    pub definitions: Vec<Definition>,
}

impl Parseable for File {
    fn parse(c: &ParsingContext, token_stream: &mut TokenStream) -> Result<Self, crate::syntax::ParseError> {
        let mut definitions = Vec::new();
        while let Some(def) = token_stream.parse_one::<Definition>(c).coalesce_eof()? {
            definitions.push(def);
        }
        Ok(File { definitions })
    }
}
#[derive(Debug, EnumDowncast)]
pub enum Definition {
    FunctionDefinition(FunctionDefinition)
}
impl Parseable for Definition {
    fn parse(c: &ParsingContext, token_stream: &mut TokenStream) -> Result<Self, crate::syntax::ParseError> {
        let func_def = token_stream.parse_one::<FunctionDefinition>(c)?;
        Ok(Definition::FunctionDefinition(func_def))
    }
}
#[derive(Debug)]
pub enum Type {
    Primitive(Token<Identifier>)
}

impl Parseable for Type {
    fn parse(c: &ParsingContext, token_stream: &mut TokenStream) -> Result<Self, crate::syntax::ParseError> {
        let token = token_stream.next_as::<Identifier>()?;
        Ok(Type::Primitive(token))
    }
}

#[derive(Debug)]
pub struct FunctionParameter {
    pub name: Token<Identifier>,
    pub colon: Token<Colon>,
    pub ty: Box<Type>,
}
impl Parseable for FunctionParameter {
    fn parse(c: &ParsingContext, token_stream: &mut TokenStream) -> Result<Self, crate::syntax::ParseError> {
        let name = token_stream.next_as::<Identifier>()?;
        let colon = token_stream.next_as::<Colon>()?;
        let ty = token_stream.parse_one(c)?;
        Ok(FunctionParameter {
            name,
            colon,
            ty: Box::new(ty),
        })
    }
}

#[derive(Debug)]
pub struct Block {
    pub left_brace: Token<LeftCurlyBracket>,
    pub statements: Vec<Statement>,
    pub right_brace: Token<RightCurlyBracket>,
}

impl Parseable for Block {
    fn parse(c: &ParsingContext, token_stream: &mut TokenStream) -> Result<Self, crate::syntax::ParseError> {
        let left_brace = token_stream.next_as::<LeftCurlyBracket>()?;
        token_stream.stack_entry_mut().ambiguous = false;
        let mut statements = Vec::new();
        while token_stream.peek_as::<RightCurlyBracket>().is_err() {
            statements.push(token_stream.parse_one(c)?);
        }
        let right_brace = token_stream.next_as::<RightCurlyBracket>()?;
        Ok(Block {
            left_brace,
            statements,
            right_brace,
        })
    }
}
#[derive(Debug)]
pub struct FunctionDefinition {
    pub func_token: Token<Keyword>,
    pub name: Token<Identifier>,
    pub left_parenthesis: Token<LeftParenthesis>,
    pub parameters: Vec<FunctionParameter>,
    pub right_parenthesis: Token<RightParenthesis>,
    pub returns: Option<(Token<Arrow>, Box<Type>)>,
    pub block: Block
}
impl Parseable for FunctionDefinition {
    fn parse(c: &ParsingContext, token_stream: &mut TokenStream) -> Result<Self, crate::syntax::ParseError> {
        let func_token = token_stream.next_as::<Keyword>()?.map(|v| v.require(Keyword::Function))?;
        token_stream.stack_entry_mut().ambiguous = false;
        let name = token_stream.next_as::<Identifier>()?;
        let left_parenthesis = token_stream.next_as::<LeftParenthesis>()?;
        let mut parameters = Vec::new();
        while token_stream.peek_as::<Identifier>().is_ok() {
            parameters.push(token_stream.parse_one(c)?);
            if token_stream.peek_as::<RightParenthesis>().is_ok() {
                break;
            }
        }
        let right_parenthesis = token_stream.next_as::<RightParenthesis>()?;
        let returns = if let Ok(t) = token_stream.peek_as::<Arrow>() {
            Some((t, Box::new(token_stream.parse_one(c)?)))
        } else {
            None
        };
        Ok(FunctionDefinition {
            func_token,
            name,
            left_parenthesis,
            parameters,
            right_parenthesis,
            returns,
            block: token_stream.parse_one(c)?,
        })
    }
}



#[cfg(test)]
mod tests {
    use string_interner::DefaultStringInterner;

    use crate::{lexer::{lexer, CharStream}, syntax::{stream::TokenStream, ParsingContext}};

    use super::File;

    #[test]
    fn file_test() {
        let mut symbols = DefaultStringInterner::new();
        let lexed = lexer(CharStream::new(r"
        
        func epic() {
            let x = 2
            return x + 7
        }
        
        "), &mut symbols).unwrap();
        let mut ts = TokenStream::new(&lexed, symbols);

        let mut file = ts.parse_one::<File>(&ParsingContext {}).unwrap();



        panic!("{:#?}", file);

    }
}