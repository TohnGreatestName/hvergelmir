use crate::{
    lexer::{
        keyword::Keyword,
        token_types::{
            Add, Divide, GreaterThan, Identifier, LeftParenthesis, LessThan, Multiply, Number, RightParenthesis, Subtract
        },
        Token,
    },
    parse_one_of,
};

use super::{
    super::{stream::TokenStream, ParseError, Parseable, ParsingContext},
    definition::Block,
};

#[derive(Debug)]
pub enum Expr {
    Factor(Box<Factor>),
    While(Box<WhileExpression>)
}

impl Parseable for Expr {
    fn parse(c: &ParsingContext, token_stream: &mut TokenStream) -> Result<Self, ParseError> {
        parse_one_of!(token_stream, c,
            [Factor : factor] => {
                Ok(Expr::Factor(Box::new(factor)))
            },
            [WhileExpression : wh] => {
                Ok(Expr::While(Box::new(wh)))
            }
        )
    }
}
#[derive(Debug)]
pub struct WhileExpression {
    pub while_token: Token<Keyword>,
    pub expr: Expr,
    pub block: Block,
}

impl Parseable for WhileExpression {
    fn parse(c: &ParsingContext, token_stream: &mut TokenStream) -> Result<Self, ParseError> {
        let while_token = token_stream
            .next_as::<Keyword>()?
            .map(|v| v.require(Keyword::While))?;
        token_stream.unambiguous();
        let expr = token_stream.parse_one::<Expr>(c)?;
        let block = token_stream.parse_one::<Block>(c)?;
        Ok(Self {
            while_token,
            expr,
            block
        })
    }
}

#[derive(Debug)]
pub enum Term {
    Number(Token<Number>),
    Ident(Token<Identifier>),
    Parenthesised(Box<Expr>),
    Mul(Box<Term>, Token<Multiply>, Box<Term>),
    Div(Box<Term>, Token<Divide>, Box<Term>),
}

impl Parseable for Term {
    fn parse(c: &ParsingContext, token_stream: &mut TokenStream) -> Result<Self, ParseError> {
        let mut left = if token_stream.peek_as::<LeftParenthesis>().is_ok() {
            token_stream.next_as::<LeftParenthesis>()?;
            token_stream.stack_entry_mut().ambiguous = false; // Mark as unambiguous
            let expr = token_stream.parse_one::<Expr>(c)?; // Use parse_one
            token_stream.next_as::<RightParenthesis>()?;
            Term::Parenthesised(Box::new(expr))
        } else {
            let v = parse_one_of!(token_stream, c,
            [Token<Number> : n] => {
                Ok(Term::Number(n))
            },
            [Token<Identifier> : i] => {
                Ok(Term::Ident(i))
            }
            )?;

            token_stream.stack_entry_mut().ambiguous = false; // Mark as unambiguous
            v
        };

        while token_stream.peek_as::<Multiply>().is_ok() || token_stream.peek_as::<Divide>().is_ok()
        {
            if token_stream.peek_as::<Multiply>().is_ok() {
                let op = token_stream.next_as::<Multiply>()?;

                let right = token_stream.parse_one::<Term>(c)?; // Use parse_one
                left = Term::Mul(Box::new(left), op, Box::new(right));
            } else if token_stream.peek_as::<Divide>().is_ok() {
                let op = token_stream.next_as::<Divide>()?;

                let right = token_stream.parse_one::<Term>(c)?; // Use parse_one
                left = Term::Div(Box::new(left), op, Box::new(right));
            }
        }

        Ok(left)
    }
}

#[derive(Debug)]
pub enum Factor {
    Term(Box<Term>),
    Add(Box<Factor>, Token<Add>, Box<Term>),
    Subtract(Box<Factor>, Token<Subtract>, Box<Term>),

    LessThan(Box<Factor>, Token<LessThan>, Box<Term>),
    GreaterThan(Box<Factor>, Token<GreaterThan>, Box<Term>)
}

impl Parseable for Factor {
    fn parse(c: &ParsingContext, token_stream: &mut TokenStream) -> Result<Self, ParseError> {
        let mut left = Factor::Term(Box::new(token_stream.parse_one::<Term>(c)?)); // Use parse_one
        token_stream.stack_entry_mut().ambiguous = false; // Mark as unambiguous

        while token_stream.peek_as::<Add>().is_ok() || token_stream.peek_as::<Subtract>().is_ok() {
            if token_stream.peek_as::<Add>().is_ok() {
                let op = token_stream.next_as::<Add>()?;

                let right = token_stream.parse_one::<Term>(c)?; // Use parse_one
                left = Factor::Add(Box::new(left), op, Box::new(right));
            } else if token_stream.peek_as::<Subtract>().is_ok() {
                let op = token_stream.next_as::<Subtract>()?;

                let right = token_stream.parse_one::<Term>(c)?; // Use parse_one
                left = Factor::Subtract(Box::new(left), op, Box::new(right));
            }
        }

        while token_stream.peek_as::<LessThan>().is_ok() || token_stream.peek_as::<GreaterThan>().is_ok() {
            if token_stream.peek_as::<LessThan>().is_ok() {
                let op = token_stream.next_as::<LessThan>()?;

                let right = token_stream.parse_one::<Term>(c)?; // Use parse_one
                left = Factor::LessThan(Box::new(left), op, Box::new(right));
            } else if token_stream.peek_as::<GreaterThan>().is_ok() {
                let op = token_stream.next_as::<GreaterThan>()?;

                let right = token_stream.parse_one::<Term>(c)?; // Use parse_one
                left = Factor::GreaterThan(Box::new(left), op, Box::new(right));
            }
        }

        Ok(left)
    }
}

#[cfg(test)]
mod tests {
    use string_interner::DefaultStringInterner;

    use crate::{
        lexer::{lexer, CharStream},
        syntax::stream::TokenStream,
    };

    use super::Expr;

    // #[test]
    // fn expr_evaluate_test() {
    //     let mut symbols = DefaultStringInterner::new();
    //     let binding = lexer(CharStream::new("1 + (6 * 2 - 4 + 100) / 3"), &mut symbols).unwrap();
    //     let mut chars = TokenStream::new(&binding, symbols);

    //     let expr = chars.parse_one::<Expr>(&super::ParsingContext {}).unwrap();

    //     assert_eq!(expr.evaluate(), 37);
    // }
}
