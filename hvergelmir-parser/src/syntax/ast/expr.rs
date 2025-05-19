use crate::{
    lexer::{
        token_types::{
            Add, Divide, Identifier, LeftParenthesis, Multiply, Number, RightParenthesis, Subtract,
        },
        Token,
    },
    parse_one_of,
};

use super::super::{stream::TokenStream, ParseError, Parseable, ParsingContext};
#[derive(Debug)]
pub enum Expr {
    Factor(Box<Factor>),
}

impl Parseable for Expr {
    fn parse(c: &ParsingContext, token_stream: &mut TokenStream) -> Result<Self, ParseError> {
        let factor = token_stream.parse_one::<Factor>(c)?; // Use parse_one
        Ok(Expr::Factor(Box::new(factor)))
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
