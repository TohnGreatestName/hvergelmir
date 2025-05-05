use crate::lexer::{
    token_types::{Add, Divide, LeftParenthesis, Multiply, Number, RightParenthesis, Subtract},
    Token,
};

use super::super::{stream::TokenStream, ParseError, Parseable, ParsingContext};
#[derive(Debug)]
pub enum Expr {
    Factor(Box<Factor>),
}

impl Expr {
    pub fn evaluate(&self) -> i32 {
        match self {
            Expr::Factor(factor) => factor.evaluate(),
        }
    }
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
    Parenthesised(Box<Expr>),
    Mul(Box<Term>, Token<Multiply>, Box<Term>),
    Div(Box<Term>, Token<Divide>, Box<Term>),
}

impl Term {
    pub fn evaluate(&self) -> i32 {
        match self {
            Term::Number(token) => token.value_ref().value.0 as i32,
            Term::Mul(left, _, right) => left.evaluate() * right.evaluate(),
            Term::Div(left, _, right) => left.evaluate() / right.evaluate(),
            Term::Parenthesised(expr) => expr.evaluate(),
        }
    }
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
            let start = token_stream.next_as::<Number>()?;
            token_stream.stack_entry_mut().ambiguous = false; // Mark as unambiguous
            Term::Number(start)
        };

        while token_stream.peek_as::<Multiply>().is_ok() || token_stream.peek_as::<Divide>().is_ok() {
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

impl Factor {
    pub fn evaluate(&self) -> i32 {
        match self {
            Factor::Term(term) => term.evaluate(),
            Factor::Add(left, _, right) => left.evaluate() + right.evaluate(),
            Factor::Subtract(left, _, right) => left.evaluate() - right.evaluate(),
        }
    }
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


    #[test]
    fn expr_evaluate_test() {
        let mut symbols = DefaultStringInterner::new();
        let binding = lexer(CharStream::new("1 + (6 * 2 - 4 + 100) / 3"), &mut symbols).unwrap();
        let mut chars = TokenStream::new(&binding, symbols);

        let expr = chars.parse_one::<Expr>(&super::ParsingContext {}).unwrap();

        assert_eq!(expr.evaluate(), 37); 
    }
}
