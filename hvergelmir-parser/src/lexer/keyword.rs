use crate::syntax::{ParseError, ParseErrorType};


#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Keyword {
    Function,
    Let,
    Return,
    While
}

impl Keyword {
    pub fn require(self, m: Self) -> Result<Self, ParseError> {
        if m == self {
            Ok(self)
        } else {
            Err(ParseError::new::<Self>( ParseErrorType::WrongKeyword { expected: m, found: self }))
        }
    }
}


pub fn try_keyword(s: &str) -> Option<Keyword> {
    match s { 
        "func" => Some(Keyword::Function),
        "let" => Some(Keyword::Let),
        "return" => Some(Keyword::Return),
        "while" => Some(Keyword::While),
        _ => None
    }
}