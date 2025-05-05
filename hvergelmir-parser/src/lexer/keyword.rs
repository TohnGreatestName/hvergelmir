
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Keyword {
    Function,
    Let
}


pub fn try_keyword(s: &str) -> Option<Keyword> {
    match s { 
        "func" => Some(Keyword::Function),
        "let" => Some(Keyword::Let),
        _ => None
    }
}