#[derive(Debug)]
pub enum Keyword {
    Function
}
pub fn try_keyword(s: &str) -> Option<Keyword> {
    match s { 
        "func" => Some(Keyword::Function),
        _ => None
    }
}