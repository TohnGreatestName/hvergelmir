use std::ops::Div;

use enum_downcast::EnumDowncast;
use string_interner::symbol::SymbolU32;

use super::keyword::Keyword;


macro_rules! dataless_tokens_def {
    ($($i:ident),*) => {
        $(
            #[derive(Debug, Clone, Copy)]
            pub struct $i;
        )*
    };
}
dataless_tokens_def!(
    Dot,
    Multiply,
    Divide,
    Add,
    Subtract,
    Colon,
    EqualsAssign,
    EqualsCompare,
    LessThan,
    LessThanOrEqualTo,
    GreaterThan,
    GreaterThanOrEqualTo,
    LeftParenthesis,
    RightParenthesis,
    LeftSquareBracket,
    RightSquareBracket,
    LeftCurlyBracket,
    RightCurlyBracket,
    Arrow
);

#[derive(Clone, Copy, Debug)]
pub struct Identifier {
    pub symbol: SymbolU32
}

#[derive(Clone, Copy, Debug)]
pub struct StringToken {
    pub symbol: SymbolU32
}

#[derive(Clone, Copy, Debug)]
pub struct Number {
    pub value: (i64, i64), // (mantissa, exponent)
}

#[derive(EnumDowncast, Debug, Clone, Copy)]
pub enum TokenValue {
    Dot(Dot),
    Multiply(Multiply),
    Divide(Divide),
    Add(Add),
    Subtract(Subtract),
    Colon(Colon),
    EqualsAssign(EqualsAssign),
    EqualsCompare(EqualsCompare),
    LessThan(LessThan),
    LessThanOrEqualTo(LessThanOrEqualTo),
    GreaterThan(GreaterThan),
    GreaterThanOrEqualTo(GreaterThanOrEqualTo),
    LeftParenthesis(LeftParenthesis),
    RightParenthesis(RightParenthesis),
    LeftSquareBracket(LeftSquareBracket),
    RightSquareBracket(RightSquareBracket),
    LeftCurlyBracket(LeftCurlyBracket),
    RightCurlyBracket(RightCurlyBracket),
    Arrow(Arrow),
    Keyword(Keyword),
    Identifier(Identifier),
    StringToken(StringToken),
    Number(Number),
}