//! The low-level close-to-assembly intermediate representation.

use std::{collections::HashMap, ffi::{CStr, CString}};

use generational_arena::Arena;
use hvergelmir_x86_64::Label;
mod x86;
mod mir;
mod builder;
pub type RegisterID = u32;
pub trait Platform {

    type InternalRegister;

    fn address_width() -> u32;
    fn register(r: Register) -> Self::InternalRegister;
}

#[derive(Debug)]
pub struct Register {
    /// Platform-dependent register indicator.
    number: RegisterID,
    /// Bit width, as 2^(bit_width)
    bit_width: u8
}
#[derive(Debug)]
pub struct Literal {
    value: i64,
    /// 2^(bit_width)
    bit_width: u8
}

// FIXME: memory accesses
#[derive(Debug)]
pub struct Memory {
    pub reg: Register,
    pub offset: i32
}
#[derive(Debug)]
pub enum SymbolType {
    Function,
    Data
}

#[derive(Debug)]
pub struct Symbol {
    pub ty: SymbolType,
    pub local: bool,
    pub name: CString
}
#[derive(Debug)]
pub enum Value {
    Register(Register),
    Memory(Memory),
}
impl Value {
    pub fn bit_width(&self) -> u8 {
        match self {
            Self::Register(r) => r.bit_width,
            Self::Memory(r) => r.reg.bit_width
        }
    }
}
#[derive(Debug)]
pub enum ValueOrLiteral {
    Value(Value),
    Literal(Literal)
}
pub type LabelIndex = usize;
#[derive(Debug)]
pub enum Instruction {
    Label(LabelIndex),
    Add(Value, ValueOrLiteral),
    Subtract(Value, Value),
    Divide(Value, Value),
    Multiply(Value, Value),
    Move(Value, Value),
    MoveImmediate(Value, Literal),
    LessThan(Value, Value),
    GreaterThan(Value, Value),
    Return(Value),
    Call(Symbol),
    UnconditionalJump(LabelIndex),
    ConditionalJump(Value, LabelIndex),
    Push(Value),
    Pop(Value),
    AllocateStack(ValueOrLiteral),
    DeallocateStack(ValueOrLiteral),
    JumpIfZero(Value, LabelIndex),
    JumpIfNotZero(Value, LabelIndex),
    // src, offset
    ReadStack(Value, Literal),
    // dst, offset
    WriteStack(ValueOrLiteral, Literal)
}

pub struct LIRFunction {
    instructions: Vec<Instruction>,
    name: String
}