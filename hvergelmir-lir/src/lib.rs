//! The low-level close-to-assembly intermediate representation.
mod x86;
mod mir;
pub type RegisterID = u32;
pub trait Platform {
    fn address_width() -> u32;
    fn general_purpose_registers() -> &'static [RegisterID];
}


pub struct Register {
    /// Platform-dependent register indicator.
    number: RegisterID,
    /// Bit width, as 2^(bit_width)
    bit_width: u8
}
pub struct Literal {
    value: u64,
    /// 2^(bit_width)
    bit_width: u8
}

// FIXME: memory accesses
pub enum Memory {

}

pub enum Value {
    Register(Register),
    Memory(Memory),
}
pub type InstructionIndex = usize;
pub enum Instruction {
    Add(Value, Value),
    Subtract(Value, Value),
    Divide(Value, Value),
    Multiply(Value, Value),
    Move(Value, Value),
    MoveImmediate(Value, Literal),
    LessThan(Value, Value),
    GreaterThan(Value, Value),
    Return(Value),
    UnconditionalJump(InstructionIndex),
    ConditionalJump(Value, InstructionIndex)
}

pub struct LIRFunction {
    instructions: Vec<Instruction>
}