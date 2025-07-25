use std::ffi::CString;

use crate::{Instruction, LIRFunction};

pub struct LIRFunctionBuilder {
    name: String,
    instructions: Vec<Instruction>
}

impl LIRFunctionBuilder {
    pub fn new(name: String) -> Self {
        Self {
            name,
            instructions: vec![]
        }
    }

    pub fn finish(self) -> LIRFunction {
        LIRFunction {
            instructions: self.instructions,
            name: self.name
        }
    }
}