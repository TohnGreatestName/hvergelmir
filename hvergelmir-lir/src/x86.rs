use hvergelmir_x86_64::{MemOrReg, Register, X86Assembler, EAX, EBX, ECX, EDX};

use crate::{Instruction, LIRFunction, Value};

pub const REGISTER_TABLE: [Register; 4] = [EAX, EBX, ECX, EDX];


fn translate_value(v: Value) -> MemOrReg {
    match v {
        Value::Register(register) => {
            MemOrReg::register(REGISTER_TABLE[register.number as usize])
        },
        Value::Memory(memory) => todo!(),
    }
}

pub fn translate(v: LIRFunction) -> Vec<u8> {
    let mut asm = X86Assembler::new();

    for inst in v.instructions {
        match inst {
            Instruction::Add(dst, src) => {
                asm.add_reg(translate_value(dst), translate_value(src));
            }
            Instruction::Subtract(dst, src) => {
                asm.sub_reg(translate_value(dst), translate_value(src));
            }
            Instruction::MoveImmediate(dst, imm) => {
                asm.mov_imm32(translate_value(dst), imm.value as u32);
            }
            Instruction::Return(val) => {
                let src = translate_value(val);
                asm.mov_reg(MemOrReg::register(EAX), src);  
                asm.ret();
            }
            _ => todo!()
        }
    }



    asm.finish()


}

// #[cfg(test)]
// mod tests {
//     use crate::{x86::translate, Instruction, LIRFunction, Literal, Register, Value};

//     #[test]
//     fn simple_translate() {
//         let mut f = LIRFunction {
//             instructions: vec![
//                 Instruction::MoveImmediate(Value::Register(Register {
//                     number: 0,
//                     bit_width: 5
//                 }), Literal {
//                     value: 9,
//                     bit_width: 5
//                 }),
//                 Instruction::MoveImmediate(Value::Register(Register {
//                     number: 1,
//                     bit_width: 5
//                 }), Literal {
//                     value: 10,
//                     bit_width: 5
//                 }),
//                 Instruction::Add(Value::Register(Register {
//                     number: 0,
//                     bit_width: 5
//                 }), Value::Register(Register {
//                     number: 1,
//                     bit_width: 5
//                 })),
//                 Instruction::Return(Value::Register(Register {
//                     number: 0,
//                     bit_width: 5
//                 }))
//             ]
//         };

//         panic!("T: {:?}", hex::encode(translate(f)));
//     }
// }