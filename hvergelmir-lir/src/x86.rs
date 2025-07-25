use std::{collections::HashMap, ffi::CString, mem, str::FromStr};

use hvergelmir_x86_64::{
    Displacement, EAX, EBX, ECX, EDI, EDX, ESI, Label, MemOrReg, R12, RAX, RBP, RBX, RDI, RDX, RSI,
    RSP, Register, RegisterMode, X86Assembler,
    hvergelmir_elf::{
        self, ELFHeader,
        section::{
            DataSection, Elf64AddendRelocation, RelocationSection, SymbolBinding, SymbolIndex,
            SymbolTableSection, SymbolType, SymbolVisibility,
        },
    },
    systemv_abi,
};

use crate::{Instruction, LIRFunction, LabelIndex, Symbol, Value, ValueOrLiteral};

pub const REGISTER_TABLE: [Register; 8] = [RAX, RBX, ECX, RDX, RDI, RSI, R12, RSP];

#[derive(Default)]
pub struct ModuleTranslator {
    code: Vec<u8>,
    relocations: Vec<Elf64AddendRelocation>,
    symbols: SymbolTableSection,
    labels: HashMap<usize, Label>,
}

impl ModuleTranslator {
    pub fn finish(mut self) -> ELFHeader {
        hvergelmir_elf::ELFHeader {
            abi: hvergelmir_elf::ABI::SystemV,
            file_type: hvergelmir_elf::FileType::Relocatable,
            architecture: hvergelmir_elf::MachineArchitecture::AMDx64,
            entry_point: 0,
            strings: hvergelmir_elf::section::StringTableSection::default(),
            symbols: self.symbols,
            program_data: hvergelmir_elf::section::ProgramDataSection { data: self.code },
            relocations: RelocationSection {
                relocation_target: 3,
                symbol_table: 2,
                relocations: self.relocations,
            },
            data: DataSection {
                data: "GRASS WORLD HAHAH this is a null-terminated string of any length!?!\0"
                    .as_bytes()
                    .to_vec(),
            },
        }
    }

    pub fn symbols(&mut self) -> &mut SymbolTableSection {
        &mut self.symbols
    }

    fn translate_value(&mut self, v: Value) -> MemOrReg {
        let width = v.bit_width();
        match v {
            Value::Register(register) => {
                MemOrReg::register(REGISTER_TABLE[register.number as usize])
            }
            Value::Memory(memory) => {
                let reg = MemOrReg::memory(REGISTER_TABLE[memory.reg.number as usize]);
                if memory.offset == 0 {
                    reg
                } else if let Ok(v) = TryInto::<i8>::try_into(memory.offset) {
                    reg.displace(Displacement::Disp8(v))
                } else {
                    reg.displace(Displacement::Disp32(memory.offset))
                }
            }
        }
        .mode(match width {
            5 => RegisterMode::Mode32,
            6 => RegisterMode::Mode64,
            3 => RegisterMode::Mode8,
            _ => panic!("unknown bit width"),
        })
    }

    fn resolve_symbol(&mut self, s: Symbol) -> SymbolIndex {
        if let Some((idx, _)) = self.symbols.get(&s.name) {
            println!("RECALLED SYMBOL {:?} = {:?}", s, idx);
            idx
        } else {
            // this is an unresolved symbol.
            assert!(!s.local, "local symbols cannot be unresolved");
            let sym = hvergelmir_elf::section::Symbol {
                ty: SymbolType::NoType,
                binding: SymbolBinding::Global,
                visibility: SymbolVisibility::Default,
                section: 0,
                offset: 0,
                size: 0,
            };
            let idx = self.symbols.add(&s.name, sym);
            println!("SYMBOL {:?} = {:?}", s, idx);
            idx
        }
    }

    pub fn define_symbol(&mut self, v: &LIRFunction) {
        self.symbols.add(
            &CString::from_str(&v.name).unwrap(),
            hvergelmir_elf::section::Symbol {
                ty: SymbolType::Function,
                binding: SymbolBinding::Global,
                visibility: SymbolVisibility::Default,
                // placeholders
                section: 3,
                offset: 0,
                size: 0,
            },
        );
    }

    fn resolve_label(&mut self, asm: &mut X86Assembler, i: LabelIndex) -> Label {
        *self.labels.entry(i).or_insert_with(|| asm.make_label())
    }

    pub fn translate(&mut self, v: LIRFunction) {
        let start_index = self.code.len();
        let mut asm = X86Assembler::new();
        asm.mov_reg(MemOrReg::register(RBP), MemOrReg::register(RSP));
        for inst in v.instructions {
            println!("INST! {:?}", inst);
            match inst {
                Instruction::Label(idx) => {
                    let label = self.resolve_label(&mut asm, idx);
                    if asm.hook_label(label) {
                        panic!("hey. label {:?} already hooked!", idx);
                    }
                }
                Instruction::Call(sym) => {
                    let sym = self.resolve_symbol(sym);
                    asm.near_call_symbol(sym);
                }
                Instruction::Move(dst, src) => {
                    asm.mov_reg(self.translate_value(dst), self.translate_value(src));
                }
                Instruction::Add(dst, src) => match src {
                    ValueOrLiteral::Value(value) => {
                        asm.add_reg(self.translate_value(dst), self.translate_value(value))
                    }
                    ValueOrLiteral::Literal(literal) => {
                        let state_before = asm.data().to_owned();
                        match literal.bit_width {
                            5 => asm.add_imm32(self.translate_value(dst), literal.value as i32),
                            3 => asm.add_imm8(self.translate_value(dst), literal.value as i8),
                            _ => panic!(),
                        };
                        if literal.bit_width == 3 {
                            //println!("here: {:#?} and {:#?}", state_before, asm.data())
                        }
                    }
                },
                Instruction::Subtract(dst, src) => {
                    asm.sub_reg(self.translate_value(dst), self.translate_value(src));
                }
                Instruction::MoveImmediate(dst, imm) => {
                    if imm.bit_width > 5 {
                        panic!("immediate too large.")
                    }

                    asm.mov_imm32(self.translate_value(dst), imm.value as u32);
                }
                Instruction::Return(val) => {
                    let src = self.translate_value(val);
                    asm.mov_reg(MemOrReg::register(EAX), src);
                    asm.ret();
                }
                Instruction::UnconditionalJump(idx) => {
                    let label = self.resolve_label(&mut asm, idx);
                    asm.jump_label(X86Assembler::near_jump_relative, label);
                }
                Instruction::Push(val) => {
                    asm.push_reg(self.translate_value(val));
                }
                Instruction::Pop(val) => {
                    asm.pop_reg(self.translate_value(val));
                }
                Instruction::AllocateStack(val) => match val {
                    ValueOrLiteral::Literal(a) => {
                        asm.sub_imm32(MemOrReg::register(RSP), a.value as i32);
                    }
                    ValueOrLiteral::Value(v) => {
                        asm.sub_reg(MemOrReg::register(RSP), self.translate_value(v));
                    }
                },
                Instruction::DeallocateStack(val) => match val {
                    ValueOrLiteral::Literal(a) => {
                        asm.add_imm32(MemOrReg::register(RSP), a.value as i32);
                    }
                    ValueOrLiteral::Value(v) => {
                        asm.add_reg(MemOrReg::register(RSP), self.translate_value(v));
                    }
                },
                Instruction::ReadStack(dst, offset) => {
                    asm.mov_reg(
                        self.translate_value(dst),
                        MemOrReg::memory(RBP)
                            .displace(Displacement::Disp32(-(offset.value as i32))),
                    );
                }
                Instruction::WriteStack(src, offset) => {
                    let dst = MemOrReg::memory(RBP)
                        .displace(Displacement::Disp32(-(offset.value as i32)));
                    match src {
                        ValueOrLiteral::Value(src) => {
                            asm.mov_reg(dst, self.translate_value(src));
                        }
                        ValueOrLiteral::Literal(src) => {
                            asm.mov_imm32(dst, src.value as u32);
                        }
                    }
                }
                Instruction::JumpIfZero(val, dest) => {
                    let label = self.resolve_label(&mut asm, dest);
                    asm.test_imm32(self.translate_value(val), 255);
                    asm.jump_label(X86Assembler::near_jump_relative_if_zero, label);
                }
                Instruction::JumpIfNotZero(val, dest) => {
                    let label = self.resolve_label(&mut asm, dest);
                    asm.test_imm32(self.translate_value(val), 255);
                    asm.jump_label(X86Assembler::near_jump_relative_if_nonzero, label);
                }

                _ => todo!(),
            }
        }
        let mut finished = asm.finish();

        let len = finished.0.len();

        self.code.extend_from_slice(&finished.0);

        for mut v in finished.1 {
            v.offset += start_index as u64;
            self.relocations.push(v);
        }

        let (_, internal_symbol) = self
            .symbols
            .get_mut(&CString::from_str(&v.name).unwrap())
            .expect("should have been preprocessed");
        internal_symbol.offset = start_index as u64;
        internal_symbol.size = len as u64;
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashMap};

    use crate::{
        Instruction, LIRFunction, Literal, Memory, Register, SymbolType, Value, ValueOrLiteral,
        x86::ModuleTranslator,
    };

    #[test]
    fn brainfrick_test() {
        #[derive(Debug)]
        enum BFInst {
            DataPointerOffset(i32),
            DataChange(i32),
            OutputByte,
            AcceptInput,
            JumpForwardIfZero,
            JumpBackIfNonZero,
        }
        const fn is_inst(c: char) -> bool {
            match c {
                '+' | '-' | '<' | '>' | '[' | ']' | ',' | '.' => true,
                _ => false
            }
        }
        pub fn lexer(s: &str) -> Vec<BFInst> {
            let mut insts = vec![];
            let mut iter = s.trim().chars().peekable();
            while let Some(ch) = iter.peek() {
                match ch {
                    '+' | '-' => {
                        let mut val = 0;
                        while let Some(ch) = iter.peek() {
                            match ch {
                                '+' => val += 1,
                                '-' => val -= 1,
                                v if is_inst(*v) => break,
                                _ => {
                                    iter.next();
                                    continue
                                },
                            }
                            iter.next();
                        }
                        insts.push(BFInst::DataChange(val));
                    }
                    '<' | '>' => {
                        let mut val = 0;
                        while let Some(ch) = iter.peek() {
                            match ch {
                                '>' => val += 1,
                                '<' => val -= 1,
                                v if is_inst(*v) => break,
                                _ => {
                                    iter.next();
                                    continue
                                },
                            }
                            iter.next();
                        }
                        insts.push(BFInst::DataPointerOffset(val));
                    }
                    '.' => {
                        iter.next();
                        insts.push(BFInst::OutputByte);
                    }
                    '[' => {
                        iter.next();
                        insts.push(BFInst::JumpForwardIfZero);
                    }
                    ']' => {
                        iter.next();
                        insts.push(BFInst::JumpBackIfNonZero);
                    }
                    ',' => {
                        iter.next();
                        insts.push(BFInst::AcceptInput)
                    }
                    _ => {
                        iter.next();
                    }
                }
            }
            insts
        }

        fn translate(v: &[BFInst]) -> Vec<Instruction> {
            let mut insts = vec![];

            insts.push(Instruction::AllocateStack(ValueOrLiteral::Literal(
                Literal {
                    value: 30_000,
                    bit_width: 5,
                },
            )));
            {
                insts.push(Instruction::Move(
                    Value::Register(Register {
                        number: 4,
                        bit_width: 6,
                    }),
                    Value::Register(Register {
                        number: 7,
                        bit_width: 6,
                    }),
                )); // first arg the data

                insts.push(Instruction::MoveImmediate(
                    Value::Register(Register {
                        number: 5,
                        bit_width: 6,
                    }),
                    Literal {
                        value: 0,
                        bit_width: 5,
                    },
                )); // second arg 0 (zeroes)

                insts.push(Instruction::MoveImmediate(
                    Value::Register(Register {
                        number: 3,
                        bit_width: 6,
                    }),
                    Literal {
                        value: 30_000,
                        bit_width: 5,
                    },
                )); // third (final) arg 30_000 (num bytes)

                insts.push(Instruction::Call(crate::Symbol {
                    ty: SymbolType::Function,
                    local: false,
                    name: c"memset".to_owned(),
                }));
            }

            insts.push(Instruction::Move(
                Value::Register(Register {
                    number: 6,
                    bit_width: 6,
                }),
                Value::Register(Register {
                    number: 7,
                    bit_width: 6,
                }),
            )); // r12 will be our data pointer register :)

            let mut label_index: usize = 0;
            let mut jumps_list = BTreeMap::new();
            for (idx, inst) in v.iter().enumerate() {
                match inst {
                    BFInst::JumpForwardIfZero => {
                        println!("FWD IDX {idx} = {label_index}");
                        jumps_list.insert(idx, (label_index, true));
                        label_index += 1;
                    }
                    BFInst::JumpBackIfNonZero => {
                        println!("BWD IDX {idx} = {label_index}");
                        jumps_list.insert(idx, (label_index, false));
                        label_index += 1;
                    }
                    _ => (),
                }
            }

            for (idx, v) in v.iter().enumerate() {
                match v {
                    BFInst::DataPointerOffset(offset) => {
                        insts.push(Instruction::Add(
                            Value::Register(Register {
                                number: 6,
                                bit_width: 6,
                            }),
                            ValueOrLiteral::Literal(Literal {
                                value: *offset as i64,
                                bit_width: 5,
                            }),
                        )); // add r12, (offset)
                    }
                    BFInst::DataChange(change) => {
                        insts.push(Instruction::Add(
                            Value::Memory(Memory {
                                reg: Register {
                                    number: 6,
                                    bit_width: 5,
                                },
                                offset: 0,
                            }),
                            ValueOrLiteral::Literal(Literal {
                                value: *change as i64,
                                bit_width: 3,
                            }),
                        )); // add [r12], (change)
                    }
                    BFInst::JumpForwardIfZero => {
                        let mut ctr = 0;
                        let range_iter = jumps_list.range((idx + 1)..);
                        let target = 'b: {
                            for (_, (label, is_forward)) in range_iter {
                                if ctr == 0 && !*is_forward {
                                    break 'b *label;
                                }
                                ctr += if *is_forward { 1 } else { -1 };
                            }
                            panic!();
                        };

                        insts.push(Instruction::JumpIfZero(
                            Value::Memory(Memory {
                                reg: Register {
                                    number: 6,
                                    bit_width: 5,
                                },
                                offset: 0,
                            }),
                            target,
                        ));

                        insts.push(Instruction::Label(jumps_list.get(&idx).unwrap().0));
                    }
                    BFInst::JumpBackIfNonZero => {
                        let range_iter = jumps_list.range(..idx).rev();
                        let mut ctr = 0;
                        let target = 'b: {
                            for (_, (label, is_forward)) in range_iter {
                                if ctr == 0 && *is_forward {
                                    break 'b *label;
                                }
                                ctr += if *is_forward { -1 } else { 1 };
                            }
                            panic!();
                        };

                        insts.push(Instruction::JumpIfNotZero(
                            Value::Memory(Memory {
                                reg: Register {
                                    number: 6,
                                    bit_width: 5,
                                },
                                offset: 0,
                            }),
                            target,
                        ));
                        insts.push(Instruction::Label(jumps_list.get(&idx).unwrap().0));
                    }
                    BFInst::AcceptInput => {
                        insts.push(Instruction::Call(crate::Symbol {
                            ty: SymbolType::Function,
                            local: false,
                            name: c"getchar".to_owned(),
                        }));

                        insts.push(Instruction::Move(
                            Value::Memory(Memory {
                                reg: Register {
                                    number: 6,
                                    bit_width: 3,
                                },
                                offset: 0,
                            }),
                            Value::Register(Register {
                                number: 0,
                                bit_width: 6,
                            }),
                        )); // second arg the data
                    }

                    BFInst::OutputByte => {
                        insts.push(Instruction::MoveImmediate(
                            Value::Register(Register {
                                number: 4,
                                bit_width: 6,
                            }),
                            Literal {
                                value: 1,
                                bit_width: 5,
                            },
                        )); // first arg 1 (stdout)

                        insts.push(Instruction::Move(
                            Value::Register(Register {
                                number: 5,
                                bit_width: 6,
                            }),
                            Value::Register(Register {
                                number: 6,
                                bit_width: 6,
                            }),
                        )); // second arg the data

                        insts.push(Instruction::MoveImmediate(
                            Value::Register(Register {
                                number: 3,
                                bit_width: 6,
                            }),
                            Literal {
                                value: 1,
                                bit_width: 5,
                            },
                        )); // third (final) arg 1 (num bytes)

                        insts.push(Instruction::Call(crate::Symbol {
                            ty: SymbolType::Function,
                            local: false,
                            name: c"write".to_owned(),
                        }));
                    }
                    _ => todo!(),
                }
            }
            insts.push(Instruction::MoveImmediate(
                Value::Register(Register {
                    number: 4,
                    bit_width: 6,
                }),
                Literal {
                    value: 0,
                    bit_width: 5,
                },
            )); // first arg 0 (exit code)

            insts.push(Instruction::Call(crate::Symbol {
                ty: SymbolType::Function,
                local: false,
                name: c"exit".to_owned(),
            }));
            insts
        }

        let bfinsts = lexer(r#"[SPDX-FileCopyrightText: Brainfuck Enterprise Solutions
 SPDX-License-Identifier: WTFPL]
[os.bf -- the source code of OS.bf, Brainfuck-based operating system.

 Commands:
 # text = commentary, noop.
 \n = noop.
 l = list existing files.
 s file contents = store the CONTENTS in FILE.
 p file = print FILE content.
 d file = delete the FILE.
 r script = run the code in SCRIPT on the OS.bf memory,
            starting from exit flag and extending to the left.
            Uses meta.bf.
 q = quit OS.bf.

 Working memory layout:
 [exit flag][0][case flag][command...]

 File layout:
 [name...][255][contents...]

 Filesystem layout:
 [0] [0] [0] [0] [file] [0] ... [file] [0] [file] [0] [0] [working memory]

 Code starts here:]

COPYRIGHT NOTICE:
+[------->++<]>+.++++.+[++>---<]>.+++[->++<]>.++++.[--->+<]>--.--[->++++<]>--.+[->+++<]>.+++++++++++++.+.----------.++++++.-.-[->+++++<]>-.[-->+++<]>.--.+++++.-.----.++.---.-[--->+<]>--.+++.[--->+<]>---.+[->+++<]>++.-[-->+<]>---.+++++++++++.>++++++++++..+[->++++++<]>+.+[--->+<]>+++.+.+++++++++.-------.---------.--.+.++++++++++++.[---->+<]>+++.++++++++.------[->++<]>-.-[--->++<]>---.---------.[-->+++<]>++.--.++.+.[--->++<]>--.[->++<]>+.--[----->+<]>-.++.+++++.----------.--.[->+++++<]>-.+[->++<]>.-[--->+<]>++++.---.+++.--------.++++++++.+++++++.>++++++++++.+[->++++++<]>+.+[--->+<]>+++.+.+++++++++.-------.---------.--.+.++++++++++++.[---->+<]>+++.++++++++.------[->++<]>-.-[--->++<]>---.---------.[-->+++<]>++.--.++.+.------.--[----->+<]>+.++.-------------.[--->+<]>----.++++[->+++<]>.+++++++++.++++++.[---->+<]>+++.+[->++<]>.---[----->+<]>-.+++[->+++<]>++.++++++++.+++++.--------.-[--->+<]>--.+[->+++<]>+.++++++++.-[++>---<]>+.++[->++<]>+.-[--->+<]>++.++++++.+++[->+++<]>.+++++++++++++.--.++.---------.++++++++++.++++[->+++<]>.--[--->+<]>-.>-[--->+<]>--.[--->+<]>--.---.+++++++++.-.-----------.++++++.-.+++++.+[---->+<]>+++.++++++[->++<]>.[-->+++<]>++.++[->+++<]>++.[->+++<]>++.>++++++++++..-[------->+<]>.++++.+[++>---<]>.+++[->++<]>.++++.[--->+<]>--.-[--->++<]>-.++++++++++.+[---->+<]>+++.[-->+++++++<]>.++.---.+++++++.[------>+<]>.-----.+.-.-[--->+<]>-.[->+++<]>+.--[--->+<]>--.+[---->+<]>+++.-[--->++<]>-.++++++++++.-[++>---<]>+.------------.--[->++++<]>-.+[->+++<]>+.+++++++++++.------------.--[--->+<]>--.[->+++<]>+.+.[--->+<]>---.----.---.+++++++++.-.+++[->+++<]>.+++++++.-[--->+<]>.-[---->+<]>++.+[----->+<]>+.+.[--->+<]>-----.--[->++++<]>-.-[->+++<]>-.--[--->+<]>---..+++[->+++<]>++.+++++++++++++.++++++.+++++.-[-->+++++<]>.------------.---[->++++<]>+.-------.----------.+.+++++++++++++.[-->+++++<]>+++.---[->++++<]>.------------.---.--[--->+<]>-.---[->++++<]>.+++[->+++<]>.+++++++++++++.-----.++++++.>++++++++++.-[------->+<]>.---------.[--->+<]>--.---[->+++<]>.---.[----->+<]>++.++++++++++.----.-[->++++<]>-.---[->++<]>.[->++++<]>+.>-[--->+<]>-.[----->+<]>+.+++++++++.++++++.-.+[--->+<]>++++.++[--->++<]>.---.------.++.+++++++++.+++++.++++[->+++<]>.[->+++<]>-.++[--->++<]>.>-[--->+<]>--.[----->+++<]>..--[--->+<]>-.---[->++++<]>.------------.---.--[--->+<]>-.>-[--->+<]>--.----.++++++.---.-[->++++<]>-.++.[--->++<]>-.[--->+++++<]>+.---.------.++.+++++++++.+++++.[->+++++++<]>.[--->++<]>--.------------.[-->+++++<]>.[->++++<]>+.>-[--->+<]>-.[----->+<]>+.+++++++++.++++++.-.+[-->+<]>++.------------.[->+++<]>+.+++++++++++++.----------.>++++++++++.>-[--->+<]>-.[----->+<]>+.+++++++++++++.-----.++++++.+[-->+<]>+++.-----[->++<]>-.---------.-[--->++<]>-.---[->++<]>-.[->+++++++<]>.+++++++++++++.++++.-------------.------.++.-[-->+<]>--.++++++++.+[--->+<]>+++.+++++++++.+++.[-->+++++<]>+++.+[->+++<]>.++++++++++++.--..--------.+++++++++++++.++++[->+++<]>+.++++++.--------.+++++++++++.[++>---<]>--.---[->++++<]>+.--.++++[->+++<]>.--[->+++<]>.---------.++[->+++<]>.+++++++++.+++.[-->+++++<]>+++.+[----->+<]>.++.+++.-------------.--[--->+<]>-.-[--->++<]>-.+++++.--------.+++++++++.+++.-----.------------.--[--->+<]>-.-----------.++++++.-.[----->++<]>++.>++++++++++.

>>
***************************
PASTE YOUR EXTENSIONS HERE:

***************************
>>>+ set the exit flag
[ main loop
 TODO: Maybe read lazily (read command char first and then use the
 argument in the handler)?
 escaped read
 https://gist dot github dot com/aartaka/dc3dfad2499ffddb638b0ca3d9700417
 >>>>,----------[<+>----------------------------------------------------------------------------------[[<<+>>-]<<++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>->]<[>,-------------------------------------------------------------------------------------------------[-[------------[----[--[<->[<<+>>-]<<++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>>]<[-<+++++++++>]>]<[-<+++++++++++++>]>]<[-<++++++++++>]>]<[-<++++++++++++>]>]<[-<+++++++>]]>>,----------]<<<[<]
 +> set the case flag and get back to the command text
 switch
 [ if exists
  hash (35)
  ----- ----- ----- -----
  ----- ----- -----
  [
   'd' (100)
   ----- ----- ----- -----
   ----- ----- ----- -----
   ----- ----- ----- ----- -----
   [ 'l' (108)
    ----- ---
    [ 'p' (112)
     ----
     [ 'q' (113)
      -
      [ 'r' (114)
       -
       [ 's' (115)
        -
        [ default case:
         <->[-] empty the flag
         error
         question mark
         +++++ +++++
         +++++ +++++
         +++++ +++++
         +++++ +++++
         +++++ +++++
         +++++ +++++ +++.[-]
         +++++ +++++.[-]
        ]
        <
        [ case 's'
         [-]<<[-]>> kill the case flag AND exit flag
         >>[-] kill the space between 's' and file name
         > file name
         separate the next two arguments by space (32)
         ----- -----
         ----- -----
         ----- ----- --
         [ find next space loop
          +++++ +++++ +++++
          +++++ +++++ +++++ ++
          >  -- ----- -----
          ----- ----- ----- -----]
         - set the byte between the name and contents to 255 (beacon)
         [<] to file start
         >[[<<<<<<+>>>>>>-]>] copy the contents six cells to the left
         <<<<+ set new exit flag
         >> to new case flag (empty)
        ]
        >
       ]
       <
       [ case 'r'
        [-]>>[-] kill the case flag and space after the command
        >[>]<[[>>+<<-]<] copy all the code to the right
        << move to N/case flag (zero: evaluation acts on exit flag)
        meta dot l dot min dot bf from https://github dot com/bf minus enterprise minus solutions/meta dot bf
        >>>>[-]>[>]<[-------------------------------<]>[<+>[------------[-[-[-[--------------[--[-----------------------------[--[++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++[<<<+>>>-]<->]<[-<<++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++[<]<[<<[>>>+<<<-]>[<+>-]>[<+>-]<<+>-]<<[>[>[>+<-]<[>+<-]>>>[<<<+>>>-]<+<-]>>>[>]><<[>>>+<<<-]>+[<+<[------------------------------------------------------------[--[>-<++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++[>>>+<<<-]]>[->+>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++<<]<]>[->->++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++<<]<]>>[<+>-]<][][][][][][]>>[<<<+>>>-]<<<[<]<[<<[>>>+<<<-]>[<+>-]>[<+>-]<<+>-]<<[>>+<<-]]>>[<<+>>-]<<>[>[>+<-]<[>+<-]>>>[<<<+>>>-]<+<-]>>>[>]>]>]<[[-]+<<++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>>[>+>[------------------------------------------------------------[--[<->++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++[<<<+>>>-]]<[-<-<++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>>]>]<[-<+<++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>>]>]<<[>+<-]>][][][][][][]<<[>>>+<<<-]>]>]<[-<<+++++++++++++++++++++++++++++++[<]<->>[>]>]>]<[-<<+++++++++++++++++++++++++++++[<]<+>>[>]>]>]<[-<<+++++++++++++++[<]<[<<[>>>+<<<-]>[<+>-]>[<+>-]<<+>-]<<.>[>[>+<-]<[>+<-]>>>[<<<+>>>-]<+<-]>>>[>]>]>]<[-<<++++++++++++++[<]<[<<[>>>+<<<-]>[<+>-]>[<+>-]<<+>-]<<->[>[>+<-]<[>+<-]>>>[<<<+>>>-]<+<-]>>>[>]>]>]<[-<<+++++++++++++[<]<[<<[>>>+<<<-]>[<+>-]>[<+>-]<<+>-]<<,>[>[>+<-]<[>+<-]>>>[<<<+>>>-]<+<-]>>>[>]>]>]<[-<<++++++++++++[<]<[<<[>>>+<<<-]>[<+>-]>[<+>-]<<+>-]<<+>[>[>+<-]<[>+<-]>>>[<<<+>>>-]<+<-]>>>[>]>]>]>]<<<<[+++++++++++++++++++++++++++++++[>>>+<<<-]<]<
        >>>>>[>]<[[-]<]<<<<[-] clear the previous input and N/case flag
       ]
       >
      ]
      case 'q': kill the case flag AND exit flag
      <[[-]<<[-]>>]>
     ]
     <
     [ case 'p':
      [-]<<[-]>>>>[-] kill the case & exit flags & the space after command
      >[[<<<+>>>-]>] copy the search name closer to the file area
      <<<<[<]> to the search name
      [ file search loop
       <<<<< move to the file
       +[-<+] until the 255 beacon
       <[<]> to the file name
       swap dot bf from https://github dot com/bf minus enterprise minus solutions/str dot bf
       [>]<[[>>[>]>+<<[<]<-]>>[[<+>-]>]<<[<]<]>>[[<+>-]>]>>[[<<+>>-]>]<<<[<]<[<]>
       [>]>[>]< to the swapped file name
       [[>+<-]<] move swapped name closer (bc equal consumes 2 cells to the left)
       >>[>]>>>[[<<+>>-]>] move the search name closer
       <<<[<]<[<]> to the file name
       equal dot min dot  bf from https://github dot com/bf minus enterprise minus solutions/str dot bf
       [+>]+>[+>]<[<]>[>]<[[>+>+<<-]>[>]<[[>+<-]<]<]>>>[[<<+>>-]>]<<<[<]>[>[>>]<<[[>>+<<-]<<]>>>]>[>>]<<[>>[[<+>-]>]<<[<]<]<[>>[[<+>-]>]>[[<+>-]>]<<[<]<<[<]<]>>[>]>[>]<[[>>+<<-]<]>>>[>]<[-<]>[>]>[>]<[[>>+<<-]<]>>>[>]<[[[>+<-]<]>>[<+>-]>[>]<]<[<<]<<[>->>>[[<<+>>-]>>]+[-<+]<[>+<-]>[>]>[[>+<-]>>]<[<<]<[[>+<-]<]<]->>>[[<<+>>-]>]>[[<<+>>-]>>]+[-<+]><<+>>[[>-<-]>[[-]<<<[-]>>>]>[[<<+>>-]>]>[[>>]<<[[-]<<]<<[[-]<]<[-]>>>>>]<<<<[<]>]<<[<+>-]<<[-[>>+<<-]>[<+>-]<<]>
       [ if equal
        [-] kill equality flag
        >>[>]>[>]< to the end of the search name
        [[-]<] kill the search name
        <[<]<] back to (empty) equality flag and exit
       >>[[<<<+>>>-]>] move file name closer to file contents
       <<<<[<]<[<]> to file contents
       swap dot bf from https://github dot com/bf minus enterprise minus solutions/str dot bf
       [>]<[[>>[>]>+<<[<]<-]>>[[<+>-]>]<<[<]<]>>[[<+>-]>]>>[[<<+>>-]>]<<<[<]<[<]>
       [>]-[>]>>>> back to search name (if any)
       [ file shuffling loop (if need to search more)
        [>]<[[>+<-]<] copy the search name to the left
        <<<< to file end
        [[>+<-]<] copy the whole file to the right (free space for shuffling)
        >> to file beginning
        [actual file movement loop
         [<<<[[<]<]<+>>>[[>]>]>-] copy the first file cell before all files
         <<<[[[>+<-]<]<] shift all other files right
         >>>[[>]>]>] to the next cell of the file and loop
        <<< to the files
        [[<]<]<< to the shuffled file
        [[>>+<<-]<] copy shuffled file closer
        >>>[[>]>]<< to the files again
        [[[>+<-]<]<] copy all files to the right
        >>>[[>]>]>>> to the former search name cell (now empty)
       ] file shuffling loop ends
       >[[<+>-]>] copy the search name back
       <<[<]> back to the search name
      ] file search loop ends
      <<<<<+[-<+] to the file contents (via 255 beacon)
      - restore beacon
      >[.>] print out all the file
      +++++ +++++.[-] newline
      >>+ set exit flag
      >> to case flag (empty)
     ]
     >
    ]
    <
    [ case 'l':
     [-] kill the case flag
     <<<<< move to file area
     [ file listing loop
      [<]> move to file name
      +[-.>+] print the file name until 255 beacon
      +++++ +++++.[-] print a newline
      - turn it back into 255 beacon
      [<] back to file beginning
      <] to next file
     >> to the last file beginning
     [[>]>] move through the files
     >>> to case flag
    ]
    >
   ]
   <
   [ case 'd':
    [-]<<[-]>>>>[-] kill the case & exit flags & the space after command
    >[[<<<+>>>-]>] copy the search name closer to the file area
    <<<<[<]> to the search name
    [ file search loop
     <<<<< move to the file
     +[-<+] until the 255 beacon
     <[<]> to the file name
     swap dot bf from https://github dot com/bf minus enterprise minus solutions/str dot bf
     [>]<[[>>[>]>+<<[<]<-]>>[[<+>-]>]<<[<]<]>>[[<+>-]>]>>[[<<+>>-]>]<<<[<]<[<]>
     [>]>[>]< to the swapped file name
     [[>+<-]<] move swapped name closer (bc equal consumes 2 cells to the left)
     >>[>]>>>[[<<+>>-]>] move the search name closer
     <<<[<]<[<]> to the file name
     equal dot min dot  bf from https://github dot com/bf minus enterprise minus solutions/str dot bf
     [+>]+>[+>]<[<]>[>]<[[>+>+<<-]>[>]<[[>+<-]<]<]>>>[[<<+>>-]>]<<<[<]>[>[>>]<<[[>>+<<-]<<]>>>]>[>>]<<[>>[[<+>-]>]<<[<]<]<[>>[[<+>-]>]>[[<+>-]>]<<[<]<<[<]<]>>[>]>[>]<[[>>+<<-]<]>>>[>]<[-<]>[>]>[>]<[[>>+<<-]<]>>>[>]<[[[>+<-]<]>>[<+>-]>[>]<]<[<<]<<[>->>>[[<<+>>-]>>]+[-<+]<[>+<-]>[>]>[[>+<-]>>]<[<<]<[[>+<-]<]<]->>>[[<<+>>-]>]>[[<<+>>-]>>]+[-<+]><<+>>[[>-<-]>[[-]<<<[-]>>>]>[[<<+>>-]>]>[[>>]<<[[-]<<]<<[[-]<]<[-]>>>>>]<<<<[<]>]<<[<+>-]<<[-[>>+<<-]>[<+>-]<<]>
     [ if equal
      [-] kill equality flag
      >>[>]>[>]< to the end of the search name
      [[-]<] kill the search name
      <[<]<] back to (empty) equality flag and exit
     >>[[<<<+>>>-]>] move file name closer to file contents
     <<<<[<]<[<]> to file contents
     swap dot bf from https://github dot com/bf minus enterprise minus solutions/str dot bf
     [>]<[[>>[>]>+<<[<]<-]>>[[<+>-]>]<<[<]<]>>[[<+>-]>]>>[[<<+>>-]>]<<<[<]<[<]>
     [>]-[>]>>>> back to search name (if any)
     [ file shuffling loop (if need to search more)
      [>]<[[>+<-]<] copy the search name to the left
      <<<< to file end
      [[>+<-]<] copy the whole file to the right (free space for shuffling)
      >> to file beginning
      [actual file movement loop
       [<<<[[<]<]<+>>>[[>]>]>-] copy the first file cell before all files
       <<<[[[>+<-]<]<] shift all other files right
       >>>[[>]>]>] to the next cell of the file and loop
      <<< to the files
      [[<]<]<< to the shuffled file
      [[>>+<<-]<] copy shuffled file closer
      >>>[[>]>]<< to the files again
      [[[>+<-]<]<] copy all files to the right
      >>>[[>]>]>>> to the former search name cell (now empty)
     ] file shuffling loop ends
     >[[<+>-]>] copy the search name back
     <<[<]> back to the search name
    ] file search loop ends
    <<<<< to the file
    [[-]<] delete the file
    >>+ set exit flag
    >> to case flag (empty)
   ]
   >
  ]
  <
  [ case hash
   [-] kill the case flag
   >>[>]<[[-]<] destroy all the text
   < to case flag (empty)
  ]
  >

 ]
 <
 [ case '\n':
  [-] kill the flag and noop
 ]
 >>[>]<[[-]<] zero the command contents and move to command beginning
 <<< back to exit flag and loop if not zeroed
] main loop
<<<[[[-]<]<]<< to the initial cell"#);
        //panic!("BFinsts: {:#?}", bfinsts);
        let f = LIRFunction {
            instructions: translate(&bfinsts),
            name: "main".to_owned(),
        };
        //panic!("insts: {:#?}", f.instructions);

        let mut translator = ModuleTranslator::default();
        translator.define_symbol(&f);
        translator.translate(f);
        let elf = translator.finish();
        //println!("FIN: {:?}", elf.program_data.data);
        let mut out = vec![];
        elf.write(&mut out).unwrap();
        std::fs::write(
            "/Users/user/Documents/Programming/rust/hvergelmir/local/fileout.o",
            out,
        )
        .unwrap();
    }

    #[test]
    fn module_translation() {
        let mut f = LIRFunction {
            name: "main".to_string(),
            instructions: vec![
                // Instruction::AllocateStack(ValueOrLiteral::Literal(Literal {
                //     bit_width: 5,
                //     value: 8,
                // })),
                // Instruction::WriteStack(
                //     ValueOrLiteral::Literal(Literal {
                //         value: 69,
                //         bit_width: 5,
                //     }),
                //     Literal {
                //         value: 8,
                //         bit_width: 5,
                //     },
                // ),
                // Instruction::Pop(Value::Register(Register {
                //     number: 4, // (also argument 1)
                //     bit_width: 5,
                // })),
                // Instruction::Call(crate::Symbol {
                //     ty: crate::SymbolType::Function,
                //     local: false,
                //     name: c"exit".to_owned(),
                // }),
                // Instruction::AllocateStack(ValueOrLiteral::Literal(Literal {
                //     bit_width: 5,
                //     value: 8,
                // })),
                // Instruction::Pop(Value::Register(Register {
                //     number: 0,
                //     bit_width: 5,
                // })),
                Instruction::Move(
                    Value::Register(Register {
                        number: 6,
                        bit_width: 5,
                    }),
                    Value::Memory(Memory {
                        reg: Register {
                            number: 5,
                            bit_width: 5,
                        },
                        offset: 8,
                    }),
                ),
                Instruction::Label(0),
                Instruction::Move(
                    Value::Register(Register {
                        number: 4,
                        bit_width: 5,
                    }),
                    Value::Register(Register {
                        number: 6,
                        bit_width: 5,
                    }),
                ),
                Instruction::Call(crate::Symbol {
                    ty: crate::SymbolType::Function,
                    local: false,
                    name: c"puts".to_owned(),
                }),
                Instruction::UnconditionalJump(0),
            ],
        };

        let mut translator = ModuleTranslator::default();
        translator.define_symbol(&f);
        translator.translate(f);
        let elf = translator.finish();
        let mut out = vec![];
        elf.write(&mut out).unwrap();
        std::fs::write(
            "/Users/user/Documents/Programming/rust/hvergelmir/local/fileout.o",
            out,
        )
        .unwrap();
    }
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
