use std::{collections::HashMap, io::Write};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum RegisterTypes {
    EAX = 0,
    ECX = 1,
    EDX = 2,
    EBX = 3,
    ESP = 4,
    EBP = 5,
    ESI = 6,
    EDI = 7,

    R8 = 8,
    R9 = 9,
    R10 = 10,
    R11 = 11,
    R12 = 12,
    R13 = 13,
    R14 = 14,
    R15 = 15,
}

impl RegisterTypes {
    pub fn is_gpr(&self) -> bool {
        *self as u8 >= Self::R8 as u8
    }

    pub fn code(&self) -> u8 {
        if self.is_gpr() {
            *self as u8 - Self::R8 as u8
        } else {
            *self as u8
        }
    }
}
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Copy)]
pub enum RegisterMode {
    Mode32,
    Mode64,
}
impl RegisterMode {
    pub fn is_64(&self) -> bool {
        matches!(self, Self::Mode64)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Register {
    pub ty: RegisterTypes,
    pub mode: RegisterMode,
}

impl Register {
    pub const fn new(ty: RegisterTypes, mode: RegisterMode) -> Self {
        Self { ty, mode }
    }
}

pub const EAX: Register = Register::new(RegisterTypes::EAX, RegisterMode::Mode32);
pub const EBX: Register = Register::new(RegisterTypes::EBX, RegisterMode::Mode32);
pub const ECX: Register = Register::new(RegisterTypes::ECX, RegisterMode::Mode32);
pub const EBP: Register = Register::new(RegisterTypes::EBP, RegisterMode::Mode32);


pub const ESI: Register = Register::new(RegisterTypes::ESI, RegisterMode::Mode32);

pub const EDI: Register = Register::new(RegisterTypes::EDI, RegisterMode::Mode32);
pub const EDX: Register = Register::new(RegisterTypes::EDX, RegisterMode::Mode32);
pub const ESP: Register = Register::new(RegisterTypes::ESP, RegisterMode::Mode32);

pub const RAX: Register = Register::new(RegisterTypes::EAX, RegisterMode::Mode64);
pub const RBX: Register = Register::new(RegisterTypes::EBX, RegisterMode::Mode64);
pub const RDX: Register = Register::new(RegisterTypes::EDX, RegisterMode::Mode64);

pub const RDI: Register = Register::new(RegisterTypes::EDI, RegisterMode::Mode64);
pub const RSI: Register = Register::new(RegisterTypes::ESI, RegisterMode::Mode64);
pub const RSP: Register = Register::new(RegisterTypes::ESP, RegisterMode::Mode64);

pub const R8: Register = Register::new(RegisterTypes::R8, RegisterMode::Mode64);
pub const R9: Register = Register::new(RegisterTypes::R9, RegisterMode::Mode64);
pub const R10: Register = Register::new(RegisterTypes::R10, RegisterMode::Mode64);
pub const R11: Register = Register::new(RegisterTypes::R11, RegisterMode::Mode64);
pub const R12: Register = Register::new(RegisterTypes::R12, RegisterMode::Mode64);
pub const R13: Register = Register::new(RegisterTypes::R13, RegisterMode::Mode64);
pub const R14: Register = Register::new(RegisterTypes::R14, RegisterMode::Mode64);
pub const R15: Register = Register::new(RegisterTypes::R15, RegisterMode::Mode64);

pub const FIRST_ARG: Register = RDI;
pub const SECOND_ARG: Register = RSI;

const fn modrm(mod_v: u8, reg_or_opcode: u8, rm: u8) -> u8 {
    mod_v << 6 | reg_or_opcode << 3 | rm
}
#[derive(Clone, Copy, Debug, Default)]
pub struct RexPrefix {
    pub rex_w: bool,
    pub rex_r: bool,
    pub rex_x: bool,
    pub rex_b: bool,
}

impl RexPrefix {
    pub const fn any_set(self) -> bool {
        self.rex_w || self.rex_r || self.rex_x || self.rex_b
    }

    pub const fn value(self) -> u8 {
        rex_prefix(self.rex_w, self.rex_r, self.rex_x, self.rex_b)
    }
}

const fn rex_prefix(rex_w: bool, rex_r: bool, rex_x: bool, rex_b: bool) -> u8 {
    0b01000000 | ((rex_w as u8) << 3) | ((rex_r as u8) << 2) | ((rex_x as u8) << 1) | (rex_b as u8)
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Displacement {
    Disp8(i8),
    Disp32(i32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DestinationMode {
    Register,
    Memory,
    MemoryDisplaced(Displacement),
}

impl DestinationMode {
    pub fn is_memory(&self) -> bool {
        match self {
            Self::Memory | Self::MemoryDisplaced(_) => true,
            _ => false,
        }
    }
}
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct MemOrReg {
    pub reg: Option<Register>,
    pub mode: DestinationMode,
}

impl MemOrReg {
    pub fn register(r: Register) -> Self {
        Self {
            reg: Some(r),
            mode: DestinationMode::Register,
        }
    }

    pub fn memory(r: Register) -> Self {
        Self {
            reg: Some(r),
            mode: DestinationMode::Memory,
        }
    }

    pub fn displaced(r: Register, displacement: Displacement) -> Self {
        Self {
            reg: Some(r),
            mode: DestinationMode::MemoryDisplaced(displacement),
        }
    }

    pub fn rip_relative(offset: i32) -> Self {
        Self {
            reg: None,
            mode: DestinationMode::MemoryDisplaced(Displacement::Disp32(offset)),
        }
    }

    pub fn reg(&self) -> Register {
        self.reg.unwrap()
    }
    pub fn has_reg(&self) -> bool {
        self.reg.is_some()
    }

    pub fn emit_modrm(&self, output: &mut X86Assembler, reg_or_opcode: u8) {
        match self.mode {
            DestinationMode::Register => {
                output.emit(&[modrm(0b11, reg_or_opcode, self.reg().ty.code())])
            }
            DestinationMode::Memory => {
                output.emit(&[modrm(0b00, reg_or_opcode, self.reg().ty.code())])
            }
            DestinationMode::MemoryDisplaced(Displacement::Disp8(v)) => {
                output.emit(&[modrm(0b01, reg_or_opcode, self.reg().ty.code()), v as u8]);
            }
            DestinationMode::MemoryDisplaced(Displacement::Disp32(v)) => {
                if self.has_reg() {
                    output.emit(&[modrm(0b10, reg_or_opcode, self.reg().ty.code())]);
                } else {
                    output.emit(&[modrm(0b00, reg_or_opcode, 0b101)]);
                }
                output.emit(&v.to_le_bytes());
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Label(pub u64);

impl Label {
    pub fn next(self) -> Self {
        Self(self.0 + 1)
    }
}

pub struct X86Assembler {
    writer: Vec<u8>,
    current_label: Label,
    label_lookup: HashMap<Label, (Option<usize>, Vec<usize>)>,
}

impl X86Assembler {
    pub fn new() -> Self {
        Self {
            writer: Vec::new(),
            current_label: Label(0),
            label_lookup: HashMap::new(),
        }
    }
    pub fn finish(mut self) -> Vec<u8> {
        for (_, (target, jumpers)) in self.label_lookup {
            if let Some(target) = target {
                for jumper in jumpers {
                    let v = target as i32 - (jumper + 5) as i32;

                    self.writer[jumper + 1..jumper + 5].copy_from_slice(&v.to_le_bytes());
                }
            } else {
                panic!("Null jump target!");
            }
        }

        self.writer
    }

    pub fn make_label(&mut self) -> Label {
        let l = self.current_label;
        self.current_label = self.current_label.next();
        l
    }

    pub fn hook_label(&mut self, l: Label) {
        let index = self.writer.len();
        self.label_lookup.entry(l).or_default().0 = Some(index);
    }

    pub fn jump_label(&mut self, l: Label) {
        let start = self.writer.len();
        self.near_jump_relative(0xDEADBEEFu32 as i32);
        self.label_lookup.entry(l).or_default().1.push(start);
    }

    pub fn add_reg(&mut self, dst: MemOrReg, src: MemOrReg) {
        self.binary_op_32or64(0x01, 0x03, dst, src);
    }

    pub fn sub_reg(&mut self, dst: MemOrReg, src: MemOrReg) {
        self.binary_op_32or64(0x2b, 0x29, src, dst);
    }

    pub fn mov_reg(&mut self, dst: MemOrReg, src: MemOrReg) {
        if src == dst { // no-op
            return;
        }
        self.binary_op_32or64(0x89, 0x8B, dst, src);
    }

    pub fn push_reg(&mut self, val: MemOrReg) {
        self.unary_op_32or64(0xFF, 6, val);
    }

    pub fn pop_reg(&mut self, dst: MemOrReg) {
        self.unary_op_32or64(0x8F, 0, dst);
    }

    pub fn lea(&mut self, dst: Register, src: MemOrReg) {
        self.binary_op_32or64(0x8d, 0x8d, MemOrReg::register(dst), src);
    }

    pub fn syscall(&mut self) {
        self.emit(&[0x0F, 0x05]);
    }
    pub fn endbr64(&mut self) {
        self.emit(&[0xf3, 0x0f, 0x1e, 0xfa]);
    }



    pub fn mov_imm32(&mut self, dst: MemOrReg, val: u32) {
        if dst.has_reg() {
            assert_eq!(dst.reg().mode, RegisterMode::Mode32);
        }
        self.emit(&[0xC7]); // MOV opcode
        dst.emit_modrm(self, 0);

        self.emit(&val.to_le_bytes()); // immediate
    }

    pub fn unary_op_32or64(&mut self, opcode: u8, extended_opcode: u8, val: MemOrReg) {
        if val.mode.is_memory() {
            // src must be a register

            let mut rex = RexPrefix::default();

            if val.has_reg() {
                rex.rex_w = val.reg().mode.is_64();
                rex.rex_r = val.reg().ty.is_gpr();
            }

            if rex.any_set() {
                self.emit(&[rex.value()]);
            }
            self.emit(&[opcode]);
            val.emit_modrm(self, extended_opcode);
        } else {
            // dst is a register

            let mut rex = RexPrefix::default();

            rex.rex_w = val.reg().mode.is_64();
            rex.rex_r = val.reg().ty.is_gpr();

            if rex.any_set() {
                self.emit(&[rex.value()]);
            }
            self.emit(&[opcode]);
            val.emit_modrm(self, extended_opcode);
        }
    }

    pub fn binary_op_32or64(
        &mut self,
        dest_memory_opcode: u8,
        dest_register_opcode: u8,
        dst: MemOrReg,
        src: MemOrReg,
    ) {
        if dst.has_reg() && src.has_reg() {
            assert_eq!(dst.reg().mode, src.reg().mode);
        }

        if dst.mode.is_memory() {
            // src must be a register
            assert_eq!(src.mode, DestinationMode::Register);

            if dst.has_reg() && matches!(dst.reg().mode, RegisterMode::Mode64) {
                self.emit(&[rex_prefix(
                    true,
                    src.reg().ty.is_gpr(),
                    false,
                    dst.reg().ty.is_gpr(),
                )]);
            } else if src.reg().ty.is_gpr() || src.reg().mode.is_64() {
                self.emit(&[rex_prefix(
                    src.reg().mode.is_64(),
                    src.reg().ty.is_gpr(),
                    false,
                    false,
                )]);
            }

            self.emit(&[dest_memory_opcode]);
            dst.emit_modrm(self, src.reg().ty.code());
        } else {
            // dst is a register

            let mut rex = RexPrefix::default();

            rex.rex_w = dst.reg().mode.is_64();
            rex.rex_r = dst.reg().ty.is_gpr();

            if src.has_reg() {
                rex.rex_b = src.reg().ty.is_gpr();
            }

            if rex.any_set() {
                self.emit(&[rex.value()]);
            }
            self.emit(&[dest_register_opcode]);
            src.emit_modrm(self, dst.reg().ty.code());
        }
    }

    pub fn near_jump_relative(&mut self, offset: i32) {
        self.emit(&[0xE9]);
        self.emit(&offset.to_le_bytes());
    }

    pub fn near_call(&mut self, dst: MemOrReg) {
        if dst.reg().ty.is_gpr() {
            self.emit(&[rex_prefix(false, false, false, true)]);
        }

        self.emit(&[0xFF]);
        dst.emit_modrm(self, 2);
    }

    /// Near return
    pub fn ret(&mut self) {
        self.emit(&[0xC3]);
    }

    /// Far return
    pub fn retf(&mut self) {
        self.emit(&[0xCB]);
    }

    fn emit(&mut self, v: &[u8]) {
        self.writer.write_all(v).unwrap();
    }
}

#[cfg(test)]
mod tests {
    use hvergelmir_elf::section::Symbol;

    use crate::{MemOrReg, X86Assembler, EAX, EBP, EBX, EDI, EDX, ESI, ESP};
    #[test]
    fn simple_emit_test() {
        let mut asm = X86Assembler::new();

        asm.mov_imm32(MemOrReg::register(EAX), 4);
        asm.mov_reg(MemOrReg::register(EBP), MemOrReg::register(ESP));
        asm.sub_reg(MemOrReg::register(EBP), MemOrReg::register(EAX));
        asm.mov_imm32(
            MemOrReg::displaced(EBP, crate::Displacement::Disp32(-4)),
            u32::from_le_bytes([0x20, 0x20, 0x20, 0]),
        );

        asm.mov_imm32(MemOrReg::register(EAX), 1);
        asm.mov_imm32(MemOrReg::register(EDI), 1);
        asm.lea(ESI, MemOrReg::displaced(EBP, crate::Displacement::Disp32(-4)));
        asm.mov_imm32(MemOrReg::register(EDX), 4);

        asm.syscall();
        
        let mut v = asm.finish();
        let mut symbols = hvergelmir_elf::section::SymbolTableSection::default();

        symbols.add_local(c"fileout.o", Symbol {
            ty: hvergelmir_elf::section::SymbolType::File,
            binding: hvergelmir_elf::section::SymbolBinding::Local,
            visibility: hvergelmir_elf::section::SymbolVisibility::Default,
            section: 0xfff1,
            offset: 0,
            size: 0,
        });
    
        // symbols.add_local(c".text", Symbol {
        //     ty: elf::section::SymbolType::Section,
        //     binding: elf::section::SymbolBinding::Local,
        //     visibility: elf::section::SymbolVisibility::Default,
        //     section: 3,
        //     offset: 0,
        //     size: 0,
        // });
    
    
        symbols.entries.insert(c"main".to_owned(), Symbol {
            ty: hvergelmir_elf::section::SymbolType::Function,
            binding: hvergelmir_elf::section::SymbolBinding::Global,
            visibility: hvergelmir_elf::section::SymbolVisibility::Default,
            section: 3,
            offset: 0,
            size: v.len() as u64,
        });
    
    
        let mut elf = hvergelmir_elf::ELFHeader {
            abi: hvergelmir_elf::ABI::SystemV,
            file_type: hvergelmir_elf::FileType::Relocatable,
            architecture: hvergelmir_elf::MachineArchitecture::AMDx64,
            entry_point: 0,
            strings: hvergelmir_elf::section::StringTableSection::default(),
            symbols,
            program_data: hvergelmir_elf::section::ProgramDataSection {
                data: v
            },
        };
    
        let mut out = vec![];
        elf.write(&mut out).unwrap();
        std::fs::write("/Users/user/Documents/Programming/rust/hvergelmir/fileout.o", out).unwrap();


        // panic!("D: {:?}");
    }
}
