/// An ELF binary emitter. Adapted from an earlier project.
use std::{io::Write, ptr::write_unaligned};

use crate::section::{DataSection, RelocationSection};

use self::section::{
    NullSection, ProgramDataSection, RawSection, StringTableSection, SymbolTableSection,
};

trait Writeable {
    const SIZE: Option<u64>;

    fn write_to(
        &self,
        target: &mut Vec<u8>,
        trailing_data: &mut Vec<u8>,
        trailing_offset: u64,
    ) -> std::io::Result<()>;
}

#[derive(Clone, Copy)]
#[repr(u8)]
pub enum ABI {
    SystemV = 0x00,
    Linux = 0x03,
}
#[derive(Clone, Copy)]
#[repr(u16)]
pub enum FileType {
    Relocatable = 0x01,
    Executable = 0x02,
    SharedObject = 0x03,
    CoreFile = 0x04,
}
#[derive(Clone, Copy)]
#[repr(u16)]
pub enum MachineArchitecture {
    AMDx64 = 0x3E,
}

pub struct ELFHeader {
    pub abi: ABI,
    pub file_type: FileType,
    pub architecture: MachineArchitecture,
    pub entry_point: u64,
    pub strings: StringTableSection,
    pub symbols: SymbolTableSection,
    pub program_data: ProgramDataSection,
    pub relocations: RelocationSection,
    pub data: DataSection,
}

impl ELFHeader {
    pub fn write(mut self, output: &mut Vec<u8>) -> std::io::Result<()> {
        output.write_all(&[0x7f, 0x45, 0x4c, 0x46])?; // magic number

        output.write_all(&[0x2, 0x1, 0x1])?; // 64 bit, little endian, ELF version 1

        output.write_all(&[self.abi as u8, 0])?;
        output.write_all(&[0; 7])?;

        output.write_all(&(self.file_type as u16).to_le_bytes())?;
        output.write_all(&(self.architecture as u16).to_le_bytes())?;

        output.write_all(&1u32.to_le_bytes())?; // ELF v1

        output.write_all(&self.entry_point.to_le_bytes())?;

        output.write_all(&0u64.to_le_bytes())?; // PH offset

        output.write_all(&0x40u64.to_le_bytes())?; // SH offset

        output.write_all(&0u32.to_le_bytes())?; // flags

        output.write_all(&0x40u16.to_le_bytes())?; // elf header size

        output.write_all(&[0, 0, 0, 0])?; // PH entry and PH numbers

        output.write_all(&(RawSection::SIZE.unwrap() as u16).to_le_bytes())?; // size of section

        let num_sections: u16 = 6;

        output.write_all(&num_sections.to_le_bytes())?; // number of sections

        output.write_all(&1u16.to_le_bytes())?; // string table section index

        let program_data = self.program_data.raw(&mut self.strings);
        let relocations = self.relocations.raw(&mut self.strings, &self.symbols);
        let symbol_table = self.symbols.raw((&mut self.strings, 1));

        let null = NullSection.raw(&mut self.strings);

        let data = self.data.raw(&mut self.strings);

        let string = self.strings.add_str(c".strtab");

        let string_table = self.strings.raw(string);

        let mut trailing_data = vec![];

        let trailing_offset = 0x40 + (num_sections as u64 * RawSection::SIZE.unwrap());

        null.write_to(output, &mut trailing_data, trailing_offset)?;
        string_table.write_to(output, &mut trailing_data, trailing_offset)?;
        symbol_table.write_to(output, &mut trailing_data, trailing_offset)?;
        program_data.write_to(output, &mut trailing_data, trailing_offset)?;
        relocations.write_to(output, &mut trailing_data, trailing_offset)?;
        data.write_to(output, &mut trailing_data, trailing_offset)?;

        output.write_all(&trailing_data)?;

        Ok(())
    }
}

#[repr(u32)]
pub enum ProgramHeaderType {
    Loadable = 0x01,
    Dynamic = 0x02,
    Interpreter = 0x03,
    Auxiliary = 0x04,
    ProgramHeaderTable = 0x06,
    ThreadLocalStorage = 0x07,
}

pub struct ProgramHeaderFlags {
    pub executable: bool,
    pub writeable: bool,
    pub readable: bool,
}
pub struct ProgramHeader {
    pub ty: ProgramHeaderType,
    pub flags: ProgramHeaderFlags,
    pub offset: u64,
    pub virtual_address: u64,
    pub physical_address: u64,
    pub segment_size_in_file: u64,
    pub segment_size_in_memory: u64,
    pub alignment: Option<u64>,
}

pub mod section {
    use std::{
        collections::HashMap,
        ffi::{CStr, CString},
        io::Write,
    };

    use indexmap::IndexMap;

    use super::Writeable;

    #[derive(Clone, Copy)]
    #[repr(u32)]
    pub enum SectionType {
        Null = 0x0,
        ProgramData = 0x1,
        SymbolTable = 0x2,
        StringTable = 0x3,
        RelocationEntriesWithAddend = 0x4,
        RelocationEntries = 0x9,
    }

    bitflags::bitflags! {
        pub struct SectionFlags: u64 {
            const STRINGS = 0x20;
            const EXECUTABLE = 0x4;
            const ALLOCATED = 0x2;
            const INFO_LINK = 0x40;
        }
    }

    pub struct RawSection {
        pub name: u32,
        pub ty: SectionType,
        pub attributes: SectionFlags,
        pub virtual_address: u64,
        pub data: Vec<u8>,
        pub sh_link: u32,
        pub sh_info: u32,
        pub required_alignment: u64,
        pub entry_size: u64,
    }

    impl Writeable for RawSection {
        const SIZE: Option<u64> = Some(0x40);

        fn write_to(
            &self,
            target: &mut Vec<u8>,
            trailing_data: &mut Vec<u8>,
            trailing_offset: u64,
        ) -> std::io::Result<()> {
            target.write_all(&self.name.to_le_bytes())?;
            target.write_all(&(self.ty as u32).to_le_bytes())?;
            target.write_all(&self.attributes.bits().to_le_bytes())?;
            target.write_all(&self.virtual_address.to_le_bytes())?;

            if !self.data.is_empty() {
                let offset = trailing_data.len() as u64 + trailing_offset;
                trailing_data.write_all(&self.data)?;
                target.write_all(&offset.to_le_bytes())?;
            } else {
                target.write_all(&[0; 8])?;
            }
            target.write_all(&(self.data.len() as u64).to_le_bytes())?;
            target.write_all(&self.sh_link.to_le_bytes())?;
            target.write_all(&self.sh_info.to_le_bytes())?;
            target.write_all(&self.required_alignment.to_le_bytes())?;
            target.write_all(&self.entry_size.to_le_bytes())?;

            Ok(())
        }
    }

    pub struct DataSection {
        pub data: Vec<u8>,
    }

    impl DataSection {
        pub fn raw(self, sh_strings: &mut StringTableSection) -> RawSection {
            RawSection {
                name: sh_strings.add_str(c".data"),
                ty: SectionType::ProgramData,
                attributes: SectionFlags::ALLOCATED,
                virtual_address: 0,
                data: self.data,
                sh_link: 0,
                sh_info: 0,
                required_alignment: 0,
                entry_size: 0,
            }
        }
    }

    pub struct RelocationSection {
        // a section!
        pub relocation_target: u32,
        pub symbol_table: u32,
        pub relocations: Vec<Elf64AddendRelocation>,
    }

    #[repr(u32)]
    pub enum Elf64RelocationTypes_x86_64 {
        /// R_X86_64_64 (S + A)
        BasicAddendOffset = 1,
        /// R_X86_64_PC32 (S + A - P)
        ProgramCounterRelative = 2,
        /// R_X86_64_PLT32 (L + A - P)
        LRelativeWat = 4,
    }

    pub struct Elf64AddendRelocation {
        pub offset: u64,
        pub symbol: SymbolIndex,
        pub info: u32,
        pub addend: i64,
    }
    impl Elf64AddendRelocation {
        pub fn bytes(&self, symbol_table: &SymbolTableSection) -> [u8; 24] {
            let mut v = [0; 24];
            v[..8].copy_from_slice(&self.offset.to_le_bytes());
            v[8..16].copy_from_slice(
                &(((symbol_table.resolve(self.symbol) as u64) << 32) + (self.info as u64))
                    .to_le_bytes(),
            );
            v[16..].copy_from_slice(&self.addend.to_le_bytes());
            v
        }
    }

    impl RelocationSection {
        pub fn raw(
            self,
            sh_strings: &mut StringTableSection,
            sh_symbols: &SymbolTableSection,
        ) -> RawSection {
            let mut data = vec![];
            for v in &self.relocations {
                data.extend_from_slice(&v.bytes(sh_symbols));
            }
            RawSection {
                // It depends what kind of ELF file you are talking about, and in any case there can be more than one relocation table.
                // In an ELF 32-bit object file, static code relocations are specified in the rel.text section; for an ELF 64-bit object file, static code relocations are specified in the rela.text section. There may be additional static relocation sections {rel|rela}.??? that specify relocations for objects in the ??? section, e.g. .rela.eh_frame, .rela.init_array.
                // In an ELF executable or DSO, the .rela.dyn section specifies dynamic relocations for variables. The rela.plt section specifies dynamic relocations for functions.
                name: sh_strings.add_str(c".rela.text"),
                ty: SectionType::RelocationEntriesWithAddend,
                attributes: SectionFlags::INFO_LINK,
                virtual_address: 0,
                data,
                sh_link: self.symbol_table,
                sh_info: self.relocation_target,
                required_alignment: 16,
                entry_size: 24,
            }
        }
    }

    pub struct NullSection;

    impl NullSection {
        pub fn raw(self, sh_strings: &mut StringTableSection) -> RawSection {
            RawSection {
                name: sh_strings.add_str(c""),
                ty: SectionType::Null,
                attributes: SectionFlags::empty(),
                virtual_address: 0,
                data: vec![],
                sh_link: 0,
                sh_info: 0,
                required_alignment: 0,
                entry_size: 0,
            }
        }
    }

    #[derive(Default)]
    pub struct ProgramDataSection {
        pub data: Vec<u8>,
    }

    impl ProgramDataSection {
        pub fn raw(mut self, strings: &mut StringTableSection) -> RawSection {
            RawSection {
                name: strings.add_str(c".text"),
                ty: SectionType::ProgramData,
                attributes: SectionFlags::EXECUTABLE | SectionFlags::ALLOCATED,
                virtual_address: 0,
                data: self.data,
                sh_link: 0,
                sh_info: 0,
                required_alignment: 16,
                entry_size: 0,
            }
        }
    }

    pub struct Symbol {
        pub ty: SymbolType,
        pub binding: SymbolBinding,
        pub visibility: SymbolVisibility,
        pub section: u16,
        pub offset: u64,
        pub size: u64,
    }

    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
    pub enum SymbolIndex {
        Local(usize),
        Global(usize),
    }

    #[derive(Default)]
    pub struct SymbolTableSection {
        pub local_entries: IndexMap<CString, Symbol>,
        pub entries: IndexMap<CString, Symbol>,
    }
    impl SymbolTableSection {
        pub fn get_mut(&mut self, i: &CStr) -> Option<(SymbolIndex, &mut Symbol)> {
            self.local_entries
                .get_full_mut(i)
                .map(|(idx, _, sym)| (SymbolIndex::Local(idx + 1), sym))
                .or_else(|| {
                    self.entries
                        .get_full_mut(i)
                        .map(|(idx, _, sym)| (SymbolIndex::Global(idx + 1), sym))
                })
        }

        pub fn get(&self, i: &CStr) -> Option<(SymbolIndex, &Symbol)> {
            self.local_entries
                .get_full(i)
                .map(|(idx, _, sym)| (SymbolIndex::Local(idx + 1), sym))
                .or_else(|| {
                    self.entries
                        .get_full(i)
                        .map(|(idx, _, sym)| (SymbolIndex::Global(idx + 1), sym))
                })
        }

        pub fn add_local(&mut self, i: &CStr, sym: Symbol) -> SymbolIndex {
            self.local_entries.insert(i.to_owned(), sym);
            SymbolIndex::Local(self.local_entries.len())
        }
        pub fn add(&mut self, i: &CStr, sym: Symbol) -> SymbolIndex {
            self.entries.insert(i.to_owned(), sym);
            SymbolIndex::Global(self.entries.len())
        }

        /// Resolve the symbol index `i` according to the
        /// current state of this symbol table.
        pub fn resolve(&self, i: SymbolIndex) -> usize {
            match i {
                SymbolIndex::Local(i) => i,
                SymbolIndex::Global(i) => i + self.local_entries.len(),
            }
        }

        pub fn raw(mut self, strings: (&mut StringTableSection, u32)) -> RawSection {
            let mut data = vec![];

            SymbolTableEntry {
                name: strings.0.add_str(c""),
                symbol: Symbol {
                    ty: SymbolType::NoType,
                    binding: SymbolBinding::Local,
                    visibility: SymbolVisibility::Default,
                    section: 0,
                    offset: 0,
                    size: 0,
                },
            }
            .write_to(&mut data, &mut vec![], 0)
            .expect("fail");

            let local = self.local_entries.len();
            for (name, sym) in self
                .local_entries
                .into_iter()
                .chain(self.entries.into_iter())
            {
                let name = strings.0.add_str(&name);
                SymbolTableEntry { name, symbol: sym }
                    .write_to(&mut data, &mut vec![], 0)
                    .expect("fail");
            }

            RawSection {
                name: strings.0.add_str(c".symtab"),
                ty: SectionType::SymbolTable,
                attributes: SectionFlags::empty(),
                virtual_address: 0,
                data,
                sh_link: strings.1,
                sh_info: (local as u32) + 1,
                required_alignment: 8,
                entry_size: SymbolTableEntry::SIZE.unwrap(),
            }
        }
    }

    #[derive(Clone, Copy)]
    #[repr(u8)]
    pub enum SymbolBinding {
        Local = 0,
        Global = 1,
        Weak = 2,
    }
    #[derive(Clone, Copy)]
    #[repr(u8)]
    pub enum SymbolType {
        NoType = 0,
        Object = 1,
        Function = 2,
        Section = 3,
        File = 4,
    }
    #[derive(Clone, Copy)]
    #[repr(u8)]
    pub enum SymbolVisibility {
        Default = 0,
        Internal = 1,
        Hidden = 2,
        Protected = 3,
    }

    pub struct SymbolTableEntry {
        pub name: u32,
        pub symbol: Symbol,
    }

    impl Writeable for SymbolTableEntry {
        const SIZE: Option<u64> = Some(24);

        fn write_to(
            &self,
            target: &mut Vec<u8>,
            _trailing_data: &mut Vec<u8>,
            _offset: u64,
        ) -> std::io::Result<()> {
            target.write_all(&self.name.to_le_bytes())?;
            target.write_all(&[((self.symbol.binding as u8) << 4) + self.symbol.ty as u8])?;
            target.write_all(&[self.symbol.visibility as u8])?;
            target.write_all(&self.symbol.section.to_le_bytes())?;
            target.write_all(&self.symbol.offset.to_le_bytes())?;
            target.write_all(&self.symbol.size.to_le_bytes())?;
            Ok(())
        }
    }

    pub struct StringTableSection {
        data: Vec<u8>,
        indices: HashMap<CString, u32>,
    }

    impl Default for StringTableSection {
        fn default() -> Self {
            Self {
                data: vec![0],
                indices: Default::default(),
            }
        }
    }
    impl StringTableSection {
        pub fn raw(mut self, name: u32) -> RawSection {
            RawSection {
                name,
                ty: SectionType::StringTable,
                attributes: SectionFlags::empty(),
                virtual_address: 0,
                data: self.data,
                sh_info: 0,
                sh_link: 0,
                required_alignment: 1,
                entry_size: 0,
            }
        }

        pub fn add_str(&mut self, cstr: &CStr) -> u32 {
            *self.indices.entry(cstr.to_owned()).or_insert_with(|| {
                let index = self.data.len() as u32;
                self.data.extend_from_slice(cstr.to_bytes_with_nul());
                index
            })
        }
    }
}
