use std::{collections::{hash_map::Entry, HashMap}, fmt::Debug};

use crate::block::{BasicBlock, BasicBlockRef};

#[derive(Default, Debug)]
pub struct VariableStore {
    idx: u32
}
impl VariableStore {
    pub fn make(&mut self) -> MIRVariable {
        let v = self.idx;
        self.idx += 1;
        MIRVariable { index: v, offset_generation: 0 }
    }
}


pub type VariableIndex = u32;
pub type VariableGeneration = u32;

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct MIRVariable {
    index: VariableIndex,
    offset_generation: VariableGeneration
}

impl MIRVariable {
    pub fn read(&self, b: &BasicBlockRef) -> Self {
        Self {
            index: self.index,
            offset_generation: *b.borrow_mut().variable_map_mut().entry(self.index).or_default()
        }
    }

    pub fn is_latest(&self, b: &BasicBlockRef) -> bool {
        *b.borrow().variable_map().get(&self.index).unwrap() == self.offset_generation
    }
    pub fn new_handle(&self, b: &BasicBlockRef) -> Self {
        Self {
            index: self.index,
            offset_generation: b.borrow().variable_map().get(&self.index).copied().unwrap_or_default()
        }
    }

    pub fn write(&self, b: &BasicBlockRef) -> Self {
        let mut borrow = b.borrow_mut();
        let v = borrow.variable_map_mut().entry(self.index);
        let g = if let Entry::Occupied(mut e) = v {
            *e.get_mut() += 1;
            *e.get()
        } else {
            // has never been read.
            v.or_default();
            0
        };
        Self {
            index: self.index,
            offset_generation: g
        }
    }

    pub fn index(&self) -> VariableIndex {
        self.index
    }

    pub fn offset_generation(&self) -> VariableGeneration {
        self.offset_generation
    }

    pub fn inc_generation(&mut self) {
        self.offset_generation += 1;
    }
}

impl Debug for MIRVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:X}[{}]", self.index + 10, self.offset_generation)
    }
}