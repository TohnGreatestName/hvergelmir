use std::{collections::{hash_map::Entry, HashMap}, fmt::Debug};

use crate::block::{BasicBlock, BasicBlockRef};

#[derive(Default, Debug)]
pub struct VariableStore {
    idx: u32
}
impl VariableStore {
    pub fn make(&mut self, blk: &BasicBlockRef) -> MIRVariable {
        let v = self.idx;
        self.idx += 1;
        blk.borrow_mut().variables_defined_mut().insert(v);
        MIRVariable { index: v }
    }
}


pub type VariableIndex = u32;
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Default)]
pub struct VariableGeneration(pub u32);

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Default)]
pub struct ConcreteGeneration(pub u32);

impl ConcreteGeneration {
    pub fn inc(&mut self) -> Self {
        self.0 += 1;
        *self
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct ResolvedMIRVariable {
    index: VariableIndex,
    generation: ConcreteGeneration
}

impl ResolvedMIRVariable {
    pub fn new(i: VariableIndex, generation: ConcreteGeneration) -> Self {
        Self {
            index: i,
            generation
        }
    }

    pub fn generation(&self) -> ConcreteGeneration {
        self.generation
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct MIRVariable {
    index: VariableIndex,
}

impl MIRVariable {
    pub fn read(&self, b: &BasicBlockRef) -> MIRVariableInstance {
        MIRVariableInstance {
            variable: *self,
            offset_generation: *b.borrow_mut().variable_map_mut().entry(self.index).or_default()
        }
    }



    pub fn write(&self, b: &BasicBlockRef) -> MIRVariableInstance {
        let mut borrow = b.borrow_mut();
        let v = borrow.variable_map_mut().entry(self.index);
        let g = if let Entry::Occupied(mut e) = v {
            e.get_mut().0 += 1;
            *e.get()
        } else {
            // has never been read.
            v.or_default();
            VariableGeneration(0)
        };
        MIRVariableInstance {
            variable: *self,
            offset_generation: g
        }
    }

    pub fn index(&self) -> VariableIndex {
        self.index
    }


}

pub struct MIRVariableInstance {
    variable: MIRVariable,
    offset_generation: VariableGeneration
}

impl MIRVariableInstance {
    pub fn variable(&self) -> MIRVariable {
        self.variable
    }

    pub fn is_latest(&self, b: &BasicBlockRef) -> bool {
        *b.borrow().variable_map().get(&self.variable.index).unwrap() == self.offset_generation
    }

    pub fn offset_generation(&self) -> VariableGeneration {
        self.offset_generation
    }

}

impl Debug for MIRVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:X}", self.index + 10)
    }
}

impl Debug for MIRVariableInstance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}[{:?}]", self.variable, self.offset_generation)
    }
}