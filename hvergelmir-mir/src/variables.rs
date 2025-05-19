use std::{collections::HashMap, fmt::Debug};

#[derive(Default, Debug)]
pub struct VariableStore {
    variables: HashMap<VariableIndex, VariableGeneration>,
    idx: u32
}
impl VariableStore {
    pub fn make(&mut self) -> Variable {
        let v = self.idx;
        self.idx += 1;
        self.variables.insert(v, 0);
        Variable { index: v, generation: 0 }
    }

    pub fn get(&mut self, index: VariableIndex) -> Variable {
        if let Some(generation) = self.variables.get_mut(&index) {
            *generation += 1;
            Variable { index, generation: *generation }
        } else {
            self.variables.insert(index, 0);
            Variable { index, generation: 0 }
        }
    }
}


pub type VariableIndex = u32;
pub type VariableGeneration = u32;

#[derive(Clone, Copy)]
pub struct Variable {
    index: VariableIndex,
    generation: VariableGeneration
}

impl Variable {
    pub fn index(&self) -> VariableIndex {
        self.index
    }

    pub fn generation(&self) -> VariableGeneration {
        self.generation
    }
}

impl Debug for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:X}[{}]", self.index + 10, self.generation)
    }
}