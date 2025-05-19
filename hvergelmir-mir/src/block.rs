use std::{cell::{Ref, RefCell, RefMut}, fmt::Debug, hash::{DefaultHasher, Hash, Hasher}, rc::Rc};

use generational_arena::{Arena, Index};
use hvergelmir_parser::lexer::token_types::Number;
use super::variables::{Variable, VariableStore};

pub type BasicBlockRef = Rc<RefCell<BasicBlock>>;
#[derive(Default)]
pub struct BlockSequence {
    blocks: Arena<BasicBlockRef>,
    variables: RefCell<VariableStore>
}

impl BlockSequence {
    pub fn add_block<'a, 'b>(&'a mut self) -> BasicBlockRef {
        let b = self.blocks.insert(Rc::new(RefCell::new(BasicBlock::default())));
        Rc::clone(&self.blocks.get(b).unwrap())
    }
    pub fn variables(&self) -> RefMut<VariableStore>{ 
        self.variables.borrow_mut()
    }
}



#[derive(Default, Debug)]
pub struct BasicBlock {
    instructions: Vec<Instruction>,
}

impl BasicBlock {
    pub fn inst(&mut self, i: Instruction) {
        self.instructions.push(i);
    }
}

pub enum Literal {
    Number(Number)
}



pub enum RValue {
    Variable(Variable),
    Literal(Literal)
}


pub enum Instruction {
    Add(Variable, RValue, RValue),
    Subtract(Variable, RValue, RValue),
    Divide(Variable, RValue, RValue),
    Multiply(Variable, RValue, RValue),
    Assign(Variable, RValue),
    Return(RValue)
}

impl Debug for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Number(arg0) => write!(f, "{:?}", arg0)
        }
    }
}

impl Debug for RValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Variable(arg0) => write!(f, "{:?}", arg0),
            Self::Literal(arg0) => write!(f, "{:?}", arg0),
        }
    }
}

impl Debug for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Add(var, r1, r2) => write!(f, "{var:?} = add {r1:?}, {r2:?}"),
            Self::Subtract(var, r1, r2) => write!(f, "{var:?} = sub {r1:?}, {r2:?}"),
            Self::Divide(var, r1, r2) => write!(f, "{var:?} = div {r1:?}, {r2:?}"),
            Self::Multiply(var, r1, r2) => write!(f, "{var:?} = mul {r1:?}, {r2:?}"),
            Self::Assign(var, r1) => write!(f, "{var:?} = {r1:?}"),
            Self::Return(r1) =>  write!(f, "ret {r1:?}"),
        }
    }
}


impl Debug for BlockSequence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn idx(n: Index) -> String {
            let mut h = DefaultHasher::new();
            n.hash(&mut h);
            format!("{:x}", h.finish())
        }

        for (index, block) in self.blocks.iter() {
            let x = idx(index);
            writeln!(f, "block #{x}:")?;

            for inst in block.borrow().instructions.iter() {
                writeln!(f, "   {:?}", inst)?;
            }

        }
        Ok(())


    }
}