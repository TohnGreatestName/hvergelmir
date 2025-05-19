use std::{
    cell::{Ref, RefCell, RefMut},
    fmt::Debug,
    hash::{DefaultHasher, Hash, Hasher},
    rc::Rc,
};

use super::variables::{Variable, VariableStore};
use generational_arena::{Arena, Index};
use hvergelmir_parser::lexer::token_types::Number;

pub type BasicBlockRef = Rc<RefCell<BasicBlock>>;

#[derive(Default)]
pub struct BlockSequence {
    blocks: Arena<BasicBlockRef>,
    variables: RefCell<VariableStore>,
}

impl BlockSequence {
    pub fn add_block<'a, 'b>(&'a mut self) -> BasicBlockRef {
        let b = self.blocks.insert(Rc::new(RefCell::new(BasicBlock::new(
            Index::from_raw_parts(0, 0),
        ))));
        let r = Rc::clone(&self.blocks.get(b).unwrap());
        r.borrow_mut().index = b; // assign actual index
        r
    }
    pub fn variables(&self) -> RefMut<VariableStore> {
        self.variables.borrow_mut()
    }
}

#[derive(Debug)]
pub enum BlockSuccessor {
    Return(RValue),
    Jump(Index),
    ConditionalJump(RValue, Index, Index),
}
#[derive(Debug)]
pub struct BasicBlock {
    index: Index,
    instructions: Vec<Instruction>,
    successor: Option<BlockSuccessor>,
}

impl BasicBlock {
    pub fn set_successor(&mut self, s: BlockSuccessor) {
        if self.successor.is_some() {
            panic!("trying to change successor of block - should have already been calculated");
        }
        self.successor = Some(s);
    }

    pub fn index(&self) -> Index {
        self.index
    }

    pub fn new(i: Index) -> Self {
        Self {
            index: i,
            instructions: vec![],
            successor: None,
        }
    }

    pub fn inst(&mut self, i: Instruction) {
        self.instructions.push(i);
    }
}

pub enum Literal {
    Number(Number),
}

pub enum RValue {
    Variable(Variable),
    Literal(Literal),
}

pub enum Instruction {
    Add(Variable, RValue, RValue),
    Subtract(Variable, RValue, RValue),
    Divide(Variable, RValue, RValue),
    Multiply(Variable, RValue, RValue),
    Assign(Variable, RValue),
    LessThan(Variable, RValue, RValue),
    GreaterThan(Variable, RValue, RValue),
    Return(RValue),
}

impl Debug for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Number(arg0) => write!(f, "{:?}", arg0),
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
            Self::LessThan(var, r1, r2) => write!(f, "{var:?} = lt {r1:?}, {r2:?}"),
            Self::GreaterThan(var, r1, r2) => write!(f, "{var:?} = gt {r1:?}, {r2:?}"),
            Self::Assign(var, r1) => write!(f, "{var:?} = {r1:?}"),
            Self::Return(r1) => write!(f, "ret {r1:?}"),
        }
    }
}

pub fn block_idx_str(n: Index) -> String {
    let mut h = DefaultHasher::new();
    n.hash(&mut h);
    format!("{:x}", h.finish())
}

impl Debug for BlockSequence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (index, block) in self.blocks.iter() {
            let x = block_idx_str(index);
            writeln!(f, "block #{x}:")?;

            for inst in block.borrow().instructions.iter() {
                writeln!(f, "   {:?}", inst)?;
            }
            match block
                .borrow()
                .successor
                .as_ref()
                .expect("Should have a successor")
            {
                BlockSuccessor::Return(v) => {
                    writeln!(f, "   ret {:?}", v)?;
                }
                BlockSuccessor::Jump(target) => {
                    writeln!(f, "   jmp #{}", block_idx_str(*target))?;
                }
                BlockSuccessor::ConditionalJump(idx, happy, sad) => {
                    writeln!(
                        f,
                        "   cond {:?}, #{}, #{}",
                        idx,
                        block_idx_str(*happy),
                        block_idx_str(*sad)
                    )?;
                }
            }
        }
        Ok(())
    }
}

impl BlockSequence {
    pub fn graphviz(&self) -> String {
        let mut s = String::new();

        for (index, block) in self.blocks.iter() {
            let x = block_idx_str(index);
            s.push_str(&format!("B{x} [ label = \"block {x}:\\l"));

            for inst in block.borrow().instructions.iter() {
                s.push_str(&format!("{inst:?}\\l"));
            }
            let mut add_commands = String::new();

            match block
                .borrow()
                .successor
                .as_ref()
                .expect("Should have a successor")
            {
                BlockSuccessor::Return(v) => {
                    s.push_str(&format!("ret {:?}\\l", v));
                }
                BlockSuccessor::Jump(target) => {
                    s.push_str("jmp\\l");
                    add_commands.push_str(&format!("B{x} -> B{}; ", block_idx_str(*target)));
                }
                BlockSuccessor::ConditionalJump(idx, happy, sad) => {
                    s.push_str(&format!("cond {:?}\\l", idx));
                    add_commands.push_str(&format!("B{x} -> B{} [label = \"true\"]; ", block_idx_str(*happy)));
                    add_commands.push_str(&format!("B{x} -> B{} [label = \"false\"]; ", block_idx_str(*sad)));
                }
            }

            s.push_str("\"];");
            s.push_str(&add_commands);
        }
        s
    }
}
