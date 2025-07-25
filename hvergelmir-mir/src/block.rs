use std::{
    cell::{Ref, RefCell, RefMut}, collections::{HashMap, HashSet, VecDeque}, fmt::Debug, hash::{DefaultHasher, Hash, Hasher}, rc::Rc
};

use crate::variables::{ConcreteGeneration, MIRVariableInstance, ResolvedMIRVariable, VariableGeneration, VariableIndex};

use super::variables::{MIRVariable, VariableStore};
use generational_arena::{Arena, Index};
use hvergelmir_parser::lexer::token_types::Number;
use string_interner::symbol::SymbolU32;

pub type BasicBlockRef = Rc<RefCell<BasicBlock>>;

#[derive(Default)]
pub struct BlockSequence {
    blocks: Arena<BasicBlockRef>,
    variables: RefCell<VariableStore>,
    entry: Option<Index>
}

impl BlockSequence {
    pub fn set_entry(&mut self, e: Index) {
        self.entry = Some(e);
    }

    pub fn entry(&self) -> Index {
        self.entry.expect("Caller should only call if entry set")
    }

    pub fn block(&self, i: Index) -> Option<BasicBlockRef> {
        self.blocks.get(i).cloned()
    }

    pub fn compute_phi_starting_from(&self, idx: Index) {
        let mut concrete_gen_map: HashMap<VariableIndex, ConcreteGeneration> = HashMap::new();

        let mut new_gen = |v| {
            *concrete_gen_map.entry(v).and_modify(|v| { v.inc(); }).or_default()
        };

        let mut phi_compute_stack = VecDeque::new();
        phi_compute_stack.push_back(idx);

        let mut already_computed = HashSet::new();


        // FIRST PASS - compute phi for *declared* variables
        while !phi_compute_stack.is_empty() {
            let index = phi_compute_stack.pop_front().unwrap();
            if already_computed.insert(index) {
                let blk = self.blocks.get(index).unwrap();

                let mut blk_borrow = blk.borrow_mut();

                for v in blk_borrow.variables_defined().clone() {
                    // no path. these are already defined.
                    blk_borrow.phi_table.insert(v, (new_gen(v), vec![]));
                }

                for v in blk_borrow.successors() {
                    phi_compute_stack.push_back(v);
                }
            }
        }
        // go again.
        phi_compute_stack.push_back(idx);
        already_computed.clear();
        while !phi_compute_stack.is_empty() {
            let index = phi_compute_stack.pop_front().unwrap();
            if already_computed.insert(index) {
                let blk = self.blocks.get(index).unwrap();

                let mut blk_borrow = blk.borrow_mut();

                for used in blk_borrow.variable_map().clone() {

                    // for every var used but not defined
                    if !blk_borrow.variables_defined().contains(&used.0) {
                        let used_but_not_defined = used;

                        let mut paths = vec![];

                        let mut phi_compute_stack_inner = VecDeque::new();
                        let mut already_computed_inner = HashSet::new();
                        already_computed_inner.insert(index);
                        for v in blk_borrow.predecessors() {
                            phi_compute_stack_inner.push_back((*v, vec![*v]));
                        }

                        while !phi_compute_stack_inner.is_empty() {
                            let (index, path) = phi_compute_stack_inner.pop_front().unwrap();
                            if already_computed_inner.insert(index) {
                            
                                let blk = self.blocks.get(index).unwrap();
                                let blk_borrow = blk.borrow();

                                let phi = blk_borrow.resolve_var(used_but_not_defined.0);
                                if let Some(phi) = phi {
                                    paths.push((path, phi.generation()));
                                } else {
                                    for v in blk_borrow.predecessors() {
                                        let mut new_path = path.clone();
                                        new_path.push(*v);
                                        phi_compute_stack_inner.push_back((*v, new_path));
                                    }
                                }

                            }
                        }

                        blk_borrow.phi_table.insert(used_but_not_defined.0, (new_gen(used_but_not_defined.0), paths));

    
                        
                    }
                }

                for v in blk_borrow.successors() {
                    phi_compute_stack.push_back(v);
                }
            }
        }
    }

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
    predecessors: Vec<Index>,
    successor: Option<BlockSuccessor>,
    variable_map: HashMap<VariableIndex, VariableGeneration>,
    variables_defined: HashSet<VariableIndex>,
    /// A map of variable indices to preceding control 
    /// flow paths and the base offset at this point.
    phi_table: HashMap<VariableIndex, (ConcreteGeneration, Vec<(Vec<Index>, ConcreteGeneration)>)>
}

impl BasicBlock {
    pub fn phi(&self) -> &HashMap<VariableIndex, (ConcreteGeneration, Vec<(Vec<Index>, ConcreteGeneration)>)> {
        &self.phi_table
    }

    // FIXME: shouldn't be heap-allocated. lazy
    pub fn successors(&self) -> Vec<Index> {
        match &self.successor {
            None => vec![],
            Some(val) => match val {
                BlockSuccessor::Return(_) => vec![],
                BlockSuccessor::Jump(j) => vec![*j],
                BlockSuccessor::ConditionalJump(_, b, c) => vec![*b, *c]
            }
        }
    }

    pub fn resolve_var(&self, i: VariableIndex) -> Option<ResolvedMIRVariable> {
        if let Some(v) = self.phi_table.get(&i) {
            Some(ResolvedMIRVariable::new(i, v.0))
        } else {
            None
        }
    }

    pub fn variable_map(&self) -> &HashMap<VariableIndex, VariableGeneration> {
        &self.variable_map
    }

    pub fn variable_map_mut(&mut self) -> &mut HashMap<VariableIndex, VariableGeneration> {
        &mut self.variable_map
    }

    pub fn variables_defined(&self) -> &HashSet<VariableIndex> {
        &self.variables_defined
    }

    pub fn variables_defined_mut(&mut self) -> &mut HashSet<VariableIndex> {
        &mut self.variables_defined
    }

    fn set_successor(&mut self, s: BlockSuccessor) {
        if self.successor.is_some() {
            panic!("trying to change successor of block - should have already been calculated");
        }
        self.successor = Some(s);
    }



    pub fn predecessors(&self) -> &[Index] {
        &self.predecessors
    }

    pub fn rtrn(&mut self, rvalue: RValue) {
        self.set_successor(BlockSuccessor::Return(rvalue));
    }

    pub fn jump(&mut self, target: BasicBlockRef) {
        let target_idx = target.borrow().index();
        self.set_successor(BlockSuccessor::Jump(target_idx));
        target.borrow_mut().predecessors.push(self.index);
    }
    
    pub fn cond_jump(&mut self, condition: RValue, happy: BasicBlockRef, sad: BasicBlockRef) {
        let happy_idx = happy.borrow().index();
        let sad_idx = sad.borrow().index();
        self.set_successor(BlockSuccessor::ConditionalJump(condition, happy_idx, sad_idx));

        happy.borrow_mut().predecessors.push(self.index);
        sad.borrow_mut().predecessors.push(self.index);

    }


    pub fn index(&self) -> Index {
        self.index
    }

    pub fn new(i: Index) -> Self {
        Self {
            index: i,
            instructions: vec![],
            successor: None,
            predecessors: vec![],
            variable_map: Default::default(),
            phi_table: Default::default(),
            variables_defined: Default::default()
        }
    }

    pub fn inst(&mut self, i: Instruction) {
        self.instructions.push(i);
    }

    pub fn instructions(&self) -> &[Instruction] {
        &self.instructions
    }
}
#[derive(Clone, Copy)]
pub enum Literal {
    Number(Number),
}

pub enum RValueInstance {
    Variable(MIRVariableInstance),
    Literal(Literal),
}

pub enum RValue {
    Variable(MIRVariable),
    Literal(Literal),
}

impl RValue {
    pub fn instance(&self, blk: &BasicBlockRef) -> RValueInstance {
        match self {
            Self::Literal(l) => RValueInstance::Literal(*l),
            Self::Variable(v) => RValueInstance::Variable(v.read(blk))
        }
    }
}


pub enum Instruction {
    Add(MIRVariableInstance, RValueInstance, RValueInstance),
    Subtract(MIRVariableInstance, RValueInstance, RValueInstance),
    Divide(MIRVariableInstance, RValueInstance, RValueInstance),
    Multiply(MIRVariableInstance, RValueInstance, RValueInstance),
    Assign(MIRVariableInstance, RValueInstance),
    LessThan(MIRVariableInstance, RValueInstance, RValueInstance),
    GreaterThan(MIRVariableInstance, RValueInstance, RValueInstance),
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

impl Debug for RValueInstance {
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

            // for (var, map) in &block.borrow().phi {
            //     write!(f, "   {var:?} = phi ")?;
            //     for (idx, orig) in map {
            //         write!(f, "[#{} = {:?}]", block_idx_str(*idx), orig)?;
            //     }
            //     writeln!(f)?;
            // }

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
        s.push_str("digraph G {");
        for (index, block) in self.blocks.iter() {
            let x = block_idx_str(index);
            s.push_str(&format!("B{x} [ label = \"block {x}:\\l"));

            // for (var, map) in &block.borrow().phi {
            //     s.push_str(&format!("{var:?} = phi "));
            //     for (idx, orig) in map {
            //         s.push_str(&format!("[#{} = {:?}]", block_idx_str(*idx), orig));
            //     }
            //     s.push_str("\\l");
            // }


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
        s.push_str("}");
        s
    }
}
