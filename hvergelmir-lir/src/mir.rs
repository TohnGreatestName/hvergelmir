use std::{collections::{HashMap, VecDeque}};

use generational_arena::Index;
use hvergelmir_mir::block::BlockSequence;

use crate::{InstructionIndex, LIRFunction, Platform};

pub fn translate_blocks<P: Platform>(b: BlockSequence) -> LIRFunction {
    
    let mut instructions = vec![];

    let mut block_lookup: HashMap<Index, InstructionIndex> = HashMap::new();

    let mut to_translate = VecDeque::new();
    to_translate.push_back(b.entry());
    
    while !to_translate.is_empty() {
        let blk = b.block(to_translate.pop_front().unwrap()).unwrap();

        

    }



    LIRFunction { instructions }

}