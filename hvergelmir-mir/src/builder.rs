use std::collections::{HashMap, HashSet};

use generational_arena::Index;
use hvergelmir_parser::{lexer::token_types::Number, syntax::ast::{
    definition::Block,
    expr::{Expr, Factor, Term},
    statement::{Statement, VariableDeclaration},
}};
use string_interner::{DefaultStringInterner, symbol::SymbolU32};

use crate::{
    block::{
        BasicBlock, BasicBlockRef, BlockSequence, BlockSuccessor, Instruction, Literal, RValue,
    },
    variables::MIRVariable,
};

#[derive(Default)]
pub struct BlockBuilderContext {
    seq: BlockSequence,
    variable_stack: Vec<HashMap<SymbolU32, MIRVariable>>
}

impl BlockBuilderContext {

    fn declare_var(&mut self, b: &BasicBlockRef, s: SymbolU32) -> MIRVariable {
        let v = self.seq.variables().make(b);
        self.variable_stack.last_mut().unwrap().insert(s, v);
        v
    }

    /// FIXME: A stack structure to keep track of scope.
    fn var(&self, b: &BasicBlockRef, s: SymbolU32) -> MIRVariable {
        for mapping in self.variable_stack.iter().rev() {
            if let Some(var) = mapping.get(&s) {
                return *var
            }
        }
        panic!("var not found")
        
        // let mut scan_list = vec![blk.clone()];
        // let mut searched = HashSet::new();
        // println!("Search: {s:?}");

        // let mut outputs = HashMap::new();
        // while !scan_list.is_empty() {
        //     let v = scan_list.pop().unwrap();
        //     let mut blk_inner = v.borrow_mut();
        //     println!("Vars: {:?}", blk_inner.variables());
        //     if let Some(v) = blk_inner.variables().get(&s) {
        //         outputs.insert(blk_inner.index(), *v);
        //     } else {
        //         for p in blk_inner.predecessors() {
        //             if searched.insert(*p) {
        //                 scan_list.push(self.seq.block(*p).unwrap());
        //             }
        //         }

        //     }
        // }

        // if outputs.is_empty() {
        //     panic!("Couldn't find var")            
        // } else if outputs.len() == 1 {
        //     return outputs.into_iter().next().unwrap().1;
        // } else {
        //     let new_var = self.declare_var(blk.clone(), s);
        //     let mut blk_mut = blk.borrow_mut();
        //     let phi = blk_mut.phi_mut().entry(s).or_default();

        //     for (index, var) in outputs {
        //         phi.insert(index, var);
        //     }
        //     return new_var;
        // }

    }

    fn put_var(&mut self, blk: BasicBlockRef, s: SymbolU32, variable: MIRVariable) {
        self.variable_stack.last_mut().unwrap().insert(s, variable);
    }

    pub fn make_blocks(mut self, input: Block) -> (Index, BlockSequence) {
        let mut b = self.seq.add_block();
        let idx = {
            b.borrow().index()
        };
        self.seq.set_entry(idx);
        self.eval_block(&mut b, &input);
        (idx, self.seq)
    }

    fn eval_block(&mut self, b: &mut BasicBlockRef, input: &Block) -> BasicBlockRef {
        self.variable_stack.push(Default::default());
        let start = b.clone();
        for stmt in &input.statements {
            self.eval_stmt(b, &stmt);
        }
        self.variable_stack.pop();
        start
    }

    fn eval_stmt(&mut self, b: &mut BasicBlockRef, stmt: &Statement) {
        match stmt {
            Statement::VariableDeclaration(d) => {
                let mut v = self.declare_var(b, d.name.value_ref().symbol);
                let _ = self.eval_expr(&mut Some(v), b, &d.value);
            }
            Statement::Return(r) => {
                let mut var = None;
                let e = self.eval_expr(&mut var, b, &r.value);
                b.borrow_mut().rtrn(e);
            }
            Statement::Assignment(a) => {
                let start = self.var(b, a.name.value_ref().symbol);
                let e = self.eval_expr(&mut Some(start), b, &a.value).instance(b);

                let write = start.write(b);
                b.borrow_mut().inst(Instruction::Assign(write, e)); // FIXME: often unnecessary assignment. Not incorrect though
                
            }
            Statement::StandaloneExpression(expr) => {
                self.eval_expr(&mut None, b, &expr);
            }
        }
    }

    // FIXME: assignments to existing variables should not be making new variables
    fn eval_term(&mut self, target: &mut Option<MIRVariable>, block: &mut BasicBlockRef, term: &Term) -> RValue {
        match term {
            Term::Parenthesised(v) => self.eval_expr(target, block, v),
            Term::Ident(a) => RValue::Variable(
                self.var(block, a.value_ref().symbol)
            ),
            Term::Number(n) => {
                let val = RValue::Literal(Literal::Number(n.clone().value()));
                val
            }
            Term::Div(a, _, b) => {
                let a = self.eval_term(target, block, a).instance(block);
                let b = self.eval_term(target, block, b).instance(block);
                let target = target.get_or_insert_with(|| self.seq.variables().make(block));
                let write = target.write(block);
                block.borrow_mut().inst(Instruction::Divide(write, a, b));
                RValue::Variable(*target)
            }
            Term::Mul(a, _, b) => {
                let a = self.eval_term(target, block, a).instance(block);
                let b = self.eval_term(target, block, b).instance(block);
                let target = target.get_or_insert_with(|| self.seq.variables().make(block));
                let write = target.write(block);
                block.borrow_mut().inst(Instruction::Multiply(write, a, b));
                RValue::Variable(*target)
            }
        }
    }
    fn eval_factor(&mut self, target: &mut Option<MIRVariable>, block: &mut BasicBlockRef, fac: &Factor) -> RValue {
        match fac {
            Factor::Term(t) => self.eval_term(target, block, t),
            Factor::Add(a, _, b) => {
                let a = self.eval_factor(target, block, a).instance(block);
                let b = self.eval_term(target, block, b).instance(block);
                let target = target.get_or_insert_with(|| self.seq.variables().make(block));
                
                let write = target.write(block);
                println!("{a:?} + {b:?} = {write:?} (was {target:?}");
                block.borrow_mut().inst(Instruction::Add(write, a, b));
                RValue::Variable(*target)
            }
            Factor::Subtract(a, _, b) => {
                let a = self.eval_factor(target, block, a).instance(block);
                let b = self.eval_term(target, block, b).instance(block);
                let target = target.get_or_insert_with(|| self.seq.variables().make(block));
                let write = target.write(block);
                block.borrow_mut().inst(Instruction::Subtract(write, a, b));
                RValue::Variable(*target)
            }
            Factor::LessThan(a, _, b) => {
                let a = self.eval_factor(target, block, a).instance(block);
                let b = self.eval_term(target, block, b).instance(block);
                let target = target.get_or_insert_with(|| self.seq.variables().make(block));;
                let write = target.write(block);
                block.borrow_mut().inst(Instruction::LessThan(write, a, b));
                RValue::Variable(*target)
            },
            Factor::GreaterThan(a, _, b) => {
                let a = self.eval_factor(target, block, a).instance(block);
                let b = self.eval_term(target, block, b).instance(block);
                let target = target.get_or_insert_with(|| self.seq.variables().make(block));
                let write = target.write(block);
                block.borrow_mut().inst(Instruction::GreaterThan(write, a, b));
                RValue::Variable(*target)
            }
        }
    }
    fn eval_expr(&mut self, target: &mut Option<MIRVariable>, b: &mut BasicBlockRef, e: &Expr) -> RValue {
        match e {
            Expr::Factor(fac) => self.eval_factor(target, b, fac),
            Expr::While(e) => {
                let mut condition_block = self.seq.add_block();

                // immediately jump to the condition block
                let cond_start = condition_block.clone();
                {
                    b.borrow_mut().jump(condition_block.clone());
                }
                let evaluated_condition = self.eval_expr(target, &mut condition_block, &e.expr);

                let mut target_block = self.seq.add_block();
                {
                    target_block
                    .borrow_mut()
                    .jump(cond_start.clone());
                }

                let successor_block = self.seq.add_block();

                {
                    condition_block.borrow_mut().cond_jump(evaluated_condition, target_block.clone(), successor_block.clone());

                }
                self.eval_block(&mut target_block, &e.block);



    
                *b = successor_block; // now, we're working in this final successor block.
                    
                    // FIXME: proper evaluation of a value.
                RValue::Literal(Literal::Number(Number { value: (0, 0) }))
            }
        }
    }
}
