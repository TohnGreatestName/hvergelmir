use std::collections::HashMap;

use hvergelmir_parser::syntax::ast::{
    definition::Block,
    expr::{Expr, Factor, Term},
    statement::{Statement, VariableDeclaration},
};
use string_interner::{DefaultStringInterner, symbol::SymbolU32};

use crate::{
    block::{BasicBlock, BasicBlockRef, BlockSequence, Instruction, Literal, RValue},
    variables::Variable,
};

#[derive(Default)]
pub struct BlockBuilderContext {
    variables: HashMap<SymbolU32, Variable>,
    seq: BlockSequence
}

impl BlockBuilderContext {
    /// FIXME: declare new variables
    fn var(&mut self, s: SymbolU32) -> Variable {
        if let Some(v) = self.variables.get(&s) {
            self.seq.variables().get(v .index())
        } else {
            let v = self.seq.variables().make();
            self.variables.insert(s, v);
            v
        }
    }

    fn put_var(&mut self, s: SymbolU32, variable: Variable) {
        self.variables.insert(s, variable);
    }

    pub fn make_blocks(mut self, input: Block) -> BlockSequence {
        let b = self.seq.add_block();
        for stmt in input.statements {
            match stmt {
                Statement::VariableDeclaration(d) => {
                    let e = self.eval_expr(b.clone(), &d.value);
                    if let RValue::Variable(v) = e {
                        self.put_var(d.name.value_ref().symbol, v);
                    } else {
                        let v = self.var(d.name.value_ref().symbol);
                        b.borrow_mut().inst(Instruction::Assign(v, e));
                    };
                }
                Statement::Return(r) => {
                    let e = self.eval_expr(b.clone(), &r.value);
                    b.borrow_mut().inst(Instruction::Return(e));
                },
                Statement::Assignment(a) => {
                    let e = self.eval_expr(b.clone(), &a.value);
                    let v = self.var(a.name.value_ref().symbol);
                    b.borrow_mut().inst(Instruction::Assign(self.seq.variables().get(v.index()), e));
                }
            }
        }
        self.seq
    }

    fn eval_term(&mut self, block: BasicBlockRef, term: &Term) -> RValue {
        match term {
            Term::Parenthesised(v) => self.eval_expr(block, v),
            Term::Ident(a) => RValue::Variable(*self.variables.get(&a.value_ref().symbol).expect("FATAL: missing variable declaration")),
            Term::Number(n) => RValue::Literal(Literal::Number(n.clone().value())),
            Term::Div(a, _, b) => {
                let a = self.eval_term(block.clone(), a);
                let b = self.eval_term(block.clone(), b);
                let v = self.seq.variables().make();
                block.borrow_mut().inst(Instruction::Divide(v, a, b));
                RValue::Variable(v)
            }
            Term::Mul(a, _, b) => {
                let a = self.eval_term( block.clone(), a);
                let b = self.eval_term(block.clone(), b);
                let v = self.seq.variables().make();
                block.borrow_mut().inst(Instruction::Multiply(v, a, b));
                RValue::Variable(v)
            }
        }
    }
    fn eval_factor(&mut self, block: BasicBlockRef, fac: &Factor) -> RValue {
        match fac {
            Factor::Term(t) => self.eval_term(block, t),
            Factor::Add(a, _, b) => {
                let a = self.eval_factor(block.clone(), a);
                let b = self.eval_term(block.clone(), b);
                let v = self.seq.variables().make();
                block.borrow_mut().inst(Instruction::Add(v, a, b));
                RValue::Variable(v)
            }
            Factor::Subtract(a, _, b) => {
                let a = self.eval_factor(block.clone(), a);
                let b = self.eval_term(block.clone(), b);
                let v = self.seq.variables().make();
                block.borrow_mut().inst(Instruction::Subtract(v, a, b));
                RValue::Variable(v)
            }
        }
    }
    fn eval_expr(&mut self, b: BasicBlockRef, e: &Expr) -> RValue {
        match e {
            Expr::Factor(fac) => self.eval_factor(b, fac),
        }
    }
}
