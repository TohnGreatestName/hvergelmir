use std::collections::HashMap;

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
    variables::Variable,
};

#[derive(Default)]
pub struct BlockBuilderContext {
    variables: HashMap<SymbolU32, Variable>,
    seq: BlockSequence,
}

impl BlockBuilderContext {
    /// FIXME: declare new variables
    fn var(&mut self, s: SymbolU32) -> Variable {
        if let Some(v) = self.variables.get(&s) {
            self.seq.variables().get(v.index())
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
        self.eval_block(&input);
        self.seq
    }

    fn eval_block(&mut self, input: &Block) -> (BasicBlockRef, BasicBlockRef) {
        let mut b = self.seq.add_block();
        let start = b.clone();
        for stmt in &input.statements {
            self.eval_stmt(&mut b, &stmt);
        }
        (start, b)
    }

    fn eval_stmt(&mut self, b: &mut BasicBlockRef, stmt: &Statement) {
        match stmt {
            Statement::VariableDeclaration(d) => {
                let e = self.eval_expr(b, &d.value);
                if let RValue::Variable(v) = e {
                    self.put_var(d.name.value_ref().symbol, v);
                } else {
                    let v = self.var(d.name.value_ref().symbol);
                    b.borrow_mut().inst(Instruction::Assign(v, e));
                };
            }
            Statement::Return(r) => {
                let e = self.eval_expr(b, &r.value);
                b.borrow_mut().set_successor(BlockSuccessor::Return(e));
            }
            Statement::Assignment(a) => {
                let e = self.eval_expr(b, &a.value);
                if let RValue::Variable(v) = e {
                    self.put_var(a.name.value_ref().symbol, v);
                } else {
                    let v = self.var(a.name.value_ref().symbol);
                    b.borrow_mut()
                        .inst(Instruction::Assign(self.seq.variables().get(v.index()), e));
                }
            }
            Statement::StandaloneExpression(expr) => {
                self.eval_expr(b, &expr);
            }
        }
    }

    fn eval_term(&mut self, block: &mut BasicBlockRef, term: &Term) -> RValue {
        match term {
            Term::Parenthesised(v) => self.eval_expr(block, v),
            Term::Ident(a) => RValue::Variable(
                *self
                    .variables
                    .get(&a.value_ref().symbol)
                    .expect("FATAL: missing variable declaration"),
            ),
            Term::Number(n) => RValue::Literal(Literal::Number(n.clone().value())),
            Term::Div(a, _, b) => {
                let a = self.eval_term(block, a);
                let b = self.eval_term(block, b);
                let v = self.seq.variables().make();
                block.borrow_mut().inst(Instruction::Divide(v, a, b));
                RValue::Variable(v)
            }
            Term::Mul(a, _, b) => {
                let a = self.eval_term(block, a);
                let b = self.eval_term(block, b);
                let v = self.seq.variables().make();
                block.borrow_mut().inst(Instruction::Multiply(v, a, b));
                RValue::Variable(v)
            }
        }
    }
    fn eval_factor(&mut self, block: &mut BasicBlockRef, fac: &Factor) -> RValue {
        match fac {
            Factor::Term(t) => self.eval_term(block, t),
            Factor::Add(a, _, b) => {
                let a = self.eval_factor(block, a);
                let b = self.eval_term(block, b);
                let v = self.seq.variables().make();
                block.borrow_mut().inst(Instruction::Add(v, a, b));
                RValue::Variable(v)
            }
            Factor::Subtract(a, _, b) => {
                let a = self.eval_factor(block, a);
                let b = self.eval_term(block, b);
                let v = self.seq.variables().make();
                block.borrow_mut().inst(Instruction::Subtract(v, a, b));
                RValue::Variable(v)
            }
            Factor::LessThan(a, _, b) => {
                let a = self.eval_factor(block, a);
                let b = self.eval_term(block, b);
                let v = self.seq.variables().make();
                block.borrow_mut().inst(Instruction::LessThan(v, a, b));
                RValue::Variable(v)
            },
            Factor::GreaterThan(a, _, b) => {
                let a = self.eval_factor(block, a);
                let b = self.eval_term(block, b);
                let v = self.seq.variables().make();
                block.borrow_mut().inst(Instruction::GreaterThan(v, a, b));
                RValue::Variable(v)
            }
        }
    }
    fn eval_expr(&mut self, b: &mut BasicBlockRef, e: &Expr) -> RValue {
        match e {
            Expr::Factor(fac) => self.eval_factor(b, fac),
            Expr::While(e) => {
                let mut condition_block = self.seq.add_block();

                // immediately jump to the condition block
                let cond_start_index = condition_block.borrow().index();
                b.borrow_mut()
                    .set_successor(BlockSuccessor::Jump(cond_start_index));
                let evaluated_condition = self.eval_expr(&mut condition_block, &e.expr);

                let (target_block, _) = self.eval_block(&e.block);

                target_block
                    .borrow_mut()
                    .set_successor(BlockSuccessor::Jump(cond_start_index));

                let successor_block = self.seq.add_block();
                condition_block
                    .borrow_mut()
                    .set_successor(BlockSuccessor::ConditionalJump(
                        evaluated_condition,
                        target_block.borrow().index(),
                        successor_block.borrow().index(),
                    ));
                
                *b = successor_block; // now, we're working in this final successor block.
                    
                    // FIXME: proper evaluation of a value.
                RValue::Literal(Literal::Number(Number { value: (0, 0) }))
            }
        }
    }
}
