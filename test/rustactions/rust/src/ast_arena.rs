//! The AST of the Rust actions in `rustarena.lig`: the same as `ast.rs`, with the nodes and
//! lists allocated in the arena of `arena.rs` instead of the heap.

use crate::arena::lists::List;
use crate::generated_arena::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Op {
    Add,
    Sub,
    Mul,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr<'a> {
    Num(i64),
    Var(&'a str),
    Str(&'a str),
    Len(u64),
    Neg(&'a Expr<'a>),
    Bin(Op, &'a Expr<'a>, &'a Expr<'a>),
    Call(&'a str, List<'a, Expr<'a>>),
    Cond(&'a Expr<'a>, &'a Expr<'a>, Option<&'a Expr<'a>>),
    Pair(&'a (Expr<'a>, Expr<'a>)),
    Triple(&'a (Expr<'a>, Expr<'a>, Expr<'a>)),
    Located(&'a str, Span),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt<'a> {
    Bind { name: &'a str, value: Expr<'a>, index: u64 },
    Print(Expr<'a>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Program<'a> {
    pub stmts: List<'a, Stmt<'a>>,
    pub count: u64,
}
