//! The hand-written AST of the Rust actions in `rustactions.lig`. It borrows its strings
//! from the source text and does not mirror `RustActions.*`.

use crate::generated::Span;
use std::collections::VecDeque;

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
    Neg(Box<Expr<'a>>),
    Bin(Op, Box<Expr<'a>>, Box<Expr<'a>>),
    Call(&'a str, VecDeque<Expr<'a>>),
    Cond(Box<Expr<'a>>, Box<Expr<'a>>, Option<Box<Expr<'a>>>),
    Pair(Box<(Expr<'a>, Expr<'a>)>),
    Triple(Box<(Expr<'a>, Expr<'a>, Expr<'a>)>),
    Located(&'a str, Span),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt<'a> {
    Bind { name: &'a str, value: Expr<'a>, index: u64 },
    Print(Expr<'a>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Program<'a> {
    pub stmts: VecDeque<Stmt<'a>>,
    pub count: u64,
}
