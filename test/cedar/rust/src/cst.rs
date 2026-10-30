// Copyright Cedar Contributors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! The Rust CST built by the Rust actions in `cedar.lig`. It was written out once from the
//! Lean CST (`test/cedar/CedarAst.lean`, which mirrors `cedar-policy-core`'s `cst.rs`) and is
//! maintained by hand: lists are `VecDeque`s, strings are owned, and large fields are boxed.

#![allow(non_snake_case)]

use std::collections::VecDeque;

pub fn cons<T>(head: T, mut tail: VecDeque<T>) -> VecDeque<T> {
    tail.push_front(head);
    tail
}

pub fn append<T>(mut front: VecDeque<T>, back: VecDeque<T>) -> VecDeque<T> {
    front.extend(back);
    front
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub struct Policies {
    pub policies: std::collections::VecDeque<Policy>,
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub struct Annotation {
    pub key: Ident,
    pub value: Box<Option<Str>>,
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum Policy {
    Policy(PolicyImpl),
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub struct VariableDef {
    pub variableName: Box<Ident>,
    pub unusedTypeName: Box<Option<Name>>,
    pub entityType: Box<Option<Add>>,
    pub ineq: Option<(RelOp, Expr)>,
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub struct Name {
    pub path: std::collections::VecDeque<Ident>,
    pub name: Ident,
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum Add {
    Mk(Box<Mult>, std::collections::VecDeque<(AddOp, Mult)>),
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum RelOp {
    Less,
    LessEq,
    GreaterEq,
    Greater,
    NotEq,
    Eq,
    InOp,
    InvalidSingleEq,
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum Expr {
    Expr(Box<ExprImpl>),
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub struct Cond {
    pub cond: Ident,
    pub expr: Expr,
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum Or {
    Mk(Box<And>, std::collections::VecDeque<And>),
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum And {
    Mk(Box<Relation>, std::collections::VecDeque<Relation>),
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum Relation {
    Common(Box<Add>, std::collections::VecDeque<(RelOp, Add)>),
    Has(Box<Add>, Box<Add>),
    Like(Box<Add>, Box<Add>),
    IsIn(Box<Add>, Box<Add>, Box<Option<Add>>),
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum AddOp {
    Plus,
    Minus,
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum MultOp {
    Times,
    Divide,
    Mod,
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum Mult {
    Mk(Box<Unary>, std::collections::VecDeque<(MultOp, Unary)>),
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum Unary {
    Mk(Option<NegOp>, Box<Member>),
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum Member {
    Mk(Box<Primary>, std::collections::VecDeque<MemAccess>),
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum MemAccess {
    Field(Ident),
    Call(std::collections::VecDeque<Expr>),
    Index(Expr),
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum Primary {
    Literal(Literal),
    Ref(Box<Ref>),
    Name(Name),
    Slot(Slot),
    Expr(Box<Expr>),
    ExprList(std::collections::VecDeque<Expr>),
    Record(std::collections::VecDeque<RecInit>),
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum RecInit {
    Mk(Expr, Expr),
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum Ident {
    Principal,
    Action,
    Resource,
    Context,
    TrueIdent,
    FalseIdent,
    Permit,
    Forbid,
    When,
    Unless,
    InIdent,
    Has,
    Like,
    Is,
    IfIdent,
    ThenIdent,
    ElseIdent,
    Ident(String),
    Invalid(String),
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub struct RefInit {
    pub field: Ident,
    pub literal: Box<Literal>,
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum Literal {
    TrueLit,
    FalseLit,
    Num(u64),
    Str(Str),
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum Str {
    String(String),
    Invalid(String),
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub struct PolicyImpl {
    pub annotations: std::collections::VecDeque<Annotation>,
    pub effect: Ident,
    pub variables: std::collections::VecDeque<VariableDef>,
    pub conds: std::collections::VecDeque<Cond>,
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum ExprImpl {
    Mk(Box<ExprData>),
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum NegOp {
    Bang(u64),
    OverBang,
    Dash(u64),
    OverDash,
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum Ref {
    Uid(Box<Name>, Str),
    Ref(Name, std::collections::VecDeque<RefInit>),
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum Slot {
    Principal,
    Resource,
    Other(String),
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum ExprData {
    Or(Box<Or>),
    IfThenElse(Box<Expr>, Box<Expr>, Box<Expr>),
}

/// `Cedar.Name.fromComponents`: the last component is the name, the rest the path.
pub fn name_from_components(mut components: VecDeque<Ident>) -> Name {
    match components.pop_back() {
        Some(name) => Name { path: components, name },
        // Lean's `default`: no path and the first identifier constructor.
        None => Name { path: VecDeque::new(), name: Ident::Principal },
    }
}

fn primary_to_add(primary: Primary, access: VecDeque<MemAccess>) -> Add {
    Add::Mk(
        Box::new(Mult::Mk(
            Box::new(Unary::Mk(None, Box::new(Member::Mk(Box::new(primary), access)))),
            VecDeque::new(),
        )),
        VecDeque::new(),
    )
}

/// `Cedar.Add.fromIdent`.
pub fn add_from_ident(identifier: Ident, access: VecDeque<MemAccess>) -> Add {
    primary_to_add(Primary::Name(Name { path: VecDeque::new(), name: identifier }), access)
}

/// `Cedar.Expr.fromIdent`: the full precedence wrapper around a bare identifier.
pub fn expr_from_ident(identifier: Ident) -> Expr {
    let add = add_from_ident(identifier, VecDeque::new());
    Expr::Expr(Box::new(ExprImpl::Mk(Box::new(ExprData::Or(Box::new(Or::Mk(
        Box::new(And::Mk(
            Box::new(Relation::Common(Box::new(add), VecDeque::new())),
            VecDeque::new(),
        )),
        VecDeque::new(),
    )))))))
}
