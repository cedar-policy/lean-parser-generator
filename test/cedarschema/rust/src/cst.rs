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

//! The Rust CST built by the Rust actions of `CedarSchema.lig`. It follows `CedarSchemaAst.lean`
//! (which mirrors `cedar_schema/ast.rs` of cedar-policy-core without locations), with lists as
//! `VecDeque`s (the grammar's lists are right-recursive) and owned strings.

use std::cell::Cell;
use std::collections::VecDeque;

pub fn cons<T>(head: T, mut tail: VecDeque<T>) -> VecDeque<T> {
    tail.push_front(head);
    tail
}

/// A schema identifier: a keyword or a name.
#[derive(Clone, Debug, PartialEq)]
pub enum Ident {
    NamespaceKw,
    EntityKw,
    SetKw,
    AppliesToKw,
    PrincipalKw,
    ActionKw,
    ResourceKw,
    ContextKw,
    AttributesKw,
    TagsKw,
    BoolKw,
    LongKw,
    StringKw,
    TypeKw,
    InKw,
    EnumKw,
    Ident(String),
}

impl Ident {
    /// The source text (`Ident.toString`).
    pub fn into_string(self) -> String {
        match self {
            Ident::Ident(s) => s,
            Ident::NamespaceKw => "namespace".to_string(),
            Ident::EntityKw => "entity".to_string(),
            Ident::SetKw => "Set".to_string(),
            Ident::AppliesToKw => "appliesTo".to_string(),
            Ident::PrincipalKw => "principal".to_string(),
            Ident::ActionKw => "action".to_string(),
            Ident::ResourceKw => "resource".to_string(),
            Ident::ContextKw => "context".to_string(),
            Ident::AttributesKw => "attributes".to_string(),
            Ident::TagsKw => "tags".to_string(),
            Ident::BoolKw => "Bool".to_string(),
            Ident::LongKw => "Long".to_string(),
            Ident::StringKw => "String".to_string(),
            Ident::TypeKw => "type".to_string(),
            Ident::InKw => "in".to_string(),
            Ident::EnumKw => "enum".to_string(),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Path {
    pub prefix: Vec<Ident>,
    pub basename: Ident,
}

/// A `Path` from a nonempty list of components, most significant first.
pub fn path_from_components(mut components: Vec<Ident>) -> Path {
    let basename = components.pop().unwrap_or(Ident::Ident(String::new()));
    Path { prefix: components, basename }
}

/// The last component, as a string.
pub fn basename_string(mut components: Vec<Ident>) -> String {
    components.pop().map(Ident::into_string).unwrap_or_default()
}

#[derive(Clone, Debug, PartialEq)]
pub struct Eid(pub String);

#[derive(Clone, Debug, PartialEq)]
pub enum QualName {
    Unqualified(String),
    Qualified(Path, String),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Annotation {
    pub key: Ident,
    pub value: Option<String>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Annotated<T> {
    pub data: T,
    pub annotations: VecDeque<Annotation>,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum PR {
    Principal,
    Resource,
}

#[derive(Clone, Debug, PartialEq)]
pub enum SType {
    Ident(Path),
    Set(Box<SType>),
    Record(VecDeque<AnnAttr>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct AttrDecl {
    pub name: String,
    pub required: bool,
    pub ty: SType,
}

pub type AnnAttr = Annotated<AttrDecl>;

#[derive(Clone, Debug, PartialEq)]
pub enum AppDecl {
    Pr(PR, Option<VecDeque<Path>>),
    ContextPath(Path),
    ContextRecord(VecDeque<AnnAttr>),
}

/// `Some(xs)` unless `xs` is empty.
pub fn some_if_nonempty<T>(xs: VecDeque<T>) -> Option<VecDeque<T>> {
    if xs.is_empty() {
        None
    } else {
        Some(xs)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StandardEntityDecl {
    pub names: VecDeque<Ident>,
    pub member_of_types: VecDeque<Path>,
    pub attrs: VecDeque<AnnAttr>,
    pub tags: Option<SType>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct EnumEntityDecl {
    pub names: VecDeque<Ident>,
    pub choices: VecDeque<Eid>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum EntityDecl {
    Standard(Box<StandardEntityDecl>),
    Enum(Box<EnumEntityDecl>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct ActionDecl {
    pub names: VecDeque<String>,
    pub parents: Option<VecDeque<QualName>>,
    pub app_decls: Option<VecDeque<AppDecl>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct TypeDecl {
    pub name: Ident,
    pub definition: SType,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Declaration {
    Entity(EntityDecl),
    Action(Box<ActionDecl>),
    Type(Box<TypeDecl>),
}

pub type AnnDecl = Annotated<Declaration>;

#[derive(Clone, Debug, PartialEq)]
pub struct Namespace {
    pub name: Option<Path>,
    pub decls: VecDeque<AnnDecl>,
}

pub type AnnNamespace = Annotated<Namespace>;

#[derive(Clone, Debug, PartialEq)]
pub struct Schema {
    pub namespaces: VecDeque<AnnNamespace>,
}

/// What cedar-policy-core's schema grammar rejects in its actions (`=>?`) and the CST does not
/// show: a reserved identifier, a repeated annotation key, a string with a bad escape sequence.
/// A Rust action cannot fail, so it records the first error here (`%option rust_ctx`) and
/// `parse` returns it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CheckError {
    ReservedIdentifier(String),
    DuplicateAnnotation(String),
    StringEscape,
}

#[derive(Default)]
pub struct Checks {
    first: Cell<Option<CheckError>>,
}

impl Checks {
    fn fail(&self, e: CheckError) {
        let cur = self.first.take();
        self.first.set(cur.or(Some(e)));
    }

    /// The first error since the last call.
    pub fn take(&self) -> Option<CheckError> {
        self.first.take()
    }
}

/// `Ident := AnyIdent` minus the reserved words.
pub fn check_ident(ctx: &Checks, id: Ident) -> Ident {
    match &id {
        Ident::InKw => ctx.fail(CheckError::ReservedIdentifier("in".to_string())),
        Ident::Ident(s)
            if matches!(s.as_str(), "true" | "false" | "if" | "then" | "else" | "is" | "like" | "has") =>
        {
            ctx.fail(CheckError::ReservedIdentifier(s.clone()))
        }
        _ => {}
    }
    id
}

/// A literal with its escape sequences replaced; a bad sequence is recorded.
pub fn unescape(ctx: &Checks, raw: &str) -> String {
    let mut out = String::with_capacity(raw.len());
    if !raw.contains('\\') {
        out.push_str(raw);
        return out;
    }
    let mut bad = false;
    rustc_literal_escaper::unescape_str(raw, |_, r| match r {
        Ok(c) => out.push(c),
        Err(e) if e.is_fatal() => bad = true,
        Err(_) => {}
    });
    if bad {
        ctx.fail(CheckError::StringEscape);
    }
    out
}

/// `Annotated<E>`: the annotation keys must be distinct.
pub fn annotated<T>(ctx: &Checks, data: T, annotations: VecDeque<Annotation>) -> Annotated<T> {
    for (i, a) in annotations.iter().enumerate() {
        if annotations.iter().skip(i + 1).any(|b| b.key == a.key) {
            ctx.fail(CheckError::DuplicateAnnotation(a.key.clone().into_string()));
            break;
        }
    }
    Annotated { data, annotations }
}
