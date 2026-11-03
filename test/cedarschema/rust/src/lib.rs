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

//! Rust lexer and parser for Cedar schemas, generated from `CedarSchema.lig`
//! (`%option gen_rust`). See docs/RUST_PARSER.md.

pub mod cst;
pub mod generated;
pub mod hooks;

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    Lex(generated::LexError),
    Parse(generated::ParseError),
    /// Rejected by a check of the grammar's actions (see `cst::CheckError`).
    Check(cst::CheckError),
}

/// Lex and parse `src` and build the CST (`generated::parse_values`), with the checks of
/// cedar-policy-core's schema grammar. `tokens` and `stacks` are buffers the caller can reuse
/// across calls; `checks` records the first rejected construct.
pub fn parse<'a>(
    src: &'a str,
    tokens: &mut Vec<generated::Token>,
    stacks: &mut generated::Stacks<'a>,
    checks: &'a cst::Checks,
) -> Result<cst::Schema, Error> {
    tokens.clear();
    generated::tokenize(src, tokens).map_err(Error::Lex)?;
    checks.take();
    let schema = generated::parse_values(src, tokens, stacks, checks).map_err(Error::Parse)?;
    match checks.take() {
        Some(e) => Err(Error::Check(e)),
        None => Ok(schema),
    }
}

/// `parse` with fresh buffers.
pub fn parse_str(src: &str) -> Result<cst::Schema, Error> {
    let checks = cst::Checks::default();
    parse(src, &mut Vec::new(), &mut generated::Stacks::new(), &checks)
}
