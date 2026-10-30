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

//! Rust lexer and parser for Cedar policies, generated from `cedar.lig`
//! (`leanparsergenerator --backend rust`). See docs/RUST_PARSER.md.

pub mod cst;
pub mod generated;
pub mod hooks;

use generated::{Entry, LexError, Node, ParseError, Spanned, Tok};

/// Reusable buffers for the parse stack and the parse trace, so repeated parses do not
/// allocate them. The tokens borrow the source, so they live in a vector the caller
/// owns for as long as the source.
#[derive(Default)]
pub struct Parser {
    pub stack: Vec<Entry>,
    pub nodes: Vec<Node>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    Lex(LexError),
    Parse(ParseError),
}

impl Parser {
    pub fn new() -> Self {
        Self::default()
    }

    /// Lex `src` into `tokens` (cleared first) and parse it; the postorder trace is left
    /// in `self.nodes`.
    pub fn parse<'a>(
        &mut self,
        src: &'a str,
        tokens: &mut Vec<Spanned<Tok<'a>>>,
    ) -> Result<(), Error> {
        tokens.clear();
        generated::tokenize(src, tokens).map_err(Error::Lex)?;
        generated::parse(tokens, &mut self.stack, &mut self.nodes).map_err(Error::Parse)
    }
}
