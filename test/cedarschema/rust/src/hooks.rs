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

//! The Rust counterparts of the two Lean functions of `CedarSchema.lig`'s lexer that are not
//! in the library: `keywordOrIdentifier` and `stripStringQuotes`. The Lean definitions are the
//! specification.

use crate::generated::Tok;

pub fn keyword_or_identifier(text: &str) -> Option<Tok<'_>> {
    Some(match text {
        "namespace" => Tok::NAMESPACE,
        "entity" => Tok::ENTITY,
        "in" => Tok::IN,
        "type" => Tok::TYPE,
        "Set" => Tok::SET,
        "appliesTo" => Tok::APPLIESTO,
        "principal" => Tok::PRINCIPAL,
        "action" => Tok::ACTION,
        "resource" => Tok::RESOURCE,
        "context" => Tok::CONTEXT,
        "attributes" => Tok::ATTRIBUTES,
        "tags" => Tok::TAGS,
        "Long" => Tok::LONG,
        "String" => Tok::STRING,
        "Bool" => Tok::BOOL,
        "enum" => Tok::ENUM,
        _ => Tok::IDENTIFIER(text),
    })
}

/// Removes the first and the last character (the quotes).
pub fn strip_string_quotes(text: &str) -> Option<&str> {
    let mut cs = text.chars();
    cs.next();
    cs.next_back();
    Some(cs.as_str())
}
