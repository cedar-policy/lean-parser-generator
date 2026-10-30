//! The Rust counterparts of the two Lean functions of `cedar.lig`'s lexer that are not in
//! the library: `keywordOrIdentifier` and `stripStringQuotes`. The Lean definitions
//! are the specification. `IDENTIFIER` carries `{s // s ∉ keywords}` in Lean; here it is a
//! string slice, and the keyword check below is what makes the invariant true.

use crate::generated::Tok;

pub fn keyword_or_identifier(text: &str) -> Option<Tok<'_>> {
    Some(match text {
        "true" => Tok::TRUE,
        "false" => Tok::FALSE,
        "if" => Tok::IF,
        "permit" => Tok::PERMIT,
        "forbid" => Tok::FORBID,
        "when" => Tok::WHEN,
        "unless" => Tok::UNLESS,
        "in" => Tok::IN,
        "has" => Tok::HAS,
        "like" => Tok::LIKE,
        "is" => Tok::IS,
        "then" => Tok::THEN,
        "else" => Tok::ELSE,
        "principal" => Tok::PRINCIPAL,
        "action" => Tok::ACTION,
        "resource" => Tok::RESOURCE,
        "context" => Tok::CONTEXT,
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
