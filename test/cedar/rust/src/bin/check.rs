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

//! Prints one line per file argument, in the format of the Lean differential driver:
//! `<path> ok`, `<path> lex`, or `<path> parse <token index> <state> <lookahead>`.
//! With `--tokens` it prints `<path> <terminal>:<start>-<end> …`, the end-of-input token
//! included, or `<path> lexerr <position>`. `--values` adds each token's value after its
//! span (`I`dentifier, `O`ther slot, `S`tring literal: hex of the bytes; `N`umber).

use cedar_rust_parser::{generated, Error, Parser};

fn hex(s: &str) -> String {
    s.bytes().map(|b| format!("{b:02x}")).collect()
}

fn value_of(t: &generated::Tok<'_>) -> String {
    use generated::Tok;
    match t {
        Tok::IDENTIFIER(s) => format!("I{}", hex(s)),
        Tok::OTHER_SLOT(s) => format!("O{}", hex(s)),
        Tok::STRINGLIT(s) => format!("S{}", hex(s)),
        Tok::NUMBER(n) => format!("N{n}"),
        _ => String::new(),
    }
}

fn main() {
    let mut p = Parser::new();
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let values = args.first().map(|a| a == "--values").unwrap_or(false);
    if values || args.first().map(|a| a == "--tokens").unwrap_or(false) {
        args.remove(0);
        for path in args {
            let src = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
            let mut toks = Vec::new();
            match cedar_rust_parser::generated::tokenize(&src, &mut toks) {
                Ok(()) => {
                    let parts: Vec<String> = toks
                        .iter()
                        .map(|t| format!(
                                "{}:{}-{}{}",
                                generated::Terminal::term(&t.tok),
                                t.start,
                                t.end,
                                if values { value_of(&t.tok) } else { String::new() }
                            ))
                        .collect();
                    println!("{path} {}", parts.join(" "));
                }
                Err(e) => println!("{path} lexerr {}", e.pos),
            }
        }
        return;
    }
    for path in args {
        let src = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
        let mut tk = Vec::new();
        match p.parse(&src, &mut tk) {
            Ok(()) => println!("{path} ok"),
            Err(Error::Lex(_)) => println!("{path} lex"),
            Err(Error::Parse(e)) => println!("{path} parse {} {} {}", e.token, e.state, e.term),
        }
    }
}
