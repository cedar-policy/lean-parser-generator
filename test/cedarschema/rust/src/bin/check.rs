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

//! Prints `<path> ok`, `<path> lex`, or `<path> parse` for each file argument.

use cedarschema_rust_parser::{parse_str, Error};

fn main() {
    for path in std::env::args().skip(1) {
        let src = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
        match parse_str(&src) {
            Ok(_) => println!("{path} ok"),
            Err(Error::Lex(_)) => println!("{path} lex"),
            Err(Error::Parse(_)) => println!("{path} parse"),
            Err(Error::Check(e)) => println!("{path} check {e:?}"),
        }
    }
}
