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

//! Prints the parse tree of a Cedar file as an indented outline, rebuilt from the
//! postorder trace that `generated::parse` returns. See docs/USING_RUST_GENERATOR.md.

use cedar_rust_parser::generated::{nonterm_name, prod_len, prod_lhs, term_name, Node, PROD_FLAG};
use cedar_rust_parser::Parser;

struct Tree {
    node: Node,
    children: Vec<Tree>,
}

/// Rebuild the tree: a token node is a leaf, and a production node takes the last
/// `prod_len(p)` subtrees as its children.
fn build(nodes: &[Node]) -> Vec<Tree> {
    let mut stack: Vec<Tree> = Vec::new();
    for &node in nodes {
        let children = if node.kind & PROD_FLAG != 0 {
            let n = prod_len((node.kind & !PROD_FLAG) as usize);
            stack.split_off(stack.len() - n)
        } else {
            Vec::new()
        };
        stack.push(Tree { node, children });
    }
    stack
}

fn print(t: &Tree, src: &str, depth: usize) {
    let n = t.node;
    let text = &src[n.start as usize..n.end as usize];
    if n.kind & PROD_FLAG != 0 {
        let lhs = prod_lhs((n.kind & !PROD_FLAG) as usize);
        println!("{}{} [{}..{}]", "  ".repeat(depth), nonterm_name(lhs), n.start, n.end);
    } else {
        println!("{}{} {:?}", "  ".repeat(depth), term_name(n.kind), text);
    }
    for c in &t.children {
        print(c, src, depth + 1);
    }
}

fn main() {
    let path = std::env::args().nth(1).expect("usage: tree <file.cedar>");
    let src = std::fs::read_to_string(&path).unwrap();
    let mut p = Parser::new();
    let mut tokens = Vec::new();
    if let Err(e) = p.parse(&src, &mut tokens) {
        eprintln!("{path}: {e:?}");
        std::process::exit(1);
    }
    for t in build(&p.nodes) {
        print(&t, &src, 0);
    }
}
