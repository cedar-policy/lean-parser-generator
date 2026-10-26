#!/usr/bin/env python3
# Copyright Cedar Contributors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
import json, subprocess, sys, threading

BIN = ".lake/build/bin/lig-language-server"

def frame(obj):
    body = json.dumps(obj).encode("utf-8")
    return b"Content-Length: " + str(len(body)).encode() + b"\r\n\r\n" + body

bad_grammar = """%tokentype Tok
%token PLUS
%token EOF
%eof EOF
%start expr
%%
expr :: Nat
  | lhs=expr PLUS rhs=bogus { 0 }
  | PLUS { 0 }
"""

good_grammar = """%tokentype Tok
%token PLUS
%token EOF
%eof EOF
%start expr
%%
expr :: Nat
  | lhs=expr PLUS { 0 }
  | PLUS { 0 }
"""

msgs = [
    {"jsonrpc":"2.0","id":1,"method":"initialize","params":{"processId":None,"rootUri":None,"capabilities":{}}},
    {"jsonrpc":"2.0","method":"initialized","params":{}},
    {"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///tmp/bad.lig","languageId":"lig","version":1,"text":bad_grammar}}},
    {"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///tmp/bad.lig","version":2},"contentChanges":[{"text":good_grammar}]}},
    {"jsonrpc":"2.0","id":2,"method":"shutdown","params":None},
    {"jsonrpc":"2.0","method":"exit","params":None},
]

p = subprocess.Popen([BIN], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
data = b"".join(frame(m) for m in msgs)
out, err = p.communicate(data, timeout=30)

# Parse framed responses
def parse_stream(b):
    results = []
    i = 0
    while True:
        hdr_end = b.find(b"\r\n\r\n", i)
        if hdr_end == -1:
            break
        header = b[i:hdr_end].decode()
        clen = None
        for line in header.split("\r\n"):
            if line.lower().startswith("content-length:"):
                clen = int(line.split(":")[1].strip())
        if clen is None:
            break
        start = hdr_end + 4
        body = b[start:start+clen]
        results.append(json.loads(body.decode()))
        i = start + clen
    return results

print("=== server exit code:", p.returncode, "===")
if err:
    print("=== stderr ===")
    print(err.decode())
for m in parse_stream(out):
    print(json.dumps(m, indent=2))
