/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

module
/-
A Language Server Protocol server providing live diagnostics for `.lig` grammar
files.

It is a small, self-contained stdio server built directly on Lean's own LSP
primitives (`Lean.Data.Lsp`, `Lean.Data.JsonRpc`, `Lean.Data.Lsp.Communication`
for `Content-Length` framing). It keeps an in-memory copy of every open document
and, on open/change, runs `Frontend.collectDiagnostics` and publishes the results
via `textDocument/publishDiagnostics`.

Document synchronization is *full* (`TextDocumentSyncKind.full`): the client
sends the whole document text on every change, which is the simplest correct
mode and is plenty for grammar files.

Supported messages:

  • `initialize`                     → advertise full text sync + open/close
  • `initialized`                    → ignored
  • `textDocument/didOpen`           → store + publish diagnostics
  • `textDocument/didChange`         → update + publish diagnostics
  • `textDocument/didClose`          → drop + clear diagnostics
  • `shutdown` / `exit`              → orderly shutdown
  • any other request                → `methodNotFound` (so clients never hang)

The analysis itself lives in `Frontend/Diagnostics.lean` and is a pure function,
so it is unit-tested independently of this transport layer.
-/
public import Lean.Data.Lsp
public import Lean.Data.JsonRpc
public import LeanParserGenerator.Frontend.Diagnostics


@[expose] public section

open Lean
open Lean.Lsp
open Lean.JsonRpc


namespace LeanParserGenerator.LSP

/-- Server state: the text of every open document plus lifecycle flags. -/
structure ServerState where
  /-- Latest text for each open document URI (association list). -/
  docs : List (DocumentUri × String) := []
  /-- Whether a `shutdown` request has been received. -/
  shutdownReceived : Bool := false

/-- Decode notification/request parameters into a typed payload. -/
def parseParams (α) [FromJson α] (params? : Option Json.Structured) : Except String α :=
  let j : Json := match params? with
    | some s => Json.Structured.toJson s
    | none => Json.null
  fromJson? j

/-- Map an engine severity to its LSP counterpart. -/
def toLspSeverity : Frontend.DiagSeverity → DiagnosticSeverity
  | .error => .error
  | .warning => .warning
  | .information => .information

/-- Convert one engine diagnostic to an LSP diagnostic, resolving byte offsets to
    line/character positions against the current document text. -/
def toLspDiagnostic (text : String) (d : Frontend.LigDiagnostic) : Diagnostic :=
  let (sl, sc) := Frontend.byteToLineCol text d.startByte
  let (el, ec) := Frontend.byteToLineCol text d.endByte
  { range := { start := ⟨sl, sc⟩, «end» := ⟨el, ec⟩ }
    severity? := some (toLspSeverity d.severity)
    source? := "lig"
    message := d.message }

/-- Analyze `text` and publish diagnostics for `uri`. -/
def publishDiagnostics (out : IO.FS.Stream) (uri : DocumentUri) (text : String) : IO Unit := do
  let diagnostics := (Frontend.collectDiagnostics text).map (toLspDiagnostic text)
  let params : PublishDiagnosticsParams := { uri, diagnostics }
  out.writeLspNotification { method := "textDocument/publishDiagnostics", param := params }

/-- Clear diagnostics for `uri` (publish an empty set). -/
def clearDiagnostics (out : IO.FS.Stream) (uri : DocumentUri) : IO Unit := do
  let params : PublishDiagnosticsParams := { uri, diagnostics := #[] }
  out.writeLspNotification { method := "textDocument/publishDiagnostics", param := params }

/-- The `initialize` result: advertise full document sync and open/close events. -/
def initializeResult : Json :=
  Json.mkObj [
    ("capabilities", Json.mkObj [
      ("textDocumentSync", Json.mkObj [
        ("openClose", Json.bool true),
        ("change", Json.num (1 : Nat))  -- TextDocumentSyncKind.Full
      ])
    ]),
    ("serverInfo", Json.mkObj [
      ("name", Json.str "lig-language-server"),
      ("version", Json.str "0.1.0")
    ])
  ]

/-- Store (replacing any prior copy) the text of a document. -/
def upsertDoc (st : ServerState) (uri : DocumentUri) (text : String) : ServerState :=
  { st with docs := (uri, text) :: st.docs.filter (·.1 != uri) }

/-- The full text carried by the last content change of a `didChange`, if any.
    With full sync every change is a `fullChange` carrying the whole document. -/
def latestChangeText? (changes : Array TextDocumentContentChangeEvent) : Option String :=
  changes.back?.map fun
    | .fullChange t => t
    | .rangeChange _ t => t

/-- Handle a single incoming message. Returns `false` to stop the loop (`exit`). -/
def handleMessage (out : IO.FS.Stream) (stRef : IO.Ref ServerState) : JsonRpc.Message → IO Bool
  | .request id "initialize" _ => do
    out.writeLspMessage (.response id initializeResult)
    return true
  | .request id "shutdown" _ => do
    stRef.modify fun s => { s with shutdownReceived := true }
    out.writeLspMessage (.response id Json.null)
    return true
  | .request id method _ => do
    out.writeLspMessage (.responseError id ErrorCode.methodNotFound s!"method not supported: {method}" none)
    return true
  | .notification "initialized" _ => return true
  | .notification "exit" _ => return false
  | .notification "textDocument/didOpen" params? => do
    match parseParams DidOpenTextDocumentParams params? with
    | .ok p =>
      let uri := p.textDocument.uri
      let text := p.textDocument.text
      stRef.modify (upsertDoc · uri text)
      publishDiagnostics out uri text
    | .error _ => pure ()
    return true
  | .notification "textDocument/didChange" params? => do
    match parseParams DidChangeTextDocumentParams params? with
    | .ok p =>
      let uri := p.textDocument.uri
      match latestChangeText? p.contentChanges with
      | some text =>
        stRef.modify (upsertDoc · uri text)
        publishDiagnostics out uri text
      | none => pure ()
    | .error _ => pure ()
    return true
  | .notification "textDocument/didClose" params? => do
    match parseParams DidCloseTextDocumentParams params? with
    | .ok p =>
      let uri := p.textDocument.uri
      stRef.modify fun s => { s with docs := s.docs.filter (·.1 != uri) }
      clearDiagnostics out uri
    | .error _ => pure ()
    return true
  | .notification _ _ => return true
  | .response _ _ => return true
  | .responseError _ _ _ _ => return true

/-- Read and dispatch messages until the stream closes or an `exit` arrives. -/
partial def serve (inp out : IO.FS.Stream) (stRef : IO.Ref ServerState) : IO Unit := do
  let msg? ← (do return some (← inp.readLspMessage)) <|> pure none
  match msg? with
  | none => return ()  -- stream closed
  | some msg =>
    let continue? ← handleMessage out stRef msg
    if continue? then serve inp out stRef else return ()

/-- Entry point: run the `.lig` language server over stdio. -/
def main (_args : List String) : IO UInt32 := do
  let inp ← IO.getStdin
  let out ← IO.getStdout
  let stRef ← IO.mkRef ({} : ServerState)
  serve inp out stRef
  let st ← stRef.get
  return (if st.shutdownReceived then 0 else 1)

end LeanParserGenerator.LSP
