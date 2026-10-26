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
public import cedarschema.CedarSchemaLexer
public import cedarschema.CedarSchemaParser
-- `native_decide`/`#eval` reduce the generated parser & lexer, so they are meta-imported.
meta import cedarschema.CedarSchemaLexer
meta import cedarschema.CedarSchemaParser


public section

open Lexer CedarSchema CedarSchemaParser

/-! Cedar schema lexer/parser regressions against `cedar-spec`'s
`validator/cedar_schema/grammar.lalrpop`. Source positions, the
annotation-deduplication error, and reserved-word rejection are intentionally
outside this port. -/

private def parseStr (input : String) : Option Schema :=
  input |> CedarSchemaLexer.tokenize |>.toOption.bind (parse · 30)

private def accepts (source : String) : Bool := (parseStr source).isSome
private def rejects (source : String) : Bool := (parseStr source).isNone

/-- A single unqualified entity decl with no members/attrs/tags. -/
def test_empty_entity : Bool :=
  accepts "entity User;"

/-- Multiple names bound at once, and a member-of list. -/
def test_entity_members : Bool :=
  accepts "entity User, Group in [Team, Org];"

/-- Entity with an attribute record, optional `?` attr, and a `Set<>` type. -/
def test_entity_attrs : Bool :=
  accepts "entity Photo { owner: User, tags?: Set<String>, size: Long };"

/-- The `=` before the record body is optional. -/
def test_entity_eq_record : Bool :=
  accepts "entity Photo = { owner: User };"

/-- Tags clause after the attribute block. -/
def test_entity_tags : Bool :=
  accepts "entity Doc { name: String } tags Set<String>;"

/-- Enumerated entity. -/
def test_enum_entity : Bool :=
  accepts "entity Color enum [\"red\", \"green\", \"blue\"];"

/-- Type (common-type) declaration. -/
def test_type_decl : Bool :=
  accepts "type Email = String;"

/-- A record common type. -/
def test_type_record : Bool :=
  accepts "type Point = { x: Long, y: Long };"

/-- Action with principal/resource/context appliesTo and an attributes block. -/
def test_action_full : Bool :=
  accepts "action view appliesTo { principal: [User], resource: Photo, context: { ip: String } } attributes {};"

/-- Action with an `in` parent list of qualified names. -/
def test_action_parents : Bool :=
  accepts "action view in [Admin::\"root\", readOnly];"

/-- Named namespace wrapping declarations. -/
def test_namespace : Bool :=
  accepts "namespace App { entity User; action view appliesTo { principal: [User], resource: [Doc] }; }"

/-- Annotations on a declaration. -/
def test_annotations : Bool :=
  accepts "@doc(\"an entity\") @internal entity User;"

/-- Qualified type path in a member-of position. -/
def test_qualified_path : Bool :=
  accepts "entity User in [App::Groups::Team];"

/-- Missing terminating semicolon must be rejected. -/
def test_reject_no_semi : Bool :=
  rejects "entity User"

/-- A bare `::` with no leading ident is not a path. -/
def test_reject_bad_path : Bool :=
  rejects "entity ::User;"

/-- The QualName disambiguation: `Ns::"eid"` is a qualified UID, parsed as an
action parent, distinct from a plain path. -/
def test_qualname_uid : Bool :=
  accepts "action a in Ns::Sub::\"theAction\";"

/-- Exact-CST check for the path/qualname spine: `entity A in B::C::D;` yields a
member-of path with prefix `[B, C]` and basename `D`. -/
def test_path_spine_shape : Bool :=
  match parseStr "entity A in B::C::D;" with
  | some ⟨[⟨⟨none, [⟨.entity (.standard sed), _⟩]⟩, _⟩]⟩ =>
      sed.memberOfTypes ==
        [⟨[.ident "B", .ident "C"], .ident "D"⟩]
  | _ => false

def allSchemaTests : List (String × Bool) :=
  [ ("empty_entity", test_empty_entity),
    ("entity_members", test_entity_members),
    ("entity_attrs", test_entity_attrs),
    ("entity_eq_record", test_entity_eq_record),
    ("entity_tags", test_entity_tags),
    ("enum_entity", test_enum_entity),
    ("type_decl", test_type_decl),
    ("type_record", test_type_record),
    ("action_full", test_action_full),
    ("action_parents", test_action_parents),
    ("namespace", test_namespace),
    ("annotations", test_annotations),
    ("qualified_path", test_qualified_path),
    ("reject_no_semi", test_reject_no_semi),
    ("reject_bad_path", test_reject_bad_path),
    ("qualname_uid", test_qualname_uid),
    ("path_spine_shape", test_path_spine_shape) ]

def schemaTestsPass : Bool := allSchemaTests.all (fun (t : String × Bool) => t.2)

/-- Fails to elaborate if any regression is false. -/
example : schemaTestsPass = true := by native_decide

#eval do
  for (name, ok) in allSchemaTests do
    if !ok then IO.eprintln s!"FAILED: {name}"
  IO.println s!"cedar schema parser: {(allSchemaTests.filter (fun (t : String × Bool) => t.2)).length}/{allSchemaTests.length} passed"
