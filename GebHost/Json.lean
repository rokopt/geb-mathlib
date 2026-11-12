/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Lean.Data.Json

set_option doc.verso true in
/-!
# JSON at the host boundary

Objects are constructed by inserting their fields into the standard tree map. Requests use
the standard JSON parser's value parser, checking that it consumes the complete input.
Whitespace is skipped with the list operations, over the string decoder admitted by the
repository's axiom audit. These interfaces avoid unapproved classical dependencies of the
standard convenience wrappers.

Source names and prose travel as byte arrays. Their UTF-8 decoding belongs to the editor,
while paths already read as host strings remain JSON strings.

## Main definitions

* {lit}`object` — construct an object by a fold of map insertions.
* {lit}`parse` — parse a value and reject trailing input.
* {lit}`readInput` — read a request through the stream's native line reader.

## Tags

JSON, host, protocol
-/

set_option doc.verso true

public section

namespace GebHost.Json

/-- An object constructed by inserting its fields in order. Later duplicate fields replace
earlier ones; the host supplies distinct field names. -/
def object (fields : List (String × Lean.Json)) : Lean.Json :=
  .obj (fields.foldl (fun map (key, value) ↦ map.insert key value) ∅)

/-- Parse a JSON value using the standard value parser and require the remaining input to
be empty. The list decoder is covered by the repository's existing upstream axiom audit. -/
def parse (text : String) : Except String Lean.Json :=
  let text := String.ofList (text.toList.dropWhile fun c ↦
    c == ' ' || c == '\t' || c == '\n' || c == '\r')
  match Lean.Json.Parser.anyCore ⟨text, text.startPos⟩ with
  | .success pos value =>
    if pos.2.offset.byteIdx == text.utf8ByteSize then .ok value
    else .error "trailing input after the JSON request"
  | .error _ _ => .error "invalid JSON request"

/-- Read all request lines through the stream's native UTF-8 reader. -/
def readInput (stream : IO.FS.Stream) : IO String :=
  IO.iterate "" fun text ↦ do
    let line ← stream.getLine
    return if line.isEmpty then .inr text else .inl (text ++ line)

end GebHost.Json
