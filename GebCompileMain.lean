/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.Kernel.Command
import GebBoot

/-!
# Compiled bootstrap compiler entry point

Run the Lean the bootstrap compiler emits from its own source with
`lake exe geb-compile image|lean INPUT OUTPUT`: `image` compiles a program's source file to its
image, and `lean` to a Lean module. The file driver is `Geb.Kernel.Command.runFile`.

The compiler's entry points return the empty tree for a program they reject. The driver then
reports on standard error what rejects it, exits with status 1 and leaves the output file
untouched, so that an empty output is never written for a failure. It finds what rejects the
program by running the compiler's stages in the order of `Compile.bundleOf`, each stage's
definitions being those the compiled compiler holds.

## Main definitions

* `GebCompileMain.rejection`: what rejects a program the compiler rejects.
* `main`: select the compiler's entry point and run it on a file.

## Tags

bootstrap, compiler, diagnostics, command line
-/

open Geb.Kernel

namespace GebCompileMain

/-- A stage's optional result, or the message of its failure. -/
def required (t : Tree) (msg : Unit → String) : Except String Tree :=
  if (GebBoot.«Prelude.isSome» t).label ≠ 0 then .ok (GebBoot.«Prelude.get» t) else .error (msg ())

/-- The position of the first element whose prefix a test of prefixes rejects. -/
def firstRejected (ok : List Tree → Bool) (es : List Tree) : Option Nat :=
  (List.range es.length).find? fun k ↦ !ok (es.take (k + 1))

/-- A nonempty name a tree holds. -/
def nameString? (t : Tree) : Option String :=
  match ofNameTree t with
  | some (c :: cs) => some (String.ofList (c :: cs))
  | _ => none

/-- A form of a program at a position, named by the atom after its head where it has one. -/
def formAt (es : List Tree) (k : Nat) : String :=
  match es[k]? |>.bind (·.children[1]?) with
  | some n =>
    if (GebBoot.«Reader.isAtom» n).label ≠ 0 then
      (nameString? (GebBoot.«Reader.nameOf» n)).getD s!"form {k + 1}"
    else s!"form {k + 1}"
  | none => s!"form {k + 1}"

/-- The first form a test of a program's prefixes rejects. -/
def firstFormRejected (ok : List Tree → Bool) (es : List Tree) : String :=
  match firstRejected ok es with
  | some k => formAt es k
  | none => "the program"

/-- The message of the seed's elaboration of a program's modules, which the elaboration in the
compiler agrees with on what it rejects and which alone says why. -/
def modulesFailure (file : Tree) : String :=
  let unknown := "the modules do not elaborate"
  match readSExps (file.children.map fun c ↦ Char.ofNat c.label) with
  | none => unknown
  | some es =>
    match elabModules es with
    | .error msg => msg
    | .ok _ => unknown

/-- The failure of a definition the typing names. Module elaboration writes a template's instance
at opaque arguments under a prefix holding the reserved `%generic`, which no source writes. -/
def checkFailure (n : String) : String :=
  let marker := "%generic"
  if (n.splitOn marker).length > 1 then
    s!"{n.replace marker ""} does not check at its template's opaque parameters"
  else s!"{n} does not check"

/-- The first stage of the compiler that rejects a program, as a message. -/
def rejection (file : Tree) : Except String Unit := do
  let sx ← required (GebBoot.«Reader.readSExps» file.children) fun _ ↦
    "the text is not well formed or its parentheses do not balance"
  if (GebBoot.«Compile.userSource» sx).label = 0 then
    throw "an atom outside a quotation or a datum begins with %, which the implementation reserves"
  let mx ← required (GebBoot.«Modules.expandModules» sx.children) fun _ ↦ modulesFailure file
  let es := mx.children
  if let some n := nameString? (GebBoot.«Datatype.typeErrorOfForms» es) then
    throw (checkFailure n)
  let expands (fs : List Tree) := (GebBoot.«Datatype.expandProgram» fs).label ≠ 0
  let kx ← required (GebBoot.«Datatype.expandProgram» es) fun _ ↦
    s!"{firstFormRejected expands es} does not expand"
  let rx ← required (GebBoot.«Recognize.insertRecognizers» kx.children) fun _ ↦
    "the recognizers of the program's datatypes cannot be written"
  let fs := rx.children
  let reads (gs : List Tree) := (GebBoot.«Reader.readProgram» gs).label ≠ 0
  let b ← required (GebBoot.«Reader.readProgram» fs) fun _ ↦
    s!"{firstFormRejected reads fs} does not read: its name is reserved or declared before, " ++
      "or a name in it does not resolve"
  let terms := (b.children.getD 0 (mk 0 [])).children
  let names := (b.children.getD 1 (mk 0 [])).children
  let checks (ts : List Tree) := (GebBoot.«Check.checkProgram» ts).label ≠ 0
  if !checks terms then
    throw <| match firstRejected checks terms with
      | some k => s!"{(names[k]?.bind nameString?).getD s!"definition {k + 1}"} is ill-typed"
      | none => "the program is ill-typed"

/-- What rejects a program, or that no stage does and the backend wrote nothing. -/
def rejectionMessage (file : Tree) : String :=
  match rejection file with
  | .error msg => msg
  | .ok () => "the backend writes nothing for the program"

/-- An entry point's output, or the message of what rejects the program of a named source. -/
def compiled (entry : Tree → Tree) (input : String) (file : Tree) : Except String Tree :=
  let out := entry file
  if out == mk 0 [] then .error s!"{input}: {rejectionMessage file}" else .ok out

/-- Compile a source file through an entry point, reporting a failure on standard error. -/
def compileFile (name : String) (entry : Tree → Tree) (input output : String) : IO UInt32 := do
  try
    Command.runFile name (compiled entry input) input output
    return 0
  catch e =>
    IO.eprintln e
    return 1

end GebCompileMain

/-- Run the compiled bootstrap compiler on a file. -/
public def main : List String → IO UInt32
  | ["image", input, output] => GebCompileMain.compileFile "main" GebBoot.«main» input output
  | ["lean", input, output] => GebCompileMain.compileFile "mainLean" GebBoot.«mainLean» input output
  | _ => do
    IO.eprintln "usage: geb-compile image|lean INPUT OUTPUT"
    return 2
