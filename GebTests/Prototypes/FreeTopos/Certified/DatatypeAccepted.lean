/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.RepresentLogic
public import Geb.Prototypes.FreeTopos.Internal.Unfolded
public import GebTests.Prototypes.FreeTopos.DatatypeBase
public import GebTests.Prototypes.ProgramCommand
public meta import Geb.Prototypes.FreeTopos.Internal.RepresentLogic -- shake: keep
public meta import Geb.Prototypes.FreeTopos.Internal.Unfolded -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.DatatypeBase -- shake: keep

set_option doc.verso true in
/-!
# The constants of the datatype language's soundness are accepted

The constants of the program the datatype language's soundness is stated in, the translated
compilers extended by the relations' definitions, are ones the developments' soundness reads
({name}`Geb.FreeTopos.Internal.Globals.accepted`): each definition compiles over the
definitions before it, the check accepts the primitive arrows and the definitions, and the
definitions they compile to are well formed. Lean's evaluator decides it. The theory of a topos
extended by those definitions therefore has models, in each of which the constants' invariant
holds, so that the validity of a development's theorems in every model of the program is that
of each of them.

The module states the other facts about the compilers' program that Lean's evaluator decides
for the soundness's transfer to Lean: the constants of the translation alone are accepted
too, and the definitions the compiler's passes call have, in the types the translation records,
the kernel types named with them.

## Main definitions

* {lit}`translatedGlobals` — the constants of the translation of the compilers' program.
* {lit}`passGlobals` — the definitions the compiler's passes call, with their kernel types.

## Main statements

* {lit}`accepted` — the constants of the extended program are accepted.
* {lit}`hasLogic` — they have the connectives' definitions from the index the program names.
* {lit}`translatedAccepted` — the constants of the translation alone are accepted.
* {lit}`passGlobalsTyped` — the definitions the passes call have the kernel types named.

## Tags

internal language, datatypes, definitional extension, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeAccepted

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)
open Kernel (tT tList tProd tArrow)
open scoped FinEnum

/-- Whether the constants of a program, where one is given, are ones the check accepts that
compile to well-formed definitions ({name}`Geb.FreeTopos.Internal.Globals.accepted`). -/
def acceptedIn {α : Type} (o : Option α) (G : α → Internal.Globals) : Bool :=
  match o with
  | some P => (G P).accepted
  | none => false

set_option doc.verso false in
/-- The constants of the extended program are accepted and compile to well-formed definitions,
as Lean's evaluator decides. -/
evaluation_axiom constantsAccepted : acceptedIn extended3 (·.1.G) = true

/-- The constants of the extended program are accepted. -/
theorem accepted {PST : Prog × Defs × Defs3} (h : extended3 = some PST) :
    PST.1.G.accepted = true := by
  have ha := constantsAccepted
  rw [h] at ha
  exact ha

/-- Whether the constants of a program, where one is given, have the connectives' definitions
from the index it names ({name}`Geb.FreeTopos.Internal.Globals.hasLogic`). -/
def hasLogicIn {α : Type} (o : Option α) (G : α → Internal.Globals) (i : α → ℕ) : Bool :=
  match o with
  | some P => (G P).hasLogic (i P)
  | none => false

set_option doc.verso false in
/-- The constants of the extended program have the connectives' definitions from the index the
program names, as Lean's evaluator decides. -/
evaluation_axiom logicPresent : hasLogicIn extended3 (·.1.G) (·.1.o) = true

/-- The constants of the extended program have the connectives' definitions. -/
theorem hasLogic {PST : Prog × Defs × Defs3} (h : extended3 = some PST) :
    Internal.HasLogic PST.1.G PST.1.o := by
  have ha := logicPresent
  rw [h] at ha
  exact Internal.Globals.hasLogic_sound ha

/-- The constants of the translation of the bundled compilers' program, where the program
bundles and translates. -/
def translatedGlobals : Option Internal.Globals := do
  let ds ← Weakening.bundled Geb.Kernel.Stage0Tests.bundler.toList programText.toList
  let (_, defs) ← Translation.program (ds.map Prod.snd)
  pure (Translation.globals defs)

set_option doc.verso false in
/-- The constants of the translation of the bundled compilers' program are accepted and compile
to well-formed definitions, as Lean's evaluator decides. -/
evaluation_axiom translatedAccepted : acceptedIn translatedGlobals id = true

/-- The bundled definitions of the compilers' program with the kernel types the translation
records for them, where the program bundles and translates. -/
def bundledTypes : Option (List (List Char × PartialHorn.Tree) × List PartialHorn.Tree) := do
  let ds ← Weakening.bundled Geb.Kernel.Stage0Tests.bundler.toList programText.toList
  let (gt, _) ← Translation.program (ds.map Prod.snd)
  pure (ds, gt)

/-- Whether each of the named definitions, among bundled definitions with their kernel types
where given, has the kernel type given with its name. -/
def typedIn (o : Option (List (List Char × PartialHorn.Tree) × List PartialHorn.Tree))
    (l : List (String × Kernel.Tree)) : Bool :=
  match o with
  | some (ds, gt) => l.all fun p ↦
    match ds.findIdx? fun d ↦ d.1 == p.1.toList with
    | some i => decide (gt[i]? = some p.2)
    | none => false
  | none => false

/-- The kernel type of the typing environment: its lists of trees. -/
def envTy : Kernel.Tree :=
  tProd (tList tT) (tProd (tList tT) (tProd (tList tT) (tProd (tList tT)
    (tProd (tList tT) (tList tT)))))

/-- The names of the compilers' definitions the passes call, each with its kernel type. -/
def passGlobals : List (String × Kernel.Tree) :=
  [("Datatype.expandTyped", tArrow (tList tT) (tProd tT (tList tT))),
    ("Typing/OName.nothing", tT),
    ("Typing.checkAll", tArrow (tProd envTy tT) (tArrow (tList tT) (tProd envTy tT))),
    ("Typing.env0", envTy),
    ("Datatype.markersFirst", tArrow (tList tT) (tList tT)),
    ("Recognize.insertRecognizers", tArrow (tList tT) tT),
    ("Datatype.kernelForms", tArrow (tList tT) (tList tT)),
    ("Reader.readProgram", tArrow (tList tT) tT),
    ("Prelude.get", tArrow tT tT),
    ("Prelude.isSome", tArrow tT tT),
    ("Check.checkProgram", tArrow (tList tT) tT)]

set_option doc.verso false in
/-- The compilers' definitions the passes call have the kernel types named with them, in the
types the translation records, as Lean's evaluator decides. -/
evaluation_axiom passGlobalsTyped : typedIn bundledTypes passGlobals = true

end GebTests.Prototypes.FreeTopos.Certified.DatatypeAccepted

end
