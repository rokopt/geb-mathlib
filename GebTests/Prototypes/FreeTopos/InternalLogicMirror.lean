/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebMirror.Authoring -- shake: keep
public meta import GebMirror.Authoring -- shake: keep
public import GebTests.Prototypes.FreeTopos.Agreement.Encode -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.Agreement.Encode -- shake: keep

set_option doc.verso true in
/-!
# The connectives written in Geb are the internal language's

The connectives of the proof-source runner, {lit}`bootstrap/free-topos/logic.geb`, are compared
with those of {lit}`Geb.FreeTopos.Internal.Logic`: the definitions of every connective from an
index, and their introduction and elimination rules from an index, each with its derivation, as
the Lean the compiler emits from the source gives them and as the checker written in Geb
represents Lean's. The connectives and the rules of a development of version 3 are the first of
them.

## Main definitions

* {lit}`definitions` — Lean's definitions of the connectives, as the checker written in Geb
  represents definitions.
* {lit}`rules` — Lean's rules of the connectives, as it represents declarations.

## Tags

internal language, connectives, mirror, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.InternalLogicMirror

open Geb Geb.Kernel Geb.FreeTopos Geb.FreeTopos.Internal
open GebTests.Prototypes.FreeTopos.Agreement.Encode

/-- Lean's definitions of the connectives from an index, as the checker written in Geb represents
definitions. -/
def definitions (o : ℕ) : List Tree := (Logic.defs o).map encLDefn

/-- Lean's rules of the connectives, the first of an index, for the definitions from an index, as
the checker written in Geb represents declarations. -/
def rules (o j : ℕ) : List Tree := (Logic.theorems o j).map fun p ↦ encDecl (.language p.1 p.2)

-- the definitions of every connective
#guard GebMirror.Metalogic.«Logic.connectivesAll» (leaf 0) == definitions 0
#guard GebMirror.Metalogic.«Logic.connectivesAll» (leaf 211) == definitions 211

-- the rules of every connective
#guard GebMirror.Metalogic.«Logic.connectiveRulesAll» (leaf 0) (leaf 0) == rules 0 0
#guard GebMirror.Metalogic.«Logic.connectiveRulesAll» (leaf 211) (leaf 17) == rules 211 17

-- those of version 3 are the first of them
#guard GebMirror.Metalogic.«Logic.connectives» (leaf 5) == (definitions 5).take 3
#guard GebMirror.Metalogic.«Logic.connectiveRules» (leaf 5) (leaf 2) == (rules 5 2).take 5

end GebTests.Prototypes.FreeTopos.InternalLogicMirror

end
