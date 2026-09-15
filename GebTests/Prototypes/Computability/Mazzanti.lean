/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Mazzanti.Words -- shake: keep; #guard needs it
public meta import Geb.Prototypes.Computability.Mazzanti.Words -- shake: keep; #guard needs it

set_option doc.verso true in
/-!
# Executable algebra checks

The compiled evaluator is compared with the scanner on short words, including
empty input, leading zeroes, malformed encodings, forks, and escaped payloads.
An arity mismatch is rejected by the raw syntax validator.
-/

set_option doc.verso true

open Geb.Mazzanti
open scoped FinEnum

#guard ([[], [false], [false, false], [false, false, false],
  [true, false, false, false, false], [false, true, false, false],
  [false, true, true, false], [false, true]] : List (List Bool)).all fun w ↦
  BitTree.recognize w == [Geb.BitTree.validBool w]

/-- A substitution whose children have the wrong arity. -/
@[expose] public def invalidRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1) fun _ ↦ (Expr.constant 2 0).1.1

#guard !wellFormed invalidRaw
