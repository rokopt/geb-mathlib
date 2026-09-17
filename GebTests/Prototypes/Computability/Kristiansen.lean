/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Kristiansen.Basic
import Geb.Prototypes.Computability.Kristiansen.Reference
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Word-algebra checks

Nullary composition, mutual recursion, and suffix references, including empty
words. The two mutually recursive parity components exchange their previous
values on a true bit, checking that step results are computed simultaneously.

## Tags

function algebra, simultaneous recursion, test
-/

set_option doc.verso true

namespace GebTests.Kristiansen

open Geb.Kristiansen

/-- Complementary parity components: empty for even parity and a singleton for odd parity. -/
public def parity (j : Fin 2) : LOf 1 :=
  srnOf (fun i ↦ constOf 0 (if i = 0 then [] else [true]))
    (fun bit i ↦ projOf 3
      (if bit then if i = 0 then 2 else 1 else if i = 0 then 1 else 2)) j

example : (parity 0).sem ![[]] = [] := rfl
example : (parity 1).sem ![[]] = [true] := rfl
example : (parity 0).sem ![[true]] = [true] := rfl
example : (parity 1).sem ![[true]] = [] := rfl
example : (parity 0).sem ![[true, false, true]] = [] := rfl
example : (parity 1).sem ![[true, false, true]] = [true] := rfl

example : (compOf (n := 0) (constOf 0 [true]) Fin.elim0).sem ![] = [true] := rfl

example : ¬ Allowed (Geb.SizeBounded.sbsOf false).1.1 := fun h ↦ h.1

/-- A suffix of length one reads the final bit of the original input. -/
theorem reference_one :
    Reference.value (K := 0) (x := ![[true, false]]) (.inr ⟨0, 1⟩) = [false] := rfl
example : Reference.value (K := 0) (x := ![[true, false]]) (.inr ⟨0, 0⟩) = [] := rfl
example : Reference.value (K := 0) (x := ![[]]) (.inr ⟨0, 0⟩) = [] := rfl

end GebTests.Kristiansen
