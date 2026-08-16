/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.Computability.CobhamFoldProto.Initial
public import Geb.Mathlib.Data.W.Basic

/-!
# The term algebra's destructor in the fold's language

The inverse of the initial algebra's structure map, as expressions of
Cobham's class, at the representation `RankedAlphabet.spell` fixes.

`codeOf` and `dropCodeOf` read a word's leading block and what follows it,
through a constant unary prefix that makes the word a self-delimiting entry
whose payload is that block, so no dispatch over the block is needed.

## Main definitions

* `Geb.CobhamFold.codeOf`, `Geb.CobhamFold.dropCodeOf` — the block reader and
  its complement.

## Main statements

* `Geb.CobhamFold.stepWord_codeOf`, `Geb.CobhamFold.stepWord_dropCodeOf` —
  what those two compute at an arbitrary word.
* `Geb.CobhamFold.stepWord_codeOf_spell_mk`,
  `Geb.CobhamFold.stepWord_dropCodeOf_spell_mk` — what they recover from a
  spelling.

## References

* [Cobham1965]
* [Strahm2003]

## Tags

Cobham, ranked tree, destructor, self-delimiting, subterm
-/

@[expose] public section

namespace Geb.CobhamFold

open Cobham RankedAlphabet

/-- The leading block of a word, as an expression of arity one: a constant
unary prefix of the alphabet's width makes the word a self-delimiting entry
whose payload is that block. -/
def codeOf (R : RankedAlphabet) : COf 1 :=
  comp1Of takeEntryOf (prependOf (List.replicate R.width true ++ [false]) idOf)

/-- The word past its leading block, by the same prefix. -/
def dropCodeOf (R : RankedAlphabet) : COf 1 :=
  comp1Of dropEntryOf (prependOf (List.replicate R.width true ++ [false]) idOf)

/-- The prefixed word, in the shape the payload primitives read. -/
private theorem stepWord_prefix (R : RankedAlphabet) (w : List Bool) :
    stepWord (prependOf (List.replicate R.width true ++ [false]) idOf) w =
      List.replicate R.width true ++ false :: w := by
  rw [stepWord_prependOf, stepWord_idOf, List.append_assoc]
  rfl

/-- The block reader truncates to the alphabet's width. -/
theorem stepWord_codeOf (R : RankedAlphabet) (w : List Bool) :
    stepWord (codeOf R) w = w.take R.width := by
  rw [codeOf, stepWord_comp1Of, stepWord_prefix, stepWord_takeEntryOf,
    takeEntrySem_replicate]

/-- Its complement drops the alphabet's width. -/
theorem stepWord_dropCodeOf (R : RankedAlphabet) (w : List Bool) :
    stepWord (dropCodeOf R) w = w.drop R.width := by
  rw [dropCodeOf, stepWord_comp1Of, stepWord_prefix, stepWord_dropEntryOf,
    dropEntrySem_replicate]

/-- At a spelling the block reader recovers the head symbol's block. -/
theorem stepWord_codeOf_spell_mk (R : RankedAlphabet) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) :
    stepWord (codeOf R) (R.spell (Term.mk R i ch)) = R.code i := by
  rw [stepWord_codeOf, spell_mk, List.take_left' (R.length_code i)]

/-- And its complement recovers the children's spellings. -/
theorem stepWord_dropCodeOf_spell_mk (R : RankedAlphabet) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) :
    stepWord (dropCodeOf R) (R.spell (Term.mk R i ch)) =
      (List.ofFn fun d ↦ R.spell (ch d)).flatten := by
  rw [stepWord_dropCodeOf, spell_mk, List.drop_left' (R.length_code i)]

end Geb.CobhamFold

end
