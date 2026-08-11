/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Mathlib.Data.Tree.Ranked.Basic

import Geb.Mathlib.Computability.Cobham.Fold

/-!
# The fold at a worked carrier

A three-element carrier encoded in two bits, whose decoding is not injective
off the image of the encoding: the fourth bit family spells no carrier value
and decodes to the same value as the third. The retraction hypothesis
`foldSem_eq` takes therefore holds without `dec` being an inverse, which is
what the fixture is chosen to exhibit.

## Main definitions

* `counterEnc`, `counterDec`, `counterStep` — the carrier's encoding, its
  decoding, and the step a bit induces.
* `counterFold` — the fold's value as a function of the word.
* `counterFoldArity` — the fold at its declared arity.
* `counterShift` — an order-sensitive step, whose branches do not commute.
* `counterDecBad` — a decoding that is not a retraction.

## Main statements

* `counterDec_counterEnc` — the decoding is a retraction of the encoding
  without being injective.
* `counterFold_values` — the fold at words whose expected value is written
  out.
* `counterFold_eq` — the fold's agreement with the carrier-level fold, from
  the retraction hypothesis at this decoding.
* `counterFold_init_values` — the fold at a nonzero initial value, showing
  the base is the encoded initial value rather than the zero word.
* `counterShift_values` — a word and its reverse take different values under
  `counterShift`, exhibiting the fold's consumption order.
* `counterFoldBad_values` — the fold at a constant decoding, showing its
  value differs from `counterFold`'s while its width does not.
* `counterFold_sweep` — the same agreement computed in the kernel over every
  word of length at most seven.

## Implementation notes

The assertions reduce in the kernel, by `decide`; `#eval` would require a
`public meta import` of the module under test, since the fold's value calls
`Cobham.constAt`, a non-`meta` declaration of another module of this package,
whose IR is not otherwise available to meta code across the boundary.

The sweep length is measured rather than conventional. At length seven the
sweep closes under `set_option maxRecDepth 100000 in decide`; at length eight
it reaches the heartbeat limit. Each step of the fold is a dispatch over two
bits followed by a constant word, and the case tree is a `Nat.rec`, so one
reduction follows a single root-to-leaf path.

## Tags

Cobham, bounded recursion on notation, fold, catamorphism
-/

set_option linter.privateModule false

open Cobham

/-- A three-element carrier encoded in two bits, the family `![true, true]`
spelling no carrier value. -/
def counterEnc : Fin 3 → Fin 2 → Bool :=
  fun a j ↦ ![![false, false], ![true, false], ![false, true]] a j

/-- The decoding, which sends the unreached family `![true, true]` to the same
value as `![false, true]`, so it is not injective off the image of
`counterEnc` while remaining a retraction of it. -/
def counterDec : (Fin 2 → Bool) → Fin 3 :=
  fun v ↦ if v 1 then 2 else if v 0 then 1 else 0

/-- The carrier-level step: a `true` bit advances the counter. -/
def counterStep : Bool → Fin 3 → Fin 3 :=
  fun b a ↦ if b then a + 1 else a

/-- The fold's value at the counter, as a function of the word. -/
def counterFold (w : List Bool) : List Bool :=
  foldSem counterEnc counterDec 0 counterStep ![w]

/-- The decoding is a retraction of the encoding without being injective:
`![false, true]` and `![true, true]` decode alike. -/
theorem counterDec_counterEnc :
    (∀ a, counterDec (counterEnc a) = a) ∧
      counterDec ![false, true] = counterDec ![true, true] :=
  ⟨fun a ↦ match a with | 0 => rfl | 1 => rfl | 2 => rfl, rfl⟩

/-- The fold's value at the words written out, the counter having advanced
once per `true` bit and wrapped at three. -/
theorem counterFold_values :
    counterFold [] = [false, false] ∧
      counterFold [true] = [true, false] ∧
      counterFold [true, true] = [false, true] ∧
      counterFold [true, true, true] = [false, false] ∧
      counterFold [false, true, false, true] = [false, true] := by decide

/-- The fold agrees with the carrier-level fold at every word, from the
retraction hypothesis at a decoding that is not injective. -/
theorem counterFold_eq (w : List Bool) :
    counterFold w = List.ofFn (counterEnc (w.foldr counterStep 0)) :=
  foldSem_eq counterEnc counterDec 0 counterStep counterDec_counterEnc.1 w

/-- The base is the encoded initial value, not the zero word: at a nonzero
initial value the empty word already carries that value's spelling. -/
theorem counterFold_init_values :
    foldSem counterEnc counterDec 1 counterStep ![[]] = [true, false] ∧
      foldSem counterEnc counterDec 1 counterStep ![[true]] = [false, true] := by
  decide

/-- The fold at its declared arity: this module's only use of `Cobham.foldOf`,
the assertions above reading `Cobham.foldSem` instead. -/
def counterFoldArity : COf 1 := foldOf counterEnc counterDec 0 counterStep

/-- An order-sensitive step: a `true` bit advances the counter, a `false` bit
doubles it. Unlike `counterStep`, its two branches do not commute. -/
def counterShift : Bool → Fin 3 → Fin 3 := fun b a ↦ if b then a + 1 else a + a

/-- The word's last bit is consumed first and the head's step applied to the
fold of the rest: a word and its reverse take different values, which no step
with commuting branches could exhibit. -/
theorem counterShift_values :
    foldSem counterEnc counterDec 0 counterShift ![[true, false]] = [true, false] ∧
      foldSem counterEnc counterDec 0 counterShift ![[false, true]] = [false, true] := by
  decide

/-- A decoding that is not a retraction: the fold still produces states of the
encoding's width, `length_foldSem` taking no retraction hypothesis. -/
def counterDecBad : (Fin 2 → Bool) → Fin 3 := fun _ ↦ 0

/-- At a constant decoding every step reads the same carrier value, so the
fold's value differs from `counterFold`'s while its width does not. -/
theorem counterFoldBad_values :
    foldSem counterEnc counterDecBad 0 counterStep ![[true, true]] = [true, false] ∧
      (foldSem counterEnc counterDecBad 0 counterStep ![[true, false, true]]).length = 2 := by
  decide

/-- The same agreement read off the reduced values, over every word of length
at most seven. -/
theorem counterFold_sweep :
    (wordsUpTo 7).all (fun w ↦
      counterFold w == List.ofFn (counterEnc (w.foldr counterStep 0))) = true := by
  set_option maxRecDepth 100000 in decide
