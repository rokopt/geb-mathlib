/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Internal.FoldSpike

/-!
# The fold at a worked carrier, across a module boundary

Does a `decide` over the fold reduce when the definitions arrive from another
module? This is the question the mirror under `GebTests/` will face.

## Main definitions

* `counterEnc`, `counterDec`, `counterStep`, `counterFold` — a three-element
  carrier in two bits, whose decoding is not injective off the encoding's
  image.

## Main statements

* `counterFold_reduces`, `counterFold_sweep_seven` — the fold's values, and
  its agreement with the carrier-level fold over an enumeration of words.

## Tags

Cobham, bounded recursion on notation, fold, catamorphism
-/

set_option linter.privateModule false

open Cobham

/-- A three-element carrier encoded in two bits, one of the four bit families
spelling no carrier value. -/
def counterEnc : Fin 3 → Fin 2 → Bool :=
  fun a j ↦ ![![false, false], ![true, false], ![false, true]] a j

/-- The decoding, which sends the unreached family `![true, true]` to the same
value as `![false, true]`, so it is not injective off the image of
`counterEnc`. -/
def counterDec : (Fin 2 → Bool) → Fin 3 :=
  fun v ↦ if v 1 then 2 else if v 0 then 1 else 0

/-- The carrier-level step: a `true` bit advances the counter. -/
def counterStep : Bool → Fin 3 → Fin 3 :=
  fun b a ↦ if b then a + 1 else a

/-- The fold's value at the counter, as a function of the word. -/
def counterFold (w : List Bool) : List Bool :=
  foldSem counterEnc counterDec 0 counterStep ![w]

/-- Does the fold's value reduce in the kernel at a literal carrier? -/
theorem counterFold_reduces :
    counterFold [] = [false, false] ∧
      counterFold [true] = [true, false] ∧
      counterFold [true, true] = [false, true] ∧
      counterFold [true, true, true] = [false, false] ∧
      counterFold [false, true, false, true] = [false, true] := by decide

/-- The words over `Bool` of at most the given length, each once. -/
def spikeWordsUpTo : ℕ → List (List Bool) :=
  Nat.rec [[]] fun _ ih ↦ [] :: ih.flatMap fun w ↦ [false :: w, true :: w]

/-- How far does a sweep of the fold against the carrier-level fold reduce? -/
theorem counterFold_sweep_seven :
    (spikeWordsUpTo 7).all (fun w ↦
      counterFold w == List.ofFn (counterEnc (w.foldr counterStep 0))) = true := by
  set_option maxRecDepth 100000 in decide


#print axioms counterFold_sweep_seven

/-- The decoding is a retraction of the encoding without being injective:
`![false, true]` and `![true, true]` decode alike. -/
theorem counterDec_counterEnc :
    (∀ a, counterDec (counterEnc a) = a) ∧
      counterDec ![false, true] = counterDec ![true, true] :=
  ⟨fun a ↦ match a with | 0 => rfl | 1 => rfl | 2 => rfl, rfl⟩

/-- The fold agrees with the carrier-level fold at every word, from the
retraction hypothesis at a decoding that is not injective. -/
theorem counterFold_eq (w : List Bool) :
    counterFold w = List.ofFn (counterEnc (w.foldr counterStep 0)) :=
  foldSem_eq counterEnc counterDec 0 counterStep counterDec_counterEnc.1 w

#print axioms counterDec_counterEnc
#print axioms counterFold_eq

theorem spike_length_seven : (spikeWordsUpTo 7).length = 255 := by
  set_option maxRecDepth 100000 in decide
