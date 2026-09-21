/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Machine.MapOutput

set_option doc.verso true in
/-!
# Streaming initial word functions

String predecessor, last-digit extraction, and numerical successor and predecessor
can process a generated word with finite control. Numerical carry follows the list's
least-significant-first order. Numerical borrow delays one output digit so that a
shortlex word losing its last digit is handled without retracting output.

## Main definitions

* {lit}`numericSuccGenerator` and {lit}`numericPredGenerator` transform generated words
  by numerical successor and predecessor.
* {lit}`predGenerator` and {lit}`lastGenerator` implement the string primitives.

## Main statements

* {lit}`numericSuccGenerator_emitsIn` and {lit}`numericPredGenerator_emitsIn` verify
  numerical carry and borrow without materializing the word's enumeration index.
* {lit}`predGenerator_emitsIn` and {lit}`lastGenerator_emitsIn` include empty input.

## Implementation notes

Each construction preserves the generator's exact valuation effect and work-head
bound. Its state space is a finite product when the generator's is finite. The
contracts inherit CSLib's {lit}`Classical.choice` dependency.

## Tags

Turing machine, logarithmic space, word arithmetic, finite-state transducer
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine

public section

/-- Numerical carry either changes a low zero or propagates through a low one. -/
@[expose] def numericSuccStep (carry b : Bool) : Bool × Option Bool :=
  if carry then (b, some (!b)) else (false, some b)

/-- A remaining numerical carry creates the high zero digit of the next shortlex length. -/
@[expose] def numericSuccFinish (carry : Bool) : Option Bool :=
  if carry then some false else none

/-- With the carry discharged, all remaining digits pass through unchanged. -/
theorem outputWord_numericSucc_false (w : List Bool) :
    outputWord numericSuccStep numericSuccFinish false w = w := by
  refine List.rec rfl (fun b w ih ↦ ?_) w
  simpa only [outputWord_cons, numericSuccStep, Bool.false_eq_true, ↓reduceIte,
    Option.toList_some, List.singleton_append] using congrArg (List.cons b) ih

/-- The carry transducer computes numerical successor in the shortlex enumeration. -/
theorem outputWord_numericSucc_true (w : List Bool) :
    outputWord numericSuccStep numericSuccFinish true w = numericSucc w := by
  refine List.rec rfl (fun b w ih ↦ ?_) w
  cases b <;> simp [outputWord_cons, numericSuccStep, outputWord_numericSucc_false,
    numericSucc_cons_false, numericSucc_cons_true, ih]

/-- Numerical successor of a generated word, retaining only a carry bit. -/
@[expose] def numericSuccGenerator {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) :=
  mapOutput P true numericSuccStep numericSuccFinish

/-- Numerical successor needs no additional work tapes, even for polynomially long arguments. -/
theorem numericSuccGenerator_emitsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (hP : EmitsIn P Pre F W T B) :
    EmitsIn (numericSuccGenerator P) Pre F (fun input σ ↦ numericSucc (W input σ))
      (fun n ↦ T n + 1) B := by
  exact (mapOutput_emitsIn hP true numericSuccStep numericSuccFinish).congr_output
    (fun input σ _ ↦ outputWord_numericSucc_true (W input σ))

/-- Borrow with one delayed output digit. The delayed digit is emitted on the next input. -/
@[expose] def numericPredStep (state : Bool × Option Bool) (b : Bool) :
    (Bool × Option Bool) × Option Bool :=
  ((state.1 && !b, some (if state.1 then !b else b)), state.2)

/-- An unresolved borrow drops the pending high digit; otherwise that digit is emitted. -/
@[expose] def numericPredFinish (state : Bool × Option Bool) : Option Bool :=
  if state.1 then none else state.2

/-- After resolving the borrow, the pending digit precedes the unchanged remaining word. -/
theorem outputWord_numericPred_false (w : List Bool) (pending : Option Bool) :
    outputWord numericPredStep numericPredFinish (false, pending) w = pending.toList ++ w := by
  refine List.rec (fun pending ↦ by cases pending <;> rfl) (fun b w ih pending ↦ ?_) w pending
  rw [outputWord_cons]
  simp only [numericPredStep, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    ih, Option.toList_some, List.singleton_append]

/-- An active borrow removes one high digit exactly when it reaches the end of the word. -/
theorem outputWord_numericPred_true (w : List Bool) (pending : Option Bool) :
    outputWord numericPredStep numericPredFinish (true, pending) w =
      if w.isEmpty then [] else pending.toList ++ numericPred w := by
  refine List.rec (fun _ ↦ rfl) (fun b w ih pending ↦ ?_) w pending
  cases b with
  | false =>
    rw [outputWord_cons]
    simp only [numericPredStep, Bool.not_false, Bool.true_and, ↓reduceIte, ih,
      List.isEmpty_cons, Bool.false_eq_true]
    cases w with
    | nil => simp
    | cons c w => simp [numericPred_cons_false_cons]
  | true =>
    simp [outputWord_cons, numericPredStep, outputWord_numericPred_false, numericPred_cons_true]

/-- Numerical predecessor of a generated word, with one borrow bit and one delayed digit. -/
@[expose] def numericPredGenerator {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) :=
  mapOutput P (true, none) numericPredStep numericPredFinish

/-- Numerical predecessor preserves the generator's space bound and saturates at the empty word. -/
theorem numericPredGenerator_emitsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (hP : EmitsIn P Pre F W T B) :
    EmitsIn (numericPredGenerator P) Pre F (fun input σ ↦ numericPred (W input σ))
      (fun n ↦ T n + 1) B := by
  refine (mapOutput_emitsIn hP (true, none) numericPredStep numericPredFinish).congr_output ?_
  intro input σ _
  change outputWord numericPredStep numericPredFinish (true, none) (W input σ) = _
  rw [outputWord_numericPred_true]
  cases W input σ <;> simp

/-- Discard the first digit and copy subsequent digits. -/
@[expose] def predStep (seen b : Bool) : Bool × Option Bool :=
  (true, if seen then some b else none)

/-- The string-predecessor transducer either copies the word or discards its first digit. -/
theorem outputWord_pred (w : List Bool) (seen : Bool) :
    outputWord predStep (fun _ ↦ none) seen w = if seen then w else w.tail := by
  refine List.rec (fun seen ↦ by cases seen <;> rfl) (fun b w ih seen ↦ ?_) w seen
  rw [outputWord_cons]
  cases seen <;> simp [predStep, ih]

/-- String predecessor of a generated word. -/
@[expose] def predGenerator {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) :=
  mapOutput P false predStep (fun _ ↦ none)

/-- String predecessor preserves the generator's tapes and drops just its first output digit. -/
theorem predGenerator_emitsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (hP : EmitsIn P Pre F W T B) :
    EmitsIn (predGenerator P) Pre F (fun input σ ↦ (W input σ).tail) (fun n ↦ T n + 1) B := by
  refine (mapOutput_emitsIn hP false predStep (fun _ ↦ none)).congr_output ?_
  intro input σ _
  exact outputWord_pred (W input σ) false

/-- Remember the first digit without emitting during the generator's run. -/
@[expose] def lastStep (first : Option Bool) (b : Bool) : Option Bool × Option Bool :=
  (first.elim (some b) some, none)

/-- Last-digit extraction in the paper's order is first-digit extraction in the list order. -/
theorem outputWord_last (w : List Bool) (first : Option Bool) :
    outputWord lastStep (fun first ↦ some (first.getD false)) first w =
      [first.getD (w.headD false)] := by
  refine List.rec (fun first ↦ by cases first <;> rfl) (fun b w ih first ↦ ?_) w first
  rw [outputWord_cons]
  cases first <;> simp [lastStep, ih]

/-- Emit the first generated digit, or a false digit when the generated word is empty. -/
@[expose] def lastGenerator {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) :=
  mapOutput P none lastStep (fun first ↦ some (first.getD false))

/-- Last-digit extraction always emits one digit and preserves all generator registers. -/
theorem lastGenerator_emitsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (hP : EmitsIn P Pre F W T B) :
    EmitsIn (lastGenerator P) Pre F (fun input σ ↦ [(W input σ).headD false])
      (fun n ↦ T n + 1) B := by
  exact (mapOutput_emitsIn hP none lastStep (fun first ↦ some (first.getD false))).congr_output
    (fun input σ _ ↦ outputWord_last (W input σ) none)

end

end Geb.Oitavem.Machine
