/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Program

set_option doc.verso true in
/-!
# The recursion loop

The loop machine reads the recursion word from a register holding its
reverse: the bit to process is the word's head, which is the register's last
cell. {lit}`caseLoop R bodyF bodyT` peels that bit off, runs the body for it,
and repeats, halting when the register is empty. Its state type is a control
automaton of four states summed with the two bodies' state types.
{lit}`liftBodyF` and {lit}`liftBodyT` embed a body configuration into a
configuration of the loop, agreeing with the loop's steps and output;
consequently a {name}`Geb.SizeBounded.Machine.Reaches` of a body lifts to a
{name}`Geb.SizeBounded.Machine.Reaches` of the loop.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.Cfg.inputSymbol`.

# Main definitions

* {lit}`caseLoopTr` — the transition of the loop, from the bodies' transitions.
* {lit}`caseLoop` — the loop over a register, with a body per bit: the machine
  built from {lit}`caseLoopTr`.
* {lit}`liftBodyF`, {lit}`liftBodyT` — the embedding of a body's
  configuration into the loop's.

# Main statements

* {lit}`caseLoop_tr` — the transition of {lit}`caseLoop` is {lit}`caseLoopTr`.
* {lit}`caseLoop_ofTr` — the loop over bodies built from transition functions is
  the machine built from {lit}`caseLoopTr` of those functions.
* {lit}`liftBodyF_halt`, {lit}`liftBodyT_halt` — a halted body configuration
  lifts to the seek state.
* {lit}`caseLoop_step_bodyF`, {lit}`caseLoop_step_bodyT` — the loop's step
  from a lifted configuration is the lift of the body's step.
* {lit}`caseLoop_runFrom_bodyF`, {lit}`caseLoop_runFrom_bodyT` — the same at
  every step, while the body has not halted.
* {lit}`caseLoop_outputString_bodyF`, {lit}`caseLoop_outputString_bodyT` —
  the loop emits what the mirrored body emits.
* {lit}`Reaches.liftBodyF`, {lit}`Reaches.liftBodyT` — a reach of a body
  lifts to a reach of the loop.

# Tags

Turing machine, loop, recursion, register
-/

set_option doc.verso true

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- The transition of the loop over register {lit}`R`, from the bodies'
transitions {lit}`trF`, {lit}`trT` and initial states {lit}`q₀F`, {lit}`q₀T`:
peel the head bit of {lit}`R`'s word from its last cell, run the body for that
bit, repeat; halt when {lit}`R` is empty. The control automaton has four
states:

* state {lit}`0` (seek): {lit}`R` reads a bit: move {lit}`R` right; reads
  blank: move {lit}`R` left, go to {lit}`1`.

* state {lit}`1` (back): {lit}`R` reads blank (the register was empty and the
  head is at {lit}`-1`): move right and halt; reads bit {lit}`c`: write
  blank, move left, go to {lit}`2` if {lit}`c = false`, {lit}`3` if
  {lit}`c = true`.

* states {lit}`2`, {lit}`3` (return with the bit remembered): {lit}`R` reads
  a bit: move left; reads blank: move right and enter the body for the bit,
  in its initial state.

In a body state the transition is that body's, with a halting successor
replaced by the seek state. It is not inlined, so that a partial application of
it holds the bodies' transitions as evaluated arguments rather than recomputing
them at each application. -/
@[expose, noinline] def caseLoopTr {k : ℕ} {SF ST : Type} (R : Fin k)
    (trF : SF → Option Bool → (Fin k → Option Bool) → Action k Bool SF)
    (trT : ST → Option Bool → (Fin k → Option Bool) → Action k Bool ST) (q₀F : SF) (q₀T : ST)
    (q : Fin 4 ⊕ (SF ⊕ ST)) (inp : Option Bool) (work : Fin k → Option Bool) :
    Action k Bool (Fin 4 ⊕ (SF ⊕ ST)) :=
  match q with
  | .inl ⟨0, _⟩ =>
    { inputTape := 0
      workTapes := fun j ↦ (none, if j = R then (if (work R).isSome then 1 else -1) else 0)
      output := none
      state := some (.inl (if (work R).isSome then 0 else 1)) }
  | .inl ⟨1, _⟩ =>
    match work R with
    | none =>
      { inputTape := 0, workTapes := fun j ↦ (none, if j = R then 1 else 0),
        output := none, state := none }
    | some c =>
      { inputTape := 0
        workTapes := fun j ↦ if j = R then (some none, -1) else (none, 0)
        output := none
        state := some (.inl (if c then 3 else 2)) }
  | .inl ⟨2, _⟩ =>
    { inputTape := 0
      workTapes := fun j ↦ (none, if j = R then (if (work R).isSome then -1 else 1) else 0)
      output := none
      state := some (if (work R).isSome then .inl 2 else .inr (.inl q₀F)) }
  | .inl ⟨3, _⟩ =>
    { inputTape := 0
      workTapes := fun j ↦ (none, if j = R then (if (work R).isSome then -1 else 1) else 0)
      output := none
      state := some (if (work R).isSome then .inl 3 else .inr (.inr q₀T)) }
  | .inr (.inl q) => let o := trF q inp work
    { o with state := some (o.state.elim (.inl 0) (fun q ↦ .inr (.inl q))) }
  | .inr (.inr q) => let o := trT q inp work
    { o with state := some (o.state.elim (.inl 0) (fun q ↦ .inr (.inr q))) }

/-- The loop over register {lit}`R` with the bodies {lit}`bodyF` and
{lit}`bodyT`: the machine built from {name}`caseLoopTr` of their transitions. -/
@[expose] noncomputable def caseLoop {k : ℕ} {SF ST : Type} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST) :
    MultiTapeTM k Bool (Fin 4 ⊕ (SF ⊕ ST)) :=
  ofTr (.inl 0) (caseLoopTr R bodyF.tr bodyT.tr bodyF.q₀ bodyT.q₀)

/-- The transition of {name}`caseLoop` is {name}`caseLoopTr`. -/
theorem caseLoop_tr {k : ℕ} {SF ST : Type} (R : Fin k) (bodyF : MultiTapeTM k Bool SF)
    (bodyT : MultiTapeTM k Bool ST) (q : Fin 4 ⊕ (SF ⊕ ST)) (inp : Option Bool)
    (work : Fin k → Option Bool) :
    (caseLoop R bodyF bodyT).tr q inp work =
      caseLoopTr R bodyF.tr bodyT.tr bodyF.q₀ bodyT.q₀ q inp work :=
  tr_ofTr _ _ _ _ _

/-- The loop over bodies built from transition functions is the machine built
from {name}`caseLoopTr` of those functions. -/
theorem caseLoop_ofTr {k : ℕ} {SF ST : Type} (R : Fin k) (q₀F : SF)
    (trF : SF → Option Bool → (Fin k → Option Bool) → Action k Bool SF) (q₀T : ST)
    (trT : ST → Option Bool → (Fin k → Option Bool) → Action k Bool ST) :
    caseLoop R (ofTr q₀F trF) (ofTr q₀T trT) = ofTr (.inl 0) (caseLoopTr R trF trT q₀F q₀T) := by
  rw [caseLoop, tr_ofTr', tr_ofTr', q₀_ofTr, q₀_ofTr]

/-- A body configuration lifted into the loop: a halted one becomes the seek
state. -/
@[expose] def liftBodyF {k : ℕ} {SF ST : Type} {input : List Bool} (cfg : Cfg k Bool SF input) :
    Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input :=
  { cfg with state := some (cfg.state.elim (.inl 0) (fun q ↦ .inr (.inl q))) }

/-- As {name}`liftBodyF`, for the body of the bit {lit}`true`. -/
@[expose] def liftBodyT {k : ℕ} {SF ST : Type} {input : List Bool} (cfg : Cfg k Bool ST input) :
    Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input :=
  { cfg with state := some (cfg.state.elim (.inl 0) (fun q ↦ .inr (.inr q))) }

/-- A halted body configuration lifts to the seek state. -/
theorem liftBodyF_halt {k : ℕ} {SF ST : Type} {input : List Bool} (cfg : Cfg k Bool SF input)
    (h : cfg.state = none) :
    liftBodyF (ST := ST) cfg = { cfg with state := some (.inl 0) } := by
  unfold liftBodyF
  rw [h]
  rfl

/-- As {name}`liftBodyF_halt`, for the body of the bit {lit}`true`. -/
theorem liftBodyT_halt {k : ℕ} {SF ST : Type} {input : List Bool} (cfg : Cfg k Bool ST input)
    (h : cfg.state = none) :
    liftBodyT (SF := SF) cfg = { cfg with state := some (.inl 0) } := by
  unfold liftBodyT
  rw [h]
  rfl

/-- A step of the loop from a lifted live body configuration is the lift of
the body's step. -/
theorem caseLoop_step_bodyF {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool SF input) (q : SF) (hq : cfg.state = some q) :
    (caseLoop R bodyF bodyT).step (liftBodyF (ST := ST) cfg) =
      liftBodyF (ST := ST) (bodyF.step cfg) := by
  have hq' : (liftBodyF (ST := ST) cfg).state = some (.inr (.inl q)) := by
    change some (cfg.state.elim _ _) = _
    rw [hq]
    rfl
  rw [MultiTapeTM.step_of_state hq', MultiTapeTM.step_of_state hq, caseLoop_tr]
  rfl

/-- As {name}`caseLoop_step_bodyF`, for the body of the bit {lit}`true`. -/
theorem caseLoop_step_bodyT {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool ST input) (q : ST) (hq : cfg.state = some q) :
    (caseLoop R bodyF bodyT).step (liftBodyT (SF := SF) cfg) =
      liftBodyT (SF := SF) (bodyT.step cfg) := by
  have hq' : (liftBodyT (SF := SF) cfg).state = some (.inr (.inr q)) := by
    change some (cfg.state.elim _ _) = _
    rw [hq]
    rfl
  rw [MultiTapeTM.step_of_state hq', MultiTapeTM.step_of_state hq, caseLoop_tr]
  rfl

/-- The loop emits what the body emits from a lifted live configuration. -/
theorem caseLoop_outputSymbol_bodyF {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool SF input) (q : SF) (hq : cfg.state = some q) :
    (caseLoop R bodyF bodyT).outputSymbol (liftBodyF (ST := ST) cfg) =
      bodyF.outputSymbol cfg := by
  unfold outputSymbol liftBodyF
  simp only [hq, caseLoop_tr]
  rfl

/-- As {name}`caseLoop_outputSymbol_bodyF`, for the body of the bit
{lit}`true`. -/
theorem caseLoop_outputSymbol_bodyT {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool ST input) (q : ST) (hq : cfg.state = some q) :
    (caseLoop R bodyF bodyT).outputSymbol (liftBodyT (SF := SF) cfg) =
      bodyT.outputSymbol cfg := by
  unfold outputSymbol liftBodyT
  simp only [hq, caseLoop_tr]
  rfl

/-- While the body has not halted, the loop mirrors it. -/
theorem caseLoop_runFrom_bodyF {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool SF input) :
    ∀ t, (∀ t' < t, (bodyF.runFrom cfg t').state ≠ none) →
      (caseLoop R bodyF bodyT).runFrom (liftBodyF (ST := ST) cfg) t =
        liftBodyF (ST := ST) (bodyF.runFrom cfg t) :=
  Nat.rec
    (fun _ ↦ by rw [runFrom_zero, runFrom_zero])
    (fun t ih hlive ↦ by
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (hlive t (by omega))
      rw [runFrom_succ_eq_step', ih (fun t' ht' ↦ hlive t' (by omega)), runFrom_succ_eq_step',
        caseLoop_step_bodyF R bodyF bodyT (bodyF.runFrom cfg t) q hq])

/-- As {name}`caseLoop_runFrom_bodyF`, for the body of the bit {lit}`true`. -/
theorem caseLoop_runFrom_bodyT {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool ST input) :
    ∀ t, (∀ t' < t, (bodyT.runFrom cfg t').state ≠ none) →
      (caseLoop R bodyF bodyT).runFrom (liftBodyT (SF := SF) cfg) t =
        liftBodyT (SF := SF) (bodyT.runFrom cfg t) :=
  Nat.rec
    (fun _ ↦ by rw [runFrom_zero, runFrom_zero])
    (fun t ih hlive ↦ by
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (hlive t (by omega))
      rw [runFrom_succ_eq_step', ih (fun t' ht' ↦ hlive t' (by omega)), runFrom_succ_eq_step',
        caseLoop_step_bodyT R bodyF bodyT (bodyT.runFrom cfg t) q hq])

/-- While the body has not halted, the loop emits what the body emits. -/
theorem caseLoop_outputString_bodyF {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool SF input) :
    ∀ t, (∀ t' < t, (bodyF.runFrom cfg t').state ≠ none) →
      (caseLoop R bodyF bodyT).outputString (liftBodyF (ST := ST) cfg) t =
        bodyF.outputString cfg t :=
  Nat.rec
    (fun _ ↦ rfl)
    (fun t ih hlive ↦ by
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (hlive t (by omega))
      rw [outputString_succ, outputString_succ, ih (fun t' ht' ↦ hlive t' (by omega)),
        caseLoop_runFrom_bodyF R bodyF bodyT cfg t (fun t' ht' ↦ hlive t' (by omega)),
        caseLoop_outputSymbol_bodyF R bodyF bodyT (bodyF.runFrom cfg t) q hq])

/-- As {name}`caseLoop_outputString_bodyF`, for the body of the bit
{lit}`true`. -/
theorem caseLoop_outputString_bodyT {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool ST input) :
    ∀ t, (∀ t' < t, (bodyT.runFrom cfg t').state ≠ none) →
      (caseLoop R bodyF bodyT).outputString (liftBodyT (SF := SF) cfg) t =
        bodyT.outputString cfg t :=
  Nat.rec
    (fun _ ↦ rfl)
    (fun t ih hlive ↦ by
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (hlive t (by omega))
      rw [outputString_succ, outputString_succ, ih (fun t' ht' ↦ hlive t' (by omega)),
        caseLoop_runFrom_bodyT R bodyF bodyT cfg t (fun t' ht' ↦ hlive t' (by omega)),
        caseLoop_outputSymbol_bodyT R bodyF bodyT (bodyT.runFrom cfg t) q hq])

/-- A reach of the body lifts to a reach of the loop. -/
theorem Reaches.liftBodyF {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    {bodyF : MultiTapeTM k Bool SF} (bodyT : MultiTapeTM k Bool ST)
    {cfg cfg' : Cfg k Bool SF input} {t B : ℕ} (h : Reaches bodyF cfg cfg' t B) :
    Reaches (caseLoop R bodyF bodyT) (liftBodyF cfg) (liftBodyF cfg') t B where
  live := fun t' ht' ↦ by
    rw [caseLoop_runFrom_bodyF R bodyF bodyT cfg t' (fun s hs ↦ h.live s (by omega))]
    exact Option.some_ne_none _
  runFrom_eq := by rw [caseLoop_runFrom_bodyF R bodyF bodyT cfg t h.live, h.runFrom_eq]
  output := (caseLoop_outputString_bodyF R bodyF bodyT cfg t h.live).trans h.output
  pos := fun t' ht' i ↦ by
    rw [caseLoop_runFrom_bodyF R bodyF bodyT cfg t' (fun s hs ↦ h.live s (by omega))]
    exact h.pos t' ht' i

/-- As {name}`Reaches.liftBodyF`, for the body of the bit {lit}`true`. -/
theorem Reaches.liftBodyT {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) {bodyT : MultiTapeTM k Bool ST}
    {cfg cfg' : Cfg k Bool ST input} {t B : ℕ} (h : Reaches bodyT cfg cfg' t B) :
    Reaches (caseLoop R bodyF bodyT) (liftBodyT cfg) (liftBodyT cfg') t B where
  live := fun t' ht' ↦ by
    rw [caseLoop_runFrom_bodyT R bodyF bodyT cfg t' (fun s hs ↦ h.live s (by omega))]
    exact Option.some_ne_none _
  runFrom_eq := by rw [caseLoop_runFrom_bodyT R bodyF bodyT cfg t h.live, h.runFrom_eq]
  output := (caseLoop_outputString_bodyT R bodyF bodyT cfg t h.live).trans h.output
  pos := fun t' ht' i ↦ by
    rw [caseLoop_runFrom_bodyT R bodyF bodyT cfg t' (fun s hs ↦ h.live s (by omega))]
    exact h.pos t' ht' i

end

end Geb.SizeBounded.Machine
