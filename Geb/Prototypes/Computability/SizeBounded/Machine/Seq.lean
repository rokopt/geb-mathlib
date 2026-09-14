/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Program

set_option doc.verso true

/-!
# Sequencing machines

Sequencing composes two machines that share a tape layout: {lit}`seq P Q`
runs {lit}`P`, and from a configuration where {lit}`P` would halt continues
instead as {lit}`Q` from {lit}`Q`'s initial state. Its state type is the sum
of the two components' state types. {lit}`liftL` and {lit}`liftR` embed a
configuration of {lit}`P` or of {lit}`Q` into a configuration of the
composite, agreeing with the composite's steps and output; consequently a
{name}`Geb.SizeBounded.Machine.Reaches` of a component lifts to a
{name}`Geb.SizeBounded.Machine.Reaches` of the composite.

# Main definitions

* {lit}`seq` — sequential composition of two machines sharing a tape layout.
* {lit}`liftL`, {lit}`liftR` — the embedding of a component's configuration
  into the composite's.

# Main statements

* {lit}`seq_step_left`, {lit}`seq_step_right` — the composite's step from a
  lifted configuration is the lift of the component's step.
* {lit}`seq_configs_left`, {lit}`seq_configs_right` — the same at every step,
  while {lit}`P` has not halted.
* {lit}`seq_outputString_left`, {lit}`seq_outputString_right` — the composite
  emits what the mirrored component emits.
* {lit}`Reaches.liftL`, {lit}`Reaches.liftR` — a reach of a component lifts
  to a reach of the composite.

# Tags

Turing machine, sequencing, composition
-/

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- Sequencing: run {lit}`P`, then {lit}`Q`. In an {lit}`inl` state the
transition is {lit}`P`'s with a halting successor replaced by {lit}`Q`'s
initial state; in an {lit}`inr` state it is {lit}`Q`'s. -/
@[expose] def seq {k : ℕ} {S₁ S₂ : Type} (P : MultiTapeTM k Bool S₁)
    (Q : MultiTapeTM k Bool S₂) : MultiTapeTM k Bool (S₁ ⊕ S₂) where
  q₀ := .inl P.q₀
  tr q inp work :=
    match q with
    | .inl q => let o := P.tr q inp work
      { o with q' := some (o.q'.elim (.inr Q.q₀) .inl) }
    | .inr q => let o := Q.tr q inp work
      { o with q' := o.q'.map .inr }

/-- A {lit}`P`-configuration lifted into {lit}`seq P Q`: a halted one becomes
{lit}`Q`'s start. -/
@[expose] def liftL {k : ℕ} {S₁ S₂ : Type} {input : List Bool} (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool S₁ input) : Cfg k Bool (S₁ ⊕ S₂) input :=
  { cfg with state := some (cfg.state.elim (.inr Q.q₀) .inl) }

/-- A {lit}`Q`-configuration lifted into {lit}`seq P Q`. -/
@[expose] def liftR {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (cfg : Cfg k Bool S₂ input) : Cfg k Bool (S₁ ⊕ S₂) input :=
  { cfg with state := cfg.state.map .inr }

/-- A step of the composite from a lifted live {lit}`P`-configuration is the
lift of {lit}`P`'s step. -/
theorem seq_step_left {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S₁) (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool S₁ input) (q : S₁) (hq : cfg.state = some q) :
    (seq P Q).step (liftL Q cfg) = liftL Q (P.step cfg) := by
  unfold step liftL
  simp only [hq]
  rfl

/-- A step of the composite from a lifted {lit}`Q`-configuration is the lift
of {lit}`Q`'s step. -/
theorem seq_step_right {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S₁) (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool S₂ input) :
    (seq P Q).step (liftR (S₁ := S₁) cfg) = liftR (Q.step cfg) := by
  cases hq : cfg.state with
  | none =>
    rw [step_of_halt hq, step_of_halt]
    simp [liftR, hq]
  | some q =>
    unfold step liftR
    simp only [hq]
    rfl

/-- A halted {lit}`P`-configuration lifts to {lit}`Q`'s start. -/
theorem liftL_halt {k : ℕ} {S₁ S₂ : Type} {input : List Bool} (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool S₁ input) (h : cfg.state = none) :
    liftL Q cfg = liftR (S₁ := S₁) { cfg with state := some Q.q₀ } := by
  unfold liftL liftR
  rw [h]
  rfl

/-- The composite emits what {lit}`P` emits from a lifted live configuration. -/
theorem seq_outputSymbol_left {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S₁) (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool S₁ input) (q : S₁) (hq : cfg.state = some q) :
    (seq P Q).outputSymbol (liftL Q cfg) = P.outputSymbol cfg := by
  unfold outputSymbol liftL
  simp only [hq]
  rfl

/-- The composite emits what {lit}`Q` emits from a lifted configuration. -/
theorem seq_outputSymbol_right {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S₁) (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool S₂ input) :
    (seq P Q).outputSymbol (liftR (S₁ := S₁) cfg) = Q.outputSymbol cfg := by
  unfold outputSymbol liftR
  cases hq : cfg.state
  · rfl
  · rfl

/-- The composite starts in {lit}`P`'s initial state. -/
theorem seq_q₀ {k : ℕ} {S₁ S₂ : Type} (P : MultiTapeTM k Bool S₁)
    (Q : MultiTapeTM k Bool S₂) : (seq P Q).q₀ = .inl P.q₀ := rfl

/-- A configuration of the composite in its initial state is the lift of the
same configuration in {lit}`P`'s initial state. -/
theorem liftL_start {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S₁) (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool (S₁ ⊕ S₂) input) (h : cfg.state = some (seq P Q).q₀) :
    cfg = liftL Q { cfg with state := some P.q₀ } := by
  apply Cfg.ext <;> dsimp only [liftL]
  exact h

section Projections

variable {k : ℕ} {S₁ S₂ : Type} {input : List Bool} (Q : MultiTapeTM k Bool S₂)
  (cfg : Cfg k Bool S₁ input) (cfg' : Cfg k Bool S₂ input)

/-- The left lift keeps the tapes. -/
@[simp] theorem liftL_workTapes : (liftL Q cfg).workTapes = cfg.workTapes := rfl

/-- The left lift keeps the heads. -/
@[simp] theorem liftL_workTapePos : (liftL Q cfg).workTapePos = cfg.workTapePos := rfl

/-- The left lift keeps the input head. -/
@[simp] theorem liftL_inputPos : (liftL Q cfg).inputPos = cfg.inputPos := rfl

/-- The left lift is live. -/
theorem liftL_state_ne_none : (liftL Q cfg).state ≠ none := by
  unfold liftL
  exact Option.some_ne_none _

/-- The right lift keeps the tapes. -/
@[simp] theorem liftR_workTapes : (liftR (S₁ := S₁) cfg').workTapes = cfg'.workTapes := rfl

/-- The right lift keeps the heads. -/
@[simp] theorem liftR_workTapePos :
    (liftR (S₁ := S₁) cfg').workTapePos = cfg'.workTapePos := rfl

/-- The right lift keeps the input head. -/
@[simp] theorem liftR_inputPos : (liftR (S₁ := S₁) cfg').inputPos = cfg'.inputPos := rfl

/-- The right lift's state is the mapped state. -/
@[simp] theorem liftR_state : (liftR (S₁ := S₁) cfg').state = cfg'.state.map .inr := rfl

end Projections

/-- While {lit}`P` has not halted, the composite mirrors {lit}`P`. -/
theorem seq_configs_left {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S₁) (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool S₁ input) :
    ∀ t, (∀ t' < t, (P.configs cfg t').state ≠ none) →
      (seq P Q).configs (liftL Q cfg) t = liftL Q (P.configs cfg t) :=
  Nat.rec
    (fun _ ↦ by rw [configs_zero, configs_zero])
    (fun t ih hlive ↦ by
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (hlive t (by omega))
      rw [configs_succ_eq_step', ih (fun t' ht' ↦ hlive t' (by omega)), configs_succ_eq_step',
        seq_step_left P Q (P.configs cfg t) q hq])

/-- The composite mirrors {lit}`Q` from a lifted {lit}`Q`-configuration. -/
theorem seq_configs_right {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S₁) (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool S₂ input) (t : ℕ) :
    (seq P Q).configs (liftR (S₁ := S₁) cfg) t = liftR (Q.configs cfg t) :=
  Nat.rec (motive := fun t ↦
      (seq P Q).configs (liftR (S₁ := S₁) cfg) t = liftR (Q.configs cfg t))
    (by rw [configs_zero, configs_zero])
    (fun t ih ↦ by rw [configs_succ_eq_step', ih, configs_succ_eq_step', seq_step_right P Q])
    t

/-- While {lit}`P` has not halted, the composite emits what {lit}`P` emits. -/
theorem seq_outputString_left {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S₁) (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool S₁ input) :
    ∀ t, (∀ t' < t, (P.configs cfg t').state ≠ none) →
      (seq P Q).outputString (liftL Q cfg) t = P.outputString cfg t :=
  Nat.rec
    (fun _ ↦ rfl)
    (fun t ih hlive ↦ by
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (hlive t (by omega))
      rw [outputString_succ, outputString_succ, ih (fun t' ht' ↦ hlive t' (by omega)),
        seq_configs_left P Q cfg t (fun t' ht' ↦ hlive t' (by omega)),
        seq_outputSymbol_left P Q (P.configs cfg t) q hq])

/-- From a lifted {lit}`Q`-configuration the composite emits what {lit}`Q`
emits. -/
theorem seq_outputString_right {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S₁) (Q : MultiTapeTM k Bool S₂)
    (cfg : Cfg k Bool S₂ input) (t : ℕ) :
    (seq P Q).outputString (liftR (S₁ := S₁) cfg) t = Q.outputString cfg t :=
  Nat.rec (motive := fun t ↦
      (seq P Q).outputString (liftR (S₁ := S₁) cfg) t = Q.outputString cfg t)
    rfl
    (fun t ih ↦ by
      rw [outputString_succ, outputString_succ, ih, seq_configs_right P Q cfg t,
        seq_outputSymbol_right P Q (Q.configs cfg t)])
    t

/-- A reach of {lit}`P` lifts to a reach of the composite. -/
theorem Reaches.liftL {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    {P : MultiTapeTM k Bool S₁} (Q : MultiTapeTM k Bool S₂)
    {cfg cfg' : Cfg k Bool S₁ input} {t B : ℕ} (h : Reaches P cfg cfg' t B) :
    Reaches (seq P Q) (liftL Q cfg) (liftL Q cfg') t B where
  live := fun t' ht' ↦ by
    rw [seq_configs_left P Q cfg t' (fun s hs ↦ h.live s (by omega))]
    exact liftL_state_ne_none Q _
  configs_eq := by rw [seq_configs_left P Q cfg t h.live, h.configs_eq]
  output := (seq_outputString_left P Q cfg t h.live).trans h.output
  pos := fun t' ht' i ↦ by
    rw [seq_configs_left P Q cfg t' (fun s hs ↦ h.live s (by omega)), liftL_workTapePos]
    exact h.pos t' ht' i

/-- A reach of {lit}`Q` lifts to a reach of the composite. -/
theorem Reaches.liftR {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S₁) {Q : MultiTapeTM k Bool S₂}
    {cfg cfg' : Cfg k Bool S₂ input} {t B : ℕ} (h : Reaches Q cfg cfg' t B) :
    Reaches (seq P Q) (liftR cfg) (liftR cfg') t B where
  live := fun t' ht' ↦ by
    rw [seq_configs_right P Q cfg t', liftR_state, ne_eq, Option.map_eq_none_iff]
    exact h.live t' ht'
  configs_eq := by rw [seq_configs_right P Q cfg t, h.configs_eq]
  output := (seq_outputString_right P Q cfg t).trans h.output
  pos := fun t' ht' i ↦ by
    rw [seq_configs_right P Q cfg t', liftR_workTapePos]
    exact h.pos t' ht' i

end

end Geb.SizeBounded.Machine
