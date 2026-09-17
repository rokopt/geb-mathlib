/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.While

set_option doc.verso true in
/-!
# The branch on a probe

{lit}`caseProbe p P Q` reads a probe once and runs {lit}`Q` when it reads a
one and {lit}`P` otherwise, halting when the chosen branch halts. Its state
type is a dispatch state summed with the two branches' state types.
{lit}`liftP` and {lit}`liftQ` embed a branch configuration into one of the
composite, agreeing with the composite's steps and output, so a run of a
branch lifts to a run of the composite. The contract
{lit}`TransformsIn.caseReg` is the instance at a work-tape probe: the
composite transforms by the transformer of the branch the register's last
bit selects, its precondition being that branch's.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's {name}`Turing.Cfg.inputSymbol`.

# Main definitions

* {lit}`caseProbe` — the branch.
* {lit}`liftP`, {lit}`liftQ` — the embeddings of a branch's configuration.

# Main statements

* {lit}`RunsTo.liftP`, {lit}`RunsTo.liftQ` — a run of a branch lifts to a run
  of the composite.
* {lit}`caseProbe_dispatch` — the dispatch step enters the selected branch.
* {lit}`RunsTo.caseProbe` — the run of the composite from the dispatch state.
* {lit}`tapeOf_zero` — a parked head reads the word's last bit.
* {lit}`TransformsIn.caseReg` — the branch's contract at a work-tape probe.

# Tags

Turing machine, branch, conditional, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine

public section

/-- The branch: in the dispatch state, enter {lit}`Q` when the probe reads a
one and {lit}`P` otherwise; in a branch state, that branch's transition. -/
@[expose] def caseProbe {k : ℕ} {SP SQ : Type} (p : Probe k) (P : MultiTapeTM k Bool SP)
    (Q : MultiTapeTM k Bool SQ) : MultiTapeTM k Bool (Unit ⊕ (SP ⊕ SQ)) where
  q₀ := .inl ()
  tr q inp work :=
    match q with
    | .inl () =>
      { inputTape := 0, workTapes := fun _ ↦ (none, 0), output := none,
        state := some (if probeRead p inp work = some true then .inr (.inr Q.q₀)
          else .inr (.inl P.q₀)) }
    | .inr (.inl s) => let o := P.tr s inp work
      { o with state := o.state.map fun s ↦ .inr (.inl s) }
    | .inr (.inr s) => let o := Q.tr s inp work
      { o with state := o.state.map fun s ↦ .inr (.inr s) }

/-- A configuration of the first branch lifted into the composite. -/
@[expose] def liftP {k : ℕ} {SP SQ : Type} {input : List Bool} (cfg : Cfg k Bool SP input) :
    Cfg k Bool (Unit ⊕ (SP ⊕ SQ)) input :=
  { cfg with state := cfg.state.map fun s ↦ .inr (.inl s) }

/-- A configuration of the second branch lifted into the composite. -/
@[expose] def liftQ {k : ℕ} {SP SQ : Type} {input : List Bool} (cfg : Cfg k Bool SQ input) :
    Cfg k Bool (Unit ⊕ (SP ⊕ SQ)) input :=
  { cfg with state := cfg.state.map fun s ↦ .inr (.inr s) }

/-- A step of the composite from a lifted first-branch configuration is the lift
of the branch's step. -/
theorem caseProbe_step_left {k : ℕ} {SP SQ : Type} {input : List Bool} (p : Probe k)
    (P : MultiTapeTM k Bool SP) (Q : MultiTapeTM k Bool SQ) (cfg : Cfg k Bool SP input) :
    (caseProbe p P Q).step (liftP (SQ := SQ) cfg) = liftP (P.step cfg) := by
  cases hq : cfg.state with
  | none =>
    rw [step_of_halt hq, step_of_halt]
    simp [liftP, hq]
  | some q =>
    unfold step liftP
    simp only [hq]
    rfl

/-- A step of the composite from a lifted second-branch configuration is the
lift of the branch's step. -/
theorem caseProbe_step_right {k : ℕ} {SP SQ : Type} {input : List Bool} (p : Probe k)
    (P : MultiTapeTM k Bool SP) (Q : MultiTapeTM k Bool SQ) (cfg : Cfg k Bool SQ input) :
    (caseProbe p P Q).step (liftQ (SP := SP) cfg) = liftQ (Q.step cfg) := by
  cases hq : cfg.state with
  | none =>
    rw [step_of_halt hq, step_of_halt]
    simp [liftQ, hq]
  | some q =>
    unfold step liftQ
    simp only [hq]
    rfl

/-- The composite emits what the first branch emits from a lifted
configuration. -/
theorem caseProbe_outputSymbol_left {k : ℕ} {SP SQ : Type} {input : List Bool} (p : Probe k)
    (P : MultiTapeTM k Bool SP) (Q : MultiTapeTM k Bool SQ) (cfg : Cfg k Bool SP input) :
    (caseProbe p P Q).outputSymbol (liftP (SQ := SQ) cfg) = P.outputSymbol cfg := by
  unfold outputSymbol liftP
  cases hq : cfg.state
  · rfl
  · rfl

/-- The composite emits what the second branch emits from a lifted
configuration. -/
theorem caseProbe_outputSymbol_right {k : ℕ} {SP SQ : Type} {input : List Bool} (p : Probe k)
    (P : MultiTapeTM k Bool SP) (Q : MultiTapeTM k Bool SQ) (cfg : Cfg k Bool SQ input) :
    (caseProbe p P Q).outputSymbol (liftQ (SP := SP) cfg) = Q.outputSymbol cfg := by
  unfold outputSymbol liftQ
  cases hq : cfg.state
  · rfl
  · rfl

/-- The composite mirrors the first branch from a lifted configuration. -/
theorem caseProbe_runFrom_left {k : ℕ} {SP SQ : Type} {input : List Bool} (p : Probe k)
    (P : MultiTapeTM k Bool SP) (Q : MultiTapeTM k Bool SQ) (cfg : Cfg k Bool SP input) (t : ℕ) :
    (caseProbe p P Q).runFrom (liftP (SQ := SQ) cfg) t = liftP (P.runFrom cfg t) :=
  Nat.rec (motive := fun t ↦
      (caseProbe p P Q).runFrom (liftP (SQ := SQ) cfg) t = liftP (P.runFrom cfg t))
    (by rw [runFrom_zero, runFrom_zero])
    (fun t ih ↦ by rw [runFrom_succ_eq_step', ih, runFrom_succ_eq_step', caseProbe_step_left])
    t

/-- The composite mirrors the second branch from a lifted configuration. -/
theorem caseProbe_runFrom_right {k : ℕ} {SP SQ : Type} {input : List Bool} (p : Probe k)
    (P : MultiTapeTM k Bool SP) (Q : MultiTapeTM k Bool SQ) (cfg : Cfg k Bool SQ input) (t : ℕ) :
    (caseProbe p P Q).runFrom (liftQ (SP := SP) cfg) t = liftQ (Q.runFrom cfg t) :=
  Nat.rec (motive := fun t ↦
      (caseProbe p P Q).runFrom (liftQ (SP := SP) cfg) t = liftQ (Q.runFrom cfg t))
    (by rw [runFrom_zero, runFrom_zero])
    (fun t ih ↦ by rw [runFrom_succ_eq_step', ih, runFrom_succ_eq_step', caseProbe_step_right])
    t

/-- From a lifted first-branch configuration the composite emits what the branch
emits. -/
theorem caseProbe_outputString_left {k : ℕ} {SP SQ : Type} {input : List Bool} (p : Probe k)
    (P : MultiTapeTM k Bool SP) (Q : MultiTapeTM k Bool SQ) (cfg : Cfg k Bool SP input) (t : ℕ) :
    (caseProbe p P Q).outputString (liftP (SQ := SQ) cfg) t = P.outputString cfg t :=
  Nat.rec (motive := fun t ↦
      (caseProbe p P Q).outputString (liftP (SQ := SQ) cfg) t = P.outputString cfg t)
    rfl
    (fun t ih ↦ by
      rw [outputString_succ, outputString_succ, ih, caseProbe_runFrom_left p P Q cfg t,
        caseProbe_outputSymbol_left])
    t

/-- From a lifted second-branch configuration the composite emits what the
branch emits. -/
theorem caseProbe_outputString_right {k : ℕ} {SP SQ : Type} {input : List Bool} (p : Probe k)
    (P : MultiTapeTM k Bool SP) (Q : MultiTapeTM k Bool SQ) (cfg : Cfg k Bool SQ input) (t : ℕ) :
    (caseProbe p P Q).outputString (liftQ (SP := SP) cfg) t = Q.outputString cfg t :=
  Nat.rec (motive := fun t ↦
      (caseProbe p P Q).outputString (liftQ (SP := SP) cfg) t = Q.outputString cfg t)
    rfl
    (fun t ih ↦ by
      rw [outputString_succ, outputString_succ, ih, caseProbe_runFrom_right p P Q cfg t,
        caseProbe_outputSymbol_right])
    t

/-- A run of the first branch lifts to a run of the composite. -/
theorem _root_.Geb.SizeBounded.Machine.RunsTo.liftP {k : ℕ} {SP SQ : Type} {input : List Bool}
    (p : Probe k) {P : MultiTapeTM k Bool SP} (Q : MultiTapeTM k Bool SQ)
    {cfg cfg' : Cfg k Bool SP input}
    {t B : ℕ} (h : RunsTo P cfg cfg' t B) :
    RunsTo (caseProbe p P Q) (Machine.liftP cfg) (Machine.liftP cfg') t B where
  live := fun t' ht' ↦ by
    rw [caseProbe_runFrom_left p P Q cfg t']
    change (P.runFrom cfg t').state.map _ ≠ none
    rw [ne_eq, Option.map_eq_none_iff]
    exact h.live t' ht'
  runFrom_eq := by rw [caseProbe_runFrom_left p P Q cfg t, h.runFrom_eq]
  pos := fun t' ht' i ↦ by
    rw [caseProbe_runFrom_left p P Q cfg t']
    exact h.pos t' ht' i
  output := by rw [caseProbe_outputString_left p P Q cfg t, h.output]
  halted := by
    change cfg'.state.map _ = none
    rw [h.halted]
    rfl

/-- A run of the second branch lifts to a run of the composite. -/
theorem _root_.Geb.SizeBounded.Machine.RunsTo.liftQ {k : ℕ} {SP SQ : Type} {input : List Bool}
    (p : Probe k) (P : MultiTapeTM k Bool SP) {Q : MultiTapeTM k Bool SQ}
    {cfg cfg' : Cfg k Bool SQ input}
    {t B : ℕ} (h : RunsTo Q cfg cfg' t B) :
    RunsTo (caseProbe p P Q) (Machine.liftQ cfg) (Machine.liftQ cfg') t B where
  live := fun t' ht' ↦ by
    rw [caseProbe_runFrom_right p P Q cfg t']
    change (Q.runFrom cfg t').state.map _ ≠ none
    rw [ne_eq, Option.map_eq_none_iff]
    exact h.live t' ht'
  runFrom_eq := by rw [caseProbe_runFrom_right p P Q cfg t, h.runFrom_eq]
  pos := fun t' ht' i ↦ by
    rw [caseProbe_runFrom_right p P Q cfg t']
    exact h.pos t' ht' i
  output := by rw [caseProbe_outputString_right p P Q cfg t, h.output]
  halted := by
    change cfg'.state.map _ = none
    rw [h.halted]
    rfl

/-- The dispatch step enters the branch the probe selects, changing nothing
else. -/
theorem caseProbe_dispatch {k : ℕ} {SP SQ : Type} {input : List Bool} (p : Probe k)
    (P : MultiTapeTM k Bool SP) (Q : MultiTapeTM k Bool SQ)
    (cfg : Cfg k Bool (Unit ⊕ (SP ⊕ SQ)) input) (hq : cfg.state = some (.inl ())) (B : ℕ)
    (hpos : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B) :
    Reaches (caseProbe p P Q) cfg
      { cfg with state := some (if probeOf p cfg = some true then .inr (.inr Q.q₀)
        else .inr (.inl P.q₀)) } 1 B := by
  have hstep : (caseProbe p P Q).step cfg =
      { cfg with state := some (if probeOf p cfg = some true then .inr (.inr Q.q₀)
        else .inr (.inl P.q₀)) } := by
    rw [step_of_state _ _ _ hq]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · rfl
    · funext j
      change cfg.workTapePos j + ((0 : SignType) : ℤ) = cfg.workTapePos j
      rw [SignType.coe_zero, add_zero]
    · exact List.append_nil _
  have hout : (caseProbe p P Q).outputSymbol cfg = none := by
    unfold outputSymbol
    rw [hq]
    rfl
  refine Reaches.ofFamily (caseProbe p P Q) (fun s ↦ if s = 0 then cfg else
    { cfg with state := some (if probeOf p cfg = some true then .inr (.inr Q.q₀)
      else .inr (.inl P.q₀)) }) 1 B ?_ ?_ ?_ ?_
  · intro s hs
    rw [ite_eq_left (by omega), hq]
    exact Option.some_ne_none _
  · intro s hs
    rw [ite_eq_left (by omega), ite_eq_right (by omega)]
    exact hstep
  · intro s hs
    rw [ite_eq_left (by omega)]
    exact hout
  · intro s _ i
    by_cases h0 : s = 0
    · rw [ite_eq_left h0]
      exact hpos i
    · rw [ite_eq_right h0]
      exact hpos i

/-- The run of the composite from the dispatch state: one step, then the run of
the branch the probe selects. -/
theorem _root_.Geb.SizeBounded.Machine.RunsTo.caseProbe {k : ℕ} {SP SQ : Type}
    {input : List Bool} (p : Probe k) (P : MultiTapeTM k Bool SP) (Q : MultiTapeTM k Bool SQ)
    (cfg : Cfg k Bool (Unit ⊕ (SP ⊕ SQ)) input) (hq : cfg.state = some (.inl ())) (B : ℕ)
    (hpos : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B)
    (cfg' : Cfg k Bool (Unit ⊕ (SP ⊕ SQ)) input) (t : ℕ)
    (hP : probeOf p cfg ≠ some true →
      RunsTo P { cfg with state := some P.q₀ } { cfg' with state := none } t B)
    (hQ : probeOf p cfg = some true →
      RunsTo Q { cfg with state := some Q.q₀ } { cfg' with state := none } t B) :
    RunsTo (Machine.caseProbe p P Q) cfg { cfg' with state := none } (1 + t) B := by
  have r₁ := caseProbe_dispatch p P Q cfg hq B hpos
  by_cases h : probeOf p cfg = some true
  · rw [ite_eq_left h] at r₁
    have r₂ := (hQ h).liftQ p P
    exact ⟨r₁.trans r₂.toReaches, r₂.halted⟩
  · rw [ite_eq_right h] at r₁
    have r₂ := (hP h).liftP p Q
    exact ⟨r₁.trans r₂.toReaches, r₂.halted⟩

/-- A parked head reads the word's last bit. -/
theorem tapeOf_zero (w : List Bool) : tapeOf w 0 = w.getLast? := by
  unfold tapeOf
  rw [ite_eq_left (le_refl _)]
  change w.reverse[0]? = w.getLast?
  rw [← List.head?_eq_getElem?, List.head?_reverse]

/-- The branch's contract at a work-tape probe: the composite transforms by the
transformer of the branch the register's last bit selects, under that branch's
precondition. -/
theorem TransformsIn.caseReg {k : ℕ} {SP SQ : Type} {P : MultiTapeTM k Bool SP}
    {Q : MultiTapeTM k Bool SQ} {PreP PreQ : List Bool → (Fin k → List Bool) → Prop}
    {F G : List Bool → (Fin k → List Bool) → Fin k → List Bool} {TP TQ B : ℕ → ℕ} (R : Fin k)
    (hP : TransformsIn P PreP F TP B) (hQ : TransformsIn Q PreQ G TQ B) :
    TransformsIn (caseProbe (some R) P Q)
      (fun input σ ↦ if (σ R).getLast? = some true then PreQ input σ else PreP input σ)
      (fun input σ ↦ if (σ R).getLast? = some true then G input σ else F input σ)
      (fun n ↦ 1 + max (TP n) (TQ n)) B := by
  intro input cfg σ hq hpark hpos hσ hpre hB
  have hprobe : probeOf (some R) cfg = (σ R).getLast? := by
    change cfg.workTapes R (cfg.workTapePos R) = _
    rw [hσ R, hpark R, tapeOf_zero]
  have hposB : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B input.length := by
    intro i
    rw [hpark i]
    constructor <;> omega
  dsimp only at hpre ⊢
  by_cases h : (σ R).getLast? = some true
  · rw [ite_eq_left h] at hpre ⊢
    obtain ⟨hGB, t, ht, r⟩ := hQ input { cfg with state := some Q.q₀ } σ rfl hpark hpos hσ hpre hB
    refine ⟨hGB, 1 + t, by have := Nat.le_max_right (TP input.length) (TQ input.length); omega, ?_⟩
    refine RunsTo.caseProbe (some R) P Q cfg hq _ hposB (after cfg (G input σ)) t
      (fun h' ↦ absurd (hprobe.trans h) h') (fun _ ↦ r)
  · rw [ite_eq_right h] at hpre ⊢
    obtain ⟨hFB, t, ht, r⟩ := hP input { cfg with state := some P.q₀ } σ rfl hpark hpos hσ hpre hB
    refine ⟨hFB, 1 + t, by have := Nat.le_max_left (TP input.length) (TQ input.length); omega, ?_⟩
    refine RunsTo.caseProbe (some R) P Q cfg hq _ hposB (after cfg (F input σ)) t (fun _ ↦ r)
      (fun h' ↦ absurd (hprobe.symm.trans h') h)

end

end Geb.SizeBounded.Logspace.Machine
