/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Contract
public import Mathlib.Logic.Function.Iterate

set_option doc.verso true in
/-!
# The loop while a probe reads a symbol

{lit}`whileNonblank p P` tests a probe, the input head or a work head, and
while it reads a symbol runs the body {lit}`P` and tests again; when it reads
a blank it halts. Its state type is a test state summed with the body's
state type, and a halting transition of the body enters the test state
instead. {lit}`liftBody` embeds a body configuration into one of the loop,
agreeing with the loop's steps and output, so a run of the body lifts to a
reach of the loop ending in the test state.

The core statement, {lit}`RunsTo.whileNonblank`, reads a run of the loop off
a family of halted body configurations, each the target of a run of the body
restarted from the previous, the probe reading a symbol at every member but
the last: the run takes one test step per member. The contract
{lit}`TransformsIn.whileReg` is its instance at a work-tape probe, for a body
under contract: the loop transforms by the iterate of the body's transformer
as many times as leaves the tested register nonempty, its precondition
supplying that count and the body's precondition at each iterate.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's {name}`Turing.Cfg.inputSymbol`.

# Main definitions

* {lit}`Probe`, {lit}`probeRead`, {lit}`probeOf` — the input head or a work
  head, the symbol under it, and the symbol a configuration's probe reads.
* {lit}`whileNonblank` — the loop.
* {lit}`liftBody` — the embedding of a body configuration into the loop's.

# Main statements

* {lit}`whileNonblank_step_body`, {lit}`whileNonblank_runFrom_body`,
  {lit}`whileNonblank_outputString_body` — the loop mirrors its body from a
  lifted configuration while the body runs.
* {lit}`RunsTo.liftBody` — a run of the body lifts to a reach of the loop.
* {lit}`whileNonblank_enter`, {lit}`whileNonblank_exit` — the test step
  enters the body or halts.
* {lit}`RunsTo.whileNonblank` — the run of the loop over a family of
  iterations.
* {lit}`tapeOf_zero_eq_none_iff` — a parked head reads a blank exactly on the
  empty word.
* {lit}`TransformsIn.whileReg` — the loop's contract at a work-tape probe.

# Tags

Turing machine, loop, iteration, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine

public section

/-- A probe: the input head, or the head of a work tape. -/
abbrev Probe (k : ℕ) : Type := Option (Fin k)

/-- The symbol under a probe. -/
@[expose] def probeRead {k : ℕ} (p : Probe k) (inp : Option Bool) (work : Fin k → Option Bool) :
    Option Bool :=
  match p with
  | none => inp
  | some R => work R

/-- The symbol a configuration's probe reads. -/
@[expose] def probeOf {k : ℕ} {State : Type} {input : List Bool} (p : Probe k)
    (cfg : Cfg k Bool State input) : Option Bool :=
  probeRead p cfg.inputSymbol cfg.workTapeSymbols

/-- The loop: in the test state, enter the body when the probe reads a symbol
and halt otherwise; in a body state, the body's transition with a halting
successor replaced by the test state. -/
@[expose] def whileNonblank {k : ℕ} {S : Type} (p : Probe k) (P : MultiTapeTM k Bool S) :
    MultiTapeTM k Bool (Unit ⊕ S) where
  q₀ := .inl ()
  tr q inp work :=
    match q with
    | .inl () =>
      { inputTape := 0, workTapes := fun _ ↦ (none, 0), output := none,
        state := if (probeRead p inp work).isSome then some (.inr P.q₀) else none }
    | .inr s => let o := P.tr s inp work
      { o with state := some (o.state.elim (.inl ()) .inr) }

/-- A body configuration lifted into the loop: a halted one becomes the test
state. -/
@[expose] def liftBody {k : ℕ} {S : Type} {input : List Bool} (cfg : Cfg k Bool S input) :
    Cfg k Bool (Unit ⊕ S) input :=
  { cfg with state := some (cfg.state.elim (.inl ()) .inr) }

/-- A halted body configuration lifts to the test state. -/
theorem liftBody_halt {k : ℕ} {S : Type} {input : List Bool} (cfg : Cfg k Bool S input)
    (h : cfg.state = none) : liftBody cfg = { cfg with state := some (.inl ()) } := by
  unfold liftBody
  rw [h]
  rfl

/-- The lift keeps the tapes. -/
@[simp] theorem liftBody_workTapes {k : ℕ} {S : Type} {input : List Bool}
    (cfg : Cfg k Bool S input) : (liftBody cfg).workTapes = cfg.workTapes := rfl

/-- The lift keeps the heads. -/
@[simp] theorem liftBody_workTapePos {k : ℕ} {S : Type} {input : List Bool}
    (cfg : Cfg k Bool S input) : (liftBody cfg).workTapePos = cfg.workTapePos := rfl

/-- The lift is live. -/
theorem liftBody_state_ne_none {k : ℕ} {S : Type} {input : List Bool}
    (cfg : Cfg k Bool S input) : (liftBody cfg).state ≠ none := by
  unfold liftBody
  exact Option.some_ne_none _

/-- A step of the loop from a lifted live body configuration is the lift of the
body's step. -/
theorem whileNonblank_step_body {k : ℕ} {S : Type} {input : List Bool} (p : Probe k)
    (P : MultiTapeTM k Bool S) (cfg : Cfg k Bool S input) (s : S) (hq : cfg.state = some s) :
    (whileNonblank p P).step (liftBody cfg) = liftBody (P.step cfg) := by
  unfold step liftBody
  simp only [hq]
  rfl

/-- The loop emits what the body emits from a lifted live configuration. -/
theorem whileNonblank_outputSymbol_body {k : ℕ} {S : Type} {input : List Bool} (p : Probe k)
    (P : MultiTapeTM k Bool S) (cfg : Cfg k Bool S input) (s : S) (hq : cfg.state = some s) :
    (whileNonblank p P).outputSymbol (liftBody cfg) = P.outputSymbol cfg := by
  unfold outputSymbol liftBody
  simp only [hq]
  rfl

/-- While the body has not halted, the loop mirrors it. -/
theorem whileNonblank_runFrom_body {k : ℕ} {S : Type} {input : List Bool} (p : Probe k)
    (P : MultiTapeTM k Bool S) (cfg : Cfg k Bool S input) :
    ∀ t, (∀ t' < t, (P.runFrom cfg t').state ≠ none) →
      (whileNonblank p P).runFrom (liftBody cfg) t = liftBody (P.runFrom cfg t) :=
  Nat.rec
    (fun _ ↦ by rw [runFrom_zero, runFrom_zero])
    (fun t ih hlive ↦ by
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (hlive t (by omega))
      rw [runFrom_succ_eq_step', ih (fun t' ht' ↦ hlive t' (by omega)), runFrom_succ_eq_step',
        whileNonblank_step_body p P (P.runFrom cfg t) q hq])

/-- While the body has not halted, the loop emits what the body emits. -/
theorem whileNonblank_outputString_body {k : ℕ} {S : Type} {input : List Bool} (p : Probe k)
    (P : MultiTapeTM k Bool S) (cfg : Cfg k Bool S input) :
    ∀ t, (∀ t' < t, (P.runFrom cfg t').state ≠ none) →
      (whileNonblank p P).outputString (liftBody cfg) t = P.outputString cfg t :=
  Nat.rec
    (fun _ ↦ rfl)
    (fun t ih hlive ↦ by
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (hlive t (by omega))
      rw [outputString_succ, outputString_succ, ih (fun t' ht' ↦ hlive t' (by omega)),
        whileNonblank_runFrom_body p P cfg t (fun t' ht' ↦ hlive t' (by omega)),
        whileNonblank_outputSymbol_body p P (P.runFrom cfg t) q hq])

/-- A run of the body lifts to a reach of the loop, ending in the test state. -/
theorem _root_.Geb.SizeBounded.Machine.RunsTo.liftBody {k : ℕ} {S : Type} {input : List Bool}
    (p : Probe k) {P : MultiTapeTM k Bool S} {cfg cfg' : Cfg k Bool S input} {t B : ℕ}
    (h : RunsTo P cfg cfg' t B) :
    Reaches (whileNonblank p P) (Machine.liftBody cfg) { cfg' with state := some (.inl ()) } t B
    where
  live := fun t' ht' ↦ by
    rw [whileNonblank_runFrom_body p P cfg t' (fun s hs ↦ h.live s (by omega))]
    exact liftBody_state_ne_none _
  runFrom_eq := by
    rw [whileNonblank_runFrom_body p P cfg t h.live, h.runFrom_eq, liftBody_halt cfg' h.halted]
  pos := fun t' ht' i ↦ by
    rw [whileNonblank_runFrom_body p P cfg t' (fun s hs ↦ h.live s (by omega)),
      liftBody_workTapePos]
    exact h.pos t' ht' i
  output := by rw [whileNonblank_outputString_body p P cfg t h.live, h.output]

/-- The test step from a configuration whose probe reads a symbol enters the
body, changing nothing else. -/
theorem whileNonblank_enter {k : ℕ} {S : Type} {input : List Bool} (p : Probe k)
    (P : MultiTapeTM k Bool S) (cfg : Cfg k Bool (Unit ⊕ S) input)
    (hq : cfg.state = some (.inl ())) (hprobe : probeOf p cfg ≠ none) (B : ℕ)
    (hpos : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B) :
    Reaches (whileNonblank p P) cfg { cfg with state := some (.inr P.q₀) } 1 B := by
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hprobe
  have hstep : (whileNonblank p P).step cfg = { cfg with state := some (.inr P.q₀) } := by
    rw [step_of_state _ _ _ hq]
    have htr : (whileNonblank p P).tr (.inl ()) cfg.inputSymbol cfg.workTapeSymbols =
        { inputTape := 0, workTapes := fun _ ↦ (none, 0), output := none,
          state := some (.inr P.q₀) } := by
      unfold probeOf at hb
      simp only [whileNonblank, hb, Option.isSome_some, ↓reduceIte]
    rw [htr]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · rfl
    · funext j
      change cfg.workTapePos j + ((0 : SignType) : ℤ) = cfg.workTapePos j
      rw [SignType.coe_zero, add_zero]
    · exact List.append_nil _
  have hout : (whileNonblank p P).outputSymbol cfg = none := by
    unfold outputSymbol
    rw [hq]
    rfl
  refine Reaches.ofFamily (whileNonblank p P) (fun s ↦ if s = 0 then cfg else
    { cfg with state := some (.inr P.q₀) }) 1 B ?_ ?_ ?_ ?_
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

/-- The test step from a configuration whose probe reads a blank halts, changing
nothing else. -/
theorem whileNonblank_exit {k : ℕ} {S : Type} {input : List Bool} (p : Probe k)
    (P : MultiTapeTM k Bool S) (cfg : Cfg k Bool (Unit ⊕ S) input)
    (hq : cfg.state = some (.inl ())) (hprobe : probeOf p cfg = none) (B : ℕ)
    (hpos : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B) :
    RunsTo (whileNonblank p P) cfg { cfg with state := none } 1 B := by
  have hstep : (whileNonblank p P).step cfg = { cfg with state := none } := by
    rw [step_of_state _ _ _ hq]
    have htr : (whileNonblank p P).tr (.inl ()) cfg.inputSymbol cfg.workTapeSymbols =
        { inputTape := 0, workTapes := fun _ ↦ (none, 0), output := none, state := none } := by
      unfold probeOf at hprobe
      simp only [whileNonblank, hprobe, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    rw [htr]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · rfl
    · funext j
      change cfg.workTapePos j + ((0 : SignType) : ℤ) = cfg.workTapePos j
      rw [SignType.coe_zero, add_zero]
    · exact List.append_nil _
  have hout : (whileNonblank p P).outputSymbol cfg = none := by
    unfold outputSymbol
    rw [hq]
    rfl
  have hlive : cfg.state ≠ none := by
    rw [hq]
    exact Option.some_ne_none _
  exact RunsTo.ofFamily (whileNonblank p P) (fun _ ↦ cfg) 0 B _ (fun _ _ ↦ hlive)
    (fun _ h ↦ absurd h (by omega)) hstep rfl (fun _ _ ↦ hout) (fun _ _ i ↦ hpos i) hpos

/-- The run of the loop over a family of iterations: from a family of halted
body configurations, each the target of a run of the body restarted from the
previous within {lit}`T` steps, the probe reading a symbol at every member but
the last, the loop runs from the first member in the test state to the last,
halted, within {lit}`N * (T + 1) + 1` steps. -/
theorem _root_.Geb.SizeBounded.Machine.RunsTo.whileNonblank {k : ℕ} {S : Type}
    {input : List Bool} (p : Probe k) (P : MultiTapeTM k Bool S) (B T : ℕ) :
    ∀ (N : ℕ) (c : ℕ → Cfg k Bool S input),
      (∀ i < N, probeOf p (c i) ≠ none) → probeOf p (c N) = none →
      (∀ i < N, ∃ t ≤ T, RunsTo P { c i with state := some P.q₀ } (c (i + 1)) t B) →
      (∀ i, -1 ≤ (c 0).workTapePos i ∧ (c 0).workTapePos i ≤ B) →
      ∃ t ≤ N * (T + 1) + 1,
        RunsTo (Machine.whileNonblank p P) { c 0 with state := some (.inl ()) }
          { c N with state := none } t B := by
  refine Nat.rec (fun c _ hexit _ hpos ↦ ⟨1, by omega, ?_⟩) (fun N ih c hin hexit hrun hpos ↦ ?_)
  · exact whileNonblank_exit p P _ rfl hexit B hpos
  · obtain ⟨t, ht, r⟩ := hrun 0 (by omega)
    have r₁ := whileNonblank_enter p P { c 0 with state := some (.inl ()) } rfl (hin 0 (by omega))
      B hpos
    have r₂ := r.liftBody p
    have hpos1 : ∀ i, -1 ≤ (c 1).workTapePos i ∧ (c 1).workTapePos i ≤ B := by
      intro i
      have := r.pos t (le_refl _) i
      rwa [r.runFrom_eq] at this
    obtain ⟨t', ht', r₃⟩ := ih (fun i ↦ c (i + 1)) (fun i hi ↦ hin (i + 1) (by omega)) hexit
      (fun i hi ↦ hrun (i + 1) (by omega)) hpos1
    refine ⟨1 + t + t', ?_, ⟨(r₁.trans r₂).trans r₃.toReaches, r₃.halted⟩⟩
    rw [Nat.succ_mul]
    omega

/-- A parked head reads a blank exactly when its register holds the empty
word. -/
theorem tapeOf_zero_eq_none_iff (w : List Bool) : tapeOf w 0 = none ↔ w = [] := by
  cases w with
  | nil => exact ⟨fun _ ↦ rfl, fun _ ↦ by rw [tapeOf_nil]⟩
  | cons b w' =>
    refine ⟨fun h ↦ ?_, fun h ↦ absurd h (List.cons_ne_nil _ _)⟩
    rw [tapeOf_of_lt _ 0 (le_refl _) (by rw [List.length_cons]; omega)] at h
    exact absurd h (Option.some_ne_none _)

/-- The loop's contract at a work-tape probe: the loop transforms by the iterate
of the body's transformer as many times as the count {lit}`N` its precondition
supplies, the body's precondition holding and the register being nonempty at
every earlier iterate, and the register empty at the last. -/
theorem TransformsIn.whileReg {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool} {T B : ℕ → ℕ} (R : Fin k)
    (hP : TransformsIn P Pre F T B) (Pre₀ : List Bool → (Fin k → List Bool) → Prop)
    (N : List Bool → (Fin k → List Bool) → ℕ) (Nb : ℕ → ℕ)
    (hN : ∀ input σ, Pre₀ input σ → N input σ ≤ Nb input.length)
    (hiter : ∀ input σ, Pre₀ input σ → ∀ j < N input σ,
      (F input)^[j] σ R ≠ [] ∧ Pre input ((F input)^[j] σ))
    (hexit : ∀ input σ, Pre₀ input σ → (F input)^[N input σ] σ R = []) :
    TransformsIn (whileNonblank (some R) P) Pre₀ (fun input σ ↦ (F input)^[N input σ] σ)
      (fun n ↦ Nb n * (T n + 1) + 1) B := by
  intro input cfg σ hq hpark hpos hσ hpre hB
  -- The body configurations: halted, parked as `cfg`, holding the iterates.
  let c : ℕ → Cfg k Bool S input := fun j ↦
    ⟨none, cfg.inputPos, fun i ↦ tapeOf ((F input)^[j] σ i), cfg.workTapePos, cfg.output⟩
  have hbnd : ∀ j ≤ N input σ, Bounded ((F input)^[j] σ) (B input.length) := by
    refine Nat.rec (fun _ ↦ hB) (fun j ih hj ↦ ?_)
    rw [Function.iterate_succ_apply']
    exact (hP input { c j with state := some P.q₀ } _ rfl hpark hpos (fun i ↦ rfl)
      (hiter input σ hpre j (by omega)).2 (ih (by omega))).1
  refine ⟨hbnd _ (le_refl _), ?_⟩
  have hprobe : ∀ j, probeOf (some R) (c j) = tapeOf ((F input)^[j] σ R) 0 := by
    intro j
    change (c j).workTapes R ((c j).workTapePos R) = _
    change tapeOf ((F input)^[j] σ R) (cfg.workTapePos R) = _
    rw [hpark R]
  have hposB : ∀ i, -1 ≤ (c 0).workTapePos i ∧ (c 0).workTapePos i ≤ B input.length := by
    intro i
    change -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B input.length
    rw [hpark i]
    constructor <;> omega
  obtain ⟨t, ht, r⟩ := RunsTo.whileNonblank (some R) P (B input.length) (T input.length)
    (N input σ) c
    (fun j hj ↦ by
      rw [hprobe]
      intro h
      exact (hiter input σ hpre j hj).1 ((tapeOf_zero_eq_none_iff _).mp h))
    (by rw [hprobe]; exact (tapeOf_zero_eq_none_iff _).mpr (hexit input σ hpre))
    (fun j hj ↦ by
      obtain ⟨_, t, ht, r⟩ := hP input { c j with state := some P.q₀ } _ rfl hpark hpos
        (fun i ↦ rfl) (hiter input σ hpre j hj).2 (hbnd j (by omega))
      refine ⟨t, ht, ?_⟩
      have hc : after { c j with state := some P.q₀ } (F input ((F input)^[j] σ)) = c (j + 1) := by
        apply Cfg.ext
        · rfl
        · rfl
        · funext i
          change tapeOf (F input ((F input)^[j] σ) i) = tapeOf ((F input)^[j + 1] σ i)
          rw [Function.iterate_succ_apply']
        · rfl
        · rfl
      rw [hc] at r
      exact r)
    hposB
  refine ⟨t, le_trans ht (Nat.add_le_add_right (Nat.mul_le_mul_right _ (hN input σ hpre)) 1), ?_⟩
  have hcfg : { c 0 with state := some (Sum.inl ()) } = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · funext i
      exact (hσ i).symm
    · rfl
    · rfl
  have hend : { c (N input σ) with state := none } = after cfg ((F input)^[N input σ] σ) := rfl
  rw [hcfg, hend] at r
  exact r

end

end Geb.SizeBounded.Logspace.Machine
