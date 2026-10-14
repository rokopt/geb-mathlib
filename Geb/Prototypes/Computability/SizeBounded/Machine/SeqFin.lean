/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Seq
public import Geb.Mathlib.Data.FinEnum

set_option doc.verso true in
/-!
# Sequencing a family

{lit}`seqFin` sequences a family of machines indexed by {lit}`Fin m`, in
index order, by recursion on {lit}`m` via {lit}`seq`; the empty family
sequences to {lit}`idle`, the machine that halts at once doing nothing.
{lit}`composeFin` composes a family of transformers in the same order, and
{lit}`Transforms.seqFin` shows the sequenced family transforms by the
composite of the family's transformers.

The state type {lit}`seqFinState` depends on the family's state types alone.
The family's initial state and transition {lit}`seqFinTr` are defined by the
same recursion from the members' transitions and initial states, and
{lit}`seqFin_ofTr` identifies the sequenced family of machines built from
transition functions with the machine built from {lit}`seqFinTr`.

# Main definitions

* {lit}`idleTr`, {lit}`idle` — the transition, and the machine, that halts at
  once, doing nothing.
* {lit}`seqFinState`, {lit}`seqFinTr` — the state type, and the initial state
  and the transition, of a sequenced family.
* {lit}`seqFin` — sequencing a family of machines indexed by {lit}`Fin m`.
* {lit}`seqFinEnum` — a choice-free enumeration of a sequenced family's
  state.
* {lit}`composeFin` — the composite of a family of transformers.

# Main statements

* {lit}`idle_tr` — the transition of {lit}`idle` is {lit}`idleTr`.
* {lit}`idle_transforms` — {lit}`idle` transforms by the identity in one
  step.
* {lit}`seqFin_zero`, {lit}`seqFin_succ` — the recursive equations of
  {lit}`seqFin`.
* {lit}`seqFin_ofTr` — the sequenced family of machines built from transition
  functions is the machine built from {lit}`seqFinTr`.
* {lit}`composeFin_zero`, {lit}`composeFin_succ` — the recursive equations of
  {lit}`composeFin`.
* {lit}`composeFin_bounded` — a composite of bound-preserving transformers
  preserves the bound.
* {lit}`Transforms.seqFin` — the sequenced family transforms by the
  composite of the family's transformers.

# Tags

Turing machine, sequencing, composition, recursion
-/

set_option doc.verso true

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM
open scoped FinEnum

public section

/-- The transition that halts at once, doing nothing. -/
@[expose] def idleTr {k : ℕ} (_ : Unit) (_ : Option Bool) (_ : Fin k → Option Bool) :
    Action k Bool Unit :=
  { inputTape := 0, workTapes := fun _ ↦ (none, 0), output := none, state := none }

/-- The machine that halts at once, doing nothing. -/
@[expose] def idle {k : ℕ} : MultiTapeTM k Bool Unit := ofTr () idleTr

/-- The transition of {name}`idle` is {name}`idleTr`. -/
theorem idle_tr {k : ℕ} (q : Unit) (inp : Option Bool) (work : Fin k → Option Bool) :
    idle.tr q inp work = idleTr q inp work :=
  tr_ofTr _ _ _ _ _

/-- {name}`idle` transforms by the identity in one step. -/
theorem idle_transforms {k : ℕ} (B : ℕ) : Transforms (idle (k := k)) (fun σ ↦ σ) 1 B := by
  intro _ cfg σ hq hpark hσ hB _
  have hhalt : idle.step cfg = after cfg σ := by
    rw [step_of_state _ _ () hq, idle_tr]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos 0 = (after cfg σ).inputPos
      rw [moveInputPos_zero, after_inputPos]
    · dsimp only
      funext i
      exact hσ i
    · change (fun i ↦ cfg.workTapePos i + (0 : ℤ)) = (after cfg σ).workTapePos
      funext i
      rw [add_zero, after_workTapePos]
    · exact List.append_nil _
  have hlive : cfg.state ≠ none := by
    rw [hq]
    exact Option.some_ne_none _
  have hout : idle.outputSymbol cfg = none := by
    unfold outputSymbol
    simp only [hq, idle_tr]
    rfl
  have hbound : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B := by
    intro i
    rw [hpark i]
    constructor <;> omega
  exact ⟨1, le_refl 1, RunsTo.ofFamily idle (fun _ ↦ cfg) 0 B _ (fun _ _ ↦ hlive)
    (fun _ h ↦ absurd h (by omega)) hhalt rfl (fun _ _ ↦ hout) (fun _ _ i ↦ hbound i)
    (fun i ↦ hbound i)⟩

/-- The state type of a sequenced family indexed by {lit}`Fin m`: an iterated
binary sum, so that the choice-free {lit}`FinEnum` instance on sums applies. -/
@[expose] def seqFinState : (m : ℕ) → (Fin m → Type) → Type :=
  Nat.rec (fun _ ↦ Unit) (fun m ih S ↦ ih (fun i ↦ S i.castSucc) ⊕ S (Fin.last m))

/-- The initial state and the transition of a sequenced family, from the members'
initial states and transitions {lit}`M`, in index order, by recursion on {lit}`m`
via {name}`seqTr`; the empty family's are those of {name}`idle`. The initial state
is the state of {name}`idle`, which the sequenced family runs first, in the
innermost summand. Members and result are pairs rather than functions, so that
evaluating the recursion evaluates each member once and builds the transition
once, rather than at every application of the transition. -/
@[expose] def seqFinTr {k : ℕ} : (m : ℕ) → (S : Fin m → Type) →
    ((i : Fin m) → S i × (S i → Option Bool → (Fin k → Option Bool) → Action k Bool (S i))) →
    seqFinState m S × (seqFinState m S → Option Bool → (Fin k → Option Bool) →
      Action k Bool (seqFinState m S)) :=
  Nat.rec (fun _ _ ↦ ((), idleTr))
    (fun m ih S M ↦
      let p := ih (fun i ↦ S i.castSucc) (fun i ↦ M i.castSucc)
      let e := M (Fin.last m)
      (.inl p.1, seqTr p.2 e.2 e.1))

/-- Sequencing a family of machines indexed by {lit}`Fin m`, in index order,
by recursion on {lit}`m` via {name}`seq`; the empty family sequences to
{name}`idle`. -/
@[expose] noncomputable def seqFin {k : ℕ} : (m : ℕ) → (S : Fin m → Type) →
    ((i : Fin m) → MultiTapeTM k Bool (S i)) → MultiTapeTM k Bool (seqFinState m S) :=
  Nat.rec (fun _ _ ↦ idle)
    (fun m ih S P ↦ seq (ih (fun i ↦ S i.castSucc) (fun i ↦ P i.castSucc)) (P (Fin.last m)))

/-- The empty family sequences to {name}`idle`. -/
theorem seqFin_zero {k : ℕ} (S : Fin 0 → Type) (P : (i : Fin 0) → MultiTapeTM k Bool (S i)) :
    seqFin 0 S P = idle := rfl

/-- A family of length {lit}`m + 1` sequences its first {lit}`m` members, then
its last. -/
theorem seqFin_succ {k m : ℕ} (S : Fin (m + 1) → Type)
    (P : (i : Fin (m + 1)) → MultiTapeTM k Bool (S i)) :
    seqFin (m + 1) S P =
      seq (seqFin m (fun i ↦ S i.castSucc) (fun i ↦ P i.castSucc)) (P (Fin.last m)) := rfl

/-- Sequencing a family of machines built from transition functions is the
machine built from the sequenced transition. -/
theorem seqFin_ofTr {k : ℕ} : ∀ (m : ℕ) (S : Fin m → Type) (q₀ : (i : Fin m) → S i)
    (tr : (i : Fin m) → S i → Option Bool → (Fin k → Option Bool) → Action k Bool (S i)),
    seqFin m S (fun i ↦ ofTr (q₀ i) (tr i)) =
      ofTr (seqFinTr m S fun i ↦ (q₀ i, tr i)).1 (seqFinTr m S fun i ↦ (q₀ i, tr i)).2 :=
  Nat.rec (fun _ _ _ ↦ rfl)
    (fun m ih S q₀ tr ↦
      (congrArg (fun M ↦ seq M (ofTr (q₀ (Fin.last m)) (tr (Fin.last m))))
        (ih (fun i ↦ S i.castSucc) (fun i ↦ q₀ i.castSucc) (fun i ↦ tr i.castSucc))).trans
        (seq_ofTr _ _ _ _))

/-- A choice-free enumeration of a sequenced family's state. -/
@[expose, instance_reducible] def seqFinEnum : (m : ℕ) → (S : Fin m → Type) →
    ((i : Fin m) → FinEnum (S i)) → FinEnum (seqFinState m S) :=
  Nat.rec (fun _ _ ↦ FinEnum.unit)
    (fun m ih S E ↦
      @FinEnum.finSum _ _ (ih (fun i ↦ S i.castSucc) (fun i ↦ E i.castSucc)) (E (Fin.last m)))

/-- The composite of a family of transformers, in index order. -/
@[expose] def composeFin {k : ℕ} : (m : ℕ) →
    (Fin m → (Fin k → List Bool) → Fin k → List Bool) → (Fin k → List Bool) → Fin k → List Bool :=
  Nat.rec (fun _ σ ↦ σ) (fun m ih F σ ↦ F (Fin.last m) (ih (fun i ↦ F i.castSucc) σ))

/-- The empty composite is the identity. -/
theorem composeFin_zero {k : ℕ} (F : Fin 0 → (Fin k → List Bool) → Fin k → List Bool)
    (σ : Fin k → List Bool) : composeFin 0 F σ = σ := rfl

/-- The composite of {lit}`m + 1` transformers applies the last after the
first {lit}`m`. -/
theorem composeFin_succ {k m : ℕ} (F : Fin (m + 1) → (Fin k → List Bool) → Fin k → List Bool)
    (σ : Fin k → List Bool) :
    composeFin (m + 1) F σ = F (Fin.last m) (composeFin m (fun i ↦ F i.castSucc) σ) := rfl

/-- A composite of bound-preserving transformers preserves the bound. -/
theorem composeFin_bounded {k : ℕ} (B : ℕ) : ∀ (m : ℕ)
    (F : Fin m → (Fin k → List Bool) → Fin k → List Bool),
    (∀ i σ, Bounded σ B → Bounded (F i σ) B) →
    ∀ σ, Bounded σ B → Bounded (composeFin m F σ) B :=
  Nat.rec
    (fun F _ σ hσ ↦ by rw [composeFin_zero]; exact hσ)
    (fun m ih F hF σ hσ ↦ by
      rw [composeFin_succ]
      exact hF (Fin.last m) _ (ih (fun i ↦ F i.castSucc) (fun i ↦ hF i.castSucc) σ hσ))

/-- Sequencing a family of programs transforms by the composite of their
transformers, in {lit}`m * T + 1` steps for a family of {lit}`m` programs
each within {lit}`T`. -/
theorem Transforms.seqFin {k : ℕ} (B T : ℕ) : ∀ (m : ℕ) (S : Fin m → Type)
    (P : (i : Fin m) → MultiTapeTM k Bool (S i))
    (F : Fin m → (Fin k → List Bool) → Fin k → List Bool),
    (∀ i, Transforms (P i) (F i) T B) → (∀ i σ, Bounded σ B → Bounded (F i σ) B) →
    Transforms (seqFin m S P) (composeFin m F) (m * T + 1) B :=
  Nat.rec
    (fun _ _ F _ _ ↦
      Transforms.mono_time
        (Transforms.congr (idle_transforms B) (fun σ ↦ (composeFin_zero F σ).symm))
        (by omega))
    (fun m ih S P F hP hF ↦
      Transforms.congr
        (Transforms.mono_time
          (Transforms.seq
            (ih (fun i ↦ S i.castSucc) (fun i ↦ P i.castSucc) (fun i ↦ F i.castSucc)
              (fun i ↦ hP i.castSucc) (fun i σ ↦ hF i.castSucc σ))
            (hP (Fin.last m))
            (composeFin_bounded B m (fun i ↦ F i.castSucc) (fun i ↦ hF i.castSucc)))
          (by rw [Nat.succ_mul]; omega))
        (fun σ ↦ (composeFin_succ F σ).symm))

end

end Geb.SizeBounded.Machine
