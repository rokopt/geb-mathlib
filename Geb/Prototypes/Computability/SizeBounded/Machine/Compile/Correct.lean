/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Basic
public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Bound

set_option doc.verso true in
/-!
# Correctness of the compiled programs

{lit}`Correct` is the contract a compiled expression's program meets: at every
admissible allocation of registers it transforms valuations by a function that
writes the expression's value into the output register, leaves the registers
below the first free one otherwise unchanged, and preserves the length bound,
within the step count {name}`Geb.SizeBounded.Machine.stepBound` reads off the
syntax. {lit}`CorrectSigma` states the same of an indexed pair whose indices
agree, the form the fold of {name}`Geb.SizeBounded.Machine.compile` produces.

The three base forms are the primitives, and their contracts are
{name}`Geb.SizeBounded.Machine.const_transforms`,
{name}`Geb.SizeBounded.Machine.copy_transforms` and
{name}`Geb.SizeBounded.Machine.sbs_transforms`: in each the transformer is an
update of the output register, so the frame and bound clauses come from the
equations of {name}`Function.update`.

A program carries a transition function, and its machine is the machine built
from it, so a program's contract is read off the machine-level combinators:
{lit}`seqProg_tm`, {lit}`seqFinProg_tm`, {lit}`caseLoopProg_tm` and the
equations for the primitives identify the machine of a program assembled from
programs with the corresponding combination of their machines, and
{lit}`Transforms.of_tm_eq` transfers a contract along such an equation.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: those
equations mention {name}`Turing.MultiTapeTM.tr`, which CSLib selects by
{lit}`Classical.choice`.

# Main definitions

* {lit}`Correct` — the contract of a compiled expression of a given arity.
* {lit}`CorrectSigma` — the contract of an indexed pair, the indices agreeing.

# Main statements

* {lit}`Transforms.of_tm_eq` — a program's contract read off a machine equal to
  its machine.
* {lit}`seqProg_tm`, {lit}`seqFinProg_tm`, {lit}`caseLoopProg_tm`,
  {lit}`constProg_tm`, {lit}`copyProg_tm`, {lit}`copyRevProg_tm`,
  {lit}`sbsProg_tm` — the machine of a program assembled by a combinator is the
  combinator's machine.
* {lit}`Correct.transport` — the contract transports along an equality of
  arities.
* {lit}`CorrectSigma.atArity` — a child's correctness at the arity its parent
  prescribes.
* {lit}`correct_const`, {lit}`correct_proj`, {lit}`correct_sbs` — the three
  base forms meet the contract.

# Tags

Turing machine, compilation, correctness, register, size-bounded
-/

set_option doc.verso true

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM
open Cobham (Sem transport)
open Geb.SizeBounded (Direction rc evalValue nsiValue sbsSem length_sbsSem_le)

public section

/-- A program's contract read off a machine equal to its machine. -/
theorem Transforms.of_tm_eq {k : ℕ} {p : Prog k} {tm : MultiTapeTM k Bool p.State}
    {F : (Fin k → List Bool) → Fin k → List Bool} {T B : ℕ} (h : p.tm = tm)
    (ht : Transforms tm F T B) : Transforms p.tm F T B :=
  h ▸ ht

/-- The machine of sequenced programs is the sequenced machines. -/
theorem seqProg_tm {k : ℕ} (p q : Prog k) : (seqProg p q).tm = seq p.tm q.tm :=
  (seq_ofTr _ _ _ _).symm

/-- The machine of a sequenced family of programs is the sequenced family of
their machines. -/
theorem seqFinProg_tm {k : ℕ} (m : ℕ) (ps : Fin m → Prog k) :
    (seqFinProg m ps).tm = seqFin m (fun i ↦ (ps i).State) fun i ↦ (ps i).tm :=
  (seqFin_ofTr _ _ _ _).symm

/-- The machine of the loop program is the loop over the bodies' machines. -/
theorem caseLoopProg_tm {k : ℕ} (R : Fin k) (pF pT : Prog k) :
    (caseLoopProg R pF pT).tm = caseLoop R pF.tm pT.tm :=
  (caseLoop_ofTr _ _ _ _ _).symm

/-- The machine of {name}`constProg` is {name}`const`. -/
theorem constProg_tm {k : ℕ} (w : List Bool) (j : Fin k) : (constProg w j).tm = const w j :=
  (const_eq_ofTr w j).symm

/-- The machine of {name}`copyProg` is {name}`copy`. -/
theorem copyProg_tm {k : ℕ} (i j : Fin k) : (copyProg i j).tm = copy i j :=
  (copy_eq_ofTr i j).symm

/-- The machine of {name}`copyRevProg` is {name}`copyRev`. -/
theorem copyRevProg_tm {k : ℕ} (i j : Fin k) : (copyRevProg i j).tm = copyRev i j :=
  (copyRev_eq_ofTr i j).symm

/-- The machine of {name}`sbsProg` is {name}`sbs`. -/
theorem sbsProg_tm {k : ℕ} (b : Bool) (x y j : Fin k) : (sbsProg b x y j).tm = sbs b x y j :=
  (sbs_eq_ofTr b x y j).symm

/-- The compiled program of arity {lit}`n` computes {lit}`f` with constant
{lit}`K` and step bound {lit}`Tf`: from every admissible allocation (an injective
environment below the first free register, an output register below it and
outside the environment) and every length bound at least {lit}`K`, its machine
transforms valuations by a function that puts the value in the output register,
leaves every other register below the first free one unchanged, and preserves the
bound. -/
@[expose] def Correct {k n : ℕ} (p : Compiled k n) (f : Sem n) (K : ℕ) (Tf : ℕ → ℕ) : Prop :=
  ∀ (env : Fin n → Fin k) (out : Fin k) (free : ℕ) (hfree : free + p.regs ≤ k),
    Function.Injective env → (∀ i, (env i).val < free) → out.val < free →
    (∀ i, env i ≠ out) → ∀ B, K ≤ B →
    ∃ F : (Fin k → List Bool) → Fin k → List Bool,
      Transforms (p.prog env out free hfree).tm F (Tf B) B ∧
      (∀ σ, F σ out = f (σ ∘ env)) ∧
      (∀ σ (i : Fin k), i.val < free → i ≠ out → F σ i = σ i) ∧
      (∀ σ, Bounded σ B → Bounded (F σ) B)

/-- Correctness of an indexed pair, the indices agreeing. -/
@[expose] def CorrectSigma {k : ℕ} (p : Σ i, Compiled k i) (m : Σ i, Sem i) (K : ℕ)
    (Tf : ℕ → ℕ) : Prop :=
  ∃ h : p.1 = m.1, Correct (transportP h p.2) m.2 K Tf

/-- Correctness transports along an equality of arities. -/
theorem Correct.transport {k i j : ℕ} (h : i = j) {p : Compiled k i} {f : Sem i} {K : ℕ}
    {Tf : ℕ → ℕ} (hp : Correct p f K Tf) : Correct (transportP h p) (transport h f) K Tf := by
  subst h
  exact hp

/-- A child's correctness at the arity its parent prescribes. -/
theorem CorrectSigma.atArity {k : ℕ} {p : Σ i, Compiled k i} {m : Σ i, Sem i} {K : ℕ}
    {Tf : ℕ → ℕ} (hk : CorrectSigma p m K Tf) {n : ℕ} (h : p.1 = n) (hm : m.1 = n) :
    Correct (transportP h p.2) (transport hm m.2) K Tf := by
  obtain ⟨e, hc⟩ := hk
  have hc' := Correct.transport hm hc
  rw [transportP_transportP] at hc'
  exact hc'

/-- A constant node is correct with its length as constant. -/
theorem correct_const {k n : ℕ} (w : List Bool) (c : Direction (.const n w) → Σ i, Compiled k i)
    (h : ∀ b, (c b).1 = rc (.const n w) b) (s : Direction (.const n w) → Σ i, Sem i)
    (hs : ∀ b, (s b).1 = rc (.const n w) b) (K : Direction (.const n w) → ℕ)
    (Tf : Direction (.const n w) → ℕ → ℕ) :
    Correct (compileValue (.const n w) c h) (evalValue (.const n w) s hs)
      (nsiValue (.const n w) K) (stepValue (.const n w) Tf) := by
  intro _ out _ _ _ _ _ _ B hK
  exact ⟨fun σ ↦ Function.update σ out w,
    Transforms.of_tm_eq (constProg_tm w out) (const_transforms w out B),
    fun _ ↦ Function.update_self .., fun σ i _ hi ↦ Function.update_of_ne hi _ _,
    fun _ hσ ↦ hσ.update hK⟩

/-- A projection node is correct with constant zero. -/
theorem correct_proj {k n : ℕ} (i : Fin n) (c : Direction (.proj n i) → Σ i, Compiled k i)
    (h : ∀ b, (c b).1 = rc (.proj n i) b) (s : Direction (.proj n i) → Σ i, Sem i)
    (hs : ∀ b, (s b).1 = rc (.proj n i) b) (K : Direction (.proj n i) → ℕ)
    (Tf : Direction (.proj n i) → ℕ → ℕ) :
    Correct (compileValue (.proj n i) c h) (evalValue (.proj n i) s hs)
      (nsiValue (.proj n i) K) (stepValue (.proj n i) Tf) := by
  intro env out _ _ _ _ _ hne B _
  exact ⟨fun σ ↦ Function.update σ out (σ (env i)), Transforms.of_tm_eq (copyProg_tm (env i) out)
      (copy_transforms (env i) out (hne i) B),
    fun _ ↦ Function.update_self .., fun σ l _ hl ↦ Function.update_of_ne hl _ _,
    fun _ hσ ↦ hσ.update (hσ (env i))⟩

/-- A successor node is correct with constant zero. -/
theorem correct_sbs {k : ℕ} (b : Bool) (c : Direction (.sbs b) → Σ i, Compiled k i)
    (h : ∀ d, (c d).1 = rc (.sbs b) d) (s : Direction (.sbs b) → Σ i, Sem i)
    (hs : ∀ d, (s d).1 = rc (.sbs b) d) (K : Direction (.sbs b) → ℕ)
    (Tf : Direction (.sbs b) → ℕ → ℕ) :
    Correct (compileValue (.sbs b) c h) (evalValue (.sbs b) s hs)
      (nsiValue (.sbs b) K) (stepValue (.sbs b) Tf) := by
  intro env out _ _ hinj _ _ hne B _
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hxy : env 0 ≠ env 1 := fun heq ↦ h01 (hinj heq)
  exact ⟨fun σ ↦ Function.update σ out (sbsSem b (σ (env 0)) (σ (env 1))),
    Transforms.of_tm_eq (sbsProg_tm b (env 0) (env 1) out)
      (sbs_transforms b (env 0) (env 1) out hxy (hne 0) (hne 1) B),
    fun _ ↦ Function.update_self .., fun σ l _ hl ↦ Function.update_of_ne hl _ _,
    fun _ hσ ↦ hσ.update (length_sbsSem_le b (hσ (env 0)) (hσ (env 1)))⟩

end

end Geb.SizeBounded.Machine
