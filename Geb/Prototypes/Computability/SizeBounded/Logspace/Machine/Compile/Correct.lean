/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile.Basic
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Correctness of the compiled programs

{lit}`Correct` is the contract a compiled expression's program meets: at every
admissible allocation of registers, every word bound at least the expression's
constant, and every input, it transforms valuations whose environment
registers are well-formed by a function that writes the expression's meaning
on representations into the output register, leaves the tapes below the first
free one otherwise unchanged, and leaves the output register well-formed,
within the step bound the compiler computed and the tape bound
{name}`Geb.SizeBounded.Logspace.Machine.bound`. {lit}`CorrectSigma` states the
same of an indexed pair against a meaning indexed by the input, the form the
fold of {name}`Geb.SizeBounded.Logspace.Machine.compile` produces against
{name}`Geb.SizeBounded.Logspace.evalRep`.

The two base forms are sequences of the primitives
{name}`Geb.SizeBounded.Machine.const` and {name}`Geb.SizeBounded.Machine.copy`,
one per tape of the output register, and their contracts are those
primitives' lifted along {name}`Geb.SizeBounded.Machine.Transforms.toIn_of`.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's {name}`Turing.Cfg.inputSymbol`.

# Main definitions

* {lit}`EnvWF` — every register of an environment is well-formed.
* {lit}`Admissible` — an allocation of registers is admissible.
* {lit}`Correct`, {lit}`CorrectSigma` — the contract of a compiled expression,
  and of an indexed pair.

# Main statements

* {lit}`Correct.transport`, {lit}`CorrectSigma.atArity` — the contract
  transports along an equality of arities, and a child's contract at the
  arity its parent prescribes.
* {lit}`correct_const`, {lit}`correct_proj` — the two base forms meet the
  contract.

# Tags

Turing machine, compilation, correctness, register, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Turing MultiTapeTM
open Geb.SizeBounded (Shape Direction rc q sig finMax le_finMax stepDir S arity nsiValue)
open Geb.SizeBounded.Machine (Prog seq copy const Transforms Bounded const_transforms
  copy_transforms)

public section

/-- Every register of an environment is well-formed at the word bound and the
input's length. -/
@[expose] def EnvWF {k n : ℕ} (M : ℕ) (input : List Bool) (σ : Fin k → List Bool)
    (env : Fin n → Reg k) : Prop :=
  ∀ i, WF M input.length σ (env i)

/-- An allocation of registers is admissible: the environment's tapes are
distinct and below the first free tape, and the output register's two tapes
are distinct, below it, and outside the environment. -/
@[expose] def Admissible {k n : ℕ} (env : Fin n → Reg k) (out : Reg k) (free : ℕ) : Prop :=
  Function.Injective (fun x : Fin n × Fin 2 ↦ env x.1 x.2) ∧ (∀ i b, (env i b).val < free) ∧
    (∀ b, (out b).val < free) ∧ out 0 ≠ out 1 ∧ ∀ i b b', env i b ≠ out b'

/-- The contract of a compiled expression of arity {lit}`n` against a meaning
{lit}`f` indexed by the input, with constant {lit}`K`: at every admissible
allocation and every word bound at least {lit}`K`, its program transforms
valuations whose environment is well-formed by a function that puts the
meaning at the environment's representations into the output register, leaves
every other tape below the first free one unchanged, and leaves the output
register well-formed, within the compiled step bound and the tape bound. -/
@[expose] def Correct {k n : ℕ} (p : Compiled k n) (f : List Bool → RepSem n) (K : ℕ) : Prop :=
  ∀ (env : Fin n → Reg k) (out : Reg k) (free : ℕ) (hfree : free + p.regs ≤ k),
    Admissible env out free → ∀ M, K ≤ M →
    ∃ F : List Bool → (Fin k → List Bool) → Fin k → List Bool,
      TransformsIn (p.prog env out free hfree).tm (fun input σ ↦ EnvWF M input σ env) F
        (p.time M) (bound M) ∧
      (∀ input σ, EnvWF M input σ env →
        readRep (F input σ) out = f input fun i ↦ readRep σ (env i)) ∧
      (∀ input σ (t : Fin k), t.val < free → t ≠ out 0 → t ≠ out 1 → F input σ t = σ t) ∧
      (∀ input σ, EnvWF M input σ env → WF M input.length (F input σ) out)

/-- Correctness of an indexed pair against a meaning indexed by the input, the
indices agreeing at every input. -/
@[expose] def CorrectSigma {k : ℕ} (p : Σ i, Compiled k i) (m : List Bool → Σ i, RepSem i)
    (K : ℕ) : Prop :=
  ∃ h : ∀ w, (m w).1 = p.1, Correct p.2 (fun w ↦ repTransport (h w) (m w).2) K

/-- Correctness transports along an equality of arities. -/
theorem Correct.transport {k i j : ℕ} (h : i = j) {p : Compiled k i} {f : List Bool → RepSem i}
    {K : ℕ} (hp : Correct p f K) :
    Correct (transportP h p) (fun w ↦ repTransport h (f w)) K := by
  subst h
  exact hp

/-- A child's correctness at the arity its parent prescribes. -/
theorem CorrectSigma.atArity {k : ℕ} {p : Σ i, Compiled k i} {m : List Bool → Σ i, RepSem i}
    {K : ℕ} (hk : CorrectSigma p m K) {n : ℕ} (h : p.1 = n) (hm : ∀ w, (m w).1 = n) :
    Correct (transportP h p.2) (fun w ↦ repTransport (hm w) (m w).2) K := by
  obtain ⟨e, hc⟩ := hk
  have hc' := Correct.transport h hc
  have : (fun w ↦ repTransport h (repTransport (e w) (m w).2)) =
      fun w ↦ repTransport (hm w) (m w).2 := by
    funext w
    rw [repTransport_repTransport]
  rw [this] at hc'
  exact hc'

/-- The tape bound admits every word within the word bound, every counter
within the input's length, and a one-bit flag. -/
theorem le_bound_of_le {M n l : ℕ} (h : l ≤ M) : l ≤ bound M n := by
  unfold bound
  omega

/-- A counter within the input's length is within the tape bound. -/
theorem length_counterWord_le_bound {M n l : ℕ} (h : l ≤ n) :
    (counterWord l).length ≤ bound M n := by
  rw [length_counterWord]
  unfold bound
  have := Nat.size_le_size h
  omega

/-- The empty word is a counter, of zero. -/
theorem counterWord_zero : counterWord 0 = [] := rfl

/-- A constant node is correct with its length as constant. -/
theorem correct_const {k n : ℕ} (w : List Bool) (c : Direction (.const n w) → Σ i, Compiled k i)
    (h : ∀ b, (c b).1 = rc (.const n w) b) (s : Direction (.const n w) → List Bool → Σ i, RepSem i)
    (hs : ∀ b x, (s b x).1 = rc (.const n w) b) :
    Correct (compileValue (.const n w) c h)
      (fun x ↦ evalRepValue x (.const n w) (fun b ↦ s b x) (hs · x)) w.length := by
  intro env out free hfree hadm M hM
  obtain ⟨_, _, _, hout, _⟩ := hadm
  refine ⟨fun _ σ ↦ Function.update (Function.update σ (out 0) w) (out 1) [], ?_, ?_, ?_, ?_⟩
  · have h1 := Transforms.toIn_of (fun n ↦ const_transforms w (out 0) (bound M n))
      (fun _ _ ↦ True) fun input σ hB _ ↦ hB.update (le_bound_of_le hM)
    have h2 := Transforms.toIn_of (fun n ↦ const_transforms [] (out 1) (bound M n))
      (fun _ _ ↦ True) fun input σ hB _ ↦ hB.update (Nat.zero_le _)
    refine TransformsIn.mono_time ((h1.seq h2).mono_pre fun _ _ _ _ ↦ ⟨trivial, trivial⟩) ?_
    intro n
    change (4 * bound M n + 9) + (4 * bound M n + 9) ≤ 2 * (4 * bound M n + 9)
    omega
  · intro input σ _
    unfold readRep
    dsimp only
    rw [Function.update_self, Function.update_of_ne hout, Function.update_self]
    rfl
  · intro input σ t _ h0 h1
    dsimp only
    rw [Function.update_of_ne h1, Function.update_of_ne h0]
  · intro input σ _
    refine ⟨?_, 0, Nat.zero_le _, ?_⟩
    · dsimp only
      rw [Function.update_of_ne hout, Function.update_self]
      exact hM
    · dsimp only
      rw [Function.update_self]
      rfl

/-- A projection node is correct with constant zero. -/
theorem correct_proj {k n : ℕ} (i : Fin n) (c : Direction (.proj n i) → Σ i, Compiled k i)
    (h : ∀ b, (c b).1 = rc (.proj n i) b) (s : Direction (.proj n i) → List Bool → Σ i, RepSem i)
    (hs : ∀ b x, (s b x).1 = rc (.proj n i) b) :
    Correct (compileValue (.proj n i) c h)
      (fun x ↦ evalRepValue x (.proj n i) (fun b ↦ s b x) (hs · x)) 0 := by
  intro env out free hfree hadm M hM
  obtain ⟨_, _, _, hout, henv⟩ := hadm
  have h00 : env i 0 ≠ out 0 := henv i 0 0
  have h01 : env i 0 ≠ out 1 := henv i 0 1
  have h10 : env i 1 ≠ out 0 := henv i 1 0
  have h11 : env i 1 ≠ out 1 := henv i 1 1
  refine ⟨fun _ σ ↦ Function.update (Function.update σ (out 0) (σ (env i 0))) (out 1)
    (σ (env i 1)), ?_, ?_, ?_, ?_⟩
  · have h1 := Transforms.toIn_of (fun n ↦ copy_transforms (env i 0) (out 0) h00 (bound M n))
      (fun _ _ ↦ True) fun input σ hB _ ↦ hB.update (hB _)
    have h2 := Transforms.toIn_of (fun n ↦ copy_transforms (env i 1) (out 1) h11 (bound M n))
      (fun _ _ ↦ True) fun input σ hB _ ↦ hB.update (hB _)
    refine TransformsIn.congr (TransformsIn.mono_time
      ((h1.seq h2).mono_pre fun _ _ _ _ ↦ ⟨trivial, trivial⟩) ?_) ?_
    · intro n
      change (5 * bound M n + 12) + (5 * bound M n + 12) ≤ copyRegTime (bound M n)
      unfold copyRegTime
      omega
    · intro input σ _
      funext t
      change Function.update (Function.update σ (out 0) (σ (env i 0))) (out 1)
        (Function.update σ (out 0) (σ (env i 0)) (env i 1)) t = _
      rw [Function.update_of_ne h10]
  · intro input σ _
    unfold readRep
    dsimp only
    rw [Function.update_self, Function.update_of_ne hout, Function.update_self]
    rfl
  · intro input σ t _ h0 h1
    dsimp only
    rw [Function.update_of_ne h1, Function.update_of_ne h0]
  · intro input σ hwf
    obtain ⟨hw, l, hl, hc⟩ := hwf i
    refine ⟨?_, l, hl, ?_⟩
    · dsimp only
      rw [Function.update_of_ne hout, Function.update_self]
      exact hw
    · dsimp only
      rw [Function.update_self]
      exact hc

end

end Geb.SizeBounded.Logspace.Machine
