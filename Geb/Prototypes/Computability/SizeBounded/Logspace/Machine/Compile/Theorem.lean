/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile.Correct
import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile.Comp
import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile.Srn
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Correctness of the compilation

{lit}`LOf.correct` is the result the node lemmas are assembled into: the
compiled program of an expression of the successor-free subalgebra meets the
contract {name}`Geb.SizeBounded.Logspace.Machine.Correct` at the constant
{name}`Geb.SizeBounded.nsiConst` read off its syntax. At every admissible
allocation of registers and every word bound at least the expression's
constant, the program transforms valuations whose environment is well-formed
by a function that writes the expression's meaning on representations,
{name}`Geb.SizeBounded.Logspace.LOf.repSem`, into the output register, leaves
the other tapes below the first free one unchanged, keeps the output register
well-formed, and halts within the expression's step bound at the tape bound.

The induction is {name}`SlicePFunctor.W.induction` in the shape of the model
fold {name}`Geb.SizeBounded.Logspace.evalRep`, carrying the hypothesis that
the tree contains no successor node: at a node the compilation and the
interpretation both reduce to their algebras applied to the children's folds,
so the two arities agree by {lit}`rfl`, and {lit}`correct_compileValue`
dispatches to the lemma for the node's shape, the successor's case being
excluded by the hypothesis.

{lit}`LOf.correct` is the compiler's half of the soundness of
{cite}`Kristiansen2005` Theorem 4.1: the compiled program computes the
expression's meaning on the representation that keeps only a bounded word and
an end segment length.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's {name}`Turing.Cfg.inputSymbol`.

# Main statements

* {lit}`correct_compileValue` — one successor-free node meets the contract
  when its children do.
* {lit}`correct_compile` — every successor-free expression's compilation
  meets the contract, as an indexed pair.
* {lit}`LOf.correct` — the compiled program of an expression of the
  subalgebra computes its meaning on representations.

# References

* {cite}`Kristiansen2005`

# Tags

Turing machine, compilation, correctness, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Geb.SizeBounded (Shape Direction rc nsiValue nsiConst S sig)
open Geb.SizeBounded.Logspace (RepSem evalRepValue evalRep fst_evalRep sbsFreeValue sbsFree LOf
  finAll finAll_eq_true_iff)

public section

/-- One successor-free node's program is correct when its children's are. -/
theorem correct_compileValue {k : ℕ} (a : Shape) (c : Direction a → Σ i, Compiled k i)
    (h : ∀ b, (c b).1 = rc a b) (s : Direction a → List Bool → Σ i, RepSem i)
    (hs : ∀ b x, (s b x).1 = rc a b) (kb : Direction a → Bool) (hkb : sbsFreeValue a kb = true)
    (K : Direction a → ℕ) (hk : ∀ b, kb b = true → CorrectSigma (c b) (s b) (K b)) :
    Correct (compileValue a c h) (fun x ↦ evalRepValue x a (fun b ↦ s b x) (hs · x))
      (nsiValue a K) := by
  cases a with
  | const n w => exact correct_const w c h s hs
  | proj n i => exact correct_proj i c h s hs
  | sbs b => exact absurd hkb Bool.false_ne_true
  | comp n m =>
    change (kb (.inl ()) && finAll m fun i ↦ kb (.inr i)) = true at hkb
    rw [Bool.and_eq_true, finAll_eq_true_iff] at hkb
    exact correct_comp c h s hs K fun b ↦ hk b (match b with
      | .inl () => hkb.1
      | .inr i => hkb.2 i)
  | srn a b j =>
    change (finAll b (fun l ↦ kb (.inl l)) &&
      (finAll b (fun l ↦ kb (.inr (.inl l))) && finAll b fun l ↦ kb (.inr (.inr l)))) = true
      at hkb
    rw [Bool.and_eq_true, Bool.and_eq_true, finAll_eq_true_iff, finAll_eq_true_iff,
      finAll_eq_true_iff] at hkb
    exact correct_srn j c h s hs K fun d ↦ hk d (match d with
      | .inl l => hkb.1 l
      | .inr (.inl l) => hkb.2.1 l
      | .inr (.inr l) => hkb.2.2 l)

/-- Every successor-free expression's program is correct, with the constant
{name}`Geb.SizeBounded.nsiConst` read off its syntax. -/
theorem correct_compile (k : ℕ) : ∀ e : S, sbsFree e.1 = true →
    CorrectSigma (compile k e) (fun w ↦ evalRep w e) (nsiConst e.1) :=
  SlicePFunctor.W.induction fun x ih hfree ↦
    ⟨fun _ ↦ rfl, correct_compileValue x.1.1 (fun b ↦ compile k (x.1.2 b)) _
      (fun b w ↦ evalRep w (x.1.2 b))
      (fun b w ↦ (fst_evalRep w (x.1.2 b)).trans
        ((sig.toSliceDomPFunctor.compatible_iff _ x.1.1 x.1.2).mp x.2 b))
      (fun b ↦ sbsFree (x.1.2 b).1) hfree
      (fun b ↦ nsiConst (x.1.2 b).1) ih⟩

/-- The compiled program of an expression of the subalgebra computes its
meaning on representations. -/
theorem LOf.correct (k : ℕ) {n : ℕ} (e : LOf n) :
    Correct (LOf.compile k e) (fun w ↦ e.repSem w) (nsiConst e.1.1.1) :=
  (correct_compile k e.1.1 e.2).atArity ((fst_compile k e.1.1).trans e.1.2)
    fun w ↦ (fst_evalRep w e.1.1).trans e.1.2

end

end Geb.SizeBounded.Logspace.Machine
