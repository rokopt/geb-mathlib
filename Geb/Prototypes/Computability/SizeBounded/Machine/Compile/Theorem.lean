/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Correct
import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Comp
import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Srn

set_option doc.verso true

/-!
# Correctness of the compilation

{lit}`SOf.correct` is the result the node lemmas are assembled into: the
compiled program of an expression of a given arity meets the contract
{name}`Geb.SizeBounded.Machine.Correct` at the constant
{name}`Geb.SizeBounded.nsiConst` and the bound
{name}`Geb.SizeBounded.Machine.stepBound` read off its syntax. At every
admissible allocation of registers and every length bound at least the
expression's constant, the program transforms valuations by a function that
writes the expression's meaning into the output register, leaves the other
registers below the first free one unchanged, preserves the length bound, and
halts within the expression's step bound at that length bound.

The induction is {name}`SlicePFunctor.W.induction` in the shape the model fold
{name}`Geb.SizeBounded.nsi_eval` takes: at a node the compilation and the
interpretation both reduce to their algebras applied to the children's folds, so
the two arities agree by {lit}`rfl`, and {lit}`correct_compileValue` dispatches
to the lemma for the node's shape.

The forms of the two bounds as functions of the arguments' lengths — the length
bound linear and the step bound polynomial — are established elsewhere.

# Main statements

* {lit}`correct_compileValue` — one node meets the contract when its children
  do.
* {lit}`correct_compile` — every expression's compilation meets the contract, as
  an indexed pair.
* {lit}`SOf.correct` — the compiled program of an expression of a given arity
  computes its meaning.

# Tags

Turing machine, compilation, correctness, size-bounded
-/

namespace Geb.SizeBounded.Machine

open Cobham (Sem)
open Geb.SizeBounded (Shape Direction rc evalValue nsiValue nsiConst eval fst_eval S SOf)

public section

/-- One node's program is correct when its children's are. -/
theorem correct_compileValue {k : ℕ} (a : Shape) (c : Direction a → Σ i, Compiled k i)
    (h : ∀ b, (c b).1 = rc a b) (s : Direction a → Σ i, Sem i) (hs : ∀ b, (s b).1 = rc a b)
    (K : Direction a → ℕ) (Tf : Direction a → ℕ → ℕ)
    (hk : ∀ b, CorrectSigma (c b) (s b) (K b) (Tf b)) :
    Correct (compileValue a c h) (evalValue a s hs) (nsiValue a K) (stepValue a Tf) := by
  cases a with
  | const n w => exact correct_const w c h s hs K Tf
  | proj n i => exact correct_proj i c h s hs K Tf
  | sbs b => exact correct_sbs b c h s hs K Tf
  | comp n m => exact correct_comp c h s hs K Tf hk
  | srn a b j => exact correct_srn j c h s hs K Tf hk

/-- Every expression's program is correct, with the constant {name}`nsiConst` and
the bound {name}`stepBound` read off its syntax. -/
theorem correct_compile (k : ℕ) : ∀ e : S,
    CorrectSigma (compile k e) (eval e) (nsiConst e.1) (stepBound e.1) :=
  SlicePFunctor.W.induction fun x ih ↦
    ⟨rfl, correct_compileValue x.1.1 (fun b ↦ compile k (x.1.2 b)) _ (fun b ↦ eval (x.1.2 b)) _
      (fun b ↦ nsiConst (x.1.2 b).1) (fun b ↦ stepBound (x.1.2 b).1) ih⟩

/-- The compiled program of an expression of a given arity computes its meaning. -/
theorem SOf.correct (k : ℕ) {n : ℕ} (e : SOf n) :
    Correct (SOf.compile k e) e.sem (nsiConst e.1.1) (stepBound e.1.1) := by
  obtain ⟨h, hc⟩ := correct_compile k e.1
  have hg := Correct.transport ((fst_eval e.1).trans e.2) hc
  rw [transportP_transportP] at hg
  exact hg

end

end Geb.SizeBounded.Machine
