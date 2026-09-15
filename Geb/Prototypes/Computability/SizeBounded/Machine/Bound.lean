/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Basic
public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Bound
public import Geb.Prototypes.Computability.SizeBounded.Cost

set_option doc.verso true in
/-!
# The register need and the polynomial step bound

The two resources the compilation spends, read off an expression's syntax.
{lit}`regsBound` folds {name}`Geb.SizeBounded.Machine.regsValue` over the tree,
and {lit}`regs_compile` identifies the result with the register need of the
compiled program, at every number of registers; {lit}`SOf.regs` states that at
a given arity. {lit}`isPolyBounded_stepBound` proves
{name}`Geb.SizeBounded.Machine.stepBound` bounded by a polynomial in the length
bound, node by node from the closure lemmas of
{name}`Geb.SizeBounded.IsPolyBounded`: a base form's bound is affine, a
substitution's and a recursion's are sums and products of its children's with
affine functions and constants.

# Main definitions

* {lit}`regsBound` — the register need of an expression, by the fold.

# Main statements

* {lit}`regs_compileValue`, {lit}`regs_compile`, {lit}`SOf.regs` — the compiled
  program's register need is the syntactic one.
* {lit}`isPolyBounded_stepValue`, {lit}`isPolyBounded_stepBound` — every
  expression's step bound is polynomially bounded.

# Tags

Turing machine, register allocation, step bound, polynomial time, size-bounded
-/

set_option doc.verso true

namespace Geb.SizeBounded.Machine

open Geb.SizeBounded (Shape Direction rc sig S SOf IsPolyBounded isPolyBounded_add
  isPolyBounded_mul isPolyBounded_const isPolyBounded_id isPolyBounded_max isPolyBounded_finMax
  isPolyBounded_linear)

public section

/-- The register need of an expression, read off its syntax by folding
{name}`regsValue` over the tree. -/
@[expose] def regsBound : sig.toPFunctor.W → ℕ := WType.elim ℕ fun x ↦ regsValue x.1 x.2

/-- One node's register need is {name}`regsValue` of its children's. -/
theorem regs_compileValue {k : ℕ} (a : Shape) (c : Direction a → Σ i, Compiled k i)
    (h : ∀ b, (c b).1 = rc a b) :
    (compileValue a c h).regs = regsValue a fun d ↦ (c d).2.regs := by
  cases a <;> rfl

/-- The compiled program's register need is the syntactic one, at every number
of registers. -/
theorem regs_compile (k : ℕ) : ∀ e : S, (compile k e).2.regs = regsBound e.1 :=
  SlicePFunctor.W.induction fun x ih ↦
    (regs_compileValue x.1.1 (fun d ↦ compile k (x.1.2 d)) _).trans
      (congrArg (regsValue x.1.1) (funext ih))

/-- The register need of an expression of a given arity. -/
theorem SOf.regs (k : ℕ) {n : ℕ} (e : SOf n) : (SOf.compile k e).regs = regsBound e.1.1 := by
  change (transportP _ (Machine.compile k e.1).2).regs = _
  rw [regs_transportP, regs_compile]

/-- One node's step bound is polynomially bounded when its children's are. -/
theorem isPolyBounded_stepValue (a : Shape) (t : Direction a → ℕ → ℕ)
    (ht : ∀ d, IsPolyBounded (t d)) : IsPolyBounded (stepValue a t) := by
  cases a with
  | const n w => exact isPolyBounded_linear 4 9
  | proj n i => exact isPolyBounded_linear 5 12
  | sbs b => exact isPolyBounded_linear 7 16
  | comp n m =>
    exact isPolyBounded_add (isPolyBounded_add
      (isPolyBounded_mul (isPolyBounded_const m) (isPolyBounded_finMax m _ fun i ↦ ht (.inr i)))
      (isPolyBounded_const 1)) (ht (.inl ()))
  | srn a b j =>
    have hbody : IsPolyBounded fun B ↦ b * max (finMax b fun l ↦ t (.inr (.inl l)) B)
        (finMax b fun l ↦ t (.inr (.inr l)) B) + 1 + (b * (5 * B + 12) + 1) + (7 * B + 16)
        + (5 * B + 12) :=
      isPolyBounded_add (isPolyBounded_add (isPolyBounded_add (isPolyBounded_add
        (isPolyBounded_mul (isPolyBounded_const b)
          (isPolyBounded_max (isPolyBounded_finMax b _ fun l ↦ ht (.inr (.inl l)))
            (isPolyBounded_finMax b _ fun l ↦ ht (.inr (.inr l)))))
        (isPolyBounded_const 1))
        (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const b) (isPolyBounded_linear 5 12))
          (isPolyBounded_const 1)))
        (isPolyBounded_linear 7 16)) (isPolyBounded_linear 5 12)
    exact isPolyBounded_add (isPolyBounded_add (isPolyBounded_add (isPolyBounded_add
      (isPolyBounded_linear 5 12) (isPolyBounded_linear 4 9))
      (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const b)
        (isPolyBounded_finMax b _ fun l ↦ ht (.inl l))) (isPolyBounded_const 1)))
      (isPolyBounded_add (isPolyBounded_mul isPolyBounded_id (isPolyBounded_add (isPolyBounded_add
        hbody (isPolyBounded_mul (isPolyBounded_const 2) isPolyBounded_id))
        (isPolyBounded_const 6))) (isPolyBounded_const 3)))
      (isPolyBounded_linear 5 12)

/-- Every expression's step bound is polynomially bounded. -/
theorem isPolyBounded_stepBound : ∀ w : sig.toPFunctor.W, IsPolyBounded (stepBound w) :=
  WType.rec (motive := fun w ↦ IsPolyBounded (stepBound w)) fun a _ ih ↦
    isPolyBounded_stepValue a _ ih

end

end Geb.SizeBounded.Machine
