/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile.Basic
public import Geb.Prototypes.Computability.SizeBounded.Cost

set_option doc.verso true in
/-!
# The resources of the compilation, read off the syntax

The two resources a compiled expression spends are its fields
{lit}`Compiled.regs` and {lit}`Compiled.time`; {lit}`regsBound` and
{lit}`timeBound` fold {name}`Geb.SizeBounded.Logspace.Machine.regsValue` and
{name}`Geb.SizeBounded.Logspace.Machine.timeValue` over the tree and are
identified with those fields, so that both are functions of the syntax alone.
At a fixed word bound the step bound is a polynomial in the input's length:
{lit}`isPolyBounded_timeBound`, node by node from the closure lemmas of
{name}`Geb.SizeBounded.IsPolyBounded`, the tape bound
{name}`Geb.SizeBounded.Logspace.Machine.bound` being linear in the input's
binary size and so in its length.

# Main definitions

* {lit}`regsBound`, {lit}`timeBound` — the tape need and the step bound of
  an expression, folded over its tree.

# Main statements

* {lit}`regs_compile`, {lit}`time_compile`, {lit}`LOf.regs`,
  {lit}`LOf.time` — the compiled program's need and step bound are the
  syntactic ones.
* {lit}`isPolyBounded_bound`, {lit}`isPolyBounded_timeValue`,
  {lit}`isPolyBounded_timeBound` — the tape bound and the step bound at a
  fixed word bound are polynomially bounded in the input's length.

# Tags

Turing machine, register allocation, step bound, polynomial time, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Geb.SizeBounded (Shape Direction rc sig S IsPolyBounded isPolyBounded_add isPolyBounded_mul
  isPolyBounded_const isPolyBounded_id isPolyBounded_max isPolyBounded_finMax
  isPolyBounded_of_le)
open Geb.SizeBounded.Logspace (LOf)

public section

/-- The tape need of an expression, read off its syntax by folding
{name}`regsValue` over the tree. -/
@[expose] def regsBound : sig.toPFunctor.W → ℕ := WType.elim ℕ fun x ↦ regsValue x.1 x.2

/-- The step bound of an expression at a word bound and an input length, read
off its syntax by folding {name}`timeValue` over the tree. -/
@[expose] def timeBound : sig.toPFunctor.W → ℕ → ℕ → ℕ :=
  WType.elim (ℕ → ℕ → ℕ) fun x ↦ timeValue x.1 x.2

/-- One node's tape need is {name}`regsValue` of its children's. -/
theorem regs_compileValue {k : ℕ} (a : Shape) (c : Direction a → Σ i, Compiled k i)
    (h : ∀ b, (c b).1 = rc a b) :
    (compileValue a c h).regs = regsValue a fun d ↦ (c d).2.regs := by
  cases a <;> rfl

/-- One node's step bound is {name}`timeValue` of its children's. -/
theorem time_compileValue {k : ℕ} (a : Shape) (c : Direction a → Σ i, Compiled k i)
    (h : ∀ b, (c b).1 = rc a b) :
    (compileValue a c h).time = timeValue a fun d ↦ (c d).2.time := by
  cases a <;> rfl

/-- The compiled program's tape need is the syntactic one. -/
theorem regs_compile (k : ℕ) : ∀ e : S, (compile k e).2.regs = regsBound e.1 :=
  SlicePFunctor.W.induction fun x ih ↦
    (regs_compileValue x.1.1 (fun d ↦ compile k (x.1.2 d)) _).trans
      (congrArg (regsValue x.1.1) (funext ih))

/-- The compiled program's step bound is the syntactic one. -/
theorem time_compile (k : ℕ) : ∀ e : S, (compile k e).2.time = timeBound e.1 :=
  SlicePFunctor.W.induction fun x ih ↦
    (time_compileValue x.1.1 (fun d ↦ compile k (x.1.2 d)) _).trans
      (congrArg (timeValue x.1.1) (funext ih))

/-- The tape need of an expression of the subalgebra. -/
theorem LOf.regs (k : ℕ) {n : ℕ} (e : LOf n) : (LOf.compile k e).regs = regsBound e.1.1.1 := by
  change (transportP _ (Machine.compile k e.1.1).2).regs = _
  rw [regs_transportP, regs_compile]

/-- The step bound of an expression of the subalgebra. -/
theorem LOf.time (k : ℕ) {n : ℕ} (e : LOf n) : (LOf.compile k e).time = timeBound e.1.1.1 := by
  change (transportP _ (Machine.compile k e.1.1).2).time = _
  rw [time_transportP, time_compile]

/-- The binary size is polynomially bounded. -/
theorem isPolyBounded_size : IsPolyBounded Nat.size :=
  isPolyBounded_of_le size_le_self isPolyBounded_id

/-- The tape bound at a fixed word bound is polynomially bounded in the input's
length. -/
theorem isPolyBounded_bound (M : ℕ) : IsPolyBounded (bound M) :=
  isPolyBounded_add (isPolyBounded_add (isPolyBounded_const M) isPolyBounded_size)
    (isPolyBounded_const 1)

/-- One node's step bound at a fixed word bound is polynomially bounded in the
input's length when its children's are. -/
theorem isPolyBounded_timeValue (M : ℕ) (a : Shape) (t : Direction a → ℕ → ℕ → ℕ)
    (ht : ∀ d, IsPolyBounded (t d M)) : IsPolyBounded (timeValue a t M) := by
  have hB := isPolyBounded_bound M
  have hC : IsPolyBounded fun n ↦ 5 * bound M n + 12 :=
    isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const 5) hB) (isPolyBounded_const 12)
  have hK : IsPolyBounded fun n ↦ 4 * bound M n + 9 :=
    isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const 4) hB) (isPolyBounded_const 9)
  have hcopy : IsPolyBounded fun n ↦ copyRegTime (bound M n) :=
    isPolyBounded_mul (isPolyBounded_const 2) hC
  cases a with
  | const n w => exact isPolyBounded_mul (isPolyBounded_const 2) hK
  | proj n i => exact hcopy
  | sbs b => exact isPolyBounded_const 1
  | comp n m =>
    exact isPolyBounded_add (isPolyBounded_add
      (isPolyBounded_mul (isPolyBounded_const m) (isPolyBounded_finMax m _ fun i ↦ ht (.inr i)))
      (isPolyBounded_const 1)) (ht (.inl ()))
  | srn a b j =>
    have hsteps : IsPolyBounded fun n ↦ max (finMax b fun l ↦ t (.inr (.inl l)) M n)
        (finMax b fun l ↦ t (.inr (.inr l)) M n) :=
      isPolyBounded_max (isPolyBounded_finMax b _ fun l ↦ ht (.inr (.inl l)))
        (isPolyBounded_finMax b _ fun l ↦ ht (.inr (.inr l)))
    have hread : IsPolyBounded fun n ↦ readInputTime (bound M n) n :=
      isPolyBounded_add (isPolyBounded_add (isPolyBounded_add (isPolyBounded_add
        (isPolyBounded_add (isPolyBounded_add (isPolyBounded_add hC (isPolyBounded_const 1))
          (isPolyBounded_add isPolyBounded_id (isPolyBounded_const 1)))
          (isPolyBounded_add (isPolyBounded_mul isPolyBounded_id
            (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const 2) hB)
              (isPolyBounded_const 8))) (isPolyBounded_const 1)))
          (isPolyBounded_const 1)) hK) (isPolyBounded_const 1))
        (isPolyBounded_add isPolyBounded_id (isPolyBounded_const 1))
    have hbody1 : IsPolyBounded fun n ↦ body1Time b (bound M n) n :=
      isPolyBounded_add (isPolyBounded_add (isPolyBounded_add
        (isPolyBounded_add hread (isPolyBounded_const 1))
        (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const b) hcopy)
          (isPolyBounded_const 1)))
        (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const 2) hB) (isPolyBounded_const 4)))
        (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const 2) hB) (isPolyBounded_const 6))
    have hbody2 : IsPolyBounded fun n ↦ body2Time b (bound M n) :=
      isPolyBounded_add (isPolyBounded_add (isPolyBounded_add
        (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const 4) hB) (isPolyBounded_const 12))
        (isPolyBounded_const 1))
        (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const b) hcopy)
          (isPolyBounded_const 1)))
        (isPolyBounded_add (isPolyBounded_const 1)
          (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const 2) hB)
            (isPolyBounded_const 6)))
    exact isPolyBounded_add (isPolyBounded_add (isPolyBounded_add (isPolyBounded_add
      (isPolyBounded_add (isPolyBounded_add
        (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const b)
          (isPolyBounded_finMax b _ fun l ↦ ht (.inl l))) (isPolyBounded_const 1))
        (isPolyBounded_mul (isPolyBounded_const 2) hK)) hC)
      (isPolyBounded_add (isPolyBounded_mul isPolyBounded_id (isPolyBounded_add (isPolyBounded_add
        (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const b) hsteps)
          (isPolyBounded_const 1)) hbody1) (isPolyBounded_const 1))) (isPolyBounded_const 1)))
      hC)
      (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const M) (isPolyBounded_add
        (isPolyBounded_add (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const b) hsteps)
          (isPolyBounded_const 1)) hbody2) (isPolyBounded_const 1))) (isPolyBounded_const 1)))
      hcopy

/-- Every expression's step bound at a fixed word bound is polynomially bounded
in the input's length. -/
theorem isPolyBounded_timeBound (M : ℕ) :
    ∀ w : sig.toPFunctor.W, IsPolyBounded (timeBound w M) :=
  WType.rec (motive := fun w ↦ IsPolyBounded (timeBound w M)) fun a _ ih ↦
    isPolyBounded_timeValue M a _ ih

end

end Geb.SizeBounded.Logspace.Machine
