/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Wrapper
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Polynomial time and logarithmic space

The meaning of an expression of the successor-free subalgebra of one argument
is {name}`Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength` with a
polynomial time bound and a space bound linear in the input's binary size:
the machine {name}`Geb.SizeBounded.Logspace.Machine.machine` of the
expression, over {lit}`Bool` and the finite state type
{name}`Geb.SizeBounded.Logspace.Machine.State`, computes the meaning within
{name}`Geb.SizeBounded.Logspace.Machine.time`, which
{lit}`isPolyBounded_time` bounds by a polynomial in the input's length, and
its tapes hold at most the tape bound at the expression's constant, which is
that constant plus the input's binary size plus one.

{lit}`computableInTimeAndSpace_sem` is the soundness half of
{cite}`Kristiansen2005` Theorem 4.1 for the algebra {lit}`[I, C_W; comp, simn]`:
every function it defines is computable in logarithmic space, and so in
polynomial time. The proof follows the paper's: a value is a bounded word
before an end segment of the input, so a register holds the word and the end
segment's length, and simultaneous recursion on notation over such a value
runs the end segment's lengths up by a counter and then the word's bits.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statement mentions {name}`Turing.MultiTapeTM.ComputableInTimeAndSpace`, which
depends on {lit}`Classical.choice` through Cslib's
{name}`Turing.Cfg.inputSymbol`.

# Main statements

* {lit}`isPolyBounded_time` — the machine's step count is polynomially
  bounded in the input's length.
* {lit}`computableInTimeAndSpace_sem` — the meaning of a unary expression of
  the subalgebra is computable in polynomial time and logarithmic space.

# References

* {cite}`Kristiansen2005`

# Tags

Turing machine, polynomial time, logarithmic space, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Turing MultiTapeTM
open Geb.SizeBounded (IsPolyBounded isPolyBounded_add isPolyBounded_mul isPolyBounded_const
  isPolyBounded_id)
open Geb.SizeBounded.Logspace (LOf)

public section

/-- The machine's step count is polynomially bounded in the input's length. -/
theorem isPolyBounded_time (e : LOf 1) : IsPolyBounded (time e) := by
  have hB := isPolyBounded_bound (wordBound e)
  have hcount : IsPolyBounded fun n ↦ countInputTime (bound (wordBound e) n) n :=
    isPolyBounded_add (isPolyBounded_add (isPolyBounded_add
      (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const 4) hB) (isPolyBounded_const 9))
      (isPolyBounded_add (isPolyBounded_mul isPolyBounded_id
        (isPolyBounded_add (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const 2) hB)
          (isPolyBounded_const 6)) (isPolyBounded_const 1))) (isPolyBounded_const 1)))
      (isPolyBounded_const 1)) (isPolyBounded_add isPolyBounded_id (isPolyBounded_const 1))
  have hemit : IsPolyBounded fun n ↦ emitSuffixTime (bound (wordBound e) n) n :=
    isPolyBounded_add (isPolyBounded_add (isPolyBounded_add (isPolyBounded_add
      (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const 5) hB) (isPolyBounded_const 12))
      (isPolyBounded_const 1)) (isPolyBounded_add isPolyBounded_id (isPolyBounded_const 1)))
      (isPolyBounded_add (isPolyBounded_mul isPolyBounded_id
        (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const 2) hB) (isPolyBounded_const 8)))
        (isPolyBounded_const 1)))
      (isPolyBounded_add isPolyBounded_id (isPolyBounded_const 1))
  exact isPolyBounded_add (isPolyBounded_add (isPolyBounded_add
    (isPolyBounded_add hcount (isPolyBounded_timeBound (wordBound e) e.1.1.1))
    (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const 2) hB) (isPolyBounded_const 3)))
    (isPolyBounded_const 1)) hemit

/-- The meaning of a unary expression of the subalgebra is computable by a
multi-tape machine in polynomial time and logarithmic space: the soundness
half of {cite}`Kristiansen2005` Theorem 4.1, by the compiled program of the
expression on the representation of its values. -/
theorem computableInTimeAndSpace_sem (e : LOf 1) :
    ∃ c d : ℕ, ComputableInTimeAndSpaceOfLength (fun w ↦ e.sem ![w]) (.refl _) (.refl _)
      (fun n ↦ c * (n + 1) ^ d) (fun n ↦ c * (Nat.size n + 1)) := by
  obtain ⟨c₁, d, hd⟩ := isPolyBounded_time e
  refine ⟨max c₁ (tapes e * (wordBound e + 3)), d, tapes e, State e, inferInstance, machine e,
    fun w ↦ ?_⟩
  obtain ⟨cfg', t', ht', h⟩ := machine_emits e w
  refine ⟨t', ?_, (machine e).spaceUsed ((machine e).initCfg w) t', ?_, ?_, ?_, rfl⟩
  · exact le_trans ht' (le_trans (hd w.length) (Nat.mul_le_mul_right _ (Nat.le_max_left _ _)))
  · have hlin : bound (wordBound e) w.length + 2 ≤
        (wordBound e + 3) * (Nat.size w.length + 1) := by
      have hs : Nat.size w.length ≤ (wordBound e + 3) * Nat.size w.length :=
        Nat.le_mul_of_pos_left _ (by omega)
      unfold bound
      rw [Nat.mul_succ]
      generalize (wordBound e + 3) * Nat.size w.length = m at hs ⊢
      omega
    refine le_trans h.spaceUsed_le (le_trans (Nat.mul_le_mul_left _ hlin) ?_)
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.le_max_right _ _)
  · change ((machine e).runFrom ((machine e).initCfg w) t').state = none
    rw [h.runFrom_eq]
    exact h.halted
  · change ((machine e).runFrom ((machine e).initCfg w) t').output = e.sem ![w]
    rw [initCfg_runFrom_output]
    exact h.output

end

end Geb.SizeBounded.Logspace.Machine
