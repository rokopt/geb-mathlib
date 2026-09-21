/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Machine.Realizer.Initial

set_option doc.verso true in
/-!
# Compositional realization of Logs expressions

A realized expression accepts generators for its virtual arguments over any
protected environment. A common polynomial length bound relates those arguments
to the physical input. The resulting generator preserves that environment and
uses logarithmic work space in the original input length.

## Main definitions

* {lit}`Expr.Realized` states this substitution property.

## Main statements

* {lit}`Expr.Realized.initial` realizes every initial expression.
* {lit}`Expr.Realized.comp` closes realization under normal composition.
* {lit}`Expr.Realized.logTransition` realizes the safe-to-normal transition.
* {lit}`Expr.Realized.computes` supplies simultaneous time and space bounds
  for a realized expression with one normal input and no safe inputs.

## Implementation notes

Finite families of generator witnesses are assembled by a natural-number
recursor. The executable programs use no choice. The machine contracts inherit
{lit}`Classical.choice` from CSLib.

## Tags

logspace, function algebra, composition, Turing machine
-/

set_option doc.verso true

namespace Geb.Oitavem

open Turing MultiTapeTM
open Geb.SizeBounded
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace.Machine
open Machine

public section

/-- A finite family of witnesses can be assembled without an axiom of choice. -/
theorem nonempty_fin_family {n : ℕ} {X : Fin n → Type 1}
    (h : ∀ i, Nonempty (X i)) : Nonempty ((i : Fin n) → X i) := by
  refine Nat.rec (motive := fun n ↦ ∀ X : Fin n → Type 1,
    (∀ i, Nonempty (X i)) → Nonempty ((i : Fin n) → X i)) ?_ ?_ n X h
  · intro X _
    exact ⟨fun i ↦ i.elim0⟩
  · intro n ih X h
    obtain ⟨x⟩ := h 0
    obtain ⟨xs⟩ := ih (fun i ↦ X i.succ) (fun i ↦ h i.succ)
    exact ⟨Fin.cases x xs⟩

/-- An expression can substitute polynomially bounded virtual inputs over any
protected environment, producing a restoring logarithmic-space generator. -/
@[expose] def Expr.Realized {n s : ℕ} (e : Expr n s) : Prop :=
  ∀ (m : ℕ) (Pre : List Bool → (Fin m → List Bool) → Prop)
    (X : Fin n → List Bool → (Fin m → List Bool) → List Bool)
    (Y : Fin s → List Bool → (Fin m → List Bool) → List Bool),
    ((i : Fin n) → Generator m Pre (X i)) → ((i : Fin s) → Generator m Pre (Y i)) →
    ∀ N : ℕ → ℕ, IsPolyBounded N →
    (∀ input σ, Pre input σ → ∀ i, (X i input σ).length ≤ N input.length) →
    (∀ input σ, Pre input σ → ∀ i, (Y i input σ).length ≤ N input.length) →
    Nonempty (Generator m Pre
      (fun input σ ↦ e.eval (fun i ↦ X i input σ) (fun i ↦ Y i input σ)))

/-- All initial expressions admit generator substitution. -/
theorem Expr.Realized.initial (p : Initial) : (Expr.initial p).Realized := by
  intro m Pre X Y G _ N hN hx _
  exact p.realize G N hN hx

/-- Normal composition reuses the child generators and their syntax-derived
polynomial output bounds, measured against the same physical input. -/
theorem Expr.Realized.comp {n k : ℕ} {safe : Bool}
    {h : Expr k safe.toNat} {g : Fin k → Expr n 0}
    (hh : h.Realized) (hg : ∀ i, (g i).Realized) : (Expr.comp h g).Realized := by
  intro m Pre X Y GX GY N hN hx hy
  have hgs (i : Fin k) : Nonempty (Generator m Pre
      (fun input σ ↦ (g i).eval (fun j ↦ X j input σ) Fin.elim0)) :=
    hg i m Pre X (fun j _ _ ↦ j.elim0) GX (fun j ↦ j.elim0) N hN hx
      (fun _ _ _ j ↦ j.elim0)
  obtain ⟨G⟩ := nonempty_fin_family hgs
  let M (n : ℕ) := max (N n) (finMax k (fun i ↦ lengthPoly (g i).1.1 (N n)))
  have hM : IsPolyBounded M := isPolyBounded_max hN
    (isPolyBounded_finMax k _ (fun i ↦ isPolyBounded_comp (lengthPoly_isPolyBounded _) hN))
  exact hh m Pre _ Y G GY M hM
    (fun input σ hp i ↦ ((g i).length_le _ _ _ (hx input σ hp)).trans
      ((le_finMax k (fun i ↦ lengthPoly (g i).1.1 (N input.length)) i).trans
        (Nat.le_max_right _ _)))
    (fun input σ hp i ↦ (hy input σ hp i).trans (Nat.le_max_left _ _))

/-- The offset expression is realized using only initial functions and composition. -/
theorem Expr.Realized.transitionOffset : Expr.transitionOffset.Realized := by
  unfold Expr.transitionOffset
  dsimp only
  repeat' first
  | apply Expr.Realized.initial
  | apply Expr.Realized.comp
  | intro i; fin_cases i

/-- Treating the safe input as an additional normal input realizes the derived
log-transition expression whenever its child is realized. -/
theorem Expr.Realized.logTransitionNormal {n : ℕ} {h : Expr (n + 1) 0}
    (hh : h.Realized) : (Expr.logTransitionNormal h).Realized := by
  unfold Expr.logTransitionNormal
  apply Expr.Realized.comp hh
  refine Fin.cases ?_ (fun _ ↦ Expr.Realized.initial _)
  apply Expr.Realized.comp Expr.Realized.transitionOffset
  intro i
  fin_cases i <;> exact Expr.Realized.initial _

/-- Log-transition is realized through its derived normal expression. Its safe
argument is already supplied with a polynomial bound in the physical input. -/
theorem Expr.Realized.logTransition {n : ℕ} {h : Expr (n + 1) 0}
    (hh : h.Realized) : (Expr.logTransition h).Realized := by
  intro m Pre X Y GX GY N hN hx hy
  obtain ⟨G⟩ := hh.logTransitionNormal m Pre (Fin.cons (Y 0) X)
    (fun i _ _ ↦ i.elim0) (Fin.cases (GY 0) GX) (fun i ↦ i.elim0) N hN
    (fun input σ hp ↦ Fin.cases (hy input σ hp 0) (hx input σ hp))
    (fun _ _ _ i ↦ i.elim0)
  refine ⟨G.congr ?_⟩
  intro input σ _
  have hcons : (fun i : Fin (n + 3) ↦
      Fin.cons (α := fun _ ↦ List Bool → (Fin m → List Bool) → List Bool)
        (Y 0) X i input σ) =
      Fin.cons (Y 0 input σ) (fun i ↦ X i input σ) := by
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  rw [hcons, Expr.eval_logTransitionNormal]
  rfl

/-- A realized unary expression has a finite machine with simultaneous polynomial
time and logarithmic space in the original input length. -/
theorem Expr.Realized.computes {e : Expr 1 0} (he : e.Realized) :
    ∃ C d : ℕ, ComputableInTimeAndSpaceOfLength (fun w ↦ e.eval ![w] Fin.elim0)
      (.refl _) (.refl _) (fun n ↦ C * (n + 1) ^ d) (fun n ↦ C * (n.size + 1)) := by
  obtain ⟨G⟩ := he 0 (fun _ _ ↦ True) (fun _ input _ ↦ input) (fun i _ _ ↦ i.elim0)
    (fun _ ↦ Generator.input) (fun i ↦ i.elim0) id isPolyBounded_id
    (fun _ _ _ _ ↦ le_rfl) (fun _ _ _ i ↦ i.elim0)
  obtain ⟨C, d, hG⟩ := G.computes (fun _ ↦ trivial)
  refine ⟨C, d, G.tapes, StateOf (seq inBack G.program), ?_, seq inBack G.program, ?_⟩
  · let := Fintype.ofFinite G.State
    infer_instance
  · have hnil : (fun i : Fin 0 ↦ (i.elim0 : List Bool)) = Fin.elim0 :=
      funext (fun i ↦ i.elim0)
    simpa only [Matrix.cons_fin_one, hnil, Function.Embedding.refl_apply] using hG

end

end Geb.Oitavem
