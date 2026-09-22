/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Foundations.Data.PFunctor.Free
public import Geb.Prototypes.RoseTree.Spine
public import Mathlib.Control.Monad.Cont
public import Mathlib.Data.PFunctor.Univariate.M
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Definitions as terms and equation morphisms

A definition over an import interface is an element of the free monad of a polynomial
signature. A family of definitions is a Kleisli arrow from its exports to its imports;
linking is Kleisli composition. A recursive block instead has both imports and exports
available in its bodies. Its equations do not assert the existence of a solution.

An export interface can be the positions of a free-polynomial shape. These positions
are dependent paths to variable leaves, retaining the direction at each operation.
They do not address internal operation nodes or the nullary operations of the signature.

## Main definitions

* {lit}`Position` gives the variable positions of a free-polynomial shape.
* {lit}`Derived` specifies operations by terms in their argument positions.
* {lit}`link` substitutes definitions for imports.
* {lit}`eval` interprets a term in a polynomial algebra and an environment.
* {lit}`Block` and {lit}`IsSolution` separate equations from their interpretation.
* {lit}`Presented` selects a definition by a structural position in its block.
* {lit}`unfold` performs finitely many simultaneous substitutions of a block's equations.
* {lit}`ofCoalgebra` presents a polynomial coalgebra as a flat, guarded block.
* {lit}`encode` embeds effectively labelled, finitely branching terms into rose trees.

## Main statements

* {lit}`link_assoc` is associativity of linking.
* {lit}`eval_bind` states that interpretation commutes with substitution.
* {lit}`eval_unfold` states that every solution satisfies every finite unfolding.
* {lit}`coalgebra_solution_unique` identifies a flat block's M-type solution.
* {lit}`encode_injective` makes the term encoding faithful.

## Implementation notes

The constructions use Cslib's {name}`PFunctor.FreeM`. The executable fold is
{name}`PFunctor.FreeM.liftM` into {name}`Cont`, as in the bit-tree encoder.
The dependent recursor is used only to define position types and to prove propositions.
Finiteness and effective coding are additional conditions on a signature and its interfaces.

## References

* {cite}`GambinoKock2013`, Theorem 4.5, for free-polynomial shapes and positions.
* {cite}`MiliusMoss2009`, Sections 3 and 6, for equation morphisms and their solutions.

## Tags

definition, polynomial functor, free monad, substitution, equation morphism
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition

open PFunctor

variable {P Q : PFunctor.{0, 0}} {Γ Δ Θ E V : Type}

/-- A position is the unique position of a variable leaf, or a direction followed by
a position in that child. These are the directions of the free polynomial. -/
def Position (s : P.FreeM Unit) : Type :=
  FreeM.rec (fun _ ↦ Unit) (fun a _ ps ↦ (b : P.B a) × ps b) s

/-- The polynomial presentation of the free monad: terms with a single variable label,
and their variable positions. -/
def freePolynomial (P : PFunctor.{0, 0}) : PFunctor.{0, 0} :=
  ⟨P.FreeM Unit, Position⟩

/-- A derived operation assigns each operation of {lit}`Q` a {lit}`P`-term in its
argument positions. Variables may be repeated or unused. -/
abbrev Derived (P Q : PFunctor.{0, 0}) := (a : Q.A) → P.FreeM (Q.B a)

/-- Extend derived operations to all terms using the free monad's interpreter. -/
def expandOps (d : Derived P Q) : Q.FreeM Γ → P.FreeM Γ := FreeM.liftM d

/-- Expanding derived operations preserves substitution. -/
theorem expandOps_bind (d : Derived P Q) (t : Q.FreeM Γ) (σ : Γ → Q.FreeM Δ) :
    expandOps d (t >>= σ) = expandOps d t >>= fun x ↦ expandOps d (σ x) :=
  FreeM.liftM_bind d t σ

/-- Linking substitutes the supplied bodies for a family's imports. -/
def link (d : E → P.FreeM Γ) (σ : Γ → P.FreeM Δ) : E → P.FreeM Δ :=
  fun i ↦ (d i).bind σ

/-- Identity linking changes no body. -/
@[simp] theorem link_pure (d : E → P.FreeM Γ) : link d pure = d :=
  funext fun i ↦ FreeM.bind_pure (d i)

/-- Linking in stages agrees with composing the import substitutions first. -/
theorem link_assoc (d : E → P.FreeM Γ) (σ : Γ → P.FreeM Δ) (τ : Δ → P.FreeM Θ) :
    link (link d σ) τ = link d (link σ τ) :=
  funext fun i ↦ FreeM.bind_assoc (d i) σ τ

/-- Interpret operation nodes by an algebra and variable leaves by an environment. -/
def eval (alg : P.Obj V → V) (env : Γ → V) (t : P.FreeM Γ) : V :=
  (t.liftM (m := Cont V) fun a k ↦ alg (.mk a k)) env

/-- Evaluating a variable looks it up in the environment. -/
@[simp] theorem eval_pure (alg : P.Obj V → V) (env : Γ → V) (x : Γ) :
    eval alg env (pure x) = env x := rfl

/-- Evaluating an operation applies the algebra to the evaluated children. -/
theorem eval_liftBind (alg : P.Obj V → V) (env : Γ → V)
    (a : P.A) (ts : P.B a → P.FreeM Γ) :
    eval alg env (.liftBind a ts) = alg (.mk a fun b ↦ eval alg env (ts b)) := rfl

/-- Interpretation commutes with substitution. -/
theorem eval_bind (alg : P.Obj V → V) (env : Δ → V)
    (t : P.FreeM Γ) (σ : Γ → P.FreeM Δ) :
    eval alg env (t.bind σ) = eval alg (fun x ↦ eval alg env (σ x)) t := by
  refine FreeM.rec (motive := fun t ↦ eval alg env (t.bind σ) =
    eval alg (fun x ↦ eval alg env (σ x)) t) (fun _ ↦ rfl) ?_ t
  intro a ts ih
  exact congrArg (fun k ↦ alg (.mk a k)) (funext ih)

/-- A recursive equation morphism. Its export type may be {name}`Position` of a
chosen layout; each body refers to imports or to exports of this same block. -/
abbrev Block (P : PFunctor.{0, 0}) (Γ E : Type) := E → P.FreeM (Γ ⊕ E)

/-- A presented definition is an export layout, its equations, and a selected export.
The operation and layout signatures are parameters of the presentation. Finitary signatures
and effective label codes supply finite representations. -/
abbrev Presented (P L : PFunctor.{0, 0}) (Γ : Type) :=
  (s : L.FreeM Unit) × Block P Γ (Position s) × Position s

/-- One simultaneous unfolding preserves imports and replaces local references by bodies. -/
def expand (d : Block P Γ E) (t : P.FreeM (Γ ⊕ E)) : P.FreeM (Γ ⊕ E) :=
  t.bind (Sum.elim (fun x ↦ .pure (.inl x)) d)

/-- The original equations followed by the requested number of simultaneous unfoldings. -/
def unfold (d : Block P Γ E) : ℕ → Block P Γ E :=
  Nat.rec d fun _ ds i ↦ expand d (ds i)

/-- Unfold the selected export of a presented definition. -/
def unfoldEntry {L : PFunctor.{0, 0}} (d : Presented P L Γ) (n : ℕ) :
    P.FreeM (Γ ⊕ Position d.1) := unfold d.2.1 n d.2.2

/-- A solution is an export interpretation satisfying the equations in the selected algebra. -/
def IsSolution (alg : P.Obj V → V) (env : Γ → V) (d : Block P Γ E) (v : E → V) : Prop :=
  ∀ i, eval alg (Sum.elim env v) (d i) = v i

/-- A solution makes a simultaneous unfolding semantics-preserving. -/
theorem eval_expand (alg : P.Obj V → V) (env : Γ → V) (d : Block P Γ E)
    (v : E → V) (h : IsSolution alg env d v) (t : P.FreeM (Γ ⊕ E)) :
    eval alg (Sum.elim env v) (expand d t) = eval alg (Sum.elim env v) t := by
  rw [expand, eval_bind]
  congr 1
  funext x
  cases x with
  | inl x => rfl
  | inr i => exact h i

/-- Every solution satisfies all finite unfoldings; no existence or uniqueness is assumed. -/
theorem eval_unfold (alg : P.Obj V → V) (env : Γ → V) (d : Block P Γ E)
    (v : E → V) (h : IsSolution alg env d v) (n : ℕ) (i : E) :
    eval alg (Sum.elim env v) (unfold d n i) = v i := by
  refine Nat.rec (h i) (fun n ih ↦ ?_) n
  exact (eval_expand alg env d v h (unfold d n i)).trans ih

/-- A polynomial coalgebra supplies one constructor and its local references per equation. -/
def ofCoalgebra (c : E → P.Obj E) : Block P Empty E :=
  fun i ↦ .liftBind (c i).fst fun b ↦ .pure (.inr ((c i).snd b))

/-- Corecursion solves the flat, guarded equations in the M-type. -/
theorem coalgebra_isSolution (c : E → P.Obj E) :
    IsSolution M.mk Empty.elim (ofCoalgebra c) (M.corec c) := by
  intro i
  exact (M.corec_def c i).symm

/-- Finality makes the M-type solution of a flat, guarded block unique. -/
theorem coalgebra_solution_unique (c : E → P.Obj E) (v : E → P.M)
    (h : IsSolution M.mk Empty.elim (ofCoalgebra c) v) : v = M.corec c := by
  have hn : ∀ n i, (v i).approx n = (M.corec c i).approx n := by
    refine Nat.rec ?_ ?_
    · intro i
      cases (v i).approx 0
      rfl
    · intro n ih i
      rw [← h i]
      exact congrArg (Approx.CofixA.intro (c i).fst) (funext fun b ↦ ih ((c i).snd b))
  exact funext fun i ↦ M.ext' P _ _ fun n ↦ hn n i

section Encoding

variable [∀ a : P.A, FinEnum (P.B a)]

/-- Variables have even labels and no children. Operations have odd labels and children
in the supplied enumeration order. Natural labels denote bitstrings via the existing
sentinel bijection; neither labels nor child ordinals are semantic addresses. -/
def encode (opCode : P.A → ℕ) (varCode : Γ → ℕ) : P.FreeM Γ → RoseTree ℕ :=
  eval (fun x ↦ RoseTree.node (2 * opCode x.fst + 1)
    (List.ofFn fun i ↦ x.snd (FinEnum.equiv.symm i)))
    (fun x ↦ RoseTree.node (2 * varCode x) [])

/-- Encoding a variable records its code in a childless node. -/
@[simp] theorem encode_pure (opCode : P.A → ℕ) (varCode : Γ → ℕ) (x : Γ) :
    encode opCode varCode (pure x) = RoseTree.node (2 * varCode x) [] := rfl

/-- Encoding an operation tabulates its children in the direction enumeration. -/
theorem encode_liftBind (opCode : P.A → ℕ) (varCode : Γ → ℕ)
    (a : P.A) (ts : P.B a → P.FreeM Γ) :
    encode opCode varCode (.liftBind a ts) = RoseTree.node (2 * opCode a + 1)
      (List.ofFn fun i ↦ encode opCode varCode (ts (FinEnum.equiv.symm i))) := rfl

/-- Injective label codes give an injective rose-tree encoding of terms. -/
theorem encode_injective (opCode : P.A → ℕ) (varCode : Γ → ℕ)
    (hop : Function.Injective opCode) (hvar : Function.Injective varCode) :
    Function.Injective (encode opCode varCode) := by
  intro t
  refine FreeM.rec (motive := fun t ↦ ∀ u, encode opCode varCode t =
    encode opCode varCode u → t = u) ?_ ?_ t
  · intro x u h
    cases u with
    | pure y =>
      have hl := congrArg RoseTree.label h
      change 2 * varCode x = 2 * varCode y at hl
      exact congrArg FreeM.pure (hvar (by omega))
    | liftBind a ts =>
      have hl := congrArg RoseTree.label h
      change 2 * varCode x = 2 * opCode a + 1 at hl
      exfalso
      omega
  · intro a ts ih u h
    cases u with
    | pure y =>
      have hl := congrArg RoseTree.label h
      change 2 * opCode a + 1 = 2 * varCode y at hl
      exfalso
      omega
    | liftBind a' us =>
      have hl := congrArg RoseTree.label h
      change 2 * opCode a + 1 = 2 * opCode a' + 1 at hl
      have ha : a = a' := hop (by omega)
      subst a'
      have hc := congrArg RoseTree.children h
      simp only [encode_liftBind, RoseTree.children_node] at hc
      have hf := List.ofFn_injective hc
      apply congrArg (FreeM.liftBind a)
      funext b
      apply ih b
      simpa only [Equiv.symm_apply_apply] using congrFun hf (FinEnum.equiv b)

/-- The existing rose-tree wire codec remains injective on encoded definition terms. -/
theorem wire_encode_injective (opCode : P.A → ℕ) (varCode : Γ → ℕ)
    (hop : Function.Injective opCode) (hvar : Function.Injective varCode) :
    Function.Injective (fun t ↦ RoseTree.wire (encode opCode varCode t)) :=
  RoseTree.wire_injective.comp (encode_injective opCode varCode hop hvar)

end Encoding

end Geb.Definition

end
