/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PHOAS.Basic

set_option doc.verso true in
/-!
# Scoped unfolding of the end

A scoped term accepts an interpretation of its context variables and satisfies the
corresponding wedge condition. A closed end element unfolds into one operation position
and, for each inner position, a scoped child whose context is that position's binder arity.

## Main definitions

* {lit}`Scoped` represents compatible families with a context of variables.
* {lit}`End.unfoldScoped` is the closed unfolding equivalence.
* {lit}`Scoped.unfold` is the unfolding of the whole family of contexts.

## Main statements

The closed unfolding is {lit}`End P ≃ Σ a, Π b, Scoped P ((P.B a).B b)`.
When contexts and binder arities inhabit the universe over which the families quantify,
the whole family unfolds as {lit}`Scoped P Γ ≃ Γ ⊕ Σ a, Π b, Scoped P (Γ ⊕ (P.B a).B b)`.
Thus a child retains the surrounding variables and gains its own bound variables.
These equations do not apply the original profunctor to the closed end as its negative argument.

## Tags

PHOAS, binding signature, context, end, polynomial profunctor
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PHOAS.PProfunctor

open PFunctor

universe uA uB uC u v

variable (P : PProfunctor.{uA, uB, uC})

/-- Open terms with variables from a context, uniform under every map of input types. -/
abbrev Scoped (Γ : Type v) : Type (max uA uB uC v (u + 1)) :=
  { t : (X : Type u) → (Γ → X) → P.Free X X //
    ∀ {X Y : Type u} (f : X → Y) (env : Γ → X),
      (t X env).map f = Free.comap f (t Y (f ∘ env)) }

namespace Scoped

variable {P} {Γ : Type v}

/-- A context variable is interpreted by the supplied environment. -/
def var (x : Γ) : P.Scoped.{uA, uB, uC, u, v} Γ :=
  ⟨fun _ env ↦ .pure (env x), fun {_ _} _ _ ↦ rfl⟩

/-- An empty context gives exactly the closed end. -/
def emptyEquivEnd : P.Scoped.{uA, uB, uC, u, v} PEmpty.{v + 1} ≃ P.End.{uA, uB, uC, u} where
  toFun t := End.mk (fun X ↦ t.val X PEmpty.elim) (by
    intro X Y f
    have h := t.property f PEmpty.elim
    have he : f ∘ (PEmpty.elim : PEmpty.{v + 1} → X) = PEmpty.elim :=
      funext fun x ↦ x.elim
    rw [he] at h
    exact h)
  invFun e := ⟨fun X _ ↦ e.eval X, fun {_ _} f _ ↦ e.wedge f⟩
  left_inv t := by
    apply Subtype.ext
    funext X env
    exact congrArg (t.val X) (funext fun x ↦ x.elim)
  right_inv _ := rfl

end Scoped

namespace End

variable {P}

/-- Currying polynomial directions turns each operation's compatible children into
scoped terms, one for each inner position. -/
def layerEquivScoped : Layer.{uA, uB, uC, u} (P := P) ≃
    ((a : P.A) × ((b : (P.B a).A) → P.Scoped.{uA, uB, uC, u, uC} ((P.B a).B b))) where
  toFun n := ⟨n.1, fun b ↦
    ⟨fun X env ↦ n.2.val X (.mk b env), fun {_ _} f env ↦ n.2.property f (.mk b env)⟩⟩
  invFun n := ⟨n.1,
    ⟨fun X d ↦ (n.2 d.fst).val X d.snd, fun {_ _} f d ↦ (n.2 d.fst).property f d.snd⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The closed end unfolds into an operation and children scoped by its binder arities. -/
def unfoldScoped : P.End.{uA, uB, uC, u} ≃
    ((a : P.A) × ((b : (P.B a).A) → P.Scoped.{uA, uB, uC, u, uC} ((P.B a).B b))) :=
  unfold.trans layerEquivScoped

end End

namespace Scoped

variable {Q : PProfunctor.{uA, uB, u}} {Γ : Type u}

/-- The root of an open term is determined at its context with the identity environment. -/
theorem root_eval (t : Q.Scoped.{uA, uB, u, u, u} Γ) (X : Type u) (env : Γ → X) :
    Free.root (t.val X env) = Free.root (t.val Γ id) := by
  have h := congrArg Free.root (t.property env id)
  simpa only [Free.root_map, Free.root_comap, Function.comp_id] using h.symm

/-- A variable at the identity environment determines the entire scoped family. -/
theorem eq_var_of_eval (t : Q.Scoped.{uA, uB, u, u, u} Γ) (x : Γ)
    (h : t.val Γ id = .pure x) : t = var x := by
  apply Subtype.ext
  funext X env
  have hw := t.property env id
  rw [h, Function.comp_id] at hw
  cases hx : t.val X env with
  | pure y =>
    rw [hx] at hw
    simpa [var, Free.comap, Free.fold, FreeM.map] using hw.symm
  | liftBind a k =>
    rw [hx] at hw
    cases hw

/-- The children at an operation root, for each interpretation of the context. -/
def children (a : Q.A) (t : Q.Scoped.{uA, uB, u, u, u} Γ)
    (h : Free.root (t.val Γ id) = some a) (X : Type u) (env : Γ → X) :
    (Q.B a).Obj X → Q.Free X X :=
  Free.childrenAt a (t.val X env) ((t.root_eval X env).trans h)

/-- Reconstruct a component of an open term from its operation root and children. -/
theorem liftBind_children (a : Q.A) (t : Q.Scoped.{uA, uB, u, u, u} Γ)
    (h : Free.root (t.val Γ id) = some a) (X : Type u) (env : Γ → X) :
    FreeM.liftBind a (children a t h X env) = t.val X env :=
  Free.liftBind_childrenAt _ _ _

/-- Open children are coherent under simultaneous renaming of both environments. -/
theorem children_wedge (a : Q.A) (t : Q.Scoped.{uA, uB, u, u, u} Γ)
    (h : Free.root (t.val Γ id) = some a) {X Y : Type u} (f : X → Y)
    (env : Γ → X) (d : (Q.B a).Obj X) :
    (children a t h X env d).map f =
      Free.comap f (children a t h Y (f ∘ env) ((Q.B a).map f d)) := by
  have hw := t.property f env
  rw [← liftBind_children a t h X env, ← liftBind_children a t h Y (f ∘ env)] at hw
  exact congrFun (Free.liftBind_injective a hw) d

/-- A child extends the surrounding context by its own binder arity. -/
def child (a : Q.A) (t : Q.Scoped.{uA, uB, u, u, u} Γ)
    (h : Free.root (t.val Γ id) = some a) (b : (Q.B a).A) :
    Q.Scoped.{uA, uB, u, u, u} (Γ ⊕ (Q.B a).B b) :=
  ⟨fun X env ↦ children a t h X (env ∘ Sum.inl) (.mk b (env ∘ Sum.inr)),
    fun {_ _} f env ↦ children_wedge a t h f (env ∘ Sum.inl) (.mk b (env ∘ Sum.inr))⟩

/-- Build an operation whose children can refer to the surrounding and bound variables. -/
def node (a : Q.A)
    (k : (b : (Q.B a).A) → Q.Scoped.{uA, uB, u, u, u} (Γ ⊕ (Q.B a).B b)) :
    Q.Scoped.{uA, uB, u, u, u} Γ :=
  ⟨fun X env ↦ .liftBind a (fun d ↦ (k d.fst).val X (Sum.elim env d.snd)), by
    intro X Y f env
    apply congrArg (FreeM.liftBind (P := Q.apply X) a)
    funext d
    have h := (k d.fst).property f (Sum.elim env d.snd)
    have he : f ∘ Sum.elim env d.snd = Sum.elim (f ∘ env) (f ∘ d.snd) := by
      funext x
      cases x <;> rfl
    rw [he] at h
    exact h⟩

/-- Recovering a child of a constructed operation returns that scoped child. -/
theorem child_node (a : Q.A)
    (k : (b : (Q.B a).A) → Q.Scoped.{uA, uB, u, u, u} (Γ ⊕ (Q.B a).B b))
    (b : (Q.B a).A) : child a (node a k) rfl b = k b := by
  apply Subtype.ext
  funext X env
  apply congrArg ((k b).val X)
  funext x
  cases x <;> rfl

/-- Reassembling all the scoped children reconstructs the open term. -/
theorem node_child (a : Q.A) (t : Q.Scoped.{uA, uB, u, u, u} Γ)
    (h : Free.root (t.val Γ id) = some a) : node a (child a t h) = t := by
  apply Subtype.ext
  funext X env
  exact liftBind_children a t h X env

/-- One layer of scoped syntax: a context variable, or an operation with extended contexts. -/
abbrev Layer (Q : PProfunctor.{uA, uB, u}) (Γ : Type u) :=
  Γ ⊕ ((a : Q.A) × ((b : (Q.B a).A) → Q.Scoped.{uA, uB, u, u, u} (Γ ⊕ (Q.B a).B b)))

/-- Expose the root at the identity environment and retain its coherent open children. -/
def unroll (t : Q.Scoped.{uA, uB, u, u, u} Γ) : Layer Q Γ :=
  match h : t.val Γ id with
  | .pure x => .inl x
  | .liftBind a _ => .inr ⟨a, child a t (by rw [h]; rfl)⟩

/-- Build one layer of scoped syntax. -/
def roll : Layer Q Γ → Q.Scoped.{uA, uB, u, u, u} Γ :=
  Sum.elim var (fun n ↦ node n.1 n.2)

/-- The whole scoped family satisfies the binding-signature fixed-point equation, when
contexts and binder arities inhabit the universe over which the families quantify. -/
def unfold (Q : PProfunctor.{uA, uB, u}) (Γ : Type u) :
    Q.Scoped.{uA, uB, u, u, u} Γ ≃ Layer Q Γ where
  toFun := unroll
  invFun := roll
  left_inv t := by
    unfold unroll
    split
    · next x h => exact (eq_var_of_eval t x h).symm
    · exact node_child _ t _
  right_inv n := by
    rcases n with x | ⟨a, k⟩
    · rfl
    · change (Sum.inr (Sigma.mk a (child a (node a k) rfl)) : Layer Q Γ) = _
      exact congrArg (fun l ↦ (Sum.inr (Sigma.mk a l) : Layer Q Γ)) (funext (child_node a k))

end Scoped

end Geb.PHOAS.PProfunctor
