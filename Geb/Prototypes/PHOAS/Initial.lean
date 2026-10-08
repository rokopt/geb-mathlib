/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PHOAS.Scoped
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Initiality of scoped polynomial syntax

Interpreting all variables in the singleton type supplies a well-founded tree for
recursion on scoped terms, even though each child extends its parent's context.
The binding-signature operator is the arbitrary-arity version of the operator in
{cite}`FiorePlotkinTuri1999`, Section 2. The context-extension construction
{name}`Geb.PHOAS.PProfunctor.BindingNode` gives
{lit}`H(M)(Γ) = Σ a, Π b, M(Γ ⊕ C(a,b))`, where
{lit}`C(a,b) = (P.B a).B b`. The free-monad/end construction realizes the initial
algebra of {lit}`Id + H`, namely {name}`Geb.PHOAS.PProfunctor.BindingLayer`.

## Main definitions

* {lit}`Scoped.recOn` eliminates scoped terms by variables and binding operations.
* {lit}`Scoped.fold` interprets scoped terms in any such family with constructors.

## Main statements

* {lit}`Scoped.fold_unique` characterizes every constructor-preserving interpretation.
* {lit}`Scoped.fold_fusion` derives composition of interpretations from uniqueness.
* {lit}`Scoped.fold_rename` makes the fold natural whenever the target constructors are natural.

## Implementation notes

Contexts and binder arities belong to {lit}`Type u`; scoped families quantify over
that same universe. Operation positions and the sets indexing their children may
have independent universes. No finiteness assumption is imposed on any arity.
The recursion uses CSLib's free-monad recursor, applied to the singleton interpretation.
{lit}`PProfunctor.scopedIsInitial` in the categorical wrapper packages the fold and
uniqueness as initiality in the functor category. At the empty context, the scoped
family is equivalent to the original closed end by
{name}`Geb.PHOAS.PProfunctor.Scoped.emptyEquivEnd`.

## References

* {cite}`FiorePlotkinTuri1999`

## Tags

PHOAS, initial algebra, binding signature, structural recursion
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PHOAS.PProfunctor

open PFunctor

universe uA uB u v w

variable {P : PProfunctor.{uA, uB, u}}

namespace Scoped

/-- Erase variable identities by interpreting every variable in the singleton type. -/
def erase {Γ : Type u} (t : P.Scoped.{uA, uB, u, u, u} Γ) :
    P.Free PUnit.{u + 1} PUnit.{u + 1} := t.val _ (fun _ ↦ PUnit.unit)

/-- Unfolding an operation returns its specified children. -/
@[simp] theorem unfold_node {Γ : Type u} (a : P.A)
    (k : (b : (P.B a).A) → P.Scoped.{uA, uB, u, u, u} (Γ ⊕ (P.B a).B b)) :
    unfold P Γ (node a k) = .inr ⟨a, k⟩ :=
  (unfold P Γ).apply_symm_apply (.inr ⟨a, k⟩)

/-- Case analysis through the scoped unfolding equivalence. -/
def casesOn {Γ : Type u} {motive : P.Scoped.{uA, uB, u, u, u} Γ → Sort v}
    (t : P.Scoped.{uA, uB, u, u, u} Γ)
    (onVar : ∀ x, motive (var x)) (onNode : ∀ a k, motive (node a k)) : motive t :=
  (unfold P Γ).left_inv t ▸
    (show motive ((unfold P Γ).symm ((unfold P Γ) t)) from
      (match (unfold P Γ) t with
      | .inl x => onVar x
      | .inr ⟨a, k⟩ => onNode a k))

/-- Case analysis on an operation uses the operation branch. -/
@[simp] theorem casesOn_node {Γ : Type u}
    {motive : P.Scoped.{uA, uB, u, u, u} Γ → Sort v}
    (onVar : ∀ x, motive (var x)) (onNode : ∀ a k, motive (node a k))
    (a : P.A) (k : (b : (P.B a).A) → P.Scoped.{uA, uB, u, u, u} (Γ ⊕ (P.B a).B b)) :
    casesOn (node a k) onVar onNode = onNode a k := by
  unfold casesOn
  apply eq_of_heq
  refine (eqRec_heq (φ := motive) ((unfold P Γ).left_inv (node a k)) _).trans ?_
  change HEq (onNode a (child a (node a k) rfl)) (onNode a k)
  rw [show child a (node a k) rfl = k from funext (child_node a k)]

/-- Erasing a binding operation erases each of its children. -/
@[simp] theorem erase_node {Γ : Type u} (a : P.A)
    (k : (b : (P.B a).A) → P.Scoped.{uA, uB, u, u, u} (Γ ⊕ (P.B a).B b)) :
    erase (node a k) = .liftBind a (fun d ↦ erase (k d.fst)) := by
  apply congrArg (FreeM.liftBind (P := P.apply PUnit.{u + 1}) a)
  funext d
  apply congrArg ((k d.fst).val PUnit.{u + 1})
  funext x
  exact Subsingleton.elim _ _

/-- Eliminate scoped terms using a free-monad tree witnessing their erased shape. -/
def recAux {motive : (Γ : Type u) → P.Scoped.{uA, uB, u, u, u} Γ → Sort v}
    (onVar : ∀ Γ x, motive Γ (var x))
    (onNode : ∀ Γ a k, (∀ b, motive (Γ ⊕ (P.B a).B b) (k b)) → motive Γ (node a k))
    (r : P.Free PUnit.{u + 1} PUnit.{u + 1}) :
    ∀ Γ (t : P.Scoped.{uA, uB, u, u, u} Γ), erase t = r → motive Γ t := by
  refine FreeM.rec (motive := fun r ↦
    ∀ Γ (t : P.Scoped.{uA, uB, u, u, u} Γ), erase t = r → motive Γ t) ?_ ?_ r
  · intro y Γ t
    refine casesOn (motive := fun t ↦ erase t = .pure y → motive Γ t)
      t (fun x _ ↦ onVar Γ x) ?_
    intro a k ht
    cases ht
  · intro a k ih Γ t
    refine casesOn (motive := fun t ↦ erase t = .liftBind a k → motive Γ t) t ?_ ?_
    · intro x ht
      cases ht
    · intro a' k' ht
      have ha : a' = a := Option.some.inj (congrArg Free.root ht)
      subst a'
      have hk := Free.liftBind_injective a ht
      apply onNode Γ a k'
      intro b
      apply ih (.mk b (fun _ ↦ PUnit.unit)) _ (k' b)
      exact congrFun hk (.mk b (fun _ ↦ PUnit.unit))

/-- Structural recursion on scoped terms, including the extended context of each child. -/
def recOn {motive : (Γ : Type u) → P.Scoped.{uA, uB, u, u, u} Γ → Sort v}
    {Γ : Type u} (t : P.Scoped.{uA, uB, u, u, u} Γ)
    (onVar : ∀ Γ x, motive Γ (var x))
    (onNode : ∀ Γ a k, (∀ b, motive (Γ ⊕ (P.B a).B b) (k b)) → motive Γ (node a k)) :
    motive Γ t := recAux onVar onNode (erase t) Γ t rfl

/-- Fold scoped syntax into a family equipped with variables and binding operations. -/
def fold {M : Type u → Type v} (onVar : ∀ Γ, Γ → M Γ)
    (onNode : ∀ Γ a, ((b : (P.B a).A) → M (Γ ⊕ (P.B a).B b)) → M Γ)
    {Γ : Type u} (t : P.Scoped.{uA, uB, u, u, u} Γ) : M Γ :=
  recOn (motive := fun Γ _ ↦ M Γ) t onVar (fun Γ a _ ih ↦ onNode Γ a ih)

/-- The scoped fold interprets a context variable. -/
@[simp] theorem fold_var {M : Type u → Type v} (onVar : ∀ Γ, Γ → M Γ)
    (onNode : ∀ Γ a, ((b : (P.B a).A) → M (Γ ⊕ (P.B a).B b)) → M Γ)
    {Γ : Type u} (x : Γ) : fold onVar onNode (var x) = onVar Γ x := by
  rfl

/-- The scoped fold interprets an operation after folding its extended-context children. -/
@[simp] theorem fold_node {M : Type u → Type v} (onVar : ∀ Γ, Γ → M Γ)
    (onNode : ∀ Γ a, ((b : (P.B a).A) → M (Γ ⊕ (P.B a).B b)) → M Γ)
    {Γ : Type u} (a : P.A)
    (k : (b : (P.B a).A) → P.Scoped.{uA, uB, u, u, u} (Γ ⊕ (P.B a).B b)) :
    fold onVar onNode (node a k) = onNode Γ a (fun b ↦ fold onVar onNode (k b)) := by
  unfold fold recOn
  conv_lhs => unfold recAux
  dsimp only [erase, node]
  erw [casesOn_node (P := P) _ _ a k]
  apply congrArg (onNode Γ a)
  funext b
  have he : Sum.elim (fun _ : Γ ↦ (PUnit.unit : PUnit.{u + 1}))
      (fun _ : (P.B a).B b ↦ PUnit.unit) = (fun _ ↦ PUnit.unit) := by
    funext x
    cases x <;> rfl
  change recAux (motive := fun Γ _ ↦ M Γ) onVar (fun Γ a _ ih ↦ onNode Γ a ih)
      ((k b).val PUnit.{u + 1} (Sum.elim (fun _ ↦ PUnit.unit) (fun _ ↦ PUnit.unit)))
      _ (k b) _ = _
  simp only [he]

/-- A family of maps preserving variables and operations is the scoped fold. -/
theorem fold_unique {M : Type u → Type v} (onVar : ∀ Γ, Γ → M Γ)
    (onNode : ∀ Γ a, ((b : (P.B a).A) → M (Γ ⊕ (P.B a).B b)) → M Γ)
    (h : ∀ Γ, P.Scoped.{uA, uB, u, u, u} Γ → M Γ)
    (hv : ∀ Γ x, h Γ (var x) = onVar Γ x)
    (hn : ∀ Γ a k, h Γ (node a k) = onNode Γ a (fun b ↦ h _ (k b))) :
    h = fun Γ ↦ fold onVar onNode (Γ := Γ) := by
  funext Γ t
  refine recOn (motive := fun Γ t ↦ h Γ t = fold onVar onNode t) t ?_ ?_
  · intro Γ x
    exact hv Γ x
  · intro Γ a k ih
    rw [hn, fold_node]
    exact congrArg (onNode Γ a) (funext ih)

/-- Composing a fold with an algebra homomorphism gives the fold into the target algebra. -/
theorem fold_fusion {M : Type u → Type v} {N : Type u → Type w}
    (mv : ∀ Γ, Γ → M Γ)
    (mn : ∀ Γ a, ((b : (P.B a).A) → M (Γ ⊕ (P.B a).B b)) → M Γ)
    (nv : ∀ Γ, Γ → N Γ)
    (nn : ∀ Γ a, ((b : (P.B a).A) → N (Γ ⊕ (P.B a).B b)) → N Γ)
    (h : ∀ Γ, M Γ → N Γ) (hv : ∀ Γ x, h Γ (mv Γ x) = nv Γ x)
    (hn : ∀ Γ a k, h Γ (mn Γ a k) = nn Γ a (fun b ↦ h _ (k b)))
    {Γ : Type u} (t : P.Scoped.{uA, uB, u, u, u} Γ) :
    h Γ (fold mv mn t) = fold nv nn t := by
  have he := fold_unique nv nn (fun Γ t ↦ h Γ (fold mv mn t))
    (fun Γ x ↦ hv Γ x) (fun Γ a k ↦ by rw [fold_node, hn])
  exact congrFun (congrFun he Γ) t

/-- Interpreting each constructor by itself fixes every scoped term. -/
@[simp] theorem fold_self {Γ : Type u} (t : P.Scoped.{uA, uB, u, u, u} Γ) :
    fold (fun _ ↦ var) (fun _ ↦ node) t = t := by
  have he := fold_unique (P := P) (fun _ ↦ var) (fun _ ↦ node) (fun _ ↦ id)
    (fun _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
  exact (congrFun (congrFun he Γ) t).symm

/-- Rename the available context variables by precomposing their environment. -/
def rename {Γ Δ : Type u} (f : Γ → Δ) (t : P.Scoped.{uA, uB, u, u, u} Γ) :
    P.Scoped.{uA, uB, u, u, u} Δ :=
  ⟨fun X env ↦ t.val X (env ∘ f), fun {_ _} g env ↦ t.property g (env ∘ f)⟩

/-- Identity renaming fixes every scoped term. -/
@[simp] theorem rename_id {Γ : Type u} (t : P.Scoped.{uA, uB, u, u, u} Γ) :
    rename id t = t := rfl

/-- Context renaming respects composition. -/
theorem rename_comp {Γ Δ Θ : Type u} (f : Γ → Δ) (g : Δ → Θ)
    (t : P.Scoped.{uA, uB, u, u, u} Γ) : rename g (rename f t) = rename (g ∘ f) t := rfl

/-- Renaming a variable applies the context map. -/
@[simp] theorem rename_var {Γ Δ : Type u} (f : Γ → Δ) (x : Γ) :
    rename (P := P) f (var x) = var (f x) := rfl

/-- Renaming under a binder retains its newly bound variables. -/
@[simp] theorem rename_node {Γ Δ : Type u} (f : Γ → Δ) (a : P.A)
    (k : (b : (P.B a).A) → P.Scoped.{uA, uB, u, u, u} (Γ ⊕ (P.B a).B b)) :
    rename f (node a k) = node a (fun b ↦ rename (Sum.map f id) (k b)) := by
  apply Subtype.ext
  funext X env
  apply congrArg (FreeM.liftBind (P := P.apply X) a)
  funext d
  apply congrArg ((k d.fst).val X)
  funext x
  cases x <;> rfl

/-- A scoped fold commutes with renaming when its variable and operation maps do. -/
theorem fold_rename {M : Type u → Type v} (onVar : ∀ Γ, Γ → M Γ)
    (onNode : ∀ Γ a, ((b : (P.B a).A) → M (Γ ⊕ (P.B a).B b)) → M Γ)
    (mapM : ∀ {Γ Δ}, (Γ → Δ) → M Γ → M Δ)
    (hv : ∀ {Γ Δ} (f : Γ → Δ) x, mapM f (onVar Γ x) = onVar Δ (f x))
    (hn : ∀ {Γ Δ} (f : Γ → Δ) a k,
      mapM f (onNode Γ a k) = onNode Δ a (fun b ↦ mapM (Sum.map f id) (k b)))
    {Γ Δ : Type u} (f : Γ → Δ) (t : P.Scoped.{uA, uB, u, u, u} Γ) :
    mapM f (fold onVar onNode t) = fold onVar onNode (rename f t) := by
  refine recOn (motive := fun Γ t ↦ ∀ {Δ} (f : Γ → Δ),
    mapM f (fold onVar onNode t) = fold onVar onNode (rename f t)) t ?_ ?_ f
  · intro Γ x Δ f
    exact hv f x
  · intro Γ a k ih Δ f
    rw [fold_node, hn, rename_node, fold_node]
    exact congrArg (onNode Δ a) (funext fun b ↦ ih b (Sum.map f id))

end Scoped

end Geb.PHOAS.PProfunctor
