/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Presentation.Slice.Free
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Equational presentations over presheaves, by restriction operations

A presheaf on a category {lit}`C` is a set sorted by the objects of {lit}`C` with a unary
restriction operation along each morphism, satisfying the equations of identity and composition.
A presheaf polynomial endofunctor with free arities ({lit}`Presheaf.Sig`) adds operations, each
over an object and with arguments over objects, and its naturality: a restriction of an
operation applied to arguments is the restricted operation applied to restrictions of the
arguments. A presentation over it ({lit}`Presheaf.Presentation`) is therefore a presentation over
a slice ({name}`Geb.Definition.Slice.Presentation`), whose sorts are the objects of {lit}`C` and
whose operations are those of the signature together with the restrictions
({lit}`Presheaf.ops`), with the equations of naturality, identity and composition
({lit}`Presheaf.REqn`) added to its own ({lit}`Presheaf.Presentation.toSlice`).

The classes of terms of each object then form a presheaf ({lit}`Presheaf.Presentation.clsPsh`),
restriction being the restriction operation on classes, whose laws are the equations of identity
and composition ({lit}`Presheaf.Presentation.restrCls_id`,
{lit}`Presheaf.Presentation.restrCls_comp`); and the operations commute with restriction by the
equations of naturality ({lit}`Presheaf.Presentation.restrCls_op`). The laws of the signature's
restriction and reindexing are not used: identity and composition are equations of the
presentation.

## Main definitions

* {lit}`Presheaf.Sig` — a presheaf polynomial endofunctor with free arities.
* {lit}`Presheaf.ops` — its operations and the restrictions, as a slice polynomial endofunctor.
* {lit}`Presheaf.REqn`, {lit}`Presheaf.reqns` — the equations of naturality, identity and
  composition.
* {lit}`Presheaf.Presentation`, {lit}`Presheaf.Presentation.toSlice` — a presentation over the
  signature, and the presentation over a slice it is.
* {lit}`Presheaf.Presentation.restrCls` — restriction of classes.
* {lit}`Presheaf.Presentation.clsPsh` — the presheaf of classes.

## Main statements

* {lit}`Presheaf.Presentation.restrCls_id`, {lit}`Presheaf.Presentation.restrCls_comp` — the
  functor laws of restriction on classes.
* {lit}`Presheaf.Presentation.restrCls_op` — the operations commute with restriction.

## References

* {cite}`Weber2007`, for parametric right adjoints on presheaf categories.
* {cite}`KellyPower1993`, for presentations of finitary monads by operations and equations.

## Tags

presheaf, equational presentation, parametric right adjoint, many-sorted algebra, restriction
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition.Presheaf

open CategoryTheory PFunctor GebProto Geb.Definition.Slice

universe uA uE u v

variable {C : Type u} [Category.{v} C]

/-- A presheaf polynomial endofunctor over {lit}`C` with free arities: shapes over objects,
arguments over objects, and the restriction of a shape along a morphism into its object, with
the reindexing of the restricted shape's arguments into the shape's arguments. -/
structure Sig (C : Type u) [Category.{v} C] : Type (max (uA + 1) (u + 1) v) where
  /-- The shapes. -/
  A : Type uA
  /-- The object over which a shape lies. -/
  q : A → C
  /-- The arguments of a shape. -/
  Gen : A → Type u
  /-- The object over which an argument lies. -/
  gobj : (a : A) → Gen a → C
  /-- The restriction of a shape along a morphism into its object. -/
  restr : (a : A) → {c' : C} → (c' ⟶ q a) → A
  /-- A restricted shape lies over the source of the morphism. -/
  q_restr : ∀ (a : A) {c' : C} (g : c' ⟶ q a), q (restr a g) = c'
  /-- The reindexing of a restricted shape's arguments: an argument of the shape and a
  morphism between their objects. -/
  reindex : (a : A) → {c' : C} → (g : c' ⟶ q a) → (b : Gen (restr a g)) →
    Σ b' : Gen a, (gobj (restr a g) b ⟶ gobj a b')

variable (S : Sig.{uA} C)

/-- The operations of the signature, as a slice polynomial endofunctor over the objects. -/
abbrev baseOps : SlicePFunctor.{uA, u, u, u} C C where
  A := S.A
  B := S.Gen
  r x := S.gobj x.1 x.2
  q := S.q

variable (C) in
/-- The restrictions: a unary operation along each morphism, from the sort of its target to the
sort of its source. -/
abbrev restrOps : SlicePFunctor.{max u v, u, u, u} C C where
  A := (c : C) × (c' : C) × (c' ⟶ c)
  B _ := PUnit
  r x := x.1.1
  q x := x.2.1

/-- The operations over a presheaf: those of the signature and the restrictions. -/
abbrev ops : SlicePFunctor.{max uA u v, u, u, u} C C := Slice.sum (baseOps S) (restrOps C)

/-- The arguments of each operation, enumerated, given enumerations of the signature's. -/
@[instance_reducible] def finEnumOps [inst : ∀ a, FinEnum (S.Gen a)] (a : (ops S).A) :
    FinEnum ((ops S).B a) :=
  match a with
  | .inl a => inst a
  | .inr _ => finEnumPUnit

section Terms

variable {S} {V : Type u}

/-- An operation of the signature applied to terms. -/
def opT (a : S.A) (k : S.Gen a → (ops S).toPFunctor.FreeM V) : (ops S).toPFunctor.FreeM V :=
  FreeM.liftBind (P := (ops S).toPFunctor) (.inl a) k

/-- A restriction applied to a term. -/
def rT {c c' : C} (g : c' ⟶ c) (t : (ops S).toPFunctor.FreeM V) : (ops S).toPFunctor.FreeM V :=
  FreeM.liftBind (P := (ops S).toPFunctor) (.inr ⟨c, c', g⟩) fun _ ↦ t

end Terms

/-- The equations of a presheaf: the naturality of each operation along each morphism into its
object, and the identity and composition laws of restriction. -/
inductive REqn : Type (max uA u v)
  | nat (a : S.A) {c' : C} (g : c' ⟶ S.q a)
  | id (c : C)
  | comp {c c' c'' : C} (g : c' ⟶ c) (h : c'' ⟶ c')

namespace REqn

variable {S}

/-- The variables of an equation: the arguments of the operation, for naturality; one, for the
laws of restriction. -/
def Var : REqn S → Type u
  | .nat a _ => S.Gen a
  | .id _ => PUnit
  | .comp .. => PUnit

/-- The sort of a variable. -/
def varSort : (e : REqn S) → e.Var → C
  | .nat a _, b => S.gobj a b
  | .id c, _ => c
  | @comp _ _ _ c _ _ _ _, _ => c

/-- The sort of an equation. -/
def sort : REqn S → C
  | @nat _ _ _ _ c' _ => c'
  | .id c => c
  | @comp _ _ _ _ _ c'' _ _ => c''

/-- The left sides: a restriction of an operation applied to its arguments; a restriction along
an identity; two restrictions in succession. -/
def lhs : (e : REqn S) → (ops S).toPFunctor.FreeM e.Var
  | .nat a g => rT g (opT a .pure)
  | .id c => rT (𝟙 c) (.pure ⟨⟩)
  | .comp g h => rT h (rT g (.pure ⟨⟩))

/-- The right sides: the restricted operation applied to restrictions of its arguments; the
variable; the restriction along the composite. -/
def rhs : (e : REqn S) → (ops S).toPFunctor.FreeM e.Var
  | .nat a g => opT (S.restr a g) fun b ↦ rT (S.reindex a g b).2 (.pure (S.reindex a g b).1)
  | .id _ => .pure ⟨⟩
  | .comp g h => rT (h ≫ g) (.pure ⟨⟩)

end REqn

/-- The equations of a presheaf, as a slice polynomial endofunctor over the objects. -/
def reqns : SlicePFunctor.{max uA u v, u, u, u} C C where
  A := REqn S
  B := REqn.Var
  r x := REqn.varSort x.1 x.2
  q := REqn.sort

/-- The left sides of the equations of a presheaf are well sorted. -/
theorem reqns_lhs_sorted :
    DerivedSorted (F := ops S) (Q := reqns S) (REqn.lhs (S := S))
  | .nat _ _ => ⟨fun _ ↦ ⟨rfl, fun _ ↦ ⟨rfl, trivial⟩⟩, rfl⟩
  | .id _ => ⟨fun _ ↦ ⟨rfl, trivial⟩, rfl⟩
  | .comp _ _ => ⟨fun _ ↦ ⟨rfl, fun _ ↦ ⟨rfl, trivial⟩⟩, rfl⟩

/-- The right sides of the equations of a presheaf are well sorted. -/
theorem reqns_rhs_sorted :
    DerivedSorted (F := ops S) (Q := reqns S) (REqn.rhs (S := S))
  | .nat a g => ⟨fun _ ↦ ⟨rfl, fun _ ↦ ⟨rfl, trivial⟩⟩, S.q_restr a g⟩
  | .id _ => ⟨trivial, rfl⟩
  | .comp _ _ => ⟨fun _ ↦ ⟨rfl, trivial⟩, rfl⟩

/-- An equational presentation over a presheaf polynomial endofunctor with free arities: further
equations, each with its sort and the sorts of its variables, and their two sides, well-sorted
terms of the operations and restrictions. -/
structure Presentation : Type (max (uA + 1) (uE + 1) (u + 1) v) where
  /-- The further equations, with their variables as directions. -/
  E : SlicePFunctor.{uE, u, u, u} C C
  /-- The left side of each further equation. -/
  lhs : Derived (ops S).toPFunctor E.toPFunctor
  /-- The right side of each further equation. -/
  rhs : Derived (ops S).toPFunctor E.toPFunctor
  /-- The left sides are well sorted. -/
  lhs_sorted : DerivedSorted lhs
  /-- The right sides are well sorted. -/
  rhs_sorted : DerivedSorted rhs

namespace Presentation

variable {S} (p : Presentation.{uA, uE} S)

/-- The sides of the equations of a presheaf and of the further equations, at the left
orientation for {lit}`false`. -/
def side (o : Bool) : Derived (ops S).toPFunctor (Slice.sum (reqns S) p.E).toPFunctor
  | .inl e => cond o (REqn.rhs e) (REqn.lhs e)
  | .inr e => cond o (p.rhs e) (p.lhs e)

/-- The sides at either orientation are well sorted. -/
theorem side_sorted (o : Bool) : DerivedSorted (F := ops S) (Q := Slice.sum (reqns S) p.E)
    (p.side o)
  | .inl e => by
    cases o
    · exact reqns_lhs_sorted S e
    · exact reqns_rhs_sorted S e
  | .inr e => by
    cases o
    · exact p.lhs_sorted e
    · exact p.rhs_sorted e

/-- The presentation over the slice of objects: the equations of a presheaf and the further
equations. -/
def toSlice : Slice.Presentation.{max uA u v, max uA u v uE, u, u} (ops S) where
  E := Slice.sum (reqns S) p.E
  lhs := p.side false
  rhs := p.side true
  lhs_sorted := p.side_sorted false
  rhs_sorted := p.side_sorted true

variable {Γ : Type u} (γ : Γ → C)

/-- A restriction applied to a well-sorted term. -/
def rTm {c c' : C} (g : c' ⟶ c) (t : Tm (ops S) γ c) : Tm (ops S) γ c' :=
  opTm (F := ops S) γ (.inr ⟨c, c', g⟩) fun _ ↦ t

/-- Restriction of classes: the restriction operation on classes. -/
def restrCls {c c' : C} (g : c' ⟶ c) (x : p.toSlice.Cls γ c) : p.toSlice.Cls γ c' :=
  letI : FinEnum ((ops S).B (.inr ⟨c, c', g⟩)) := finEnumPUnit.{u}
  p.toSlice.op γ (.inr ⟨c, c', g⟩) fun _ ↦ x

/-- Restriction of the class of a term is the class of its restriction. -/
theorem restrCls_cls {c c' : C} (g : c' ⟶ c) (t : Tm (ops S) γ c) :
    p.restrCls γ g (p.toSlice.cls γ t) = p.toSlice.cls γ (rTm γ g t) :=
  let _ : FinEnum ((ops S).B (.inr ⟨c, c', g⟩)) := finEnumPUnit.{u}
  p.toSlice.op_cls γ (.inr ⟨c, c', g⟩) fun _ ↦ t

/-- Restriction along an identity is the identity. -/
theorem restrCls_id (c : C) (x : p.toSlice.Cls γ c) : p.restrCls γ (𝟙 c) x = x := by
  refine Quot.ind (β := fun x ↦ p.restrCls γ (𝟙 c) x = x) (fun t ↦ ?_) x
  exact (p.restrCls_cls γ (𝟙 c) t).trans
    (p.toSlice.cls_bind_lhs γ (.inl (.id c)) (fun _ ↦ t.1) fun _ ↦ t.2)

/-- Restriction along a composite is the composite of restrictions. -/
theorem restrCls_comp {c c' c'' : C} (g : c' ⟶ c) (h : c'' ⟶ c') (x : p.toSlice.Cls γ c) :
    p.restrCls γ h (p.restrCls γ g x) = p.restrCls γ (h ≫ g) x := by
  refine Quot.ind (β := fun x ↦ p.restrCls γ h (p.restrCls γ g x) = p.restrCls γ (h ≫ g) x)
    (fun t ↦ ?_) x
  exact (congrArg (p.restrCls γ h) (p.restrCls_cls γ g t)).trans ((p.restrCls_cls γ h _).trans
    ((p.toSlice.cls_bind_lhs γ (.inl (.comp g h)) (fun _ ↦ t.1) fun _ ↦ t.2).trans
      (p.restrCls_cls γ (h ≫ g) t).symm))

/-- The presheaf of classes: the classes of each object, with restriction of classes. -/
def clsPsh : Cᵒᵖ ⥤ Type (max uA u v) where
  obj c := p.toSlice.Cls γ c.unop
  map f := ↾ p.restrCls γ f.unop
  map_id c := by
    ext x
    exact p.restrCls_id γ c.unop x
  map_comp f g := by
    ext x
    exact (p.restrCls_comp γ f.unop g.unop x).symm

variable [∀ a, FinEnum (S.Gen a)]

attribute [local instance] finEnumOps

/-- The operations commute with restriction: a restriction of an operation applied to classes is
the restricted operation applied to restrictions of the classes, as elements of the classes of
all objects. -/
theorem restrCls_op (a : S.A) {c' : C} (g : c' ⟶ S.q a)
    (f : (b : S.Gen a) → p.toSlice.Cls γ (S.gobj a b)) :
    (⟨c', p.restrCls γ g (p.toSlice.op γ (.inl a) f)⟩ : Σ c, p.toSlice.Cls γ c) =
      ⟨S.q (S.restr a g), p.toSlice.op γ (.inl (S.restr a g)) fun b ↦
        p.restrCls γ (S.reindex a g b).2 (f (S.reindex a g b).1)⟩ := by
  obtain ⟨ts, hts⟩ := p.toSlice.exists_cls γ f
  obtain rfl : f = fun b ↦ p.toSlice.cls γ (ts b) := (funext hts).symm
  have hσ : IsSorted (fun b ↦ (reqns S).r ⟨.nat a g, b⟩) γ fun b ↦ (ts b).1 := fun b ↦ (ts b).2
  have hl : p.restrCls γ g (p.toSlice.op γ (.inl a) fun b ↦ p.toSlice.cls γ (ts b)) =
      p.toSlice.cls γ (p.toSlice.lhsBind γ (.inl (.nat a g)) (fun b ↦ (ts b).1) hσ) :=
    (congrArg (p.restrCls γ g) (p.toSlice.op_cls γ (.inl a) ts)).trans (p.restrCls_cls γ g _)
  have hr : p.toSlice.op γ (.inl (S.restr a g)) (fun b ↦
        p.restrCls γ (S.reindex a g b).2 (p.toSlice.cls γ (ts (S.reindex a g b).1))) =
      p.toSlice.cls γ (opTm (F := ops S) γ (.inl (S.restr a g)) fun b ↦
        rTm γ (S.reindex a g b).2 (ts (S.reindex a g b).1)) :=
    (congrArg (p.toSlice.op γ (.inl (S.restr a g)))
      (funext fun b ↦ p.restrCls_cls γ _ _)).trans (p.toSlice.op_cls γ _ _)
  exact (congrArg (Sigma.mk c') hl).trans ((congrArg (Sigma.mk c')
    (p.toSlice.cls_bind_lhs γ (.inl (.nat a g)) (fun b ↦ (ts b).1) hσ)).trans
      ((p.toSlice.sigma_cls γ _ (S.q_restr a g).symm).trans (congrArg (Sigma.mk _) hr.symm)))

end Presentation

end Geb.Definition.Presheaf

end
