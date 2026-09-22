/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.Basic

meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Presheaf polynomial functors with free arities

A presheaf polynomial endofunctor over a category {lit}`C` has free arities when the
arity of each shape is a coproduct of representable presheaves: the shape has a type
of arguments, each lying over an object of {lit}`C`, and its directions over {lit}`c`
are the pairs of an argument and a morphism from {lit}`c` to the argument's object.
Restriction of directions precomposes the morphism. The reindexing of a restricted
shape's arity into the shape's arity, a morphism of coproducts of representables, is
determined by where it sends each argument: to an argument of the shape and a
morphism between their objects.

{lit}`FreeArity` is that data. {lit}`FreeArity.toData` assembles the operations of the
presheaf polynomial functor, of which the direction laws and the naturality of
reindexing hold for every instance ({lit}`FreeArity.directionRestr_id`,
{lit}`FreeArity.directionRestr_comp`, {lit}`FreeArity.reindex_naturality`), so an
instance supplies only the laws of its shape restriction and argument reindexing. A
node over a presheaf {lit}`Z` is then determined by the values of its arguments
({lit}`FreeArity.freeNode`), and restricting such a node restricts the argument values
along the reindexing morphisms ({lit}`FreeArity.map_freeNode`).

## Main definitions

* {lit}`FreeArity` — the shapes, their arguments and the restrictions.
* {lit}`FreeArity.Dir` — the directions, elements of the free presheaf on the
  arguments.
* {lit}`FreeArity.toData` — the operations of the presheaf polynomial functor.
* {lit}`FreeArity.toPresheaf` — the functor, from the instance-specific laws.
* {lit}`FreeArity.freeNode` — the node with given argument values.

## Main statements

* {lit}`FreeArity.directionRestr_id`, {lit}`FreeArity.directionRestr_comp`,
  {lit}`FreeArity.reindex_naturality` — the laws common to every instance.
* {lit}`FreeArity.map_freeNode` — restriction of a node with given argument values.

## References

* {cite}`Weber2007`
* {cite}`nLabParametricRightAdjoint`

## Tags

polynomial functor, presheaf, parametric right adjoint, free arity, representable
-/

set_option doc.verso true

@[expose] public section

open CategoryTheory

namespace GebProto.QuotientPRA

universe uC vC uA uB w

/-- A presheaf polynomial endofunctor over {lit}`C` with free arities: shapes over
objects, arguments over objects, the restriction of shapes along morphisms, and the
reindexing of a restricted shape's arguments into the shape's arguments. -/
structure FreeArity (C : Type uC) [Category.{vC} C] : Type (max uC vC (uA + 1) (uB + 1)) where
  /-- The shapes. -/
  A : Type uA
  /-- The object over which a shape lies. -/
  q : A → C
  /-- The arguments of a shape. -/
  Gen : A → Type uB
  /-- The object over which an argument lies. -/
  gobj : (a : A) → Gen a → C
  /-- The restriction of a shape along a morphism into its object. -/
  restr : ∀ {c c' : C}, (c' ⟶ c) → A → A
  /-- A restricted shape lies over the source of the morphism. -/
  q_restr : ∀ {c c' : C} (g : c' ⟶ c) (a : A), q a = c → q (restr g a) = c'
  /-- The reindexing of a restricted shape's arguments: an argument of the shape and a
  morphism between their objects. -/
  reindex : ∀ {c c' : C} (g : c' ⟶ c) (a : A) (b : Gen (restr g a)),
    Σ b' : Gen a, (gobj (restr g a) b ⟶ gobj a b')

namespace FreeArity

variable {C : Type uC} [Category.{vC} C] (S : FreeArity.{uC, vC, uA, uB} C)

/-- The directions of a shape: an argument with a morphism into its object, the
elements of the free presheaf on the arguments. -/
def Dir (a : S.A) : Type (max uB uC vC) := Σ b : S.Gen a, Σ c : C, (c ⟶ S.gobj a b)

/-- The restriction of a direction over {lit}`i` along a morphism {lit}`i' ⟶ i`:
precompose its morphism. -/
def restrDir (a : S.A) {i i' : C} (g : i' ⟶ i) : (d : S.Dir a) → d.2.1 = i → S.Dir a
  | ⟨b, _, k⟩, rfl => ⟨b, i', g ≫ k⟩

/-- The reindexing of the directions of a restricted shape: send the argument along
{lit}`reindex` and postcompose its morphism. -/
def reindexDir {c c' : C} (g : c' ⟶ c) (a : S.A) (d : S.Dir (S.restr g a)) : S.Dir a :=
  ⟨(S.reindex g a d.1).1, d.2.1, d.2.2 ≫ (S.reindex g a d.1).2⟩

/-- The operations of the presheaf polynomial functor. -/
def toData : PresheafPFunctorData.{uC, uC, uA, max uB uC vC, vC, vC} C C where
  A := S.A
  B := S.Dir
  r := fun x ↦ x.2.2.1
  q := S.q
  directionRestr := fun a _ i' g d ↦
    ⟨S.restrDir a g d.1 d.2, by obtain ⟨⟨b, c, k⟩, rfl⟩ := d; rfl⟩
  shapeRestr := fun _ _ g a ↦ ⟨S.restr g a.1, S.q_restr g a.1 a.2⟩
  reindex := fun _ _ g a _ d ↦ ⟨S.reindexDir g a.1 d.1, d.2⟩

/-- Restriction of directions along an identity is the identity. -/
theorem directionRestr_id : S.toData.DirectionRestrId := by
  intro a i
  funext d
  obtain ⟨⟨b, c, k⟩, rfl⟩ := d
  exact Subtype.ext (Sigma.ext rfl (heq_of_eq (Sigma.ext rfl (heq_of_eq (Category.id_comp k)))))

/-- Restriction of directions along a composite is the composite of restrictions. -/
theorem directionRestr_comp : S.toData.DirectionRestrComp := by
  intro a i i' i'' f g
  funext d
  obtain ⟨⟨b, c, k⟩, rfl⟩ := d
  exact Subtype.ext (Sigma.ext rfl (heq_of_eq (Sigma.ext rfl (heq_of_eq (Category.assoc g f k)))))

/-- Reindexing commutes with restricting directions: postcomposition commutes with
precomposition. -/
theorem reindex_naturality : S.toData.ReindexNaturality := by
  intro j j' g a i i' f
  funext d
  obtain ⟨⟨b, c, k⟩, rfl⟩ := d
  exact Subtype.ext (Sigma.ext rfl (heq_of_eq (Sigma.ext rfl
    (heq_of_eq (Category.assoc f k (S.reindex g a.1 b).2).symm))))

/-- The presheaf polynomial functor of an instance, from the laws of its shape
restriction and argument reindexing. -/
def toPresheaf (restr_id : S.toData.ShapeRestrId) (restr_comp : S.toData.ShapeRestrComp)
    (reindex_id : S.toData.ReindexId restr_id) (reindex_comp : S.toData.ReindexComp restr_comp) :
    PresheafPFunctor.{uC, uC, uA, max uB uC vC, vC, vC} C C where
  toPresheafPFunctorData := S.toData
  isFunctorial :=
    { directionRestr_id := S.directionRestr_id
      directionRestr_comp := S.directionRestr_comp
      shapeRestr_id := restr_id
      shapeRestr_comp := restr_comp
      reindex_naturality := S.reindex_naturality
      reindex_id := reindex_id
      reindex_comp := reindex_comp }

variable {S} {restr_id : S.toData.ShapeRestrId} {restr_comp : S.toData.ShapeRestrComp}
  {reindex_id : S.toData.ReindexId restr_id} {reindex_comp : S.toData.ReindexComp restr_comp}

/-- A node over a presheaf {lit}`Z` from the values of its arguments: at the direction
{lit}`⟨b, c, k⟩` it carries the restriction along {lit}`k` of the value of the argument
{lit}`b`. -/
def freeNode (Z : Cᵒᵖ ⥤ Type w) (a : S.A) {c : C} (hq : S.q a = c)
    (ts : (b : S.Gen a) → Z.obj ⟨S.gobj a b⟩) :
    ((S.toPresheaf restr_id restr_comp reindex_id reindex_comp).objPresheaf Z).obj ⟨c⟩ :=
  ⟨⟨⟨⟨a, fun d ↦ ⟨d.2.1, Z.map d.2.2.op (ts d.1)⟩⟩, rfl⟩, by
    intro i i' f d
    obtain ⟨⟨b, c, k⟩, rfl⟩ := d
    exact Functor.map_comp_apply Z k.op f.op (ts b)⟩, hq⟩

/-- Restricting a node with given argument values restricts the values along the
reindexing morphisms. -/
theorem map_freeNode (Z : Cᵒᵖ ⥤ Type w) (a : S.A) {c c' : C} (hq : S.q a = c) (g : c' ⟶ c)
    (ts : (b : S.Gen a) → Z.obj ⟨S.gobj a b⟩) :
    ((S.toPresheaf restr_id restr_comp reindex_id reindex_comp).objPresheaf Z).map g.op
        (freeNode Z a hq ts) =
      freeNode Z (S.restr g a) (S.q_restr g a hq)
        fun b ↦ Z.map (S.reindex g a b).2.op (ts (S.reindex g a b).1) := by
  refine Subtype.ext (Subtype.ext (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun d ↦ ?_)))))
  obtain ⟨b, c'', k⟩ := d
  refine Sigma.ext rfl (heq_of_eq ?_)
  change Z.map (k ≫ (S.reindex g a b).2).op (ts (S.reindex g a b).1) =
    Z.map k.op (Z.map (S.reindex g a b).2.op (ts (S.reindex g a b).1))
  exact Functor.map_comp_apply Z (S.reindex g a b).2.op k.op (ts (S.reindex g a b).1)

end FreeArity

end GebProto.QuotientPRA
