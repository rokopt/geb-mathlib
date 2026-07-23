/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Presheaf.Decidable
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.Fin.Basic

/-!
# Tests for the presheaf naturality decidability instance

A presheaf-domain polynomial functor over the preorder category on `Fin 2`,
paired with the constant `Fin 2` input presheaf, makes `IsNatural`
falsifiable: over the non-identity morphism `0 ⟶ 1` the naturality equation
forces the direction assignment to give equal values to the two directions.
A constant assignment satisfies it; an assignment recording each direction's
index refutes it.

The finite enumerations the instance consumes are supplied choice-free: a
`FinEnum (Fin 2)` from an explicit equivalence, and a `FinEnum` of the
preorder hom-sets built from a `FinEnum (PLift p)` for a decidable `p` and
stated at the `⟶` head (instance resolution does not unfold `Quiver.Hom`).

A second fixture, `wFixture`, is a presheaf polynomial endofunctor over the
same category, built so that `PresheafPFunctor.IsHereditarilyNatural` is both
inhabited and falsifiable, and exercises
`PresheafPFunctor.decidableIsHereditarilyNatural` by reduction: `hereditaryTrue`
and `hereditaryFalse` reduce to `true` and `false` respectively.

## Tags

polynomial functor, presheaf, naturality, hereditary naturality, decidability,
W-type, FinEnum
-/

set_option linter.privateModule false

open CategoryTheory PresheafDomPFunctorData

/-- A choice-free `FinEnum (Fin 2)` for the index objects, from the identity
equivalence rather than `FinEnum.fin` (which routes through `Classical.choice`). -/
instance finEnumFin2 : FinEnum (Fin 2) where
  card := 2
  equiv := Equiv.refl (Fin 2)
  decEq := inferInstance

/-- A choice-free `FinEnum (PLift p)` for a decidable proposition `p`: one
element when `p` holds, none otherwise. The equivalence laws are discharged
by case analysis (`PLift p` is a subsingleton), not `decide`. -/
instance finEnumPLift {p : Prop} [Decidable p] : FinEnum (PLift p) :=
  if h : p then
    { card := 1
      equiv :=
        { toFun := fun _ => 0
          invFun := fun _ => ⟨h⟩
          left_inv := fun x => by cases x; rfl
          right_inv := fun i => Fin.cases rfl (fun j => j.elim0) i }
      decEq := fun a b => isTrue (by cases a; cases b; rfl) }
  else
    { card := 0
      equiv :=
        { toFun := fun x => absurd x.down h
          invFun := fun i => i.elim0
          left_inv := fun x => absurd x.down h
          right_inv := fun i => i.elim0 }
      decEq := fun a _ => absurd a.down h }

/-- A choice-free `FinEnum` of a preorder hom-set, stated at the `⟶` head and
delegating to the `ULift`/`PLift` enumeration. An instance at `PLift` alone
does not fire on a goal headed by `⟶`, since `Quiver.Hom` is a `def` that
instance resolution does not unfold. -/
instance finEnumHom (i i' : Fin 2) : FinEnum (i' ⟶ i) :=
  inferInstanceAs (FinEnum (ULift (PLift (i' ≤ i))))

/-- The constant input presheaf on `(Fin 2)ᵒᵖ` at `Fin 2`, every restriction
the identity. Its two-element fiber is what makes `IsNatural` falsifiable.
Reducible so `Zfix.obj ⟨i⟩` unfolds to `Fin 2`. -/
@[reducible] def Zfix : (Fin 2)ᵒᵖ ⥤ Type where
  obj _ := Fin 2
  map _ := 𝟙 _

/-- Decidable equality of the input presheaf's fibers, needed to decide the
naturality equation. -/
instance : ∀ i : Fin 2, DecidableEq (Zfix.obj ⟨i⟩) :=
  fun _ => inferInstanceAs (DecidableEq (Fin 2))

/-- In `Fin 2`, the unique direction of shape `x` over base point `i` has
underlying value `i + x`: `x + (i + x) = i`. -/
private theorem fin2_add_idx (x i : Fin 2) : x + (i + x) = i := by omega

/-- The direction-only fixture over the preorder category on `Fin 2`: two
shapes, two directions per shape, constraint `r ⟨a, b⟩ = a + b`, and
`directionRestr` picking the unique direction of the target fiber. Only the
domain-side data is needed to state and decide `IsNatural`. -/
@[reducible] def presheafWitness : PresheafDomPFunctorData (Fin 2) where
  A := Fin 2
  B := fun _ => Fin 2
  r := fun x => x.1 + x.2
  directionRestr := fun a {_i i'} _f _b => ⟨i' + a, fin2_add_idx a i'⟩

/-- The fixture is finitary: each shape has the two directions of `Fin 2`. -/
instance finitaryPresheafWitness : presheafWitness.Finitary := fun _ => finEnumFin2

/-- A natural direction assignment: shape `0` with the constant `Fin 2`-value
`0` on both directions. Over `0 ⟶ 1` the two directions receive equal values,
so naturality holds. -/
def xGood : presheafWitness.toSliceDomPFunctor.Obj (elemProj Zfix) :=
  ⟨⟨(0 : Fin 2), fun b => ⟨(0 : Fin 2) + b, (0 : Fin 2)⟩⟩,
    (presheafWitness.toSliceDomPFunctor.compatible_iff _ _ _).mpr fun _ => rfl⟩

/-- An unnatural direction assignment: shape `0` recording each direction's
own index as its `Fin 2`-value. Over `0 ⟶ 1` the two directions receive the
distinct values `0` and `1`, refuting naturality. -/
def xBad : presheafWitness.toSliceDomPFunctor.Obj (elemProj Zfix) :=
  ⟨⟨(0 : Fin 2), fun b => ⟨(0 : Fin 2) + b, b⟩⟩,
    (presheafWitness.toSliceDomPFunctor.compatible_iff _ _ _).mpr fun _ => rfl⟩

/-- A natural direction assignment. -/
def isNaturalTrue : Bool := decide (presheafWitness.IsNatural xGood)

/-- An unnatural direction assignment. -/
def isNaturalFalse : Bool := decide (presheafWitness.IsNatural xBad)

example : isNaturalTrue = true := by decide
example : isNaturalFalse = false := by decide

/-! ## Hereditary-naturality fixture and reduction test

`wFixture` is a presheaf polynomial endofunctor over the preorder category on
`Fin 2`, built to make `PresheafPFunctor.IsHereditarilyNatural` both inhabited
and falsifiable, exercising `PresheafPFunctor.decidableIsHereditarilyNatural`
by reduction. It has a branching shape `Shp.R` with two directions over the
distinct base indices `0` and `1`, and three leaf shapes so the W-type is
inhabited and admits two distinct subtrees (`Shp.L0a`, `Shp.L0b`) over the
common index `0`. Over the non-identity morphism `0 ⟶ 1` the local naturality
equation forces the child at the restricted direction to equal the
root-restriction of its sibling; `goodTree` satisfies it and `badTree` refutes
it. The seven functor laws are proved directly: the five direction-side laws by
`Subsingleton.elim` (every direction fiber is a singleton or empty), and the two
shape-side laws from the shape-restriction combinatorics. -/

/-- A choice-free `FinEnum (Fin 0)`, from the identity equivalence rather than
`FinEnum.fin` (which routes through `Classical.choice`). Supplies the direction
enumeration of the leaf shapes. -/
instance finEnumFin0 : FinEnum (Fin 0) where
  card := 0
  equiv := Equiv.refl (Fin 0)
  decEq := inferInstance

/-- The shapes of the fixture: a branching root `R` over index `1`, a leaf `L1`
over index `1`, and two distinct leaves `L0a`, `L0b` over index `0`. -/
inductive Shp
  | R
  | L1
  | L0a
  | L0b
  deriving DecidableEq

/-- The shape-output map: `R` and `L1` are over index `1`, `L0a` and `L0b` over
index `0`. Separating the two indices is what lets a child and a sibling's
root-restriction be compared. -/
def qFix : Shp → Fin 2
  | .R => 1
  | .L1 => 1
  | .L0a => 0
  | .L0b => 0

/-- The direction type of each shape: `R` has the two directions of `Fin 2`,
every leaf has none (`Fin 0`), so the W-type is inhabited. Reducible so
`IsEmpty (Bfix s)` and `OfNat (Bfix Shp.R) 0` resolve at the concrete shapes. -/
@[reducible] def Bfix : Shp → Type
  | .R => Fin 2
  | _ => Fin 0

/-- The direction-input map: `R`'s direction `b` lies over base index `b`, so
its two directions lie over the distinct indices `0` and `1`; leaves have no
directions. -/
def rFix : (Σ a : Shp, Bfix a) → Fin 2
  | ⟨.R, b⟩ => b
  | ⟨.L1, b⟩ => b.elim0
  | ⟨.L0a, b⟩ => b.elim0
  | ⟨.L0b, b⟩ => b.elim0

/-- The shape restriction to a target index `t`: keep the shape when `t` is its
own output index, otherwise send it to the designated index-`0` leaf `L0a`. This
is the root-restriction underlying `wRestrTree`. -/
def restrShapeTo (a : Shp) (t : Fin 2) : Shp :=
  if t = qFix a then a else .L0a

/-- Every non-`R` shape is a leaf: its direction type is empty. -/
theorem bfix_leaf_empty : ∀ (s : Shp), s ≠ .R → IsEmpty (Bfix s)
  | .R, h => absurd rfl h
  | .L1, _ => inferInstanceAs (IsEmpty (Fin 0))
  | .L0a, _ => inferInstanceAs (IsEmpty (Fin 0))
  | .L0b, _ => inferInstanceAs (IsEmpty (Fin 0))

/-- The shape restriction of a leaf is a leaf: it never produces `R`. -/
theorem restr_ne_R (a : Shp) (t : Fin 2) (h : a ≠ .R) : restrShapeTo a t ≠ .R := by
  unfold restrShapeTo
  split
  · exact h
  · decide

/-- The restricted shape lies over the target index (given the index is at most
the original output index, as a restriction morphism guarantees). -/
theorem restr_over (a : Shp) (t : Fin 2) (h : t ≤ qFix a) : qFix (restrShapeTo a t) = t := by
  unfold restrShapeTo
  split
  · next heq => exact heq.symm
  · next hne =>
    have hlt : t < qFix a := lt_of_le_of_ne h hne
    have ht0 : t = 0 := by omega
    subst ht0
    rfl

/-- Restriction to a shape's own output index is the identity. -/
theorem restr_self (a : Shp) : restrShapeTo a (qFix a) = a :=
  if_pos rfl

/-- The shape restriction is functorial in the index. -/
theorem restr_comp (a : Shp) (s t : Fin 2) (hts : t ≤ s) (hs : s ≤ qFix a) :
    restrShapeTo a t = restrShapeTo (restrShapeTo a s) t := by
  by_cases hsq : s = qFix a
  · rw [show restrShapeTo a s = a from if_pos hsq]
  · have hlt : s < qFix a := lt_of_le_of_ne hs hsq
    have ht0 : t = 0 := by omega
    have hqa : qFix a = 1 := by omega
    have hL : restrShapeTo a t = Shp.L0a := by
      unfold restrShapeTo; rw [ht0, hqa]; exact if_neg (by decide)
    have hR : restrShapeTo (restrShapeTo a s) t = Shp.L0a := by
      rw [show restrShapeTo a s = Shp.L0a from if_neg hsq]
      unfold restrShapeTo; exact ite_self _
    rw [hL, hR]

/-- The operations of the fixture endofunctor. `directionRestr` picks the unique
direction over the target index (leaves have none); `shapeRestr` uses
`restrShapeTo` with the target-index proof from the restriction morphism;
`reindex` is total but its value is unconstrained, every `reindex` law holding by
`Subsingleton.elim`. -/
@[reducible] def wFixtureData : PresheafPFunctorData (Fin 2) (Fin 2) where
  A := Shp
  B := Bfix
  r := rFix
  q := qFix
  directionRestr := fun a {i i'} _g d => by
    cases a with
    | R => exact ⟨i', rfl⟩
    | L1 => exact d.1.elim0
    | L0a => exact d.1.elim0
    | L0b => exact d.1.elim0
  shapeRestr := fun {j j'} g s =>
    ⟨restrShapeTo s.1 j', restr_over s.1 j' (by
      have hs : qFix s.1 = j := s.2
      rw [hs]; exact leOfHom g)⟩
  reindex := fun {j j'} _g a {i} d => by
    obtain ⟨as, has⟩ := a
    cases as with
    | R => exact ⟨i, rfl⟩
    | L1 => exact (bfix_leaf_empty _ (restr_ne_R .L1 j' (by decide))).elim d.1
    | L0a => exact (bfix_leaf_empty _ (restr_ne_R .L0a j' (by decide))).elim d.1
    | L0b => exact (bfix_leaf_empty _ (restr_ne_R .L0b j' (by decide))).elim d.1

/-- Every direction fiber of the fixture is a subsingleton: `R`'s direction over
`i` is unique (its input map is the identity on `Fin 2`), and leaves have none.
This discharges the five direction-side functor laws. -/
instance subsingletonDirection (a : Shp) (i : Fin 2) :
    Subsingleton (wFixtureData.toSliceDomPFunctor.Direction a i) := by
  cases a with
  | R => exact ⟨fun x y => Subtype.ext (show x.1 = y.1 from x.2.trans y.2.symm)⟩
  | L1 => exact ⟨fun x _ => x.1.elim0⟩
  | L0a => exact ⟨fun x _ => x.1.elim0⟩
  | L0b => exact ⟨fun x _ => x.1.elim0⟩

/-- The fixture endofunctor: the operations with the seven functor laws. The
direction-side laws hold by `Subsingleton.elim`; the shape-side laws by
`restr_self` and `restr_comp`. -/
@[reducible] def wFixture : PresheafPFunctor (Fin 2) (Fin 2) where
  toPresheafPFunctorData := wFixtureData
  isFunctorial :=
    { directionRestr_id := by intro a i; funext b; exact Subsingleton.elim _ _
      directionRestr_comp := by intro a i i' i'' f g; funext b; exact Subsingleton.elim _ _
      shapeRestr_id := by
        intro j; funext s
        obtain ⟨a0, ha0⟩ := s
        refine Subtype.ext ?_
        change restrShapeTo a0 j = a0
        have hq : qFix a0 = j := ha0
        rw [← hq]
        exact restr_self a0
      shapeRestr_comp := by
        intro j j' j'' g h; funext s
        refine Subtype.ext ?_
        change restrShapeTo s.1 j'' = restrShapeTo (restrShapeTo s.1 j') j''
        refine restr_comp s.1 j' j'' (leOfHom h) ?_
        have hs : qFix s.1 = j := s.2
        rw [hs]; exact leOfHom g
      reindex_naturality := by intro j j' g a i i' f; funext d; exact Subsingleton.elim _ _
      reindex_id := by intro j a i b; exact Subsingleton.elim _ _
      reindex_comp := by intro j j' j'' g h a i b; exact Subsingleton.elim _ _ }

/-- The fixture is finitary: `R` has the two directions of `Fin 2`, each leaf
none. Supplies `PresheafPFunctor.decidableIsHereditarilyNatural`. -/
instance finitaryWFixture : wFixture.Finitary := by
  intro a
  cases a with
  | R => exact finEnumFin2
  | L1 => exact finEnumFin0
  | L0a => exact finEnumFin0
  | L0b => exact finEnumFin0

/-- A leaf W-tree of the fixture at a shape with no directions. -/
def leafTree (s : Shp) [IsEmpty (Bfix s)] : wFixture.toSlicePFunctor.W :=
  SlicePFunctor.W.mk ⟨⟨s, fun b => isEmptyElim b⟩,
    (wFixture.toSliceDomPFunctor.compatible_iff _ s _).mpr fun b => isEmptyElim b⟩

/-- The hereditarily-natural tree: root `R` with the index-`0` child `L0a` (the
root-restriction of the index-`1` child `L1` along `0 ⟶ 1`) and the index-`1`
child `L1`. -/
def goodTree : wFixture.toSlicePFunctor.W :=
  SlicePFunctor.W.mk
    ⟨⟨.R, fun b => if b = 0 then leafTree .L0a else leafTree .L1⟩,
      (wFixture.toSliceDomPFunctor.compatible_iff _ .R _).mpr
        (fun b => Fin.cases rfl (fun i => Fin.cases rfl (fun j => j.elim0) i) b)⟩

/-- The tree failing naturality at the root: the index-`0` child is `L0b`, which
differs from the root-restriction `L0a` of the index-`1` child `L1`. -/
def badTree : wFixture.toSlicePFunctor.W :=
  SlicePFunctor.W.mk
    ⟨⟨.R, fun b => if b = 0 then leafTree .L0b else leafTree .L1⟩,
      (wFixture.toSliceDomPFunctor.compatible_iff _ .R _).mpr
        (fun b => Fin.cases rfl (fun i => Fin.cases rfl (fun j => j.elim0) i) b)⟩

/-- A hereditarily natural tree. -/
def hereditaryTrue : Bool := decide (wFixture.IsHereditarilyNatural goodTree)

/-- A tree failing naturality at one node. -/
def hereditaryFalse : Bool := decide (wFixture.IsHereditarilyNatural badTree)

example : hereditaryTrue = true := by decide
example : hereditaryFalse = false := by decide
