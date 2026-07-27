/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.Finite.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Fin.Basic

/-!
# Shared fixtures for the presheaf `PFunctor` tests

The concrete presheaf polynomial endofunctor over the preorder category on
`Fin 2` that the presheaf test modules share, together with the choice-free
`FinEnum` evidence its decision procedures consume. Defined once here rather
than repeated per module so every test module exercises the same object.

`wFixture` is built so that `PresheafPFunctor.IsHereditarilyNatural` is both
inhabited and falsifiable: a branching shape `Shp.R` with two directions over
the distinct base indices `0` and `1`, and three leaf shapes, so the W-type is
inhabited and admits two distinct subtrees (`Shp.L0a`, `Shp.L0b`) over the
common index `0`. Over the non-identity morphism `0 ⟶ 1` the local naturality
equation forces the child at the restricted direction to equal the
root-restriction of its sibling; `goodTree` satisfies it and `badTree` refutes
it.

## Main definitions

* `zFix` — the constant `Fin 2` input presheaf, whose two-element fiber makes
  `IsNatural` falsifiable.
* `Shp` / `qFix` / `BFix` / `rFix` / `restrShapeTo` — the fixture's shapes,
  output indices, directions, input indices, and root restriction.
* `wFixture` — the fixture endofunctor, the operations with the seven functor
  laws.
* `finiteWFixture` — `wFixture` bundled with its finiteness evidence as a
  `FinitePresheafPFunctor`.
* `leafTree` / `goodTree` / `badTree` — the W-trees the reduction tests use.

## Implementation notes

The `FinEnum` instances are built from explicit equivalences rather than from
mathlib's `FinEnum.fin`, which routes through `Classical.choice`. The hom-set
enumeration is stated at the `⟶` head: an instance at `PLift` alone does not
fire on a goal headed by `⟶`, since `Quiver.Hom` is a `def` that instance
resolution does not unfold.

`finitaryWFixture` is a `def` rather than an `instance` so that the forwarding
instances on `FinitePresheafPFunctor` are exercised by the `Finite` test
modules rather than the general-tier instances; a module wanting the
general-tier behaviour installs it locally.

## Tags

polynomial functor, presheaf, fixture, W-type, FinEnum
-/

-- The fixtures must be `@[expose]`d so their shape and direction types unfold
-- across the module boundary, which is what lets the importing modules'
-- `decide` tests reduce; `expose` is meaningful on public definitions only.
@[expose] public section

open CategoryTheory

namespace PresheafFixture

/-! ## Choice-free `FinEnum` evidence -/

/-- A choice-free `FinEnum (Fin 2)` for the index objects, from the identity
equivalence rather than `FinEnum.fin` (which routes through
`Classical.choice`). -/
instance finEnumFin2 : FinEnum (Fin 2) where
  card := 2
  equiv := Equiv.refl (Fin 2)
  decEq := inferInstance

/-- A choice-free `FinEnum (Fin 0)`, from the identity equivalence. Supplies the
direction enumeration of the leaf shapes. -/
instance finEnumFin0 : FinEnum (Fin 0) where
  card := 0
  equiv := Equiv.refl (Fin 0)
  decEq := inferInstance

/-- A choice-free `FinEnum (PLift p)` for a decidable proposition `p`: one
element when `p` holds, none otherwise. The equivalence laws are discharged by
case analysis (`PLift p` is a subsingleton), not `decide`. -/
instance finEnumPLift {p : Prop} [Decidable p] : FinEnum (PLift p) :=
  if h : p then
    { card := 1
      equiv :=
        { toFun := fun _ ↦ 0
          invFun := fun _ ↦ ⟨h⟩
          left_inv := fun x ↦ by cases x; rfl
          right_inv := fun i ↦ Fin.cases rfl (fun j ↦ j.elim0) i }
      decEq := fun a b ↦ isTrue (by cases a; cases b; rfl) }
  else
    { card := 0
      equiv :=
        { toFun := fun x ↦ absurd x.down h
          invFun := fun i ↦ i.elim0
          left_inv := fun x ↦ absurd x.down h
          right_inv := fun i ↦ i.elim0 }
      decEq := fun a _ ↦ absurd a.down h }

/-- A choice-free `FinEnum` of a preorder hom-set, stated at the `⟶` head and
delegating to the `ULift`/`PLift` enumeration. -/
instance finEnumHom (i i' : Fin 2) : FinEnum (i' ⟶ i) :=
  inferInstanceAs (FinEnum (ULift (PLift (i' ≤ i))))

/-! ## The input presheaf -/

/-- The constant input presheaf on `(Fin 2)ᵒᵖ` at `Fin 2`, every restriction the
identity. Its two-element fiber is what makes `IsNatural` falsifiable. Reducible
so `zFix.obj ⟨i⟩` unfolds to `Fin 2`. -/
@[reducible] def zFix : (Fin 2)ᵒᵖ ⥤ Type where
  obj _ := Fin 2
  map _ := 𝟙 _

/-- Decidable equality of the input presheaf's fibers, needed to decide the
naturality equation. -/
instance decidableEqZFixObj : ∀ i : Fin 2, DecidableEq (zFix.obj ⟨i⟩) :=
  fun _ ↦ inferInstanceAs (DecidableEq (Fin 2))

/-! ## The fixture endofunctor -/

/-- The shapes of the fixture: a branching root `R` over index `1`, a leaf `L1`
over index `1`, and two distinct leaves `L0a`, `L0b` over index `0`. -/
inductive Shp
  | R
  | L1
  | L0a
  | L0b
  deriving DecidableEq

/-- A choice-free `FinEnum Shp`: four constructors mapped to `Fin 4`. -/
instance finEnumShp : FinEnum Shp where
  card := 4
  equiv :=
    { toFun := fun s ↦ match s with
        | .R => 0
        | .L1 => 1
        | .L0a => 2
        | .L0b => 3
      invFun := fun i ↦
        Fin.cases .R
          (Fin.cases .L1
            (Fin.cases .L0a
              (Fin.cases .L0b fun j ↦ j.elim0))) i
      left_inv := fun s ↦ by cases s <;> rfl
      right_inv := fun i ↦
        Fin.cases rfl
          (Fin.cases rfl
            (Fin.cases rfl
              (Fin.cases rfl fun j ↦ j.elim0))) i }
  decEq := inferInstance

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
`IsEmpty (BFix s)` and `OfNat (BFix Shp.R) 0` resolve at the concrete shapes. -/
@[reducible] def BFix : Shp → Type
  | .R => Fin 2
  | _ => Fin 0

/-- The direction-input map: `R`'s direction `b` lies over base index `b`, so its
two directions lie over the distinct indices `0` and `1`; leaves have no
directions. -/
def rFix : (Σ a : Shp, BFix a) → Fin 2
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
theorem bFix_leaf_empty : ∀ (s : Shp), s ≠ .R → IsEmpty (BFix s)
  | .R, h => absurd rfl h
  | .L1, _ => inferInstanceAs (IsEmpty (Fin 0))
  | .L0a, _ => inferInstanceAs (IsEmpty (Fin 0))
  | .L0b, _ => inferInstanceAs (IsEmpty (Fin 0))

/-- The shape restriction of a leaf is a leaf: it never produces `R`. -/
theorem restr_ne_r (a : Shp) (t : Fin 2) (h : a ≠ .R) : restrShapeTo a t ≠ .R := by
  unfold restrShapeTo
  split
  · exact h
  · decide

/-- The restricted shape lies over the target index (given the index is at most
the original output index, as a restriction morphism guarantees). -/
theorem restr_over (a : Shp) (t : Fin 2) (h : t ≤ qFix a) :
    qFix (restrShapeTo a t) = t := by
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
  B := BFix
  r := rFix
  q := qFix
  directionRestr := fun a {i i'} _g d ↦ by
    cases a with
    | R => exact ⟨i', rfl⟩
    | L1 => exact d.1.elim0
    | L0a => exact d.1.elim0
    | L0b => exact d.1.elim0
  shapeRestr := fun {j j'} g s ↦
    ⟨restrShapeTo s.1 j', restr_over s.1 j' (by
      have hs : qFix s.1 = j := s.2
      rw [hs]; exact leOfHom g)⟩
  reindex := fun {j j'} _g a {i} d ↦ by
    obtain ⟨as, has⟩ := a
    cases as with
    | R => exact ⟨i, rfl⟩
    | L1 => exact (bFix_leaf_empty _ (restr_ne_r .L1 j' (by decide))).elim d.1
    | L0a => exact (bFix_leaf_empty _ (restr_ne_r .L0a j' (by decide))).elim d.1
    | L0b => exact (bFix_leaf_empty _ (restr_ne_r .L0b j' (by decide))).elim d.1

/-- Every direction fiber of the fixture is a subsingleton: `R`'s direction over
`i` is unique (its input map is the identity on `Fin 2`), and leaves have none.
This discharges the five direction-side functor laws. -/
instance subsingletonDirection (a : Shp) (i : Fin 2) :
    Subsingleton (wFixtureData.toSliceDomPFunctor.Direction a i) := by
  cases a with
  | R => exact ⟨fun x y ↦ Subtype.ext (show x.1 = y.1 from x.2.trans y.2.symm)⟩
  | L1 => exact ⟨fun x _ ↦ x.1.elim0⟩
  | L0a => exact ⟨fun x _ ↦ x.1.elim0⟩
  | L0b => exact ⟨fun x _ ↦ x.1.elim0⟩

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

set_option warn.classDefReducibility false in
/-- The fixture is finitary: `R` has the two directions of `Fin 2`, each leaf
none. A `def` rather than an `instance`; see the module's implementation
notes. -/
def finitaryWFixture : wFixture.toPFunctor.Finitary := by
  intro a
  cases a with
  | R => exact finEnumFin2
  | L1 => exact finEnumFin0
  | L0a => exact finEnumFin0
  | L0b => exact finEnumFin0

/-- The `wFixture` bundled as a `FinitePresheafPFunctor (Fin 2) (Fin 2)` with its
finiteness evidence. Reducible so instance resolution can unfold it and the
`decide` tactic reduces through the forwarding instances. -/
@[reducible] def finiteWFixture : FinitePresheafPFunctor (Fin 2) (Fin 2) where
  toPresheafPFunctor := wFixture
  finEnumI := finEnumFin2
  finEnumHomI := finEnumHom
  finEnumJ := finEnumFin2
  finEnumA := finEnumShp
  finitary := finitaryWFixture

/-! ## W-tree fixtures -/

/-- A leaf W-tree of the fixture at a shape with no directions. -/
def leafTree (s : Shp) [IsEmpty (BFix s)] : wFixture.toSlicePFunctor.W :=
  SlicePFunctor.W.mk ⟨⟨s, fun b ↦ isEmptyElim b⟩,
    (wFixture.toSliceDomPFunctor.compatible_iff _ s _).mpr fun b ↦ isEmptyElim b⟩

/-- The hereditarily-natural tree: root `R` with the index-`0` child `L0a` (the
root-restriction of the index-`1` child `L1` along `0 ⟶ 1`) and the index-`1`
child `L1`. -/
def goodTree : wFixture.toSlicePFunctor.W :=
  SlicePFunctor.W.mk
    ⟨⟨.R, fun b ↦ if b = 0 then leafTree .L0a else leafTree .L1⟩,
      (wFixture.toSliceDomPFunctor.compatible_iff _ .R _).mpr
        (fun b ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun j ↦ j.elim0) i) b)⟩

/-- The tree failing naturality at the root: the index-`0` child is `L0b`, which
differs from the root-restriction `L0a` of the index-`1` child `L1`. -/
def badTree : wFixture.toSlicePFunctor.W :=
  SlicePFunctor.W.mk
    ⟨⟨.R, fun b ↦ if b = 0 then leafTree .L0b else leafTree .L1⟩,
      (wFixture.toSliceDomPFunctor.compatible_iff _ .R _).mpr
        (fun b ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun j ↦ j.elim0) i) b)⟩

/-- An inadmissible tree: a raw `WType` whose root shape is `R` but whose child
at direction `0` has shape `L1` (over index `1`), while `rFix ⟨.R, 0⟩ = 0`
requires the child to be over index `0`. A well-formed `WType` that fails
`WValid`. -/
def inadmissibleTree : WType BFix :=
  WType.mk .R
    (fun b ↦ if b = 0 then WType.mk .L1 (fun c ↦ c.elim0)
             else WType.mk .L0a (fun c ↦ c.elim0))

end PresheafFixture
