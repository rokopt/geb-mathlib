/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Presheaf.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.Fin.Basic

/-!
# Tests for the presheaf-domain polynomial functor core
-/

set_option linter.privateModule false

open CategoryTheory PresheafDomPFunctorData

-- A caller can name the law condition to state things of that type.
example {I : Type} [Category I] (F : PresheafDomPFunctor I) : F.DirectionRestrComp :=
  F.isFunctorial.directionRestr_comp

-- `obj` is the `IsNatural` subtype of the slice object on `elemProj Z`.
example {I : Type} [Category I] (F : PresheafDomPFunctor I) (Z : Iᵒᵖ ⥤ Type) :
    F.obj Z = { x : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj Z)
      // F.IsNatural x } := rfl

-- `map` of the hand-built identity transformation is the identity, by
-- `map_id`. The identity transformation is hand-built (not `NatTrans.id`)
-- to stay choice-free.
example {I : Type} [Category I] (F : PresheafDomPFunctor I) (Z : Iᵒᵖ ⥤ Type) :
    F.map { app := fun i ↦ 𝟙 (Z.obj i), naturality := fun _ _ _ ↦ rfl } =
      (id : F.obj Z → F.obj Z) := F.map_id Z

-- The full bundle projects the inherited dom law and names a `J`-side law.
example {I J : Type} [Category I] [Category J] (F : PresheafPFunctor I J) :
    F.DirectionRestrComp := F.isFunctorial.directionRestr_comp
example {I J : Type} [Category I] [Category J] (F : PresheafPFunctor I J) :
    F.ShapeRestrComp := F.isFunctorial.shapeRestr_comp

-- The output presheaf's fibre over `j` is the `q`-indexed subtype of the dom
-- functor's value on `Z`.
example {I J : Type} [Category I] [Category J] (F : PresheafPFunctor I J)
    (Z : Iᵒᵖ ⥤ Type) (j : J) :
    (F.objPresheaf Z).obj ⟨j⟩ =
      { z : F.toPresheafDomPFunctorData.obj Z // F.q z.1.1.1 = j } := rfl

-- The dom morphism map is natural with respect to `objPresheaf`'s
-- `J`-restriction: `map α` commutes with `objRestr g`, preserving the
-- `q`-output index.
example {I J : Type} [Category I] [Category J] (F : PresheafPFunctor I J)
    {Z Z' : Iᵒᵖ ⥤ Type} (α : NatTrans Z Z') ⦃j j' : J⦄ (g : j' ⟶ j)
    (x : F.toPresheafDomPFunctorData.obj Z) (hq : F.q x.1.1.1 = j) :
    F.toPresheafDomPFunctorData.map α (F.objRestr g x hq) =
      F.objRestr g (F.toPresheafDomPFunctorData.map α x) hq :=
  F.map_objRestr α g x hq

-- The preorder category on `Fin 2` has a genuine non-identity morphism.
example : ((0 : Fin 2) ⟶ 1) := homOfLE (by decide)

/-- In `Fin 2`, the unique direction of shape `x` over base point `i` has
underlying value `i + x`: `x + (i + x) = i`. -/
private theorem fin2_add_idx (x i : Fin 2) : x + (i + x) = i := by omega

/-- A concrete presheaf polynomial functor over the preorder category on
`Fin 2` (for both index categories). Two shapes (`A := Fin 2`), with output
index assigned by `q := id` so each shape lies over its own object, two
directions per shape (`B _ := Fin 2`), and constraint `r ⟨a, b⟩ = a + b`. Each
fibre `Direction a i` is the singleton `{a + i}`, so `directionRestr`,
`shapeRestr`, and `reindex` each pick out the unique element of the target
fibre. `reindex` along the non-identity `0 ⟶ 1` reindexes the shape (via
`shapeRestr`) from `1` to `0` and maps the underlying direction value to
`i + a.1` (here `1 = 0 + 1`). -/
@[reducible] def presheafWitnessData : PresheafPFunctorData (Fin 2) (Fin 2) where
  A := Fin 2
  B := fun _ ↦ Fin 2
  r := fun x ↦ x.1 + x.2
  q := id
  directionRestr := fun a {_i i'} _f _b ↦ ⟨i' + a, fin2_add_idx a i'⟩
  shapeRestr := fun {_j j'} _g _s ↦ ⟨j', rfl⟩
  reindex := fun {_j _j'} _g a {i} _b ↦ ⟨i + a.1, fin2_add_idx a.1 i⟩

/-- The constraint `r ⟨a, ·⟩ = a + ·` is injective, so each fibre
`Direction a i` has at most one element. -/
private theorem fin2_direction_cancel (a x y i : Fin 2) (hx : a + x = i) (hy : a + y = i) :
    x = y := by omega

/-- Each direction fibre of the witness is a singleton. -/
private instance subsingleton_direction (a i : Fin 2) :
    Subsingleton (presheafWitnessData.toSliceDomPFunctor.Direction a i) :=
  ⟨fun x y ↦ Subtype.ext (fin2_direction_cancel a x.1 y.1 i x.2 y.2)⟩

/-- Each shape fibre of the witness is a singleton (the shape-output map
`q = id` separates the two shapes). -/
private instance subsingleton_shape (j : Fin 2) :
    Subsingleton (presheafWitnessData.toSlicePFunctor.Shape j) :=
  ⟨fun x y ↦ Subtype.ext (by
    have hx : (x.1 : Fin 2) = j := x.2
    have hy : (y.1 : Fin 2) = j := y.2
    exact hx.trans hy.symm)⟩

/-- The witness, with all seven functor laws discharged. Because every
direction fibre and shape fibre is a singleton, each law equates elements of
(functions into) a subsingleton, so `Subsingleton.elim` closes every goal;
in particular the `cast`-transport laws `reindex_id` / `reindex_comp` hold
without computing the transports. -/
def presheafWitness : PresheafPFunctor (Fin 2) (Fin 2) where
  toPresheafPFunctorData := presheafWitnessData
  isFunctorial :=
    { directionRestr_id := by intro a i; funext b; exact Subsingleton.elim _ _
      directionRestr_comp := by intro a i i' i'' f g; funext b; exact Subsingleton.elim _ _
      shapeRestr_id := by intro j; funext s; exact Subsingleton.elim _ _
      shapeRestr_comp := by intro j j' j'' g h; funext s; exact Subsingleton.elim _ _
      reindex_naturality := by intro j j' g a i i' f; funext b; exact Subsingleton.elim _ _
      reindex_id := by intro j a i b; exact Subsingleton.elim _ _
      reindex_comp := by intro j j' j'' g h a i b; exact Subsingleton.elim _ _ }

/-- The non-identity morphism `0 ⟶ 1` in the preorder category on `Fin 2`,
used by the computational examples. -/
private def h01 : (0 : Fin 2) ⟶ 1 := homOfLE (by decide)

-- The direction-input map computes as `a + b`.
example : presheafWitness.r ⟨(0 : Fin 2), (1 : Fin 2)⟩ = 1 := rfl
example : presheafWitness.r ⟨(1 : Fin 2), (1 : Fin 2)⟩ = 0 := rfl

-- The shape-output map is the identity, so each shape lies over its own object.
example : presheafWitness.q (0 : Fin 2) = 0 := rfl
example : presheafWitness.q (1 : Fin 2) = 1 := rfl

-- `shapeRestr` along the non-identity `0 ⟶ 1` reindexes shape `1` to shape `0`.
example : (presheafWitness.shapeRestr h01 ⟨(1 : Fin 2), rfl⟩).1 = (0 : Fin 2) := rfl

-- `directionRestr` along `0 ⟶ 1` sends the unique direction of shape `0` over `1` to the
-- unique direction over `0`.
example : (presheafWitness.directionRestr (0 : Fin 2) h01 ⟨(1 : Fin 2), rfl⟩).1 = (0 : Fin 2) := rfl

-- `reindex` along `0 ⟶ 1` moves the underlying direction value: the
-- direction of value `0` over `i = 0` (for shape `0`, the image of shape `1`
-- under `shapeRestr`) is reindexed to the direction of value `1` over `i = 0`
-- (for shape `1`). (With singleton fibres the target value is forced by the
-- constraint; a non-degenerate witness would be needed to discriminate a
-- wrong `reindex`.)
example :
    (presheafWitness.reindex h01 ⟨(1 : Fin 2), rfl⟩ (i := (0 : Fin 2)) ⟨(0 : Fin 2), rfl⟩).1 =
      (1 : Fin 2) := rfl

-- The output presheaf's fibre over `j` is the `q`-indexed subtype of `obj Z`.
example (Z : (Fin 2)ᵒᵖ ⥤ Type) :
    (presheafWitness.objPresheaf Z).obj ⟨(0 : Fin 2)⟩ =
      { z : presheafWitness.toPresheafDomPFunctorData.obj Z //
        presheafWitness.q z.1.1.1 = (0 : Fin 2) } :=
  rfl

-- `map` of a composite transformation acts as the composite of the maps.
example {I : Type} [Category I] (F : PresheafDomPFunctor I) {Z Z' Z'' : Iᵒᵖ ⥤ Type}
    (α : NatTrans Z Z') (β : NatTrans Z' Z'') :
    F.map { app := fun i ↦ α.app i ≫ β.app i, naturality := fun _ _ g ↦
        (by rw [← Category.assoc, α.naturality, Category.assoc, β.naturality,
          ← Category.assoc]) } =
      F.map β ∘ F.map α := F.map_comp α β

-- The reindex identity and composition laws project from `PresheafPFunctor.isFunctorial`.
example {I J : Type} [Category I] [Category J] (F : PresheafPFunctor I J) :
    F.ReindexId F.isFunctorial.shapeRestr_id := F.isFunctorial.reindex_id
example {I J : Type} [Category I] [Category J] (F : PresheafPFunctor I J) :
    F.ReindexComp F.isFunctorial.shapeRestr_comp := F.isFunctorial.reindex_comp

/-- A concrete choice-free input presheaf: the constant presheaf on `(Fin 2)ᵒᵖ`
at `PUnit`. Every fibre is `PUnit` and every restriction is the identity, so any
direction assignment over it is natural. Reducible so the `PUnit` fibre's
`Subsingleton` instance resolves through `.obj`. -/
@[reducible] private def constPUnit : (Fin 2)ᵒᵖ ⥤ Type where
  obj _ := PUnit
  map _ := 𝟙 _

/-- A concrete element of `objPresheaf constPUnit`'s fibre over `1`: shape `1`
(with output index `1`, since `q = id`) with the compatibility-forced assignment
`b ↦ ⟨1 + b, ⟨⟩⟩` of directions to total-space elements. -/
private def constFiberElt :
    (presheafWitness.objPresheaf constPUnit).obj ⟨(1 : Fin 2)⟩ :=
  ⟨⟨⟨⟨(1 : Fin 2), fun (b : Fin 2) ↦ ⟨1 + b, ⟨⟩⟩⟩,
      (presheafWitness.toSliceDomPFunctor.compatible_iff _ _ _).mpr fun _ ↦ rfl⟩,
      fun _ _ _ _ ↦ Subsingleton.elim _ _⟩,
    rfl⟩

-- `objPresheaf.map` along `h01.op` reindexes the shape `1` to `0` (the
-- `shapeRestr` action), end to end through `objRestr` / `objRestrElt`.
example :
    ((presheafWitness.objPresheaf constPUnit).map h01.op constFiberElt).1.1.1.1 =
      (0 : Fin 2) := rfl

-- `objPresheaf.map` reindexes the assignment: the reindexed element sends direction
-- `b'` to a total-space element whose base index is `reindex`-and-compatibility
-- determined (`b' + 1` under `reindex`, then `1 + (b' + 1) = b'`).
example :
    (((presheafWitness.objPresheaf constPUnit).map h01.op constFiberElt).1.1.1.2
        (0 : Fin 2)).1 = (0 : Fin 2) := rfl
example :
    (((presheafWitness.objPresheaf constPUnit).map h01.op constFiberElt).1.1.1.2
        (1 : Fin 2)).1 = (1 : Fin 2) := rfl

-- `objRestrElt` generalizes over the projection: it applies at any `p : X → I`,
-- not only `elemProj Z`. Here `p` is a constant map on `PUnit`.
example (g : (0 : Fin 2) ⟶ 1)
    (x : presheafWitness.toSliceDomPFunctor.Obj (fun _ : PUnit ↦ (1 : Fin 2)))
    (hq : presheafWitness.q x.1.1 = 1) :
    presheafWitness.toSliceDomPFunctor.Obj (fun _ : PUnit ↦ (1 : Fin 2)) :=
  presheafWitness.objRestrElt g x hq

/-!
## Non-degenerate witness

`presheafWitness` has singleton direction and shape fibres, so every functor
law equates elements of a subsingleton and `Subsingleton.elim` closes each
goal; no test can distinguish a correct `reindex` / `shapeRestr` / cast-transport
from a buggy one. The witness below breaks both degeneracies. The index
category is `Fin 1`: its only morphism is `𝟙`, so `directionRestr` is forced to be the
identity transport and `directionRestr_id` / `directionRestr_comp` / `reindex_naturality` are
immediate, while each direction fibre `Direction a 0` carries the two elements
of `Fin 2` (non-singleton directions). The output category is `Fin 3` with its
preorder `Category` instance (`0 ⟶ 1 ⟶ 2`), giving a genuine composite of two
non-identity morphisms for `shapeRestr_comp` / `reindex_comp`. Four shapes
(`Fin 4`) with output index `![0, 0, 1, 2]` place two shapes over output index
`0` (non-singleton shape fibre). `shapeRestr` is the identity on the diagonal
and the chosen representative `repOf2` off it; `reindex` swaps the two
directions exactly across the `0`-to-positive output-index boundary. All
seven laws are discharged without
`Subsingleton.elim`: the two `reindex` cast-transport laws reduce to the
underlying `Fin 2` value via `cast_dir_val2` and the `reindexVal2` identity /
composition lemmas.
-/

/-- Shape-output map of the non-degenerate witness: shapes `0, 1` over output
index `0`, shape `2` over output index `1`, shape `3` over output index `2`.
Written arithmetically (rather than as a `Matrix` literal `![0, 0, 1, 2]`) so
that the discriminating examples reduce by `decide`. -/
private def qVal2 (i : Fin 4) : Fin 3 := ⟨i.val - 1, by omega⟩

/-- A chosen shape over each output index, the off-diagonal target of
`shapeRestr` (`0, 2, 3` over output indices `0, 1, 2`). Written arithmetically
for the same reason as `qVal2`. -/
private def repOf2 (j : Fin 3) : Fin 4 := ⟨if j.val = 0 then 0 else j.val + 1, by split <;> omega⟩

/-- Underlying shape map of `shapeRestr` for a morphism with target output
index `j'` and source output index `j`: the identity on the diagonal, the
representative `repOf2 j'` off it. -/
private def shapeRestrVal2 (j' j : Fin 3) (x : Fin 4) : Fin 4 :=
  if j' = j then x else repOf2 j'

/-- The representatives lie over their output indices. -/
private theorem repOf2_output : ∀ j' : Fin 3, qVal2 (repOf2 j') = j' := by decide

/-- `shapeRestrVal2` preserves the shape-output map. -/
private theorem shapeRestrVal2_output (j' j : Fin 3) (x : Fin 4) (hx : qVal2 x = j) :
    qVal2 (shapeRestrVal2 j' j x) = j' := by
  unfold shapeRestrVal2
  split
  · next h => rw [hx]; exact h.symm
  · next _ => exact repOf2_output j'

/-- `shapeRestrVal2` along an output-index-fixing morphism is the identity. -/
private theorem shapeRestrVal2_self :
    ∀ (j : Fin 3) (x : Fin 4), shapeRestrVal2 j j x = x := by decide

/-- Composition law for the underlying shape map, along a chain `j'' ≤ j' ≤ j`. -/
private theorem shapeRestrVal2_comp : ∀ (j'' j' j : Fin 3), j'' ≤ j' → j' ≤ j → ∀ x : Fin 4,
    shapeRestrVal2 j'' j x = shapeRestrVal2 j'' j' (shapeRestrVal2 j' j x) := by decide

/-- Underlying value map of `reindex` for a morphism with source output index
`j'` and target output index `j`: the swap of the two directions across the
`0`-to-positive output-index boundary, the identity otherwise. -/
private def reindexVal2 (j' j : Fin 3) : Fin 2 → Fin 2 :=
  if j' = 0 ∧ j ≠ 0 then Fin.rev else id

/-- `reindexVal2` is the identity along an output-index-fixing morphism. -/
private theorem reindexVal2_id (j : Fin 3) (x : Fin 2) : reindexVal2 j j x = x := by
  rw [reindexVal2, if_neg (fun h ↦ h.2 h.1)]
  rfl

/-- Composition law for the value map, along a chain `j'' ≤ j' ≤ j`. -/
private theorem reindexVal2_comp : ∀ (j'' j' j : Fin 3), j'' ≤ j' → j' ≤ j → ∀ x : Fin 2,
    reindexVal2 j'' j x = reindexVal2 j' j (reindexVal2 j'' j' x) := by decide

/-- The non-degenerate witness operations. The index category `Fin 1` forces
`directionRestr` to be the identity transport; the output category `Fin 3`
(preorder) carries a length-two composite; `qVal2` gives a non-singleton shape
fibre over output index `0`; `B _ = Fin 2` and `r _ = 0` give non-singleton
direction fibres. -/
def presheafWitness2Data : PresheafPFunctorData (Fin 1) (Fin 3) where
  A := Fin 4
  B := fun _ ↦ Fin 2
  r := fun _ ↦ 0
  q := qVal2
  directionRestr := fun _a {_i i'} _f b ↦ ⟨b.1, (Fin.fin_one_eq_zero i').symm⟩
  shapeRestr := fun {j j'} _g a ↦ ⟨shapeRestrVal2 j' j a.1, shapeRestrVal2_output j' j a.1 a.2⟩
  reindex := fun {j j'} _g _a {i} b ↦ ⟨reindexVal2 j' j b.1, (Fin.fin_one_eq_zero i).symm⟩

/-- The underlying value of a direction cast along a shape equality is the
underlying value of the original. A local, `Subsingleton`-free counterpart of
the source module's private `cast_val_heq`, specialised to the constant
direction type `Fin 2`. -/
private theorem cast_dir_val2 {j : Fin 3} {s s' : presheafWitness2Data.Shape j} (h : s = s')
    {i : Fin 1} (p : presheafWitness2Data.Direction s.1 i) :
    (cast (congrArg (fun t : presheafWitness2Data.Shape j ↦
        presheafWitness2Data.Direction t.1 i) h) p).1 = p.1 := by
  cases h
  rfl

/-- The underlying value of a `reindex` is the value map applied to the
underlying input value. -/
private theorem reindex_fst2 {j j' : Fin 3} (g : j' ⟶ j) (a : presheafWitness2Data.Shape j)
    {i : Fin 1} (b : presheafWitness2Data.Direction (presheafWitness2Data.shapeRestr g a).1 i) :
    (presheafWitness2Data.reindex g a b).1 = reindexVal2 j' j b.1 := rfl

/-- The non-degenerate witness, with all seven functor laws discharged
genuinely. `directionRestr_id` / `directionRestr_comp` / `reindex_naturality` hold because the
index category `Fin 1` makes `directionRestr` the identity transport (so both sides
agree on the underlying value). `shapeRestr_id` / `shapeRestr_comp` reduce to the
`shapeRestrVal2` lemmas, `reindex_id` / `reindex_comp` to the `reindexVal2` lemmas after
discharging the shape-equality cast with `cast_dir_val2`. -/
def presheafWitness2 : PresheafPFunctor (Fin 1) (Fin 3) where
  toPresheafPFunctorData := presheafWitness2Data
  isFunctorial :=
    { directionRestr_id := by intro _a _i; funext _b; exact Subtype.ext rfl
      directionRestr_comp := by intro _a _i _i' _i'' _f _g; funext _b; exact Subtype.ext rfl
      shapeRestr_id := by
        intro j; funext a; apply Subtype.ext
        change shapeRestrVal2 j j a.1 = a.1
        exact shapeRestrVal2_self j a.1
      shapeRestr_comp := by
        intro j j' j'' g h; funext a; apply Subtype.ext
        change shapeRestrVal2 j'' j a.1 = shapeRestrVal2 j'' j' (shapeRestrVal2 j' j a.1)
        exact shapeRestrVal2_comp j'' j' j (leOfHom h) (leOfHom g) a.1
      reindex_naturality := by intro _j _j' _g _a _i _i' _f; funext _b; exact Subtype.ext rfl
      reindex_id := by
        intro j a i b; apply Subtype.ext
        rw [reindex_fst2, cast_dir_val2]
        · exact reindexVal2_id j b.1
        · exact Subtype.ext (shapeRestrVal2_self j a.1)
      reindex_comp := by
        intro j j' j'' g h a i b; apply Subtype.ext
        rw [reindex_fst2, reindex_fst2, reindex_fst2, cast_dir_val2]
        · exact reindexVal2_comp j'' j' j (leOfHom h) (leOfHom g) b.1
        · exact Subtype.ext (by
            change shapeRestrVal2 j'' j a.1 = shapeRestrVal2 j'' j' (shapeRestrVal2 j' j a.1)
            exact shapeRestrVal2_comp j'' j' j (leOfHom h) (leOfHom g) a.1) }

/-- The non-identity morphisms of the preorder category on `Fin 3`. -/
private def k01 : (0 : Fin 3) ⟶ 1 := homOfLE (by decide)
private def k02 : (0 : Fin 3) ⟶ 2 := homOfLE (by decide)

/-- The singleton shape over output index `1` (shape index `2`), reused by the
discriminating examples. -/
private def shapeOverOne : presheafWitness2.toSlicePFunctor.Shape (1 : Fin 3) :=
  ⟨(2 : Fin 4), by change qVal2 (2 : Fin 4) = 1; decide⟩

-- `reindex` along the non-identity `0 ⟶ 1` moves the underlying value on the
-- two-element fibre: the direction of value `0` is sent to value `1`.
example :
    (presheafWitness2.reindex k01 shapeOverOne (i := (0 : Fin 1)) ⟨(0 : Fin 2), by rfl⟩).1 =
      (1 : Fin 2) := rfl
example :
    (presheafWitness2.reindex k01 shapeOverOne (i := (0 : Fin 1)) ⟨(1 : Fin 2), by rfl⟩).1 =
      (0 : Fin 2) := rfl

-- `reindex` along `𝟙` does NOT move the value (would catch a wrong
-- `reindex_id`): the identity arrow leaves both directions fixed.
example :
    (presheafWitness2.reindex (𝟙 (1 : Fin 3)) shapeOverOne (i := (0 : Fin 1))
        ⟨(1 : Fin 2), by rfl⟩).1 = (1 : Fin 2) := rfl
example :
    (presheafWitness2.reindex (𝟙 (1 : Fin 3)) shapeOverOne (i := (0 : Fin 1))
        ⟨(0 : Fin 2), by rfl⟩).1 = (0 : Fin 2) := rfl

-- `shapeRestr` along `0 ⟶ 1` reindexes the singleton shape `2` (over output
-- index `1`) to the representative shape `0` (over output index `0`), not the
-- other shape `1` over output index `0`.
example : (presheafWitness2.shapeRestr k01 shapeOverOne).1 = (0 : Fin 4) := rfl

/-- A concrete choice-free input presheaf with a two-element fibre: the constant
presheaf on `(Fin 1)ᵒᵖ` at `Fin 2`. The index category has only the identity
morphism, so any direction assignment over it is natural. -/
@[reducible] private def constFin2 : (Fin 1)ᵒᵖ ⥤ Type where
  obj _ := Fin 2
  map _ := 𝟙 _

/-- An element of `objPresheaf constFin2`'s fibre over output index `2`: shape `3`, with
the assignment `b ↦ ⟨0, b⟩` recording each direction's value in the `Fin 2`
fibre. -/
private def fin2FiberElt : (presheafWitness2.objPresheaf constFin2).obj ⟨(2 : Fin 3)⟩ :=
  ⟨⟨⟨⟨(3 : Fin 4), fun (b : Fin 2) ↦ ⟨0, b⟩⟩,
      (presheafWitness2.toSliceDomPFunctor.compatible_iff _ _ _).mpr fun _ ↦ rfl⟩,
      fun _ _ _ _ ↦ rfl⟩,
    by change qVal2 (3 : Fin 4) = 2; decide⟩

-- `objPresheaf.map` along the composite `0 ⟶ 2` reindexes shape `3` to shape `0`,
-- end to end through `objRestr` / `objRestrElt` and `shapeRestr`.
example :
    ((presheafWitness2.objPresheaf constFin2).map k02.op fin2FiberElt).1.1.1.1 = (0 : Fin 4) :=
  rfl

-- `objPresheaf.map` along the composite `0 ⟶ 2` reindexes the assignment with
-- the boundary-crossing swap: direction `0` now records the value `1` and
-- direction `1` the value `0`, distinguishing the moved `reindex` end to end.
example :
    (((presheafWitness2.objPresheaf constFin2).map k02.op fin2FiberElt).1.1.1.2 (0 : Fin 2)).2 =
      (1 : Fin 2) := rfl
example :
    (((presheafWitness2.objPresheaf constFin2).map k02.op fin2FiberElt).1.1.1.2 (1 : Fin 2)).2 =
      (0 : Fin 2) := rfl
