/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinCat.Category
public import Mathlib.CategoryTheory.Functor.Basic

/-!
# Functor specifications

A functor between two finite-category specifications is specified by a
map on object indices, a map on client morphisms, and a `Bool` equation
asserting preservation of composition. The client morphism map lands in
the target's full hom type, a functor being free to send a non-identity
morphism to an identity. Preservation of identities is not checked: the
extension of the morphism map to the full hom types sends the reserved
identity to the reserved identity by construction.

## Main definitions

* `FinCat.Hom.mapTotalOf`, `FinCat.Hom.mapTotal` — the extension of the
  morphism map to the full hom types.
* `FinCat.Hom.compCheckOf`, `FinCat.Hom.compCheck` — the decidable
  preservation-of-composition check on pairs of client morphisms.
* `FinCat.Hom` — the functor specification type.

## Main statements

* `FinCat.Hom.compCheck_eq_true_iff` — the check reflects preservation
  of composition on pairs of client morphisms.
* `FinCat.Hom.mapTotal_emb`, `FinCat.Hom.mapTotal_id` — the total map on
  a client morphism and on the reserved identity.
* `FinCat.Hom.mapTotal_compTotal` — preservation of composition, on all
  pairs of morphisms.

## Implementation notes

`mapTotalOf` and `compCheckOf` precede the structure because the
`compValid` field's type mentions them. The enclosing `namespace FinCat`
stays open throughout; the inner `namespace Hom` block closes before
`structure Hom`, which cannot be declared inside a namespace of its own
name, and reopens after.

The check is stated over the total composition and the total morphism
map rather than over the client data alone: a composite of two client
morphisms may land on the reserved identity index, on which the client's
morphism map is undefined.

`mapTotal_compTotal` extends the check off the client range. The
extension, rather than the check itself, is what the composite of two
functor specifications needs: its validity field is the outer
specification's preservation of composition at two morphisms of the form
`mapTotal (emb _)`, which need not be embedded client morphisms of the
middle specification.

## References

* [JohnsonYau2021] § 1.1 — the notion of functor, of which this module's
  specification type is a presentation.

## Tags

category, functor, finite category, decidable, constructive, choice-free
-/

@[expose] public section

open CategoryTheory

namespace FinCat

namespace Hom

/-- The extension of a functor specification's morphism map to the full
hom types, sending the reserved identity to the reserved identity. The
identity branch's bound needs `i = j`, which `eq_of_nonIdCount_le`
supplies; the value component crosses with no `Eq.rec`. -/
def mapTotalOf {S T : FinCat} (objMap : Fin S.objCount → Fin T.objCount)
    (map : (i j : Fin S.objCount) → Fin (S.nonIdCount i j) → T.Mor (objMap i) (objMap j))
    {i j : Fin S.objCount} (x : S.Mor i j) : T.Mor (objMap i) (objMap j) :=
  if hx : x.val < S.nonIdCount i j then map i j ⟨x.val, hx⟩
  else ⟨(T.id (objMap i)).val, by
    have hij := S.eq_of_nonIdCount_le x (Nat.not_lt.mp hx)
    subst hij
    exact (T.id (objMap i)).isLt⟩

/-- Preservation of composition, as a `Bool`, on pairs of client
morphisms. Stated over the total composition and the total morphism
map: a client composite may land on the reserved index, on which the
partial map is undefined. -/
def compCheckOf (S T : FinCat) (objMap : Fin S.objCount → Fin T.objCount)
    (map : (i j : Fin S.objCount) → Fin (S.nonIdCount i j) → T.Mor (objMap i) (objMap j)) :
    Bool :=
  decide <| ∀ (i j k : Fin S.objCount) (f : Fin (S.nonIdCount i j))
    (g : Fin (S.nonIdCount j k)),
      mapTotalOf objMap map (S.compTotal (S.emb f) (S.emb g))
        = T.compTotal (mapTotalOf objMap map (S.emb f)) (mapTotalOf objMap map (S.emb g))

end Hom

/-- A functor specification between two finite-category
specifications. `FinCat.Hom` is named for its position — the 1-cells of
a 2-category — not for its shape: unlike `CategoryTheory.Cat.Hom` it is
not a one-field bundling. -/
@[ext] structure Hom (S T : FinCat) where
  /-- The map on object indices. -/
  objMap : Fin S.objCount → Fin T.objCount
  /-- The map on client morphisms. It lands in the target's full hom
  type, since a functor may send a non-identity morphism to an
  identity; every functor into the terminal category does. -/
  map : (i j : Fin S.objCount) →
    Fin (S.nonIdCount i j) → T.Mor (objMap i) (objMap j)
  /-- Preservation of composition. -/
  compValid : FinCat.Hom.compCheckOf S T objMap map = true

namespace Hom

variable {S T : FinCat}

/-- The composition check reflects preservation of composition on pairs
of client morphisms. -/
theorem compCheck_eq_true_iff (S T : FinCat) (objMap : Fin S.objCount → Fin T.objCount)
    (map : (i j : Fin S.objCount) → Fin (S.nonIdCount i j) → T.Mor (objMap i) (objMap j)) :
    compCheckOf S T objMap map = true ↔
      ∀ (i j k : Fin S.objCount) (f : Fin (S.nonIdCount i j)) (g : Fin (S.nonIdCount j k)),
        mapTotalOf objMap map (S.compTotal (S.emb f) (S.emb g))
          = T.compTotal (mapTotalOf objMap map (S.emb f)) (mapTotalOf objMap map (S.emb g)) :=
  decide_eq_true_iff

/-- `F` on the full hom types. -/
def mapTotal (F : FinCat.Hom S T) {i j : Fin S.objCount} (x : S.Mor i j) :
    T.Mor (F.objMap i) (F.objMap j) := mapTotalOf F.objMap F.map x

/-- `F`'s composition check. -/
def compCheck (F : FinCat.Hom S T) : Bool := compCheckOf S T F.objMap F.map

/-- On an embedded client morphism the total map is the client map. -/
theorem mapTotal_emb (F : FinCat.Hom S T) {i j : Fin S.objCount}
    (f : Fin (S.nonIdCount i j)) : F.mapTotal (S.emb f) = F.map i j f := by
  have hlt : (S.emb f).val < S.nonIdCount i j := f.isLt
  unfold FinCat.Hom.mapTotal mapTotalOf
  rw [dif_pos hlt]
  rfl

/-- The total map preserves the reserved identity. -/
theorem mapTotal_id (F : FinCat.Hom S T) (i : Fin S.objCount) :
    F.mapTotal (S.id i) = T.id (F.objMap i) := by
  have hlt : ¬ ((S.id i).val < S.nonIdCount i i) := Nat.lt_irrefl _
  unfold FinCat.Hom.mapTotal mapTotalOf
  rw [dif_neg hlt]

/-- The total map preserves the total composition, on all pairs of
morphisms. -/
theorem mapTotal_compTotal (F : FinCat.Hom S T) {i j k : Fin S.objCount}
    (x : S.Mor i j) (y : S.Mor j k) :
    F.mapTotal (S.compTotal x y) = T.compTotal (F.mapTotal x) (F.mapTotal y) := by
  by_cases hx : x.val < S.nonIdCount i j
  · by_cases hy : y.val < S.nonIdCount j k
    · exact (compCheck_eq_true_iff S T F.objMap F.map).mp F.compValid i j k
        ⟨x.val, hx⟩ ⟨y.val, hy⟩
    · have hjk := S.eq_of_nonIdCount_le y (Nat.not_lt.mp hy)
      subst hjk
      rw [show y = S.id _ from Fin.ext (S.val_eq_of_nonIdCount_le y (Nat.not_lt.mp hy)),
        S.comp_id, mapTotal_id, T.comp_id]
  · have hij := S.eq_of_nonIdCount_le x (Nat.not_lt.mp hx)
    subst hij
    rw [show x = S.id _ from Fin.ext (S.val_eq_of_nonIdCount_le x (Nat.not_lt.mp hx)),
      S.id_comp, mapTotal_id, T.id_comp]

end Hom

end FinCat
