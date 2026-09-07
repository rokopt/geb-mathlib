/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PresheafIRUniv -- shake: keep

/-!
# Tests for the walking-arrow presheaf universe prototype

Exercises the construction of `Geb.Prototypes.PresheafIRUniv`: the walking
arrow, the presheaf polynomial endofunctor `univPsh`, and its W-type, the
presheaf inductive-inductive universe whose fibre over `0` is the codes and
whose fibre over `1` is the terms, with the restriction map `fib` the
decoding.

The tests cover the parts of the construction that compute at the level of
the functor and the W-type's fibres: the shapes and directions are finite,
the direction-input map is constantly over the code fibre, the shape-output
map sends the term shapes over the term fibre, the shape-restriction sends the
term shapes to their codes, the raw reindexing is the code-component
injection, the shape laws hold, and the constructors inhabit the two fibres
with `fib` mapping the terms into the codes. The computation of `fib` on the
constructors (the decoding equations) goes through the root-restriction of
the presheaf W-type and is deferred to the review the prototype is intended
for, as recorded in the `Basic` module's decoding section.

## Tags

prototype, inductive-inductive, presheaf, walking arrow, W-type, universe
-/

@[expose] public section

open CategoryTheory

namespace PresheafIRUniv

/-! ## The walking arrow -/

-- The walking arrow has a morphism from the code object `0` to the term
-- object `1`.
example : (0 : Fin 2) ⟶ (1 : Fin 2) := waHom

/-! ## The shapes and directions are finite -/

-- The direction of a `sigma` code is a point: the bound code.
example : univDir PUnit (.sigma : univShape PUnit) = PUnit := rfl

-- The directions of a term are two points: the code and the payload.
example : univDir PUnit (.termSigma : univShape PUnit) = (PUnit ⊕ PUnit) := rfl


/-! ## The direction-input and shape-output maps -/

-- Every direction lies over the code fibre: the recursion of the W-type runs
-- through the codes.
example (K : Type) : univR K ⟨.sigma, PUnit.unit⟩ = (0 : Fin 2) := rfl
example (K : Type) : univR K ⟨.termSigma, Sum.inl PUnit.unit⟩ = (0 : Fin 2) := rfl

-- The code shapes lie over `0` and the term shapes over `1`.
example (K : Type) : univQ K (.sigma : univShape K) = (0 : Fin 2) := rfl
example (K : Type) : univQ K (.termSigma : univShape K) = (1 : Fin 2) := rfl

-- The restriction of a term shape along `0 ⟶ 1` is the code shape of the
-- same former: `termSigma` to `sigma`, `termPi` to `pi`.
example (K : Type) : univRestrShape K (.termSigma : univShape K) (0 : Fin 2) =
    (.sigma : univShape K) := rfl
example (K : Type) : univRestrShape K (.termPi : univShape K) (0 : Fin 2) =
    (.pi : univShape K) := rfl

-- The shape-restriction laws hold.
example (K : Type) : (univPshData K).ShapeRestrId := univShapeRestr_id_thm K
example (K : Type) : (univPshData K).ShapeRestrComp := univShapeRestr_comp_thm K

/-! ## The reindexing -/

-- The raw reindexing on a `sigma` shape is the identity, and on a term shape
-- restricted along `0 ⟶ 1` it is the code-component injection.
example (K : Type) (b : PUnit) : univReindexDir K (.sigma : univShape K) (1 : Fin 2) b = b := rfl
example (K : Type) (b : PUnit) :
    univReindexDir K (.termSigma : univShape K) (0 : Fin 2) b = Sum.inl b := rfl
example (K : Type) (b : PUnit) :
    univReindexDir K (.termPi : univShape K) (0 : Fin 2) b = Sum.inr b := rfl

-- There are no directions over the term fibre.
example (K : Type) : IsEmpty (SliceDomPFunctor.Direction (univSlice K).toSliceDomPFunctor
    (.sigma : univShape K) (1 : Fin 2)) :=
  univDirection_empty K (.sigma : univShape K)

/-! ## The endofunctor and its W-type -/

-- The operations form a presheaf polynomial endofunctor over the walking
-- arrow, and the functor laws hold.
example (K : Type) : PresheafPFunctor (Fin 2) (Fin 2) := univPsh K
example (K : Type) : (univPshData K).IsFunctorial := univPshLaws K

-- The W-type is a presheaf over the walking arrow.
example (K : Type) : (Fin 2)ᵒᵖ ⥤ Type := univW K

/-! ## The codes and terms -/

-- The two fibres of the presheaf initial algebra: the codes over `0` and the
-- terms over `1`.
example (K : Type) : Codes K = (univW K).obj ⟨(0 : Fin 2)⟩ := rfl
example (K : Type) : Terms K = (univW K).obj ⟨(1 : Fin 2)⟩ := rfl

-- The constructors inhabit the fibres: one code per starting type, the
-- dependent-sum and dependent-product codes, and the terms with a code and a
-- payload.
example (K : Type) (k : K) : Codes K := univIota K k
example (K : Type) (u : Codes K) : Codes K := univSigma K u
example (K : Type) (u : Codes K) : Codes K := univPi K u
example (K : Type) (p d : Codes K) : Terms K := univTermSigma K p d
example (K : Type) (p d : Codes K) : Terms K := univTermPi K p d

-- The decoding is the restriction map of the presheaf along `0 ⟶ 1`, a
-- function from the terms into the codes.
example (K : Type) (t : Terms K) : Codes K := fib K t

-- A concrete instantiation: the universe generated by one starting type.
example : Codes PUnit := univIota PUnit PUnit.unit
example : Terms PUnit :=
  univTermSigma PUnit (univIota PUnit PUnit.unit) (univIota PUnit PUnit.unit)

end PresheafIRUniv

end
