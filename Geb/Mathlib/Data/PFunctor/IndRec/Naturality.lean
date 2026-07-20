/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FreeCoprodCompDisc.NatTrans
public import Geb.Mathlib.Data.PFunctor.IndRec.Functor
public import Geb.Mathlib.Data.PFunctor.IndRec.Hom

/-!
# Naturality of the IR interpretation and Theorem 3

Toward Theorem 3 of [HancockMcBrideGhaniMalatestaAltenkirch2013]:
the per-summand decomposition of transformation spaces at a `delta`
code (the naturality upgrade of the paper's Lemma 3). Each copower
summand — the value of `IR.interpObj` at a subcode, copowered by
the morphisms out of the lifted direction assignment — includes
into the `delta` interpretation naturally (`IR.deltaInto`); the
inclusions admit a cotuple (`IR.deltaDesc`) and are jointly epic;
and transformations out of the `delta` interpretation decompose
into families of transformations out of the summands
(`IR.natDeltaEquiv`).

## Main definitions

* `IR.deltaInto`, `IR.deltaDesc` — the natural inclusions of the
  copower summands into the `delta` interpretation and their
  cotuple ([HancockMcBrideGhaniMalatestaAltenkirch2013], Lemma 3,
  upgraded to per-summand natural form).
* `IR.natDeltaEquiv` — the per-summand decomposition of
  transformation spaces at a `delta` code.

## Main statements

* `IR.deltaInto_desc`, `IR.deltaDesc_eta`, `IR.deltaHom_ext` — the
  computation and uniqueness laws of the cotuple, and joint
  epicness of the inclusions.
* `IR.deltaInto_natural` — naturality of the inclusions in the
  interpreted object.

## Implementation notes

The total coproduct of Lemma 3 has an index type exceeding the
uniform index universe, so it never appears as a
`FreeCoprodCompDisc.Map`; the decomposition is per summand. The
`delta`-side morphism map is rewritten by `IR.interpMor_delta`,
and transports of names along equalities of direction assignments
are eliminated by the cast lemmas `IR.interpObj_snd_cast` and
`IR.interpMor_cast`, with `Eq.rec` motives at projection-reduced
types and dependent `rfl`-proofs quantified inside the motive.

## References

* [HancockMcBrideGhaniMalatestaAltenkirch2013]

## Tags

inductive-recursive, interpretation, natural transformation
-/

@[expose] public section

universe uA uB uI uO

namespace IndRec

open CategoryTheory

variable (I : Type uI) (O : Type uO)

namespace IR

/-- Decoding of interpretation names commutes with transport along an
equality of direction assignments. -/
theorem interpObj_snd_cast (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) {i j : B → I}
    (e : i = j) (n : (interpObj I O (c i) X).1) :
    (interpObj I O (c j) X).2
        (cast (congrArg (fun t ↦ (interpObj I O (c t) X).1) e) n) =
      (interpObj I O (c i) X).2 n :=
  Eq.rec (motive := fun j' e' ↦
      (interpObj I O (c j') X).2
          (cast (congrArg (fun t ↦ (interpObj I O (c t) X).1) e') n) =
        (interpObj I O (c i) X).2 n)
    rfl e

/-- The injection of the `i`-th copower summand into the `delta`
interpretation: a copower name `⟨e, n⟩` maps to the delta name whose
direction is `e.1` restricted along `ULift.up`, with `n` transported
along the induced equality of direction assignments. -/
def deltaInto (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (i : B → I) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom O
      (FreeCoprodCompDisc.copowerHomMap
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
        (interpObj I O (c i)) X)
      (interpObj I O (delta I O B c) X) :=
  ⟨fun p ↦ ⟨p.1.1 ∘ ULift.up,
      cast (congrArg (fun t ↦ (interpObj I O (c t) X).1)
        (congrArg (· ∘ ULift.up) p.1.2).symm) p.2⟩,
    funext (fun p ↦
      interpObj_snd_cast I O B c X
        (congrArg (· ∘ ULift.up) p.1.2).symm p.2)⟩

/-- The cotuple out of the `delta` interpretation: a delta name
`⟨g, n⟩` is dispatched to the component of `m` at the direction
assignment `X.2 ∘ g`, at the copower name pairing the lifted
direction with `n`. -/
def deltaDesc (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (Z : FreeCoprodCompDisc.{max uA uB, uO} O)
    (m : (i : B → I) → FreeCoprodCompDisc.Hom O
      (FreeCoprodCompDisc.copowerHomMap
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
        (interpObj I O (c i)) X) Z) :
    FreeCoprodCompDisc.Hom O (interpObj I O (delta I O B c) X) Z :=
  ⟨fun q ↦ (m (X.2 ∘ q.1)).1 ⟨⟨q.1 ∘ ULift.down, rfl⟩, q.2⟩,
    funext (fun q ↦
      congrFun (m (X.2 ∘ q.1)).2 ⟨⟨q.1 ∘ ULift.down, rfl⟩, q.2⟩)⟩

/-- The transport-elimination step of `IR.deltaInto_desc`: the target
direction assignment is generalized together with the transport
equality and the inner commutation proof, so the base case is
definitional. -/
theorem deltaInto_desc_aux (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (Z : FreeCoprodCompDisc.{max uA uB, uO} O)
    (m : (i' : B → I) → FreeCoprodCompDisc.Hom O
      (FreeCoprodCompDisc.copowerHomMap
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i'⟩)
        (interpObj I O (c i')) X) Z)
    (e : FreeCoprodCompDisc.Hom I
      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
    (n : (interpObj I O (c i) X).1) (j : B → I) (h : i = j)
    (pf : X.2 ∘ ((e.1 ∘ ULift.up) ∘ ULift.down) =
      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, j⟩).2) :
    (m j).1 ⟨⟨(e.1 ∘ ULift.up) ∘ ULift.down, pf⟩,
        cast (congrArg (fun t ↦ (interpObj I O (c t) X).1) h) n⟩ =
      (m i).1 ⟨e, n⟩ :=
  Eq.rec (motive := fun j' h' ↦
      ∀ pf' : X.2 ∘ ((e.1 ∘ ULift.up) ∘ ULift.down) =
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, j'⟩).2,
      (m j').1 ⟨⟨(e.1 ∘ ULift.up) ∘ ULift.down, pf'⟩,
          cast (congrArg (fun t ↦ (interpObj I O (c t) X).1) h') n⟩ =
        (m i).1 ⟨e, n⟩)
    (fun _ ↦ rfl) h pf

/-- Restricting the delta cotuple along the `i`-th injection recovers
the component. -/
theorem deltaInto_desc (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (Z : FreeCoprodCompDisc.{max uA uB, uO} O)
    (m : (i' : B → I) → FreeCoprodCompDisc.Hom O
      (FreeCoprodCompDisc.copowerHomMap
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i'⟩)
        (interpObj I O (c i')) X) Z) :
    FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i X)
      (deltaDesc I O B c X Z m) = m i :=
  Subtype.ext (funext (fun p ↦
    deltaInto_desc_aux I O B c i X Z m p.1 p.2
      (X.2 ∘ (p.1.1 ∘ ULift.up))
      ((congrArg (· ∘ ULift.up) p.1.2).symm) rfl))

/-- Every morphism out of the delta interpretation is the cotuple of
its restrictions along the injections. -/
theorem deltaDesc_eta (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (Z : FreeCoprodCompDisc.{max uA uB, uO} O)
    (h : FreeCoprodCompDisc.Hom O (interpObj I O (delta I O B c) X) Z) :
    deltaDesc I O B c X Z
        (fun i ↦ FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i X) h) =
      h :=
  Subtype.ext (funext (fun _ ↦ rfl))

/-- The `IR.deltaInto` family is jointly epic: two morphisms out of
the delta interpretation agree when their restrictions along every
injection agree. -/
theorem deltaHom_ext (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (Z : FreeCoprodCompDisc.{max uA uB, uO} O)
    (f g : FreeCoprodCompDisc.Hom O (interpObj I O (delta I O B c) X) Z)
    (hfg : ∀ i : B → I,
      FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i X) f =
        FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i X) g) :
    f = g :=
  (deltaDesc_eta I O B c X Z f).symm.trans
    ((congrArg (deltaDesc I O B c X Z) (funext hfg)).trans
      (deltaDesc_eta I O B c X Z g))

/-- `IR.interpMor` commutes with transport of names along an equality
of direction assignments. -/
theorem interpMor_cast (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (X Y : FreeCoprodCompDisc.{max uA uB, uI} I)
    (h : FreeCoprodCompDisc.Hom I X Y) {i j : B → I} (e : i = j)
    (n : (interpObj I O (c i) X).1) :
    cast (congrArg (fun t ↦ (interpObj I O (c t) Y).1) e)
        ((interpMor I O (c i) X Y h).1 n) =
      (interpMor I O (c j) X Y h).1
        (cast (congrArg (fun t ↦ (interpObj I O (c t) X).1) e) n) :=
  Eq.rec (motive := fun j' e' ↦
      cast (congrArg (fun t ↦ (interpObj I O (c t) Y).1) e')
          ((interpMor I O (c i) X Y h).1 n) =
        (interpMor I O (c j') X Y h).1
          (cast (congrArg (fun t ↦ (interpObj I O (c t) X).1) e') n))
    rfl e

/-- The motive of the commutation-equality elimination in
`IR.deltaInto_natural`: the domain decoding is generalized together
with the morphism's commutation proof, and the delta-side morphism
map appears in its `IR.interpMorDelta` form. -/
def DeltaIntoNaturalMotive (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
    (X1 : Type (max uA uB)) (Y : FreeCoprodCompDisc.{max uA uB, uI} I)
    (h1 : X1 → Y.1) (x2 : X1 → I) (hcomm : Y.2 ∘ h1 = x2) : Prop :=
  FreeCoprodCompDisc.Hom.comp O
      (FreeCoprodCompDisc.copowerHomMapMor
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
        (interpMor I O (c i)) ⟨X1, x2⟩ Y ⟨h1, hcomm⟩)
      (deltaInto I O B c i Y) =
    FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i ⟨X1, x2⟩)
      (interpMorDelta I O B (fun f ↦ interpObj I O (c f))
        (fun f ↦ interpMor I O (c f)) ⟨X1, x2⟩ Y ⟨h1, hcomm⟩)

/-- The base case of `IR.deltaInto_natural`: at a factored domain
decoding with reflexive commutation proof, the `homOfEq` transport in
`IR.interpMorDelta` reduces definitionally and the square reduces to
`IR.interpMor_cast` componentwise. -/
theorem deltaInto_natural_base (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
    (X1 : Type (max uA uB)) (Y : FreeCoprodCompDisc.{max uA uB, uI} I)
    (h1 : X1 → Y.1) :
    DeltaIntoNaturalMotive I O B c i X1 Y h1 (Y.2 ∘ h1) rfl :=
  Subtype.ext (funext (fun p ↦
    congrArg
      (fun t ↦ (⟨h1 ∘ (p.1.1 ∘ ULift.up), t⟩ :
        Σ g : B → Y.1, (interpObj I O (c (Y.2 ∘ g)) Y).1))
      (interpMor_cast I O B c ⟨X1, Y.2 ∘ h1⟩ Y ⟨h1, rfl⟩
        ((congrArg (· ∘ ULift.up) p.1.2).symm) p.2)))

/-- Naturality of `IR.deltaInto` in the object. -/
theorem deltaInto_natural (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I) :
    FreeCoprodCompDisc.IsNatTrans I O
      (FreeCoprodCompDisc.copowerHomMap
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
        (interpObj I O (c i)))
      (interpObj I O (delta I O B c))
      (FreeCoprodCompDisc.copowerHomMapMor
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
        (interpMor I O (c i)))
      (interpMor I O (delta I O B c))
      (deltaInto I O B c i) :=
  fun X Y h ↦
    match X, h with
    | ⟨X1, x2⟩, ⟨h1, hcomm⟩ =>
      (Eq.rec (motive := fun x2' hcomm' ↦
          DeltaIntoNaturalMotive I O B c i X1 Y h1 x2' hcomm')
        (deltaInto_natural_base I O B c i X1 Y h1) hcomm).trans
        (congrArg
          (fun t ↦ FreeCoprodCompDisc.Hom.comp O
            (deltaInto I O B c i ⟨X1, x2⟩) (t ⟨X1, x2⟩ Y ⟨h1, hcomm⟩))
          (interpMor_delta I O B c).symm)

/-- The per-summand decomposition of transformation spaces at a
`delta` code: transformations out of the `delta` interpretation
correspond to families, over the direction assignments, of
transformations out of the copower summands. -/
def natDeltaEquiv (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    {G : FreeCoprodCompDisc.Map.{max uA uB, uI, uO} I O}
    (mG : FreeCoprodCompDisc.MapMor I O G) :
    FreeCoprodCompDisc.NatTrans I O (interpObj I O (delta I O B c)) G
        (interpMor I O (delta I O B c)) mG ≃
      ((i : B → I) → FreeCoprodCompDisc.NatTrans I O
        (FreeCoprodCompDisc.copowerHomMap
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
          (interpObj I O (c i))) G
        (FreeCoprodCompDisc.copowerHomMapMor
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
          (interpMor I O (c i))) mG) :=
  { toFun := fun η i ↦
      ⟨fun X ↦
        FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i X) (η.1 X),
        fun X Y h ↦
          (congrArg
              (fun t ↦ FreeCoprodCompDisc.Hom.comp O t (η.1 Y))
              (deltaInto_natural I O B c i X Y h)).trans
            (congrArg
              (FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i X))
              (η.2 X Y h))⟩,
    invFun := fun θ ↦
      ⟨fun X ↦ deltaDesc I O B c X (G X) (fun i ↦ (θ i).1 X),
        fun X Y h ↦
          deltaHom_ext I O B c X (G Y) _ _ (fun i ↦
            (((congrArg
                  (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
                    (deltaDesc I O B c Y (G Y) (fun i' ↦ (θ i').1 Y)))
                  (deltaInto_natural I O B c i X Y h)).symm.trans
              ((congrArg
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.copowerHomMapMor
                      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB}
                        I ⟨B, i⟩)
                      (interpMor I O (c i)) X Y h))
                  (deltaInto_desc I O B c i Y (G Y)
                    (fun i' ↦ (θ i').1 Y))).trans
                ((θ i).2 X Y h))).trans
            (congrArg
              (fun t ↦ FreeCoprodCompDisc.Hom.comp O t (mG X Y h))
              (deltaInto_desc I O B c i X (G X)
                (fun i' ↦ (θ i').1 X)).symm)))⟩,
    left_inv := fun η ↦ Subtype.ext (funext (fun X ↦
      deltaDesc_eta I O B c X (G X) (η.1 X))),
    right_inv := fun θ ↦ funext (fun i ↦ Subtype.ext (funext (fun X ↦
      deltaInto_desc I O B c i X (G X) (fun i' ↦ (θ i').1 X)))) }

end IR

end IndRec
