/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.IndRec.Basic

/-!
# Functoriality of the IR interpretation

Toward the functoriality content of Theorem 2.4 of
[GhaniNordvallForsbergMalatesta2015] (which attributes the theorem
to [DybjerSetzer2003]): the characterizing equations of
`IR.interpMor` at each code constructor, from the propositional
computation rule `IR.rec_mk`.

## Main statements

* `IR.interpMor_mk` — the characterizing equation of `IR.interpMor`
  at `IR.mk`, with the per-constructor forms `IR.interpMor_iota`,
  `IR.interpMor_sigma`, and `IR.interpMor_delta`.
* `IR.interpMor_id` — preservation of identities
  ([GhaniNordvallForsbergMalatesta2015], Theorem 2.4).

## Implementation notes

The characterizing equations follow from the propositional
computation rule `IR.rec_mk`. The mathlib `Category`/`Functor`
packaging is deferred to a `Classical.choice`-enabled wrapper (see
`TODO.md`). The functor laws are `Prop`-valued and go through
`IR.induction` with the objects and morphisms quantified in the motive.

## References

* [DybjerSetzer2003]
* [GhaniNordvallForsbergMalatesta2015]

## Tags

inductive-recursive, interpretation, functor, free coproduct
completion
-/

@[expose] public section

universe uA uB uI uO w

namespace IndRec

open CategoryTheory

variable (I : Type uI) (O : Type uO)

namespace IR

/-- The characterizing equation of `IR.interpMor` at `IR.mk`: the
morphism map computes by one step of `IR.interpMorStep`
([GhaniNordvallForsbergMalatesta2015], Theorem 2.4). -/
theorem interpMor_mk (s : Shape O)
    (d : Direction I O s → IR.{uA, uB, uI, uO} I O) :
    interpMor I O (mk I O s d) =
      interpMorStep I O s d (fun x ↦ interpMor I O (d x)) :=
  rec_mk I O (interpMorStep I O) s d

/-- The characterizing equation of `IR.interpMor` at `IR.iota`
([GhaniNordvallForsbergMalatesta2015], Theorem 2.4). -/
theorem interpMor_iota (o : O) :
    interpMor.{uA, uB, uI, uO} I O (iota I O o) =
      interpMorIota.{uA, uB, uI, uO} I O o :=
  rec_mk I O (interpMorStep I O) (Sum.inl o) PEmpty.elim

/-- The characterizing equation of `IR.interpMor` at `IR.sigma`
([GhaniNordvallForsbergMalatesta2015], Theorem 2.4). -/
theorem interpMor_sigma (A : Type uA)
    (c : A → IR.{uA, uB, uI, uO} I O) :
    interpMor I O (sigma I O A c) =
      interpMorSigma I O A (fun a ↦ interpObj I O (c a))
        (fun a ↦ interpMor I O (c a)) :=
  rec_mk I O (interpMorStep I O) (Sum.inr (Sum.inl A)) (c ∘ ULift.down)

/-- The characterizing equation of `IR.interpMor` at `IR.delta`
([GhaniNordvallForsbergMalatesta2015], Theorem 2.4). -/
theorem interpMor_delta (B : Type uB)
    (c : (B → I) → IR.{uA, uB, uI, uO} I O) :
    interpMor I O (delta I O B c) =
      interpMorDelta I O B (fun f ↦ interpObj I O (c f))
        (fun f ↦ interpMor I O (c f)) :=
  rec_mk I O (interpMorStep I O) (Sum.inr (Sum.inr B)) (c ∘ ULift.down)

/-- The motive of the identity functor law: at every object, the
morphism map sends the identity to the identity. -/
def InterpMorIdMotive (γ : IR.{uA, uB, uI, uO} I O) : Prop :=
  ∀ X : FreeCoprodCompDisc.{max uA uB, uI} I,
    interpMor I O γ X X (FreeCoprodCompDisc.Hom.id I X) =
      FreeCoprodCompDisc.Hom.id O (interpObj I O γ X)

/-- The inductive step of the identity functor law: after the
characterizing equation `IR.interpMor_mk`, the `ι` case is
definitional and the `σ`/`δ` cases are the inductive hypotheses
followed by `FreeCoprodCompDisc.coprodMor_id` (the `δ`-case
`homOfEq` transport reduces definitionally at the identity, whose
commutation proof is reflexivity). -/
theorem interpMor_id_step :
    InductionStep.{uA, uB, uI, uO} I O (InterpMorIdMotive I O) :=
  fun s d ih X ↦
    (congrFun (congrFun (congrFun (interpMor_mk I O s d) X) X)
      (FreeCoprodCompDisc.Hom.id I X)).trans
      (match s, d, ih with
        | Sum.inl _, _, _ => rfl
        | Sum.inr (Sum.inl A), d, ih =>
            (congrArg
              (FreeCoprodCompDisc.coprodMor O A A _root_.id
                (fun a ↦ interpObj I O (d (ULift.up a)) X)
                (fun a ↦ interpObj I O (d (ULift.up a)) X))
              (funext (fun a ↦ ih (ULift.up a) X))).trans
              (FreeCoprodCompDisc.coprodMor_id O A
                (fun a ↦ interpObj I O (d (ULift.up a)) X))
        | Sum.inr (Sum.inr B), d, ih =>
            (congrArg
              (FreeCoprodCompDisc.coprodMor O (B → X.1) (B → X.1) _root_.id
                (fun g ↦ interpObj I O (d (ULift.up (X.2 ∘ g))) X)
                (fun g ↦ interpObj I O (d (ULift.up (X.2 ∘ g))) X))
              (funext (fun g ↦ ih (ULift.up (X.2 ∘ g)) X))).trans
              (FreeCoprodCompDisc.coprodMor_id O (B → X.1)
                (fun g ↦ interpObj I O (d (ULift.up (X.2 ∘ g))) X)))

/-- Preservation of identities by the interpretation
([GhaniNordvallForsbergMalatesta2015], Theorem 2.4). -/
theorem interpMor_id (γ : IR.{uA, uB, uI, uO} I O) :
    InterpMorIdMotive I O γ :=
  induction I O (InterpMorIdMotive I O) (interpMor_id_step I O) γ

end IR

end IndRec
