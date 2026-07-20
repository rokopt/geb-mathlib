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

## Implementation notes

The characterizing equations follow from the propositional
computation rule `IR.rec_mk`. The mathlib `Category`/`Functor`
packaging is deferred to a `Classical.choice`-enabled wrapper (see
`TODO.md`).

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

end IR

end IndRec
