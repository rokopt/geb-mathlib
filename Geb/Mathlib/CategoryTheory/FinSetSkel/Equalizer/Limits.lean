/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Equalizer.Core
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# The equalizer cone of `FinSetSkel`

The mathlib packaging of the agreement sub-object, its injection and
its factorisation as a `LimitCone (parallelPair f g)`. `LimitCone`
and `parallelPair` depend on `Classical.choice`, so this module is
allowlisted and the construction it packages is not.

`HasEqualizers` is not registered: nothing in this workstream
consumes it, and it is one of the `Prop` classes derived once from
`ElementaryTopos`.

## Main definitions

* `FinSetSkel.equalizerCone` — the chosen equalizer cone.

## References

* [Freyd1972]

## Tags

finite sets, skeleton, equalizer, limit cone
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace FinSetSkel

/-- The chosen equalizer cone. -/
def equalizerCone {X Y : FinSetSkel.{u}} (f g : X ⟶ Y) :
    LimitCone (parallelPair f g) where
  cone := Fork.ofι (Equalizer.ι f g) (Equalizer.ι_comp f g)
  isLimit :=
    Fork.IsLimit.mk _ (fun s ↦ Equalizer.lift f g s.ι s.condition)
      (fun s ↦ Equalizer.lift_ι f g s.ι s.condition)
      (fun s m hm ↦ Equalizer.lift_uniq f g s.ι s.condition m hm)

end FinSetSkel
