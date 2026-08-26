/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.FinCardUniverse.Restriction
import Geb.Prototypes.FinCardUniverse.Value

/-!
# Tests for the universe functor's value as a family of codes

The shape identification and the decoding's independence of what a code binds.

## Tags

prototype, presheaf, universe, free coproduct completion, reduction test
-/

set_option linter.privateModule false

open CategoryTheory GebProto GebProto.FamBoundary GebProto.FinCardUniverse

/-- The generic shape at the base-type code lies over the object that code
decodes to. -/
def genericIota : Shp sigmaFormer := genericShape sigmaFormer (.iota ⟨2⟩)

example : genericIota.2.1 = ⟨2⟩ := rfl

-- The shape identification is a relabelling: the two spellings of a shape agree.
example : shapePshEquiv sigmaFormer genericIota = ⟨⟨2⟩, .iota ⟨2⟩, 𝟙 _⟩ := rfl

example : (shapePshEquiv sigmaFormer).symm (shapePshEquiv sigmaFormer genericIota)
    = genericIota := rfl

-- The decoding is fixed by the code former, whatever the code binds.
example (Z : Cardᵒᵖ ⥤ Type)
    (x y : ArityHom (universeFunctor sigmaFormer)
      (genericShape sigmaFormer emptyBindCode) Z) :
    famDec sigmaFormer Z ⟨emptyBindCode, x⟩ = famDec sigmaFormer Z ⟨emptyBindCode, y⟩ :=
  famDec_eq sigmaFormer Z emptyBindCode x y

/-- The junk arity hom of `Value` decodes by its declaration: the code binds a
singleton-denoting code but decodes to the empty object all the same. Named
rather than stated as an `example` so that `lake shake` sees the import. -/
theorem famDec_junk : famDec sigmaFormer (famPresheaf Unit oneFam)
    ⟨emptyBindCode, (arityHomEquiv sigmaFormer (genericShape sigmaFormer emptyBindCode)
      Unit oneFam).symm junkArity⟩ = ⟨0⟩ := rfl
