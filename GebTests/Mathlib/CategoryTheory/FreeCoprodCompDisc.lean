/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FreeCoprodCompDisc

/-!
# Tests for the free coproduct completion

A sample object and endomorphism exercise `FreeCoprodCompDisc.Hom.comp`,
checking that composing the sample endomorphism with itself returns
the same endomorphism.

## Tags

free coproduct completion, family, discrete category
-/

@[expose] public section

open CategoryTheory

/-- A sample object: two names decoding into `Bool` by the
identity assignment. -/
def sampleX : FreeCoprodCompDisc.{0, 0} Bool :=
  ⟨Bool, id⟩

/-- A sample endomorphism of `sampleX`: the identity index
function, a hom because the decodings agree definitionally. -/
def sampleHom : FreeCoprodCompDisc.Hom Bool sampleX sampleX :=
  ⟨id, rfl⟩

/-- Composition of the sample endomorphism with itself is
itself. -/
theorem sampleHom_comp :
    FreeCoprodCompDisc.Hom.comp Bool sampleHom sampleHom = sampleHom :=
  Subtype.ext rfl
