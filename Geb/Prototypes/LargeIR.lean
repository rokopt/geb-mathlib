/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LargeIR.Basic
public import Geb.Prototypes.LargeIR.Code

/-!
# LargeIR — index

Prototype transcription of a slice polynomial functor `Type/X → Type/Y` into
a presheaf polynomial endofunctor on the walking arrow, whose presheaves are
the free coproduct completion `Fam(Type)`, and the computation of what the
endofunctor does: the base map `X → Z 0` survives as data of the value, which
is the `δ` constructor of large inductive-recursive codes rather than the
slice functor itself. See `Basic` for the construction and the comparison map
along the identity section, and `Code` for the reading of the value as the
interpretation of that `δ` code in the repository's `IndRec.IR` at index type
`Type`.
-/
