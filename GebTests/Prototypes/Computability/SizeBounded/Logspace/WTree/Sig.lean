/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree -- shake: keep; #guard needs it
public meta import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree -- shake: keep; #guard needs it
public import Geb.Prototypes.Computability.SizeBounded.Sharing -- shake: keep; #guard needs it
public meta import Geb.Prototypes.Computability.SizeBounded.Sharing -- shake: keep; #guard needs it

/-!
# The algebra's own signature, its code and its recognizer, on worked words

The code and the decoder of the algebra's shapes on each kind of shape, and
the recognizer of the algebra's expressions: its specification on the
spellings of expressions of the subalgebra and on corrupted words, and the
expression itself evaluated with sharing on the smallest spelling.

## Main definitions

* `roundTrip` — a shape's code read back through the decoder.
* `constZero` — the raw tree of the constant of arity zero.

## Main statements

The decoder inverts the code on each kind of shape and rejects a projection
out of range; the recognizer's specification accepts the spellings of
expressions of the subalgebra and rejects a spelling with a corrupted arity
and one with a projection out of range; and the recognizer as an expression,
evaluated with sharing, accepts the smallest spelling, by `#guard`.

## Tags

size-bounded algebra, signature, recognizer
-/

set_option linter.privateModule false

open Geb.SizeBounded.Logspace Geb.SizeBounded.Logspace.WTree Geb.SizeBounded.Logspace.WTree.Sig
  Geb.SizeBounded.Logspace.WTree.SigCheck

/-- A shape's code read back through the decoder, the shapes themselves
having no decidable equality. -/
def roundTrip (a : Geb.SizeBounded.Shape) : Option (List Bool) := (decode (code a)).map code

#guard roundTrip (.const 3 [true, false]) = some (code (.const 3 [true, false]))

#guard roundTrip (.proj 3 ⟨2, by decide⟩) = some (code (.proj 3 ⟨2, by decide⟩))

#guard roundTrip (.sbs true) = some (code (.sbs true))

#guard roundTrip (.comp 2 5) = some (code (.comp 2 5))

#guard roundTrip (.srn 1 2 ⟨1, by decide⟩) = some (code (.srn 1 2 ⟨1, by decide⟩))

-- A projection out of range: the tag, the arity two and the index two.
#guard (decode ([false, false, true] ++
  (Geb.SizeBounded.Logspace.WTree.Numeral.natCode 2 ++
    Geb.SizeBounded.Logspace.WTree.Numeral.natCode 2))).isSome = false

/-- The raw tree of the constant of arity zero with the empty word. -/
def constZero : Geb.SizeBounded.sig.toPFunctor.W := WType.mk (.const 0 []) Fin.elim0

#guard sigCoded.recognize (sigCoded.spell constZero) = true

#guard sigCoded.recognize (sigCoded.spell tailL.1.1.1) = true

#guard sigCoded.recognize (sigCoded.spell condL.1.1.1) = true

#guard sigCoded.recognize (sigCoded.spell dropBy.1.1.1) = true

-- A substitution of arity two whose head has arity three, with two arguments:
-- the head's arity is not the number of arguments.
#guard sigCoded.recognize (sigCoded.spell (WType.mk (.comp 2 2)
  (Sum.elim (fun _ ↦ WType.mk (.const 3 []) Fin.elim0)
    (fun _ ↦ WType.mk (.const 2 []) Fin.elim0)))) = false

-- The spelling of a projection out of range: the label of the raw tree of a
-- projection with the index field raised to the arity.
#guard sigCoded.recognize (Geb.BitTree.Elias.encode (Geb.BitTree.leaf
  (false :: false :: true :: (Geb.SizeBounded.Logspace.WTree.Numeral.natCode 2 ++
    Geb.SizeBounded.Logspace.WTree.Numeral.natCode 2)))) = false

#guard sigCoded.recognize (Geb.BitTree.Elias.encode (Geb.BitTree.leaf
  (false :: false :: true :: (Geb.SizeBounded.Logspace.WTree.Numeral.natCode 2 ++
    Geb.SizeBounded.Logspace.WTree.Numeral.natCode 1)))) = true

-- The recognizer as an expression, evaluated with sharing, on the smallest
-- spelling; the evaluation takes tens of seconds.
#guard sigRecognizer.1.semVec ![sigCoded.spell constZero] = [true]
