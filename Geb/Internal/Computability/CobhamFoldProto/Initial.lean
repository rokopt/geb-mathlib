/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.Computability.CobhamFoldProto.SmashFree

/-!
# The term algebra's constructor in the fold's language

The initial algebra's structure map at the carrier `List Bool`, whose
elements are read as spellings.

`Term.fold` at `algMk` is `RankedAlphabet.spell` itself, so `algMk` is the
step `spell`'s own `WType.elim` runs, named apart from it, and the preorder
encoding is the unique morphism from the term algebra into it by the
initiality `Term.fold_unique` carries [GambinoHyland2004]. The carrier
`List Bool` is not itself initial — the spellings are a proper subalgebra of
it — so what the equation says is that `algMk` is the initial algebra's
structure map transported along the encoding.

## Main definitions

* `Geb.CobhamFold.algMk` — the initial algebra's structure map.

## Main statements

* `Geb.CobhamFold.fold_algMk` — the fold at that map is the spelling.
* `Geb.CobhamFold.length_algMk` — it lengthens by the alphabet's width.
* `Geb.CobhamFold.foldOut_algMk` — the fold at that map is the identity on
  the recognized language.

## References

* [Cobham1965]
* [GambinoHyland2004]

## Tags

Cobham, ranked tree, initial algebra, term algebra, preorder encoding
-/

@[expose] public section

namespace Geb.CobhamFold

/-- The initial algebra's structure map, at the carrier `List Bool`: a
symbol's block followed by its children's spellings. -/
def algMk (R : RankedAlphabet) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool) : List Bool :=
  R.code i ++ (List.ofFn f).flatten

/-- The fold at that map is the preorder encoding, so `RankedAlphabet.spell`
is the unique morphism from the term algebra into it, by the initiality
`Geb.CobhamFold.Term.fold_unique` carries [GambinoHyland2004]. -/
theorem fold_algMk (R : RankedAlphabet) : Term.fold R (algMk R) = R.spell := rfl

/-- It lengthens its arguments' total by exactly the alphabet's width. -/
theorem length_algMk (R : RankedAlphabet) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool) :
    (algMk R i f).length = (List.ofFn fun d ↦ (f d).length).sum + R.width := by
  rw [algMk, List.length_append, R.length_code, List.length_flatten,
    List.map_ofFn]
  exact Nat.add_comm _ _

/-- The fold at that map is the identity on the recognized language. -/
theorem foldOut_algMk (R : RankedAlphabet) (w : List Bool) :
    foldOut R (algMk R) w = (R.parse w).map (fun _ ↦ w) := by
  rw [foldOut_eq, fold_algMk]
  cases h : R.parse w with
  | none => rfl
  | some t => exact congrArg some (R.parse_eq_some_iff.mp h)

end Geb.CobhamFold

end
