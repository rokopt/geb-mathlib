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

`mkOf` computes that map inside the class: the symbol's block prepended to
`flattenOf`, a `Nat.rec` on the arity whose step composes the arity-`n` tail
against the shifted projections, so no `def` calls itself.

## Main definitions

* `Geb.CobhamFold.algMk` — the initial algebra's structure map.
* `Geb.CobhamFold.flattenOf` — the concatenation of an arity's slots.
* `Geb.CobhamFold.mkOf` — the structure map as an expression of the class.

## Main statements

* `Geb.CobhamFold.fold_algMk` — the fold at that map is the spelling.
* `Geb.CobhamFold.length_algMk` — it lengthens by the alphabet's width.
* `Geb.CobhamFold.foldOut_algMk` — the fold at that map is the identity on
  the recognized language.
* `Geb.CobhamFold.flattenOf_succ` — the slot concatenation at a successor,
  which `Nat.rec` generates no equation lemma for.
* `Geb.CobhamFold.semAt_flattenOf`, `Geb.CobhamFold.semAt_mkOf` — what those
  two expressions compute.
* `Geb.CobhamFold.growth_algMk`, `Geb.CobhamFold.stackSize_algMk_le` — the
  per-symbol growth condition at the constant `R.width`, and the linearity
  hypothesis it discharges.
* `Geb.CobhamFold.smashFreeBool_flattenOf`,
  `Geb.CobhamFold.smashFreeBool_mkOf` — those expressions carry no `smash`.

## References

* [Cobham1965]
* [GambinoHyland2004]

## Tags

Cobham, ranked tree, initial algebra, term algebra, preorder encoding, expression, smash-free
-/

@[expose] public section

namespace Geb.CobhamFold

open Cobham

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

/-- The concatenation of an arity's slots, in index order. Built by `Nat.rec`
on the arity, the arity-`n` tail composed against the shifted projections, so
no `def` calls itself. -/
def flattenOf : (n : ℕ) → COf n :=
  Nat.rec (zeroAtOf 0) fun n ih ↦
    concatCompOf (n + 1) (compOf ih fun i ↦ projOf (n + 1) i.succ)
      (projOf (n + 1) 0)

/-- One more slot concatenates onto the shifted tail, its own value first.
`flattenOf` is a bare `Nat.rec`, for which Lean generates no equation
lemma. -/
theorem flattenOf_succ (n : ℕ) :
    flattenOf (n + 1) =
      concatCompOf (n + 1) (compOf (flattenOf n) fun i ↦ projOf (n + 1) i.succ)
        (projOf (n + 1) 0) := rfl

/-- It computes the concatenation of its slots. The single unfolding step is
definitional but the closed form is not, `List.ofFn_succ` itself not being
`rfl`. -/
theorem semAt_flattenOf : ∀ (n : ℕ) (x : Fin n → List Bool),
    semAt n (flattenOf n).1.1 (flattenOf n).2 x = (List.ofFn x).flatten :=
  Nat.rec (fun x ↦ by rw [List.ofFn_zero, List.flatten_nil]; rfl)
    fun n ih x ↦ by
      rw [flattenOf_succ, semAt_concatCompOf, semAt_projOf, semAt_compOf]
      simp only [semAt_projOf]
      rw [ih fun i ↦ x i.succ, List.ofFn_succ, List.flatten_cons]

/-- The initial algebra's structure map as an expression of Cobham's class:
the symbol's block prepended to the concatenation of the slots. -/
def mkOf (R : RankedAlphabet) (i : Fin R.card) : COf (R.arity i) :=
  prependOf (R.code i) (flattenOf (R.arity i))

/-- The expression computes the structure map. -/
theorem semAt_mkOf (R : RankedAlphabet) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool) :
    semAt (R.arity i) (mkOf R i).1.1 (mkOf R i).2 f = algMk R i f := by
  rw [mkOf, semAt_prependOf, semAt_flattenOf, algMk]

/-- The growth condition at the constant `R.width`, which `length_algMk`
gives with equality. -/
theorem growth_algMk (R : RankedAlphabet) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool) :
    (algMk R i f).length ≤ (List.ofFn fun d ↦ (f d).length).sum + R.width :=
  Nat.le_of_eq (length_algMk R i f)

/-- The pending values stay linear in the input, at the same constant. This
is the hypothesis `Geb.CobhamFold.foldOutExprV` takes, discharged by
`Geb.CobhamFold.stackSize_le_of_growth` from the per-symbol condition
alone. -/
theorem stackSize_algMk_le (R : RankedAlphabet) (w : List Bool) :
    stackSize (foldScanFinal R (algMk R) w).stack ≤ R.width * w.length :=
  stackSize_le_of_growth R (algMk R) R.width (growth_algMk R) w

/-- The slot concatenation carries no `smash`: the empty bitstring at arity
zero, and a `concat` composition of projections at every successor. -/
theorem smashFreeBool_flattenOf : ∀ n : ℕ,
    smashFreeBool (flattenOf n).1.1.1 = true :=
  Nat.rec (smashFreeBool_zeroAtOf 0) fun n ih ↦
    smashFreeBool_concatCompOf (n + 1) _ _
      (smashFreeBool_compOf _ _ ih fun i ↦ smashFreeBool_projOf (n + 1) i.succ)
      (smashFreeBool_projOf (n + 1) 0)

/-- The structure map's expression carries no `smash`, which is
`Geb.CobhamFold.smashFree_foldOutExprV`'s hypothesis at this algebra. -/
theorem smashFreeBool_mkOf (R : RankedAlphabet) (i : Fin R.card) :
    smashFreeBool (mkOf R i).1.1.1 = true :=
  smashFreeBool_prependOf _ _ (smashFreeBool_flattenOf (R.arity i))

end Geb.CobhamFold

end
