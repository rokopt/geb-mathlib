/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Choice-free product and exponential encodings of `Fin`

mathlib's `finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)` and
`finFunctionFinEquiv : (Fin n → Fin m) ≃ Fin (m ^ n)` both depend on
`Classical.choice`, the first through `Fin.divNat` and the second
through the `Finset.sum` lemmas its round trips run on. The two
equivalences here are their choice-free counterparts.

The exponential is built by recursion on the arity over the product
encoding rather than by base-`n` digit arithmetic: the digit
construction's round trips are `Finset.sum` lemmas, each a separate
choice audit, and mathlib's version of that construction is the one
that depends on `Classical.choice`. The recursion is an explicit
`Nat.rec` at the motive `fun k ↦ (Fin k → Fin m) ≃ Fin (m ^ k)`, per
`docs/rules/lean-coding.md` § Recursion and induction through
recursors.

## Main definitions

* `finProdFinEquivC` — the product encoding.
* `finFunctionFinEquivC` — the exponential encoding.
* `Fin.funEncodeC`, `Fin.funDecodeC` — its two directions under
  names the `simp` lemmas are stated over.

## Main statements

* `Fin.funDecodeC_funEncodeC`, `Fin.funEncodeC_funDecodeC` — the two
  round trips of the exponential encoding.

## Tags

fin, equiv, product, exponential, choice-free
-/

@[expose] public section

/-- The choice-free product encoding, assembled from `Fin.pairC`,
`Fin.divNatC` and `Fin.modNatC` (unlike mathlib's
`finProdFinEquiv`, which depends on `Classical.choice`). -/
def finProdFinEquivC {m n : ℕ} : Fin m × Fin n ≃ Fin (m * n) where
  toFun p := Fin.pairC p.1 p.2
  invFun i := (Fin.divNatC i, Fin.modNatC i)
  left_inv p := Prod.ext (Fin.divNatC_pairC p.1 p.2) (Fin.modNatC_pairC p.1 p.2)
  right_inv i := Fin.pairC_divNatC_modNatC i
