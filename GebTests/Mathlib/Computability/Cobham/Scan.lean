/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Computability.Cobham.Scan
public import Geb.Mathlib.Computability.Cobham.Tree

/-!
# Tests for the scan combinator

A scanner over two steps that compute differently, so that the samples
distinguish the two step children; the bound child at a growth other than
one and at zero; and a scanner whose recursion bound is discharged from
`Cobham.scanSem_eq`.
-/

set_option linter.privateModule false

open Cobham

/-- A scan whose `false` step prepends a bit and whose `true` step drops
one, so that the two steps are told apart by their values. -/
def splitRaw : sig.toPFunctor.W := scanRaw (oneAtRaw 0) incRaw predRaw 1

/-- The meaning of that scan, read at the raw tree. -/
def splitSem : Sem 1 :=
  transport (fst_eval ⟨splitRaw, by decide⟩) (eval ⟨splitRaw, by decide⟩).2

/-- The scan of the empty word is the base, `[true]`. -/
theorem splitSem_nil : splitSem ![[]] = [true] := rfl

/-- The `true` step drops the base's bit and the `false` step prepends to
that, so the value is `[true]` again. Transposing the two step children
would prepend first and drop after, giving `[true]` as well at this word but
not at the next. -/
theorem splitSem_false_true : splitSem ![[false, true]] = [true] := rfl

/-- With the bits exchanged the order of application reverses: the `false`
step prepends to the base and the `true` step drops from that. -/
theorem splitSem_true_false : splitSem ![[true, false]] = [true] := rfl

/-- Two `true` bits drop both bits, leaving the empty word. -/
theorem splitSem_true_true : splitSem ![[true, true]] = [] := rfl

/-- The bound child at growth zero is the recursion variable itself. -/
theorem boundSem_zero (u : List Bool) : boundSem 0 ![u] = u := by
  rw [boundSem_eq]
  rfl

/-- The bound child at a growth other than one prepends that many bits. -/
theorem boundSem_three (u : List Bool) :
    boundSem 3 ![u] = [true, true, true] ++ u := by
  rw [boundSem_eq]
  rfl

/-- The identity on the sole argument, as a raw tree of arity one. Named
apart from `constScan` because instance search discharges `WValid` by
`decide` only at a named constant, not at a literal `WType.mk`
application. -/
def idRaw : sig.toPFunctor.W := WType.mk (.proj 1 0) Fin.elim0

/-- `idRaw` as an expression of arity one. -/
def idOf : COf 1 :=
  ⟨⟨⟨idRaw, by decide⟩, ⟨trivial, fun c ↦ c.elim0⟩⟩, rfl⟩

/-- The scan step built from `idOf` on both branches is the identity,
whichever bit selects it: both branches read back the state unchanged. -/
theorem scanStepWord_idOf (b : Bool) (r : List Bool) :
    scanStepWord idOf idOf b r = r := by
  cases b <;> rfl

/-- The fold of the identity step over any word returns the base
unchanged. -/
theorem foldr_scanStepWord_idOf (w : List Bool) :
    w.foldr (scanStepWord idOf idOf) (baseWord (oneAtOf 0)) = baseWord (oneAtOf 0) :=
  List.rec rfl (fun b v ih ↦ by rw [List.foldr_cons, ih, scanStepWord_idOf]) w

/-- A scanner whose recursion bound is discharged from `scanSem_eq`: both
steps are the identity on the state, so the fold returns the base at every
word, of length one. -/
def constScan : C :=
  scan (oneAtOf 0) idOf idOf 1
    (fun w ↦ by
      rw [scanSem_eq, foldr_scanStepWord_idOf]
      exact Nat.le_add_left 1 w.length)
