/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Translation -- shake: keep
public meta import Geb.Prototypes.FreeTopos.Translation -- shake: keep
public import Geb.Prototypes.FreeTopos.Internal.Prove -- shake: keep
public meta import Geb.Prototypes.FreeTopos.Internal.Prove -- shake: keep

set_option doc.verso true in
/-!
# The translation of kernel programs

The library of the translation compiles, each definition over those before it, and computes:
the arithmetic, comparison, logarithm and iteration of bitstrings, normalized, give the numerals
of the natural numbers' operations. The translation of a program read from its source is tested
by {lit}`GebTests.Prototypes.FreeTopos.TranslationSources`.

## Main definitions

* {lit}`baseRules` — the rules of the language's equations at the translation's primitive arrows.
* {lit}`value`, {lit}`computes` — the value of a closed term of the library, and whether it is a
  number's numeral.
* {lit}`sizeM` — the number of nodes of a term.

## Tags

internal language, System T, translation, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Translation

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation
open scoped FinEnum
open Internal (Term NormRule)

-- the library compiles, each definition over those before it
#guard (Internal.compileDefs (globals [])).isSome

/-- The rules of the language's equations at the translation's primitive arrows: β, the
components of pairs, the folds of lists and of rose trees at their constructions, and the case
analysis of bits. -/
def baseRules : List NormRule := [.rule .beta, .rule .fstPair, .rule .sndPair,
  .rule (.listNil 0), .rule (.listCons 1), .rule (.roseNode 2 0 1), .rule (.caseInl 5 3),
  .rule (.caseInr 5 4)]

/-- The value of a closed term of the library: its normal form, every definition unfolded. -/
def value (t : Term) : Option Term :=
  (Internal.normalizeW (globals []) #[] 0 (baseRules ++ (List.range lib.length).map .delta) 4096
    [] [] t).map Prod.fst

/-- Whether a closed term of the library computes the numeral of a number. -/
def computes (t : Term) (n : ℕ) : Bool := match value t, value (numeral n) with
  | some a, some b => decide (a = b)
  | _, _ => false

/-- The numerals below a bound. -/
def below (k : ℕ) : List ℕ := List.range k

/-- The pairs of numbers below a bound. -/
def pairsBelow (k : ℕ) : List (ℕ × ℕ) := (below k).flatMap fun m ↦ (below k).map (m, ·)

/-- The numeral of a truth value: one or zero. -/
def ofBool (b : Bool) : ℕ := if b then 1 else 0

-- the successor, the predecessor, doubling and the logarithm
#guard (below 40).all fun n ↦ computes (call D.succ [] [numeral n]) (n + 1)
#guard (below 40).all fun n ↦ computes (call D.pred [] [numeral n]) (n - 1)
#guard (below 40).all fun n ↦ computes (call D.dbl [] [numeral n]) (2 * n)
#guard (below 70).all fun n ↦ computes (call D.log2 [] [numeral n]) n.log2

-- the binary operations, the comparisons as one or zero
#guard (pairsBelow 9).all fun (m, n) ↦ computes (call D.add [] [numeral m, numeral n]) (m + n)
#guard (pairsBelow 9).all fun (m, n) ↦ computes (call D.sub [] [numeral m, numeral n]) (m - n)
#guard (pairsBelow 9).all fun (m, n) ↦ computes (call D.mul [] [numeral m, numeral n]) (m * n)
#guard (pairsBelow 9).all fun (m, n) ↦
  computes (Term.fst (call D.divMod [] [numeral m, numeral n])) (m / n) &&
    computes (Term.snd (call D.divMod [] [numeral m, numeral n])) (m % n)
#guard (pairsBelow 9).all fun (m, n) ↦
  computes (call D.ltB [] [numeral m, numeral n]) (ofBool (decide (m < n))) &&
    computes (call D.eqB [] [numeral m, numeral n]) (ofBool (decide (m = n)))

-- iteration of the successor
#guard (pairsBelow 6).all fun (m, n) ↦ computes
  (call D.iter [bitsTy] [numeral n, Term.lam bitsTy (call D.succ [] [v 0]), numeral m]) (m + n)

-- larger numbers
#guard computes (call D.add [] [numeral 100000, numeral 234567]) 334567 &&
  computes (call D.mul [] [numeral 123, numeral 456]) (123 * 456) &&
  computes (Term.fst (call D.divMod [] [numeral 12345, numeral 67])) (12345 / 67) &&
  computes (Term.snd (call D.divMod [] [numeral 12345, numeral 67])) (12345 % 67) &&
  computes (call D.sub [] [numeral 1000000, numeral 999]) 999001 &&
  computes (call D.log2 [] [numeral 1000000]) (Nat.log2 1000000)

/-- The number of nodes of a term. -/
def sizeM : Internal.Term → ℕ := RoseTree.elim fun _ rs ↦ 1 + rs.sum

end GebTests.Prototypes.FreeTopos.Translation

end
