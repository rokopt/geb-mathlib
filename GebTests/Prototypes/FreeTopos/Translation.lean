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
public import GebTests.Prototypes.Stage0 -- shake: keep
public meta import GebTests.Prototypes.Stage0 -- shake: keep

set_option doc.verso true in
/-!
# The translation of kernel programs

The library of the translation compiles, each definition over those before it, and computes:
the arithmetic, comparison, logarithm and iteration of bitstrings, normalized, give the numerals
of the natural numbers' operations. The programs the proofs in Gödel's T are about, the
prelude, the reader and the kernel's type checker written in the kernel's syntax, translate: each
definition's translation has, in the internal language, the translation of its kernel type. The
literals' cost is printed: the sizes of the program and of its translation, and of the latter's
numerals.

## Main definitions

* {lit}`kernelText` — the text of the prelude, the reader and the type checker.
* {lit}`translated` — a program's translation.
* {lit}`value`, {lit}`computes` — the value of a closed term of the library, and whether it is a
  number's numeral.
* {lit}`literalCost` — the sizes of the program and of its translation.

## Tags

internal language, System T, translation, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Translation

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation
open scoped FinEnum
open Internal (Term NormRule)

/-- The text of the prelude, the reader and the kernel's type checker. -/
def kernelText : String :=
  Kernel.Stage0Tests.prelude ++ "\n" ++ Kernel.Stage0Tests.reader ++ "\n" ++
    Kernel.Stage0Tests.check

/-- A program's translation, from its text read by the seed: the kernel types of its globals and
the definitions of the internal language. -/
def translated (text : List Char) : Option (List Tree × List Internal.Defn) :=
  (Kernel.readProgram text).bind fun ds ↦ program (ds.map Prod.snd)

-- the library compiles, each definition over those before it
#guard (Internal.compileDefs (globals [])).isSome

-- the program translates
#guard (translated kernelText.toList).isSome

-- each translated definition compiles, to the translation of its kernel type
#guard (translated kernelText.toList).any fun (gt, defs) ↦
  (Internal.compileDefs (globals defs)).isSome &&
    (gt.zip defs).all fun (A, d) ↦ ty A == some d.type

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

/-- The number of nodes of a tree. -/
def sizeK : Tree → ℕ := RoseTree.elim fun _ rs ↦ 1 + rs.sum

/-- The number of nodes of a term. -/
def sizeM : Internal.Term → ℕ := RoseTree.elim fun _ rs ↦ 1 + rs.sum

/-- The number of the nodes of a term's numerals: the applications of the definitions of the
empty bitstring and of a bit before a bitstring. -/
def numeralNodes : Internal.Term → ℕ := RoseTree.elim fun l rs ↦
  (match l with
    | .defn k [] => if k = D.bnil ∨ k = D.b0 ∨ k = D.b1 then 1 else 0
    | _ => 0) + rs.sum

/-- The number of quoted trees in a kernel term, and their nodes. -/
def quotes : Tree → ℕ × ℕ := RoseTree.para fun l cs ↦
  if l = Kernel.Label.quote then (1, (cs.head?.map fun c ↦ sizeK c.1).getD 0)
  else ((cs.map (·.2.1)).sum, (cs.map (·.2.2)).sum)

/-- The literals' cost of a program, from its text, printed: the program's definitions, nodes,
quoted trees and their nodes, and its translation's nodes, the numerals' nodes among them, and
the library's nodes. -/
def literalCost (text : List Char) : IO Unit := do
  match Kernel.readProgram text, translated text with
  | some ds, some (_, defs) =>
    IO.println ("definitions,kernel_nodes,quoted_trees,quoted_nodes,translation_nodes," ++
      "numeral_nodes,library_nodes")
    let row := [ds.length, (ds.map fun d ↦ sizeK d.2).sum, (ds.map fun d ↦ (quotes d.2).1).sum,
      (ds.map fun d ↦ (quotes d.2).2).sum, (defs.map fun d ↦ sizeM d.body).sum,
      (defs.map fun d ↦ numeralNodes d.body).sum, (lib.map fun d ↦ sizeM d.body).sum]
    IO.println (",".intercalate (row.map toString))
  | _, _ => throw (IO.userError "the program does not translate")

#eval literalCost kernelText.toList

end GebTests.Prototypes.FreeTopos.Translation

end
