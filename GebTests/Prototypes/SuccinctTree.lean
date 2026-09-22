/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.SuccinctTree -- shake: keep
public meta import Geb.Prototypes.SuccinctTree -- shake: keep
public import Geb.Prototypes.Computability.SizeBounded.Logspace.EliasTree -- shake: keep
public meta import Geb.Prototypes.Computability.SizeBounded.Logspace.EliasTree -- shake: keep
public import Geb.Prototypes.Computability.SizeBounded.Sharing -- shake: keep
public meta import Geb.Prototypes.Computability.SizeBounded.Sharing -- shake: keep
public import Geb.Prototypes.CanonicalSExpr -- shake: keep
public meta import Geb.Prototypes.CanonicalSExpr -- shake: keep

set_option doc.verso true in
/-!
# Executed storage experiments

These checks cover malformed parentheses, word boundaries, independently scanned
blocks, and the repository's worked Elias encodings. The benchmark evaluates the
existing native scanner and shared algebra interpretation in Lean's interpreter.
Its timings are diagnostic, not compiled-C or end-to-end typechecking measurements.
The syntax experiment uses the repository's rose-tree parser and printer, including
the one-child orientation exercised by its concrete-syntax examples.

## Tags

balanced parentheses, differential test, benchmark, Elias code
-/

set_option doc.verso true
set_option linter.privateModule false

open Geb.SuccinctTree

#guard balanced (bitSteps [true, false])
#guard balanced (bitSteps [true, true, false, false])
#guard balanced (bitSteps [true, false, true, false]) -- A forest, not a single root.
#guard !balanced (bitSteps [false, true])
#guard !balanced (bitSteps [true, true, false])
#guard wordBits 8 0 = List.replicate 8 false
#guard wordBits 8 256 = wordBits 8 0 -- Bits beyond the declared width are excluded.
example (a b : ℕ) : summarize (bitSteps (wordBits 8 a ++ wordBits 8 b)) =
    (wordSummary 8 a).append (wordSummary 8 b) := by
  simp [bitSteps, wordSummary, summarize_append]

/-- Evaluate and time one recognizer; the input is prepared before the timer starts. -/
def timeRecognition (label : String) (recognize : List Bool → Bool) (w : List Bool) : IO Unit := do
  let start ← IO.monoNanosNow
  let accepted := recognize w
  if !accepted then throw (IO.userError s!"{label}: expected a valid encoding")
  let stop ← IO.monoNanosNow
  IO.println s!"{label},{w.length},{stop - start}"

/-- Compare the existing streaming scanner with the shared expression interpreter on a leaf. -/
def benchmarkRecognition : IO Unit := do
  IO.println "implementation,input_bits,nanoseconds"
  for payload in [0, 1, 8, 32] do
    let w := Geb.BitTree.Elias.encode (Geb.BitTree.leaf (List.replicate payload true))
    timeRecognition "native-scanner" Geb.BitTree.Elias.Scanner.validBool w
    timeRecognition "shared-algebra" (fun w ↦
      !(Geb.SizeBounded.Logspace.EliasTree.isEliasTree.1.semVec ![w]).isEmpty) w

#eval benchmarkRecognition

/-- Time parsing and exact comparison of the existing rose syntax, with printing excluded. -/
def timeSyntax (label : String) (tree : Geb.Rose 3) : IO Unit := do
  let input := Geb.Rose.print tree
  let start ← IO.monoNanosNow
  if Geb.Rose.parse 3 input != some tree then
    throw (IO.userError s!"{label}: parse/print disagreement")
  let stop ← IO.monoNanosNow
  IO.println s!"{label},{input.length},{stop - start}"

/-- Exercise deep and wide syntax trees using the existing parser, printer, and equality. -/
def benchmarkSyntax : IO Unit := do
  IO.println "syntax_shape,input_characters,parse_and_equality_nanoseconds"
  for n in [16, 64, 256] do
    let tip : Geb.Rose 3 := Geb.Rose.node 2 Fin.elim0
    let chain := n.rec tip (fun _ t ↦ Geb.Rose.node 1 ![t])
    let wide : Geb.Rose 3 := Geb.Rose.node 0 (fun _ : Fin n ↦ tip)
    timeSyntax s!"chain-{n}" chain
    timeSyntax s!"wide-{n}" wide

#eval benchmarkSyntax
