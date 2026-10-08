/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.CanonicalSExpr
public import Geb.Prototypes.Computability.SizeBounded.Logspace.EliasTree
public import Geb.Prototypes.Computability.SizeBounded.Sharing

set_option doc.verso true in
/-!
# Recognition and syntax of succinct trees, timed

The native scanner and the shared algebra's interpretation recognizing Elias encodings of growing
payloads, and the rose syntax's parser and equality on deep and wide trees, each timed in
nanoseconds, the input prepared before the timer starts.

## Main definitions

* {lit}`benchmarkRecognition` — the recognizers at payload lengths.
* {lit}`benchmarkSyntax` — parsing and equality at chains and fans.
* {lit}`run` — both.

## Tags

balanced parentheses, Elias code, rose syntax, benchmark
-/

set_option doc.verso true

@[expose] public section

namespace GebBench.Prototypes.SuccinctTree

/-- Evaluate and time one recognizer; the input is prepared before the timer starts. -/
def timeRecognition (label : String) (recognize : List Bool → Bool) (w : List Bool) : IO Unit := do
  let start ← IO.monoNanosNow
  let accepted := recognize w
  if !accepted then throw (IO.userError s!"{label}: expected a valid encoding")
  let stop ← IO.monoNanosNow
  IO.println s!"{label},{w.length},{stop - start}"

/-- Compare the native scanner with the shared expression interpreter at the
given payload lengths. -/
def benchmarkRecognition (payloads : List ℕ) : IO Unit := do
  IO.println "implementation,input_bits,nanoseconds"
  for payload in payloads do
    let w := Geb.BitTree.Elias.encode (Geb.BitTree.leaf (List.replicate payload true))
    timeRecognition "native-scanner" Geb.BitTree.Elias.Scanner.validBool w
    timeRecognition "shared-algebra" (fun w ↦
      !(Geb.SizeBounded.Logspace.EliasTree.isEliasTree.1.semVec ![w]).isEmpty) w

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

set_option compiler.extract_closed false in
/-- The recognizers at the payloads of lengths zero, one, two and four, and the syntax. Closed
terms are not extracted, so that each evaluation runs when it is timed rather than when the
program starts. -/
def run : IO Unit := do
  benchmarkRecognition [0, 1, 2, 4]
  benchmarkSyntax

end GebBench.Prototypes.SuccinctTree

end
