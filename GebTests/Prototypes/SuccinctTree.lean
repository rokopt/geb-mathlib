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
blocks, the repository's worked Elias encodings, the native scanner's and the shared
algebra's acceptance of them, and the rose-tree parser's inversion of the printer on
deep and wide trees, including the one-child orientation exercised by its
concrete-syntax examples. The recognizers and the syntax are timed by
{lit}`GebBench.Prototypes.SuccinctTree`.

## Tags

balanced parentheses, differential test, Elias code
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

-- both recognizers accept the Elias encodings of payloads of lengths zero and one
#guard [0, 1].all fun payload ↦
  let w := Geb.BitTree.Elias.encode (Geb.BitTree.leaf (List.replicate payload true))
  Geb.BitTree.Elias.Scanner.validBool w &&
    !(Geb.SizeBounded.Logspace.EliasTree.isEliasTree.1.semVec ![w]).isEmpty

-- the rose syntax parses what it prints, at chains and fans of 16, 64 and 256 nodes
#guard [16, 64, 256].all fun n ↦
  let tip : Geb.Rose 3 := Geb.Rose.node 2 Fin.elim0
  let chain := n.rec tip (fun _ t ↦ Geb.Rose.node 1 ![t])
  let wide : Geb.Rose 3 := Geb.Rose.node 0 (fun _ : Fin n ↦ tip)
  Geb.Rose.parse 3 (Geb.Rose.print chain) == some chain &&
    Geb.Rose.parse 3 (Geb.Rose.print wide) == some wide
