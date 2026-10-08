/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import GebBench

/-!
# Benchmark entry point

Run the benchmarks of `GebBench` with `lake exe geb-bench`, each table preceded by the line naming
its module; the entry point is outside the library's module prefix.

## Main definitions

* `main`: run every benchmark.
-/

/-- Run every benchmark, each table preceded by the line naming its module. -/
public def main : IO Unit := do
  IO.println "# GebBench.Prototypes.SuccinctTree"
  GebBench.Prototypes.SuccinctTree.run
  IO.println "# GebBench.Prototypes.FreeTopos.TranslationProofs"
  GebBench.Prototypes.FreeTopos.TranslationProofs.run
