/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebBench.Prototypes.FreeTopos.TranslationProofs
public import GebBench.Prototypes.SuccinctTree

set_option doc.verso true in
/-!
# Benchmarks

Measurements of the prototypes' programs, run by {lit}`lake exe geb-bench` rather than built with
the tests: each prints a table of its timings, which change from run to run and machine to machine
and so are no test's result. {lit}`slow-checks.yml` runs them daily and on demand.

## Tags

benchmark, measurement
-/
