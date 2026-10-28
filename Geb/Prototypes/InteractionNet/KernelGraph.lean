/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ProgramGraph
public import Geb.Prototypes.InteractionNet.Kernel
public import Geb.Prototypes.InteractionNet.GraphObservation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Executing compiled kernel programs as port graphs

Kernel syntax compiles through the existing first-order program translation. Linear textual
rule bodies and the initial configuration are assembled as finite port graphs, stored as
partner arrays, and reduced by the verified graph runtime. Tree read-back accepts only
rose-tree constructors after graph reduction has reached a normal form.

## Main definitions

* {lit}`Kernel.graphSystem` — kernel rules compiled to finite graph replacements.
* {lit}`Kernel.graphInitial` — the initial graph for a closed function and input tree.
* {lit}`Kernel.graphRun` — bounded array-graph execution and tree read-back.

## Main statements

* {lit}`Kernel.graphRun_result_eq` — every successful execution bound returns the same tree.

## Tags

bootstrap, kernel, compiler, interaction net, graph runtime, tree, read-back
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Kernel

open Geb.Kernel FirstOrder

/-- Compile the kernel program's rules to oriented finite graph replacements. -/
def graphSystem (P : List Tree) : PortSystem (netArity (φ := Op) dataArity) :=
  FirstOrder.graphSystem dataArity (program P)

/-- Compile a closed function and input tree to the initial finite port graph. -/
def graphInitial (t x : Tree) : Option (FiniteNet (netArity (φ := Op) dataArity) 1) :=
  (compile t []).map fun f ↦ FirstOrder.graphInitial dataArity (apply f (literal x))

/-- Only a rose-tree constructor supplies a read-back node label. -/
def graphTreeTag : Agent (φ := Op) dataArity → Option ℕ
  | .inl (.inl (.tree l _)) => some l
  | _ => none

/-- Execute the compiled partner-array graph, then read its whole normal tree. -/
def graphRun (P : List Tree) (steps : ℕ) (t x : Tree) : Option Tree := do
  let n ← graphInitial t x
  let m ← GraphRuntime.run (graphSystem P) steps (GraphRuntime.encode n)
  GraphRuntime.readTree graphTreeTag m

/-- Every successful graph-execution bound computes the same observed tree. -/
theorem graphRun_result_eq (P : List Tree) (steps steps' : ℕ) (t x y z : Tree)
    (h : graphRun P steps t x = some y) (h' : graphRun P steps' t x = some z) : y = z := by
  unfold graphRun at h h'
  cases hi : graphInitial t x with
  | none =>
    simp only [hi, bind, Option.bind_none] at h
    cases h
  | some n =>
    simp only [hi, bind, Option.bind_some] at h h'
    obtain ⟨m, hm, hy⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨k, hk, hz⟩ := Option.bind_eq_some_iff.mp h'
    have hr := GraphRuntime.run_readTree_eq graphTreeTag hm hk
    exact Option.some.inj (hy.symm.trans (hr.trans hz))

end Geb.InteractionNet.Kernel

end
