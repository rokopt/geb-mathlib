/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.W.Basic

/-!
# Tests for the W-type fold laws

A concrete fold over binary trees exercises the computation rule and the
uniqueness of `WType.elim`.

## Tags

W-type, fold, initial algebra
-/

set_option linter.privateModule false

/-- The branching family of the test W-type: `false` a leaf (no
children), `true` a node with two children. -/
abbrev TestBranch : Bool → Type := fun b ↦ cond b Bool Empty

/-- The algebra computing a node count. Factored out as a named
definition so that `WType.elim_mk` and `WType.elim_unique` unify with it
without unfolding the fold. -/
def nodeCountStep : (Σ b : Bool, TestBranch b → Nat) → Nat
  | ⟨false, _⟩ => 1
  | ⟨true, f⟩ => 1 + f true + f false

/-- The node count of a test tree, as a fold. -/
def nodeCount : WType TestBranch → Nat :=
  WType.elim Nat nodeCountStep

-- The computation rule fires on a constructor application.
example (f : Bool → WType TestBranch) :
    nodeCount (WType.mk true f) = 1 + nodeCount (f true) + nodeCount (f false) :=
  WType.elim_mk nodeCountStep true f

/-- Uniqueness: any function satisfying the same recursion is the fold.
This is the declaration that anchors the import: its proof term names
`WType.elim_unique`, so `lake shake` observes the module under test. -/
theorem nodeCount_unique (g : WType TestBranch → Nat)
    (hg : ∀ (b : Bool) (f : TestBranch b → WType TestBranch),
      g (WType.mk b f) = nodeCountStep ⟨b, fun c ↦ g (f c)⟩) :
    g = nodeCount :=
  WType.elim_unique nodeCountStep g hg

/-- A concrete tree: a branching root over two leaves. -/
def testTree : WType TestBranch :=
  WType.mk true (fun _ ↦ WType.mk false Empty.elim)

-- The fold evaluates: the test tree has three nodes.
example : nodeCount testTree = 3 := rfl
