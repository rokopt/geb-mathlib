/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.SingletonGraph
public import Geb.Prototypes.InteractionNet.ConfigGraphNormal
public import Geb.Prototypes.InteractionNet.KernelGraph
public import Geb.Prototypes.InteractionNet.Observation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Reading compiled kernel result graphs

The graph compiler preserves the canonical final tree configuration used by the kernel's
textual normalization theorem. Its graph is normal and the whole-net reader recovers the
represented tree, including the checks that every cell is visited once and no closed wire
remains. These results identify the canonical target of graph normalization.

## Main definitions

* {lit}`Kernel.graphFinal` — compile the canonical final tree configuration.

## Main statements

* {lit}`Kernel.graphFinal_readTree` — whole-net observation recovers the represented tree.
* {lit}`Kernel.graphFinal_normal` — the compiled final configuration is graph-normal.

## Tags

bootstrap, kernel, interaction net, compiler, graph, normal form, read-back
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Kernel

open Geb.Kernel FirstOrder

/-- The generic constructor fold uses exactly the kernel's existing tree observation. -/
theorem constructorReadback_eq (t : Term (netArity (φ := Op) dataArity) ℕ) :
    t.constructorReadback graphTreeTag = readback t := by
  refine PFunctor.FreeM.rec (fun _ ↦ rfl) (fun a ts ih ↦ ?_) t
  rcases a with (a | a) | a
  · cases a <;> try rfl
    rename_i l n
    change (do
      let cs ← (List.ofFn fun i ↦ Term.constructorReadback graphTreeTag (ts i)).mapM id
      pure (RoseTree.node l cs)) = _
    simp only [ih]
    change (do
      let cs ← (List.ofFn fun i ↦ readback (ts i)).mapM id
      pure (RoseTree.node l cs)) =
        ((List.ofFn fun i ↦ readback (ts i)).mapM id).map (RoseTree.node l)
    cases (List.ofFn fun i ↦ readback (ts i)).mapM id <;> rfl
  · rfl
  · rfl

/-- Assemble the canonical final tree configuration with its otherwise unused name supply. -/
def graphFinal (t : Tree) (next : ℕ) : FiniteNet (netArity (φ := Op) dataArity) 1 :=
  (Config.singleton (treeTerm t) next).toFiniteNet
    (Config.singleton_closed _ _ (treeTerm_names t))

/-- The whole compiled result graph reads back the represented kernel tree. -/
theorem graphFinal_readTree (t : Tree) (next : ℕ) :
    FiniteNet.readTree graphTreeTag (graphFinal t next) = some t := by
  change FiniteNet.readTree graphTreeTag
    ((Config.singleton (treeTerm t) next).toFiniteNet _) = _
  rw [Config.singleton_readTree _ _ _ (treeTerm_names t),
    constructorReadback_eq, readback_treeTerm]

/-- Every compiled canonical result is a normal graph for the kernel's interaction rules. -/
theorem graphFinal_normal (P : List Tree) (t : Tree) (next : ℕ) :
    Schedule.Normal (Graph.Step (graphSystem P)) (Graph.ofNet (graphFinal t next)) :=
  (Config.singleton (treeTerm t) next).graph_normal_of_equations_eq_nil
    (Config.singleton_closed _ _ (treeTerm_names t)) rfl (graphSystem P)

end Geb.InteractionNet.Kernel

end
