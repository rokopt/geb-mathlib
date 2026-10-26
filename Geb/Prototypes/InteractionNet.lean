/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module -- shake: keep-all

public import Geb.Prototypes.InteractionNet.Allocation
public import Geb.Prototypes.InteractionNet.Calculus
public import Geb.Prototypes.InteractionNet.Call
public import Geb.Prototypes.InteractionNet.Copying
public import Geb.Prototypes.InteractionNet.CopyingNormalization
public import Geb.Prototypes.InteractionNet.Data
public import Geb.Prototypes.InteractionNet.Erasure
public import Geb.Prototypes.InteractionNet.Evaluation
public import Geb.Prototypes.InteractionNet.Execution
public import Geb.Prototypes.InteractionNet.Expression
public import Geb.Prototypes.InteractionNet.FiniteSum
public import Geb.Prototypes.InteractionNet.Kernel
public import Geb.Prototypes.InteractionNet.KernelAdequacy
public import Geb.Prototypes.InteractionNet.KernelApplication
public import Geb.Prototypes.InteractionNet.KernelContext
public import Geb.Prototypes.InteractionNet.KernelControl
public import Geb.Prototypes.InteractionNet.KernelEquality
public import Geb.Prototypes.InteractionNet.KernelEvaluation
public import Geb.Prototypes.InteractionNet.KernelPrimitives
public import Geb.Prototypes.InteractionNet.KernelRecursors
public import Geb.Prototypes.InteractionNet.KernelRules
public import Geb.Prototypes.InteractionNet.KernelSaturation
public import Geb.Prototypes.InteractionNet.KernelValue
public import Geb.Prototypes.InteractionNet.KernelValueShape
public import Geb.Prototypes.InteractionNet.Normalization
public import Geb.Prototypes.InteractionNet.Observation
public import Geb.Prototypes.InteractionNet.Output
public import Geb.Prototypes.InteractionNet.PortNet
public import Geb.Prototypes.InteractionNet.Preservation
public import Geb.Prototypes.InteractionNet.Program
public import Geb.Prototypes.InteractionNet.ProgramCorrect
public import Geb.Prototypes.InteractionNet.Schedule
public import Geb.Prototypes.InteractionNet.Term
public import Geb.Prototypes.InteractionNet.Substitution
public import Geb.Prototypes.InteractionNet.Tasks
public import Geb.Prototypes.InteractionNet.Wiring
public import Geb.Prototypes.InteractionNet.WiringGlue
public import Geb.Prototypes.InteractionNet.WiringSplice

set_option doc.verso true in
/-!
# First-order interaction nets for the bootstrap kernel

The prototype compiles the kernel to a program-specific interaction system with
defunctionalized closures, constructor copying, explicit allocation, a sequential reducer
and tree read-back. Its rules are linear, every finite execution preserves the wire
invariant, erasure and copying terminate on every constructor value, and a successful bounded run
returns the read-back of a reached normal configuration.
Tree read-back recovers every represented tree. Contextual expression evaluation composes
the environment-copying, child-evaluation and constructor-dispatch phases of the reducer.
Runtime values are related to the existing evaluator's values. Tree and list recursion
operations preserve this relation whenever the step's applications do.
Primitive dispatch preserves the relation, including recursive tree equality.

The first bootstrap milestone is complete. Evaluation and application are simulated at
every fuel level, connecting contextual net execution to the kernel evaluator's logical
relation. Every accepted closed tree-to-tree term, with successfully loaded globals, reaches
the canonical normal configuration for its denotation on every input. The executable runner
therefore returns that denotation at some finite bound, and any successful bound returns
the same result. Loaded globals satisfy the corresponding execution theorem.

## Main statements

* {lit}`Kernel.normalizes_of_infer` — every accepted closed term reaches its normal tree result.
* {lit}`Kernel.run_of_infer` — the executable runner computes the kernel denotation.
* {lit}`Kernel.result_eq_of_infer` — a successful run cannot return a different tree.
* {lit}`Kernel.run_of_load` — execution adequacy for loaded globals.

The next milestones are in progress: confluence across schedules and refinement by a graph
runtime. The finite-net foundation has explicit cells and ordered ports, boundary-preserving
renamings, wire matchings and closed loops. Splicing and finite boundary gluing preserve the
matching invariant; disjoint splices commute, including their closed-loop counts.
The general strict-diamond theorems separate normal-form agreement from termination of
arbitrary schedules. Applying them to graph contraction and bridging the existing compiler
remain the next steps.

## Tags

bootstrap, interaction net, kernel, sequential reduction, defunctionalization
-/
