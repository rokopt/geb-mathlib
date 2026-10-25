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
public import Geb.Prototypes.InteractionNet.KernelContext
public import Geb.Prototypes.InteractionNet.KernelRecursors
public import Geb.Prototypes.InteractionNet.KernelRules
public import Geb.Prototypes.InteractionNet.KernelValue
public import Geb.Prototypes.InteractionNet.KernelValueShape
public import Geb.Prototypes.InteractionNet.Normalization
public import Geb.Prototypes.InteractionNet.Observation
public import Geb.Prototypes.InteractionNet.Output
public import Geb.Prototypes.InteractionNet.Preservation
public import Geb.Prototypes.InteractionNet.Program
public import Geb.Prototypes.InteractionNet.ProgramCorrect
public import Geb.Prototypes.InteractionNet.Term
public import Geb.Prototypes.InteractionNet.Substitution
public import Geb.Prototypes.InteractionNet.Tasks

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

The first bootstrap milestone remains in progress. The missing acceptance theorem is that
every well-typed closed tree-to-tree program, on every input, reaches such a configuration
and that its read-back equals the kernel denotation. In particular, the structural
preservation and successful-run theorems do not establish normalization or adequacy.
The remaining proof connects the compiled kernel's contextual evaluations to the existing
logical relation for its first-order evaluator.

## Tags

bootstrap, interaction net, kernel, sequential reduction, defunctionalization
-/
