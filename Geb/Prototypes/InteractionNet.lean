/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module -- shake: keep-all

public import Geb.Prototypes.InteractionNet.ActivePair
public import Geb.Prototypes.InteractionNet.Allocation
public import Geb.Prototypes.InteractionNet.ArrayContraction
public import Geb.Prototypes.InteractionNet.ArrayNet
public import Geb.Prototypes.InteractionNet.ArrayReadback
public import Geb.Prototypes.InteractionNet.ArrayWiring
public import Geb.Prototypes.InteractionNet.AssemblyEmbedding
public import Geb.Prototypes.InteractionNet.AssemblyIso
public import Geb.Prototypes.InteractionNet.BoundaryClosure
public import Geb.Prototypes.InteractionNet.BoundaryComposition
public import Geb.Prototypes.InteractionNet.BoundaryJoin
public import Geb.Prototypes.InteractionNet.BoundaryRenaming
public import Geb.Prototypes.InteractionNet.BoundarySplice
public import Geb.Prototypes.InteractionNet.Calculus
public import Geb.Prototypes.InteractionNet.CalculusGraphSimulation
public import Geb.Prototypes.InteractionNet.CalculusInterface
public import Geb.Prototypes.InteractionNet.Call
public import Geb.Prototypes.InteractionNet.ClosedTermReadback
public import Geb.Prototypes.InteractionNet.ConfigAgentPairContext
public import Geb.Prototypes.InteractionNet.ConfigAgentPairForest
public import Geb.Prototypes.InteractionNet.ConfigAppendForest
public import Geb.Prototypes.InteractionNet.ConfigAppendOccurrences
public import Geb.Prototypes.InteractionNet.ConfigEliminationAllocation
public import Geb.Prototypes.InteractionNet.ConfigEliminationContext
public import Geb.Prototypes.InteractionNet.ConfigEliminationForest
public import Geb.Prototypes.InteractionNet.ConfigEliminationOccurrences
public import Geb.Prototypes.InteractionNet.ConfigEliminationSimulation
public import Geb.Prototypes.InteractionNet.ConfigGraph
public import Geb.Prototypes.InteractionNet.ConfigGraphBoundary
public import Geb.Prototypes.InteractionNet.ConfigGraphContext
public import Geb.Prototypes.InteractionNet.ConfigGraphIso
public import Geb.Prototypes.InteractionNet.ConfigGraphNormal
public import Geb.Prototypes.InteractionNet.ConfigGraphPermutation
public import Geb.Prototypes.InteractionNet.ConfigGraphRenaming
public import Geb.Prototypes.InteractionNet.ConfigHeadForest
public import Geb.Prototypes.InteractionNet.ConfigHeadOccurrences
public import Geb.Prototypes.InteractionNet.ConfigInteractionAllocation
public import Geb.Prototypes.InteractionNet.ConfigInteractionAssembly
public import Geb.Prototypes.InteractionNet.ConfigInteractionBoundary
public import Geb.Prototypes.InteractionNet.ConfigInteractionContext
public import Geb.Prototypes.InteractionNet.ConfigInteractionEmbedding
public import Geb.Prototypes.InteractionNet.ConfigInteractionForest
public import Geb.Prototypes.InteractionNet.ConfigInteractionLeaves
public import Geb.Prototypes.InteractionNet.ConfigInteractionSimulation
public import Geb.Prototypes.InteractionNet.ConfigInteractionWiring
public import Geb.Prototypes.InteractionNet.ConfigNamelessGraph
public import Geb.Prototypes.InteractionNet.ConfigSubstitutionGraph
public import Geb.Prototypes.InteractionNet.ConfigVariableEquation
public import Geb.Prototypes.InteractionNet.ConstructorReadback
public import Geb.Prototypes.InteractionNet.Contraction
public import Geb.Prototypes.InteractionNet.ContractionCommute
public import Geb.Prototypes.InteractionNet.ContractionCoupling
public import Geb.Prototypes.InteractionNet.ContractionEmbedding
public import Geb.Prototypes.InteractionNet.ContractionIso
public import Geb.Prototypes.InteractionNet.ContractionPorts
public import Geb.Prototypes.InteractionNet.ContractionRenaming
public import Geb.Prototypes.InteractionNet.ContractionSequence
public import Geb.Prototypes.InteractionNet.Copying
public import Geb.Prototypes.InteractionNet.CopyingNormalization
public import Geb.Prototypes.InteractionNet.CouplingCancellation
public import Geb.Prototypes.InteractionNet.CouplingComposition
public import Geb.Prototypes.InteractionNet.CouplingIdentity
public import Geb.Prototypes.InteractionNet.CouplingWires
public import Geb.Prototypes.InteractionNet.Data
public import Geb.Prototypes.InteractionNet.EquationGraph
public import Geb.Prototypes.InteractionNet.EquationGraphSubstitution
public import Geb.Prototypes.InteractionNet.Erasure
public import Geb.Prototypes.InteractionNet.Evaluation
public import Geb.Prototypes.InteractionNet.Execution
public import Geb.Prototypes.InteractionNet.ExecutionGraphSimulation
public import Geb.Prototypes.InteractionNet.Expression
public import Geb.Prototypes.InteractionNet.FiniteCells
public import Geb.Prototypes.InteractionNet.FinitePorts
public import Geb.Prototypes.InteractionNet.FiniteSum
public import Geb.Prototypes.InteractionNet.FiniteWiring
public import Geb.Prototypes.InteractionNet.ForestAttachment
public import Geb.Prototypes.InteractionNet.ForestAttachmentContext
public import Geb.Prototypes.InteractionNet.ForestIso
public import Geb.Prototypes.InteractionNet.ForestSubstitution
public import Geb.Prototypes.InteractionNet.GraphAssembly
public import Geb.Prototypes.InteractionNet.GraphClosure
public import Geb.Prototypes.InteractionNet.GraphConfluence
public import Geb.Prototypes.InteractionNet.GraphContext
public import Geb.Prototypes.InteractionNet.GraphObservation
public import Geb.Prototypes.InteractionNet.GraphReadback
public import Geb.Prototypes.InteractionNet.GraphReadbackBoundary
public import Geb.Prototypes.InteractionNet.GraphRuntime
public import Geb.Prototypes.InteractionNet.GraphRuntimeAdequacy
public import Geb.Prototypes.InteractionNet.HeadPairGraph
public import Geb.Prototypes.InteractionNet.JoinClosure
public import Geb.Prototypes.InteractionNet.Kernel
public import Geb.Prototypes.InteractionNet.KernelAdequacy
public import Geb.Prototypes.InteractionNet.KernelApplication
public import Geb.Prototypes.InteractionNet.KernelContext
public import Geb.Prototypes.InteractionNet.KernelControl
public import Geb.Prototypes.InteractionNet.KernelEquality
public import Geb.Prototypes.InteractionNet.KernelEvaluation
public import Geb.Prototypes.InteractionNet.KernelGraph
public import Geb.Prototypes.InteractionNet.KernelGraphAdequacy
public import Geb.Prototypes.InteractionNet.KernelGraphReadback
public import Geb.Prototypes.InteractionNet.KernelPrimitives
public import Geb.Prototypes.InteractionNet.KernelRecursors
public import Geb.Prototypes.InteractionNet.KernelRules
public import Geb.Prototypes.InteractionNet.KernelSaturation
public import Geb.Prototypes.InteractionNet.KernelValue
public import Geb.Prototypes.InteractionNet.KernelValueShape
public import Geb.Prototypes.InteractionNet.NamedSplice
public import Geb.Prototypes.InteractionNet.NamedWiring
public import Geb.Prototypes.InteractionNet.Normalization
public import Geb.Prototypes.InteractionNet.Observation
public import Geb.Prototypes.InteractionNet.OccurrencePermutation
public import Geb.Prototypes.InteractionNet.OpenPair
public import Geb.Prototypes.InteractionNet.Output
public import Geb.Prototypes.InteractionNet.PairReconstruction
public import Geb.Prototypes.InteractionNet.PairedBoundary
public import Geb.Prototypes.InteractionNet.PartialClosure
public import Geb.Prototypes.InteractionNet.PartialClosureCoupling
public import Geb.Prototypes.InteractionNet.PartialClosureIdentity
public import Geb.Prototypes.InteractionNet.PlugEmbedding
public import Geb.Prototypes.InteractionNet.PlugIso
public import Geb.Prototypes.InteractionNet.PortNet
public import Geb.Prototypes.InteractionNet.PortNetOperations
public import Geb.Prototypes.InteractionNet.PortNetPlug
public import Geb.Prototypes.InteractionNet.PortNetSum
public import Geb.Prototypes.InteractionNet.PortSystem
public import Geb.Prototypes.InteractionNet.Preservation
public import Geb.Prototypes.InteractionNet.Program
public import Geb.Prototypes.InteractionNet.ProgramCorrect
public import Geb.Prototypes.InteractionNet.ProgramGraph
public import Geb.Prototypes.InteractionNet.RedexDiamond
public import Geb.Prototypes.InteractionNet.RemainingCells
public import Geb.Prototypes.InteractionNet.RuleBoundaryOccurrences
public import Geb.Prototypes.InteractionNet.RuleGraph
public import Geb.Prototypes.InteractionNet.RuleInstantiationAllocation
public import Geb.Prototypes.InteractionNet.RuleInstantiationCancellation
public import Geb.Prototypes.InteractionNet.RuleInstantiationCells
public import Geb.Prototypes.InteractionNet.RuleInstantiationForest
public import Geb.Prototypes.InteractionNet.RuleInstantiationLeaves
public import Geb.Prototypes.InteractionNet.RuleInstantiationSplices
public import Geb.Prototypes.InteractionNet.RuleInternalWiring
public import Geb.Prototypes.InteractionNet.RuleLeafPartition
public import Geb.Prototypes.InteractionNet.RuleOpenForest
public import Geb.Prototypes.InteractionNet.Schedule
public import Geb.Prototypes.InteractionNet.SingletonGraph
public import Geb.Prototypes.InteractionNet.Substitution
public import Geb.Prototypes.InteractionNet.Tasks
public import Geb.Prototypes.InteractionNet.Term
public import Geb.Prototypes.InteractionNet.TermAttachmentAgent
public import Geb.Prototypes.InteractionNet.TermAttachmentVariable
public import Geb.Prototypes.InteractionNet.TermCellOrder
public import Geb.Prototypes.InteractionNet.TermGraph
public import Geb.Prototypes.InteractionNet.TermGraphAttachment
public import Geb.Prototypes.InteractionNet.TermGraphNormal
public import Geb.Prototypes.InteractionNet.TermGraphReadback
public import Geb.Prototypes.InteractionNet.TermGraphRenaming
public import Geb.Prototypes.InteractionNet.TermGraphSimulation
public import Geb.Prototypes.InteractionNet.TermGraphSubstitution
public import Geb.Prototypes.InteractionNet.TermGraphSum
public import Geb.Prototypes.InteractionNet.Wiring
public import Geb.Prototypes.InteractionNet.WiringCancellation
public import Geb.Prototypes.InteractionNet.WiringCompose
public import Geb.Prototypes.InteractionNet.WiringEmbedding
public import Geb.Prototypes.InteractionNet.WiringGlue
public import Geb.Prototypes.InteractionNet.WiringIndex
public import Geb.Prototypes.InteractionNet.WiringRelocation
public import Geb.Prototypes.InteractionNet.WiringSelection
public import Geb.Prototypes.InteractionNet.WiringSplice
public import Geb.Prototypes.InteractionNet.WiringSubdivision
public import Geb.Prototypes.InteractionNet.WiringSwap

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
matching invariant; disjoint graph contractions commute, including their closed-loop counts.
Contraction respects cell renaming. Oriented rule tables have a strict graph diamond,
confluence of finite schedules and termination whenever one schedule reaches a normal form.
The array runtime refines graph contraction and preserves its matching invariant.
A successful bounded run reads back a graph normal form; graph normalization guarantees
success at some finite bound. Linear textual rules and closed configurations compile to
finite graphs, and the kernel has an executable array-graph entry point. Tree observation
is invariant under cell renaming and agrees across all normalizing graph schedules.
Every finite textual execution remains closed and eligible for graph assembly.
Textual substitution of arbitrary nested terms agrees with attachment of their graph fragments,
including both the wire matching and closed-loop count.
The correspondence extends to assembled forests and complete substituted configurations.
Boundary attachment preserves graph contractions and finite schedules.
Linear rule instantiation retains the rule's cells and inserts each argument's cells once,
preserving their symbols. A successful textual agent contraction exposes graph progress
in either orientation and at any equation position.
Injective wire renaming, equation permutation and equation reversal preserve the compiled graph.
Equation-free configurations compile to graph normal forms for every rule table.
The whole-net reader recovers every represented kernel tree from its compiled final configuration,
including the checks for complete cell coverage and absence of closed wires.
Textual wire elimination preserves the complete represented graph, including its ordered
external interface and closed-wire count. Its proof cancels variable extensions in the
substitution forest and identifies the surviving root and named-wire matchings.
The head interaction now decomposes into its argument forest and unchanged context;
contracting its reconstructed pair inserts the replacement at the exposed argument roots.
Linear rule instantiation preserves all source named wires and adds the internal rule wires.
The compiler-to-graph simulation remains in progress: textual interaction must refine graph
contraction, then transfer the established typed normalization and denotation theorem.

## Tags

bootstrap, interaction net, kernel, sequential reduction, defunctionalization
-/
