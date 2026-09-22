# Reflection for interaction nets and polynomial operational semantics

This document specifies possible extensions of interaction combinators and
polynomial operational semantics with structural observation. It records
the mathematical constructions, their relation to published results, and
the definitions and proof obligations needed for an implementation.

The proposed marked-cell decomposition and GSOS observation enrichment
below are mathematical constructions to formalize. They are not attributed
to the cited papers, and no completed Lean implementation of either is
claimed here. The existing source declarations are identified separately.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope and conclusions](#scope-and-conclusions)
- [The tree-calculus comparison](#the-tree-calculus-comparison)
- [A structural eliminator for interaction nets](#a-structural-eliminator-for-interaction-nets)
  - [Nets contain wiring as well as cell symbols](#nets-contain-wiring-as-well-as-cell-symbols)
  - [Removing a designated cell](#removing-a-designated-cell)
  - [The coproduct universal property](#the-coproduct-universal-property)
  - [An indexed polynomial presentation](#an-indexed-polynomial-presentation)
- [From a destructor to an executing calculus](#from-a-destructor-to-an-executing-calculus)
  - [Local inspection and whole-net access](#local-inspection-and-whole-net-access)
  - [Observation must have an evaluation protocol](#observation-must-have-an-evaluation-protocol)
  - [What universality supplies](#what-universality-supplies)
- [Structural observation for abstract GSOS](#structural-observation-for-abstract-gsos)
  - [The ordinary rule format](#the-ordinary-rule-format)
  - [Enriching behavior with one syntax layer](#enriching-behavior-with-one-syntax-layer)
  - [What the enrichment does and does not establish](#what-the-enrichment-does-and-does-not-establish)
- [Effective reflection of operational specifications](#effective-reflection-of-operational-specifications)
- [Fair merge and polynomial evolution](#fair-merge-and-polynomial-evolution)
  - [The separation result and its scope](#the-separation-result-and-its-scope)
  - [Polynomial branching does not choose fair paths](#polynomial-branching-does-not-choose-fair-paths)
  - [A nonblocking polling construction](#a-nonblocking-polling-construction)
  - [Specifying fair executions](#specifying-fair-executions)
- [Existing formalizations](#existing-formalizations)
- [Implementation order and proof obligations](#implementation-order-and-proof-obligations)
  - [Fix the observation contract](#fix-the-observation-contract)
  - [Establish structural reconstruction first](#establish-structural-reconstruction-first)
  - [Connect graph values to reduction](#connect-graph-values-to-reduction)
  - [Formalize the generic enrichment](#formalize-the-generic-enrichment)
  - [Add the selected progress guarantee](#add-the-selected-progress-guarantee)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope and conclusions

There is a structural eliminator for an interaction net with a designated
cell: remove that cell, expose its ports as boundary ports, and branch on
its symbol. The result retains the surrounding graph, including sharing,
cycles, and disconnected components. This gives a coproduct elimination
principle, although it is not the recursive tree decomposition used by
tree calculus.

Making this eliminator available inside an executing calculus requires a
representation and an observation protocol. A local interaction agent can
inspect a cell presented at its principal port. An operator that inspects
an arbitrary whole net additionally needs access to its graph and control
over concurrent reduction. Frozen graph values with explicit stepping
provide a first implementation target.

For abstract GSOS, a natural construction enriches the behavior functor
with one layer of syntax. On closed terms its coalgebra is the pair of
ordinary behavior and structural decomposition. This establishes a
semantic interface for structural observation; an internal interpreter
and an object-language destructor require further constructions.

Fairness is a separate property of executions. Polynomial functors can
describe branching and nonblocking polling, and GSOS can compose those
operations. Neither a polynomial presentation nor reflection alone
selects fair executions or supplies a polling interface for opaque inputs.

The following distinctions determine the implementation's claims:

| Property | Required evidence |
| --- | --- |
| Structural observation | A representation, destructor, and reconstruction laws. |
| Internal reflection | Object-language code for inspection and execution, with adequacy proofs. |
| Reflection of the semantics | Represented rules and an interpreter that accepts their representations. |
| Preservation of ordinary behavior | A projection or simulation relating the enriched system to the original. |
| Preservation of graph composition and concurrency | Compatibility with interfaces, gluing, and independent reductions. |
| Fair execution | A scheduler or admissibility condition, with a progress theorem for the specified inputs. |

These properties do not assert an increase in the partial recursive
functions on natural numbers. They concern the structure available to
programs and the preservation of observations, interaction, and progress.

## The tree-calculus comparison

The triage formulation makes the comparison with SK explicit. Its values
have the polynomial decomposition

```text
V ≅ 1 + V + V².
```

Writing application left-associatively and using `D` for the tree
constructor, its reduction rules are:

```text
D D         y z       → y
D (D x)     y z       → x z (y z)
D (D w x)   y D       → w
D (D w x)   y (D u)   → x u
D (D w x)   y (D u v) → y u v
```

Thus `D D` acts as `K`, `D (D x)` as `S x`, and the last three rules
dispatch on leaf, stem, and fork. Jay gives these correspondences in
[Jay2024CalculusCalculi]. The distinction between triage and the earlier
tree-calculus presentation matters when transcribing the rules; see also
[TreeCalculusSpecification].

For handlers `h₀ : 1 → R`, `h₁ : V → R`, and `h₂ : V² → R`, the
structural eliminator is the composite

```text
V ──out──▶ 1 + V + V² ──[h₀,h₁,h₂]──▶ R.
```

The values themselves have this observable structure. This is stronger
than choosing an external encoding of SK terms and writing an interpreter
for the encoding. It does not mean that arbitrary reducible expressions
can be inspected without specifying evaluation behavior.

The current [triage syntax][triage-syntax] uses a W-type with leaf, stem,
and fork shapes. Its expression syntax distinguishes values from pending
applications. The [reduction module][triage-reduction] defines `contract`
and its selection, duplication, and triage equations. These provide the
existing reference for the distinction between stable values and active
computation.

## A structural eliminator for interaction nets

### Nets contain wiring as well as cell symbols

For interaction combinators, the polynomial

```text
1 + X² + X²
```

records the auxiliary arities of epsilon, gamma, and delta. Its initial
algebra consists of trees. It does not record the arbitrary wiring of an
interaction net.

Use a signature `Σ` with an auxiliary arity `a(α)` for each symbol. A
finite net with finite boundary `Γ` can be represented by:

- A finite type of cells `C` and a labeling map `ℓ : C → Σ`.
- For each cell `c`, ports `Fin (a(ℓ(c)) + 1)`, with port zero principal
  and the others ordered auxiliary ports.
- A fixed-point-free involution on the endpoint type
  `Γ + Σ (c : C), Fin (a(ℓ(c)) + 1)`.
- A natural number recording closed wire components with no endpoints.

The involution pairs every endpoint with exactly one other endpoint.
Wires between two ports of the same cell, disconnected subnets, and
boundary-to-boundary wires are permitted. A closed wire is separate data;
it is not a fixed point of the involution on actual ports. This choice
retains the closed wires allowed by Lafont's definition
([Lafont1997], §1.1). De Falco provides a permutation-based treatment of
interaction nets and their gluing [DeFalco2010].

The observational convention here identifies internal cell renamings,
while preserving boundary labels, cell symbols, and port positions. Write
`NΣ(Γ)` for the resulting isomorphism classes. An implementation can first
use explicit graph isomorphisms and only later form a quotient. Exposing
allocation identifiers would define a different observation interface.

### Removing a designated cell

Let `NΣ•(Γ)` denote nets with a distinguished cell, with isomorphisms
required to preserve that cell. Put

```text
Pα = Fin (a(α) + 1).
```

The proposed structural equivalence is

```text
NΣ•(Γ) ≅ Σ (α : Σ), NΣ(Γ + Pα).                    (1)
```

For the forward map, remove the distinguished cell of symbol `α` and
reinterpret each of its ports as a fresh boundary port indexed by `Pα`.
Retain every wire and every other cell. For the inverse, insert a fresh
`α` cell and reinterpret the `Pα` part of the boundary as its ports.

These constructions are inverse up to internal renaming. A wire joining
two ports of the removed cell becomes a wire joining two newly exposed
boundary ports. A wire to another cell retains that connection. No
unfolding, copying, traversal, or reduction occurs. Closed wires and
disconnected components are unchanged.

For the original or symmetric interaction-combinator signature, (1)
specializes to

```text
N•(Γ) ≅ N(Γ + 3) + N(Γ + 3) + N(Γ + 1),
```

with summands for gamma, delta, and epsilon. The numbers include the
principal port. This operation removes a single designated cell; an
ordinary interaction reduction instead consumes two principal-connected
cells and exposes their auxiliary interfaces.

### The coproduct universal property

For a family of handlers

```text
hα : NΣ(Γ + Pα) → R,
```

the composite of (1) with the coproduct map `[hα]` is the unique function
on designated-cell nets with the prescribed behavior in each symbol case.
This is the requested universal property for mapping out of a coproduct.
It also has a dependent elimination form when the result type depends on
the exposed symbol and residual graph.

The designation is part of the input. An arbitrary unrooted net has no
given cell to inspect, and a boundary may reach an auxiliary port or no
cell at all. There need not be a cell fixed by every automorphism, so a
concrete choice commuting with all graph isomorphisms is unavailable in
general. An allocation-order traversal is possible on a concrete
representation, but its independence from that order is a separate
obligation.

Repeated deletion ends in a net with no cells. That base case consists of
a matching of the original and exposed boundary ports together with the
closed-wire count. It is not necessarily the empty net. A whole-net fold
that is independent of deletion order needs coherence laws relating
different orders of deletion.

### An indexed polynomial presentation

Let `Wire(Γ)` be the no-cell nets on `Γ`. On families indexed by finite
boundaries, consider

```text
(F X)(Γ) = Wire(Γ) + Σ (α : Σ), X(Γ + Pα).           (2)
```

This polynomial describes insertion histories: a finite sequence of
cell insertions ending in a wiring. Every finite net has such a history,
given an enumeration of its cells. Different histories can describe
isomorphic graphs.

Consequently, `μ F` alone is not the intended graph type. A presentation
by (2) requires equations for exchanging insertion order and transporting
boundary names. Proving that those equations identify exactly the
isomorphic nets is a further presentation theorem. It is unnecessary for
the first formalization of (1), which can use finite graphs directly.

## From a destructor to an executing calculus

### Local inspection and whole-net access

A new interaction agent can have rules for its active pairs with gamma,
delta, and epsilon. Such rules can branch on the encountered symbol and
route its auxiliary connections to a continuation. To remain an ordinary
interaction system, each rule must have the correct interface and each
unordered pair of symbols must have at most one rule.

This observes cells that can be presented at the probe's principal port.
It does not supply access to a cell already participating in another
active pair, a cell reached only through an auxiliary port, or an
unconnected component. In particular, changing a disconnected component
cannot affect a purely local boundary observer. This is an access
limitation for arbitrary raw nets, not an impossibility of interpreting
an explicit representation of them.

Equation (1) is therefore a specification for graph values. It does not
by itself supply a single additional interaction agent implementing
whole-net reflection. A proposed set of agent rules must demonstrate the
access protocol as well as the symbol cases.

### Observation must have an evaluation protocol

Structural observation of a running net can conflict with reduction.
Suppose a whole-net observer reports the number of cells. A net consisting
of an epsilon-epsilon active pair has two cells before reduction and none
afterward. If both inspection and internal reduction may occur first,
and the two results are distinct terminal observations, the extended
system is not confluent.

Possible protocols include:

- Inspect stable graph values whose object-level reductions are disabled.
- Inspect an immutable snapshot produced by an explicit ownership or
  synchronization operation.
- Specify scheduled live observation, accepting its dependence on the
  reduction schedule and proving the resulting semantics.

The first option is the proposed initial target. Object graphs are data;
`view`, reconstruction, and an explicit `step` operate on that data.
The host computation implementing those operations may itself use nets.
Representing an object graph as data does not globally suspend arbitrary
host nets: crossing between the two representations needs a separate
quotation or execution interface.

Inspection must not require normalization. Normalization may diverge,
and it can erase the structure that inspection was intended to reveal.
Copying an active net, copying its frozen representation, and sharing an
immutable graph value also have different operational meanings.

### What universality supplies

Lafont gives encodings of interaction systems into interaction
combinators and develops packaged nets with copying and decoding
operations ([Lafont1997], §§1.7, 2.6). This is evidence for implementing a
finite reflective interaction system through an encoding, once that
system satisfies the translation theorem's hypotheses. It does not
supply a runtime function that quotes an arbitrary live net while leaving
its original representation and behavior unchanged.

In particular, a translation may replace every old cell by an encoding.
It need not be a macro expansion that preserves all existing cells and
only replaces the new destructor. Likewise, a sequential interpreter
does not establish preservation of graph composition, available
parallelism, or asymptotic cost.

The same design issues apply to symmetric interaction combinators. Their
translation properties differ from those of Lafont's original system;
equal computational expressiveness does not identify the translations.
See [Lafont1997], §3.4, and [Mazza2009] for the symmetric system and its
observational semantics.

## Structural observation for abstract GSOS

### The ordinary rule format

Let `Σ` be a syntax functor, `B` a behavior functor, and `T = TΣ` the free
monad on `Σ`, with unit `η`. An abstract GSOS law has type

```text
ρX : Σ(X × B X) → B(T X),
```

natural in `X`. It receives the current subterms abstractly and their
one-step behaviors. It does not receive arbitrary operations for
inspecting the internal syntax of elements of `X`.

Under the usual existence hypotheses, this format supports bialgebraic
operational semantics. Under the additional hypotheses used for the
bisimilarity result, including weak-pullback preservation of `B`, the
induced behavioral equivalence is a congruence
([TuriPlotkin1997], §§4, 7).

This constrains structural extensions that keep the old observations.
For example, two differently constructed deadlocked terms may be
`B`-bisimilar. A new context that emits different observable labels
according to their root syntax would distinguish them. It cannot both
retain that old bisimilarity and satisfy the applicable congruence
theorem. The obstruction concerns the specified behavior and theorem
hypotheses; it is not an impossibility of intensional GSOS semantics.

### Enriching behavior with one syntax layer

Define

```text
B♯ X = B X × Σ X.
```

For each `X`, let the following projections discard the additional
structural observation or select the current operand:

```text
pX : X × (B X × Σ X) → X × B X
pX(x, (b, s)) = (x, b)

rX : X × (B X × Σ X) → X
rX(x, (b, s)) = x.
```

The proposed enriched GSOS law is

```text
ρ♯X : Σ(X × B♯ X) → B♯(T X)

ρ♯X(z) = (ρX(Σ(pX)(z)), Σ(ηX ∘ rX)(z)).            (3)
```

The first component applies the old rule. The second retains the current
outer constructor, placing each operand in the free monad by `η`. Both
components are natural. If `Σ` and `B` are polynomial, so is `B♯`.

Suppose `S = μ Σ` exists, with constructor `in : Σ S → S` and inverse
`out`. Let `c : S → B S` be the original induced operational coalgebra.
The intended theorem for (3) is

```text
c♯ : S → B S × Σ S
c♯ = (c, out).                                      (4)
```

To prove it, use the bialgebra equation and the evaluation algebra
`eval : T S → S`. The second component of that equation is

```text
second(c♯(in(u)))
  = Σ(eval)(Σ(ηS)(u))
  = u,
```

using `eval ∘ ηS = id`. The first component is the original operational
equation after forgetting the added observation. The uniqueness of the
induced operational coalgebra then identifies it with `c`.

This proof gives explicit obligations: type (3), prove naturality,
identify the induced coalgebra, and prove its projection is `c`.
No closed terms need exist for a particular signature; for example, a
signature with only binary constructors has an empty initial algebra.
The law itself can still be studied on supplied coalgebras and final
behaviors.

### What the enrichment does and does not establish

Repeated structural observations in (4) expose the term's construction
tree. Projecting away those observations recovers the original behavior.
Thus ordinary behavior is preserved by projection, while the enriched
behavioral equivalence can distinguish formerly equivalent terms.
Preservation by projection is not full abstraction for the old
equivalence.

Equation (3) keeps the same syntax functor. It does not yet add syntax
for invoking a destructor, reassembling a term, or interpreting rule
code. Adding those operators requires their syntax, result sorts, and
operational rules. Those rules must form a law for the extended signature
and chosen observations.

For graphs, a construction tree may reveal insertion history rather than
the graph up to isomorphism. Using (3) on a graph-expression language
therefore requires either retaining that history intentionally or proving
compatibility with its graph equations. Equation (1) addresses graph
structure directly.

More generally, for a polynomial coalgebra `c : S → P S`, inspecting
`c(s)` exposes one behavioral layer. This need not reconstruct the state
`s`, its implementation, or the code of `c`. A state representation and
an evaluator are additional data.

## Effective reflection of operational specifications

For an effectively presented system, use codes for signatures, terms or
graphs, rules, and execution states. Define structural elimination on
codes and an interpreter for the represented rules. An elementary-step
interface permits execution without requiring normalization.

The minimum adequacy obligations are:

- Encoding and decoding preserve the selected structural equivalence.
- Every represented object step is simulated by the interpreter.
- Every reported interpreter step corresponds to an object step.
- Administrative interpreter steps do not introduce spurious visible
  behavior; claims about divergence require a corresponding progress
  argument.

A nondeterministic system needs a relation, an enumerator, or explicit
choices in this interface. A deterministic selection function alone does
not establish completeness for all executions. Finitely enumerable
successors allow a total list-valued `step`; an arbitrary effective rule
system need not permit terminating enumeration of all successors.

To reflect the semantics itself, rules and the interpreter's own language
must also have representations. Rewriting logic has an established
reflective construction of this kind [ClavelMeseguer1996]. The Maude work
on SOS meta-theory explicitly represents transition specifications and
GSOS conditions ([MousaviReniers2006], §§3–6). These are implementation
precedents, not proofs that every mathematical natural transformation
has executable finite code.

An arbitrary polynomial can have infinitely many or uncountably many
shapes, and its direction sets need not be finite or effectively
presented. Even a natural transformation between constant polynomial
functors can contain a noncomputable function. A uniform effective
interpreter therefore needs an effective presentation of both the
signature and the rule law. The categorical construction (3) has broader
scope than a finite executable reflective language.

## Fair merge and polynomial evolution

### The separation result and its scope

Ordinary interaction nets are confluent. The extension with McCarthy's
`amb` introduces nondeterminism and supports angelic and infinity merge,
but does not thereby implement fair merge [FernandezKhalil2002].

Panangaden and Shanbhogue prove that no total subset of the input-output
relation of fair merge is implementable by a finite network of components
with Hoare-monotone, limit-closed trace sets
([PanangadenShanbhogue1992], Theorem 9). Their completed computations
already incorporate a weak fairness condition (Definition 5). Thus the
separation cannot be explained solely by permitting an unfair scheduler.
A proposed implementation must identify which interface or semantic
hypothesis it changes.

A related elementary observation concerns infinite binary schedules:
every finite left/right prefix has a fair extension, while the all-left
schedule is unfair. Hence the fair schedules alone cannot be exactly all
paths through a prefix tree whose membership depends only on those
finite prefixes. This is a restricted statement. It does not rule out
hidden state, other branching structures, or a separate acceptance
condition on infinite paths.

### Polynomial branching does not choose fair paths

Finite ordered branching has the polynomial presentation

```text
List (L × X) ≅ Σ (labels : List L), X^(Fin labels.length).
```

It retains transition order and multiplicity. Replacing it by the finite
powerset changes the functor; finite powerset is not itself this
polynomial functor. Either representation describes available choices.
Fairness still needs a scheduler, an acceptance condition, or a stronger
type of execution.

The older GSOS prototype embeds any specified polynomial state machine
using one nullary operation for each complete state. This establishes a
GSOS presentation of the machine. Because complete configurations are
constants, it does not establish a compositional presentation of the
graph operations that constitute those configurations.

### A nonblocking polling construction

Assume source states with total elementary ticks

```text
left  : S → Option A × S
right : T → Option B × T.
```

Here `none` means a silent step. It is neither an end-of-stream test nor a
decision that a computation will never return. An executable interface
must make each tick terminate without waiting for an output event.

A merger state is `(s, t, turn)`. On a left turn, execute one left tick,
emit its optional output tagged by `inl`, retain `t`, and switch turns.
On a right turn, do the symmetric operation. Its behavior functor is

```text
Q X = Option (A + B) × X.
```

Starting on the left, the left source's tick numbered `n` contributes its
output at merger tick `2n`; the right source's tick numbered `n`
contributes at `2n + 1`, numbering from zero. Every source event is
preserved in order even if the other source remains silent forever.
The existing `merge_even`, `merge_left_output`, and `merge_right_output`
declarations express these properties.

For a common output alphabet, this also has a compositional GSOS law.
Take `Σ X = X² + X²`, with constructors `M_L` and `M_R`, and
`Q X = Option A × X`. Writing target variables as free-monad leaves:

```text
ρ(M_L((x, (a, x′)), (y, (b, y′)))) = (a, M_R(x′, y))
ρ(M_R((x, (a, x′)), (y, (b, y′)))) = (b, M_L(x, y′)).
```

Only the selected operand advances. The abstract law receives both
behaviors as mathematical data; a runtime must implement the intended
nonblocking access discipline rather than evaluate a blocking source to
produce that data. The older `pollingGSOS` declaration implements this
law in the polynomial API.

This is one fair servicing policy for the supplied tick interfaces.
It is not an implementation of the full fair-merge relation on opaque
streams. Relating it to that relation requires specifications for input
delivery, hiding silent steps, admissible runs, and completeness of the
allowed interleavings. Hiding must also account for finite output and
infinite silence; filtering silent ticks is not automatically a total
operation into productive infinite streams.

Reflection can support this construction by exposing source code and
allowing one computation step at a time. An explicit interpreter for
encoded SK terms can also provide such dovetailing. What matters is the
nonblocking step interface. Obtaining it from an opaque stream with only
a potentially blocking head operation is additional capability.

### Specifying fair executions

There are several distinct specifications to formalize:

- A fixed scheduler, such as the alternating polling policy, with a
  theorem that every source receives service after finitely many ticks.
- A transition system together with an explicit predicate selecting
  admissible fair runs.
- A type of executions whose constructors enforce finite waiting between
  recurring service events.

The last approach can combine least fixed points, for finite waiting,
with greatest fixed points, for indefinite repetition. Fair reactive
programming gives a typed treatment of such scheduling
([CaveFerreiraPanangadenPientka2014], §2.5). Its liveness guarantees depend
on the source and type interfaces; they are not a way to extract events
from arbitrary blocking computations.

If the scheduler or admissibility predicate is itself reflected as code,
the interpreter can expose it. Arbitrary transformations of that code
need not preserve fairness. Either restrict accepted transformations or
require a proof that they preserve the relevant progress property.

## Existing formalizations

The current implementation of triage is in
[Syntax.lean][triage-syntax] and [Reduction.lean][triage-reduction]. The
interaction-net, fair-merge, and GSOS sources discussed below belong to
the older `rokopt/geb` repository, under `geb-lean/GebLean/`. The links
pin revision `9c24f4727d3c6c34abece2174b04fd74e1ab37aa` so that these
claims can be checked independently of subsequent changes.

| Source | Reusable content | Limits relevant to this design |
| --- | --- | --- |
| [InteractionNets.lean][legacy-nets] | Cell symbols, raw nets, gluing, interaction rules, and a boundary observation. | The raw record does not enforce the port-pairing invariant. `obs` sees a principal-connected boundary cell, not the whole graph. |
| [PolyGSOS.lean][legacy-polygsos] | Polynomial GSOS rules, free constructions, distributive laws, and universal semantics. | These supply the categorical machinery; structural reflection still needs its law and adequacy theorems. |
| [Utilities/GSOSRule.lean][legacy-gsos] | The abstract GSOS rule type for functors. | Naturality does not expose syntax hidden in the carrier. |
| [InteractionExecution.lean][legacy-execution] | `machineGSOS`, list branching, `pollingGSOS`, polling progress equations, and schedule examples. | Whole-machine encodings do not prove graph compositionality; polling assumes total nonblocking ticks. |
| [FairMerge.lean][legacy-fairmerge] | `fair_not_paths`, concerning fair bitstreams and prefix-tree paths. | Its conclusion has the restricted scope stated above, not an impossibility theorem for all polynomial state spaces. |

The older net record stores an interface size, an array of optional cell
symbols, and a list of wire pairs. Its comment describes an invariant
that the type does not enforce. Its `contractOne` operation also drops a
closed connector cycle. Porting it as a representation of all nets in
Lafont's definition therefore requires a well-formedness invariant and
an explicit decision about closed-wire observations. Keeping closed
wires requires preserving them during gluing and reduction.

These source declarations identify reuse candidates and stated proof
interfaces. They do not substitute for compiling a port under the current
toolchain. The marked-cell equivalence and enrichment (3) should not be
reported as existing results on the basis of this inventory.

## Implementation order and proof obligations

### Fix the observation contract

For the initial implementation, use finite graph values up to internal
renaming, with named boundary ports, ordered auxiliary ports, and retained
closed wires. Observe a designated cell and retain the entire residual
graph. Execute object reductions only through an explicit step operation.
These choices make the destructor and reconstruction laws precise.

Keep three equivalences separate: equality of concrete encodings, graph
isomorphism, and behavioral equivalence. State which one every theorem
uses. In particular, graph reconstruction does not mean behavioral
normalization, and a behavioral quotient may discard exactly the
structure the destructor observes.

### Establish structural reconstruction first

Define well-formed finite nets and their boundary-preserving
isomorphisms, then the two maps in (1). Prove:

1. Removing a designated cell preserves well-formedness.
2. Inserting it reconstructs the original designated net up to
   isomorphism; removing an inserted cell reconstructs the residual net.
3. Both maps respect internal renaming and boundary bijections.
4. Removal decreases the number of cells by exactly one and preserves
   all wire incidences under the stated endpoint relabeling.
5. The induced coproduct eliminator satisfies its computation and
   uniqueness laws.

Use a cell with two ports joined to each other, a disconnected residual
component, and a retained closed wire as concrete examples. A test on
tree-shaped nets alone would not exercise the additional graph structure.

If a quotient representation is used, expose the equivalence only after
proving that the raw operations descend to the quotient. If insertion
histories are used instead, additionally prove the presentation theorem
for (2). Reuse the repository's polynomial and equivalence infrastructure
where its types match these statements.

### Connect graph values to reduction

Specify an active pair, a rule interface, and wire splicing. Prove that
one step preserves well-formedness, the external boundary, and internal
renaming. Account for closed wires produced by splicing. For simultaneous
independent redexes, prove the required commuting square.

Then define the code representation and explicit step interpreter, with
the soundness and completeness properties stated above. A bridge from
live nets to frozen graph values needs its own ownership, snapshot, or
representation protocol. The epsilon-epsilon observation example should
be resolved by that protocol, not left to an unspecified reduction order.

Only after these interfaces are established should the destructor be
realized as particular interaction-agent rules or compiled graph code.
For a compilation claim, state separately which of behavior, interface
composition, independent reductions, and costs it preserves.

### Formalize the generic enrichment

Implement (3) at the abstract GSOS level and prove naturality and (4).
For a polynomial implementation, prove agreement with that abstract law
rather than defining an unrelated operation with the same intended
behavior. Preserve the distinction between a general effective rule
language and an arbitrary mathematical GSOS law.

A subsequent internal language needs constructors for code and
observations, structural elimination, and a step evaluator. Specify the
extended signature and its operational law before claiming internal
reflection. Reflecting rule specifications is an additional stage, with
the interpreter itself among the representable programs.

### Add the selected progress guarantee

Port the nonblocking polling law and its existing progress equations as
the first scheduling instance. Include the case where one source is
silent forever and the other emits repeatedly. State the executable
termination condition on every elementary tick.

If the target is the full fair-merge relation, formulate that relation
and its admissible inputs independently, then prove both soundness and
completeness after hiding silent steps. The polling equations alone
establish neither this completeness nor a contradiction of the published
separation theorem.

For arbitrary polynomial evolution systems, parameterize any fairness
claim by its scheduler, execution type, or admissibility predicate. The
final specification should identify both the reflected structural data
and the condition that ensures progress.

## References

Bibliographic details are recorded in [references.bib](references.bib).
The source locations relevant to the constructions are:

- [Jay2024CalculusCalculi] — triage and the SK correspondences.
- [TreeCalculusSpecification] — the triage value forms and reduction rules.
- [Lafont1997] — §1.1 on nets, §1.7 on translations, §2.6 on codes,
  and §3.4 on the symmetric variant.
- [DeFalco2010] — finite permutation representations and net gluing.
- [Mazza2009] — observational equivalence for symmetric combinators.
- [TuriPlotkin1997] — abstract GSOS and its bialgebraic semantics;
  §7 supplies the behavioral-equivalence hypotheses.
- [ClavelMeseguer1996] — reflection of rewriting theories and strategies.
- [MousaviReniers2006] — represented SOS specifications, GSOS checks,
  and execution in Maude.
- [FernandezKhalil2002] — interaction nets extended with `amb` and the
  distinction between merge operators.
- [PanangadenShanbhogue1992] — Definition 5 and Theorem 9 delimit the
  fair-merge separation used here.
- [CaveFerreiraPanangadenPientka2014] — mixed inductive and coinductive
  types for liveness, especially §2.5 on scheduling.

[triage-syntax]: ../Geb/Prototypes/Computability/Triage/Syntax.lean
[triage-reduction]: ../Geb/Prototypes/Computability/Triage/Reduction.lean
[legacy-nets]: https://github.com/rokopt/geb/blob/9c24f4727d3c6c34abece2174b04fd74e1ab37aa/geb-lean/GebLean/InteractionNets.lean
[legacy-polygsos]: https://github.com/rokopt/geb/blob/9c24f4727d3c6c34abece2174b04fd74e1ab37aa/geb-lean/GebLean/PolyGSOS.lean
[legacy-gsos]: https://github.com/rokopt/geb/blob/9c24f4727d3c6c34abece2174b04fd74e1ab37aa/geb-lean/GebLean/Utilities/GSOSRule.lean
[legacy-execution]: https://github.com/rokopt/geb/blob/9c24f4727d3c6c34abece2174b04fd74e1ab37aa/geb-lean/GebLean/InteractionExecution.lean
[legacy-fairmerge]: https://github.com/rokopt/geb/blob/9c24f4727d3c6c34abece2174b04fd74e1ab37aa/geb-lean/GebLean/FairMerge.lean
[Jay2024CalculusCalculi]: https://github.com/barry-jay-personal/blog/blob/main/2024-12-12-calculus-calculi.md
[TreeCalculusSpecification]: https://treecalcul.us/specification/
[Lafont1997]: https://doi.org/10.1006/inco.1997.2643
[DeFalco2010]: https://arxiv.org/abs/1010.1066
[Mazza2009]: https://arxiv.org/abs/0906.0380
[TuriPlotkin1997]: https://homepages.inf.ed.ac.uk/gdp/publications/Math_Op_Sem.pdf
[ClavelMeseguer1996]: https://doi.org/10.1016/S1571-0661(04)00037-4
[MousaviReniers2006]: https://doi.org/10.1016/j.entcs.2005.09.030
[FernandezKhalil2002]: https://doi.org/10.1016/S1571-0661(05)80363-9
[PanangadenShanbhogue1992]: https://www.cs.mcgill.ca/~prakash/Pubs/fair_merge_iandc.pdf
[CaveFerreiraPanangadenPientka2014]: https://franciscoferreira.org/papers/fair-reactive.pdf
