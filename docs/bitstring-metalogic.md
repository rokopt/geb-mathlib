# A bitstring metalogic with bounded computation

This document records the proposed architecture, the reasoning about
syntactic recognition, and the selected resource target. It is a design
discussion, not a formalization or a claim that the proposed complexity
bounds have been proved in Lean.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Carrier and recognized types](#carrier-and-recognized-types)
- [Generated equality](#generated-equality)
- [Syntactic categories and recognition](#syntactic-categories-and-recognition)
- [Certificate size and smaller checker classes](#certificate-size-and-smaller-checker-classes)
- [Selected resource target](#selected-resource-target)
- [Recognition, evaluation, and categorical structure](#recognition-evaluation-and-categorical-structure)
- [A single Turing-machine transition](#a-single-turing-machine-transition)
- [Tree-calculus reduction](#tree-calculus-reduction)
  - [The variant in the linked article](#the-variant-in-the-linked-article)
  - [Reusing the bit-tree carrier](#reusing-the-bit-tree-carrier)
  - [Size of one contraction](#size-of-one-contraction)
  - [Finding and contracting one redex](#finding-and-contracting-one-redex)
  - [Iteration and generated equality](#iteration-and-generated-equality)

<!-- END doctoc -->

## Carrier and recognized types

The proposed carrier is a type `B : Type 0` with decidable equality.
The initial instance is `B = List Bool`. Pair encodings, constructor
tags, acceptance conventions, and a computational size measure are
additional structure; decidable equality alone does not supply them.
Operations should assume the further properties they require.

A class of admissible endofunctions is a predicate
`C : (B → B) → Prop`, containing identity and closed under composition.
It is a submonoid of the endomorphism monoid of `B`, hence a one-object
category. The category whose objects are recognized types is a further
construction from this data.

Fix a computable acceptance test `accept : B → Bool`. Each admissible
recognizer `r : B → B` presents the Lean subtype
`{x : B // accept (r x) = true}`. For bitstrings, one convention is to
accept exactly `[true]`; a Boolean recognizer is then represented by
`fun x ↦ [r x]`. The cost of the acceptance test is part of recognition.
Different recognizers can present the same subset without being the
same endofunction.

The existing [bit-tree encoding][bit-tree-encoding] provides binary
forks and leaves carrying bitstrings. Its Boolean recognizer accepts
exactly the encodings of trees, with unique decoding. The existing
[complexity theorem][bit-tree-bound]
`Geb.BitTree.computableInTimeAndSpace_validBool` proves simultaneous
time `n + 3` and space `n + 2` for the singleton-bit output function.
This supplies a candidate recognized type of binary trees with
bitstrings at the leaves.

An arrow from recognizer `r` to recognizer `s` is represented by an
endofunction `f` preserving validity. Two representatives `f` and `g`
represent the same arrow when they agree on every valid input of `r`.
Their behavior on invalid inputs does not distinguish them. Whether
arrow representatives must belong to `C`, as well as recognizers,
must be explicit in the definition.

## Generated equality

A second level equips each recognized type with a computable binary
relation on its valid representatives. Pairs are encoded in `B` so the
test can still be an admissible endofunction. The relation generates
an equivalence relation, and the interpreted type is the quotient of
the valid representatives by that equivalence relation.

Membership in the representative type remains decidable. Equality in
the quotient can be undecidable, but need not be. The binary generator
is a check for an equality-generating step, not necessarily a decision
procedure for the resulting equality.

For bitstrings, generated equality is semidecidable: enumerate finite
paths of valid representatives and check that each adjacent pair is
related in either direction. A path exists exactly when the endpoints
are equivalent. Thus this construction gives computably enumerable
equality, rather than arbitrary undecidable equality. The relevant
literature is [Gao and Gerdes, *Computably Enumerable Equivalence
Relations*][ceers], arXiv:1012.0944.

Arrows must preserve both validity and generated equality. Their own
equality becomes pointwise equivalence of outputs on valid inputs.
Preservation of generating pairs into the codomain equivalence
relation suffices to establish preservation of the generated relation.
Pointwise equality of arrows quantifies over all valid inputs and is
not thereby semidecidable, even when equality of individual outputs is.

An alternative interface checks an explicit equality derivation:
`checkEq(x, y, p)`. Equality is existence of an accepted certificate
`p`, with reflexivity, symmetry, and transitivity supplied by the
derivation calculus. This fits the same bitstring carrier.

To recover a decidable binary generator from this interface, enlarge
the representatives with tagged, verified certificates `(x, y, p)`.
Connect each certificate representative to its two endpoints. Each
edge is decidable; connectivity between original terms gives their
provable equality. Every verified certificate is connected to an
original term, so it creates no additional quotient class. Without
such auxiliary representatives or an appropriate direct rewrite
presentation, checking whether some certificate connects two terms
would already be the semidecidable equality problem.

## Syntactic categories and recognition

The intended examples include the implemented
[`FinSetSkel` elementary topos][finset-topos] and the free elementary
topos with a natural numbers object, abbreviated NNO. The category of
finite sets itself has no NNO; these are separate examples.

In the syntactic construction described by [Lambek and Scott,
*Reflections on a categorical foundations of mathematics*,
Section 1.4][lambek-scott], objects are represented by predicates and
arrows by relations provably total and single-valued, modulo provable
equality. Pure intuitionistic higher-order arithmetic supplies the
free-topos example discussed in Section 1.7.1.

The recognition tasks must be distinguished:

| Input | Question | Computational requirement |
| --- | --- | --- |
| An expression | Is it well-formed and explicitly well-typed? | Syntax checking |
| A relation and a derivation | Does this prove functionality? | Proof checking |
| Two arrows and a derivation | Does this prove equality? | Proof checking |
| A relation without a derivation | Is functionality provable? | Proof search |
| Two arrows without a derivation | Is equality provable? | Proof search |

To obtain a decidable presentation of arrows, store a domain,
codomain, relation, and functionality derivation. Verify the supplied
derivation rather than search for one. Subsequent quotient equality
can ignore the choice of functionality derivation. A bare relation
whose functionality happens to be provable need not belong to a
decidable set.

A direct checker can use explicit types, contexts, intermediate
formulas, rule names, premise references, and equality derivations.
It checks substitutions and binding conditions syntactically, without
implicitly invoking normalization or mathematical proof search.
Repeated scans of an explicit presentation give a route to polynomial
time and linear storage. This is an algorithmic design argument; a
particular calculus and encoding are required for a formal bound.

[Cook and Reckhow, *The Relative Efficiency of Propositional Proof
Systems*, page 37][cook-reckhow], explicitly distinguish polynomial-time
proof verification from the length and discovery of proofs, including
proofs in set theory. Higher-order expressiveness does not by itself
force a higher-order or primitive-recursive evaluator into the checker.

## Certificate size and smaller checker classes

For any fixed effective proof system, a certificate can instead contain
a complete accepting computation history of a theorem recognizer.
Check the initial configuration, consecutive transitions, and final
acceptance. [Pfenning's computation-history lecture][histories]
describes the underlying use of configuration sequences as evidence.

For explicit, padded configurations, a multitape verifier can copy and
compare successive rows in time proportional to their lengths. Each
row participates in a bounded number of scans and rewinds. This gives
an algorithmic route to linear time and linear space in the total
certificate length. Repeated scans with position counters also give
a route to logarithmic auxiliary space under the usual read-only-input
convention. Neither assertion is a bound already proved in this
repository, nor a claim about a compact proof format.

Certificate length is not bounded by statement length in these
arguments. For undecidable theoremhood, there cannot be a total
computable bound on the shortest certificates for all theorems as a
function of statement length: checking all certificates up to such a
bound would decide theoremhood.

Consequently, inexpensive verification can present a theory with
undecidable theoremhood. It does not provide an inexpensive proof
search procedure, or a proof of that theory's consistency or soundness.

## Selected resource target

The selected target is simultaneous polynomial time and linear space,
measured in the length of the complete encoded input. One machine must
satisfy both bounds. Separate witnesses for polynomial time and linear
space do not establish this simultaneous claim.

The motivation combines polynomial time as a formal notion of feasible
computation with the relation between linear space and level two of
the Grzegorczyk hierarchy, below the elementary recursive functions
at level three. The latter correspondence requires explicit numerical
encoding and output-space conventions; an unrestricted write-only
output tape permits more output growth than a linear bound on all
stored data.

[Clote, *Computation Models and Function Algebras*, Section 3.3,
Theorem 3.36 and Corollary 3.37][clote], presents the level-two
linear-space correspondence with a proof, attributing it to Ritchie.
Section 3.5 identifies the elementary functions with level three.
These are function-class characterizations, not an identification of
the proof-theoretic strength of an arithmetic theory with a space bound.

For this design, require linear output length as well as linear
workspace, or use a space measure that charges the materialized output.
Under a binary numerical encoding preserving leading zeros by a
sentinel, a linear bit-length bound gives a polynomial bound on the
numerical output. This is the growth behavior appropriate to the
level-two comparison. The precise correspondence with the chosen
CSLib machine conventions remains a formalization obligation.

This restriction also provides a direct composition argument. If
`f` and `g` satisfy the target, store `f(x)` and then run `g`. The
intermediate string has length linear in `|x|`; storage remains linear,
and the sum of the two polynomial running times remains polynomial.
Constants and polynomial degrees may depend on the fixed functions.
Closure under fixed composition does not imply closure under an
input-dependent number of iterations.

For a chosen collection `G` of required operations, its closure under
identity and finite composition is the smallest admissible submonoid
containing `G`. It need not contain every function satisfying the
ambient resource bound. Different encodings, proof formats, and
primitive operations can produce incomparable choices; no unique
smallest familiar complexity class has been established.

## Recognition, evaluation, and categorical structure

Constructing syntax for a power object or an NNO recursor can be
inexpensive without enumerating its values or executing its programs.
For example, materializing all functions between finite sets can
require exponential output. NNO recursion on ordinary numerical
representations can exceed the selected resource bounds.

Even without an NNO, [Statman, *The Typed Lambda-Calculus Is Not
Elementary Recursive*][statman], proves a nonelementary lower bound
for deciding beta-convertibility of simply typed terms. This concerns
conversion, not parsing or checking an explicit conversion derivation;
it is not automatically a lower bound for the proposed equality
presentation.

Identity and composition alone do not supply products, exponentials,
a subobject classifier, or an NNO in the category of recognized types.
Each requires suitable operations and laws. Likewise, all bitstring
maps that Lean proves validity-preserving need not be precisely the
arrows definable in the intended object theory. Equality on closed
values need not capture equality in every context. Recovering the
free syntactic category requires specifying and proving these
relationships, rather than identifying them by construction.

The proposed metalogic is therefore a bounded computational language
for representing syntax and checking evidence for a stronger object
logic. Its proof-theoretic ability to establish that object's soundness,
consistency, or normalization is a separate question.

## A single Turing-machine transition

A total single-step interpreter fits the selected resource target,
including when the machine description is part of the input. Encode
the transition table, state, and finite tape contents with explicit
head markers. Measure input length `n` over the complete description
and configuration.

For a fixed machine with a fixed tape alphabet, a transition reads a
fixed number of scanned symbols, changes the state and those symbols,
and moves each head by at most one cell. A sequential representation
can be validated, copied, and updated in linear time and linear space.
The represented tape grows by at most a constant number of cells.

For a machine supplied as data, validate its finite description, locate
the applicable table entry, and compare its state and symbol fields.
Repeated scans give a polynomial-time, linear-space implementation,
including checking determinism if required. Copying the unchanged table
and tape plus the replacement fields gives linear output length.
These claims assume explicit encodings of finite transition tables,
not compressed descriptions that execute arbitrary programs to
determine a transition.

Define the function on malformed encodings and halted configurations
as well, for example by returning the input unchanged. It then is a
total endofunction on bitstrings. Its restriction to valid, active
configurations implements the intended transition. Totality of this
function makes no assertion about termination of repeated execution.

## Tree-calculus reduction

### The variant in the linked article

[Bader's *A visual introduction to tree calculus*][visual-trees]
explicitly uses triage calculus, a variant of the original rules in
Jay's book. Jay explains the distinction in
[*Calculus or Calculi*][jay-calculi]. The analysis here uses the
[triage specification][triage-spec], matching the linked article.

With application associated to the left and `D` denoting the triangle
constant, its computational rules are:

```text
D D y z           → y
D (D x) y z       → x z (y z)
D (D w x) y D     → w
D (D w x) y (D u) → x u
D (D w x) y (D u v) → y u v
```

The visual presentation additionally has absorption rules turning a
leaf applied to a value into a stem, and a stem applied to a value
into a fork. In applicative syntax these are already the forms `D u`
and `D u v`; representing their construction needs no mathematical
normalization. A visual machine with distinct value constructors can
implement these as structural transitions with the same resource
bounds.

### Reusing the bit-tree carrier

The article's values have zero, one, or two children, whereas the
repository's bit trees have labelled leaves and binary forks.
Intermediate visual expressions also contain application nodes.
Those are different abstract syntaxes, but they need no different
concrete carrier.

One representation uses the applicative grammar `E ::= D | E E`:

```text
encodeTerm(D)       = BitTree.leaf []
encodeTerm(App a b) = BitTree.fork (encodeTerm a) (encodeTerm b)
```

These equations specify an encoding, not Lean declarations. Under
the existing bit-tree serialization, `D` is `00` and application is
`1` followed by its two encoded operands. Thus closed expressions,
including reducible ones, occupy the recognized bit-tree subset with
empty leaf payloads. Stems and value forks are particular nested
applications of `D`. A validity check for this expression subset adds
the requirement that every leaf payload is empty.

With `a` application nodes and `l` constant leaves, the serialized
length is exactly `a + 2*l`. This representation has no graph sharing,
compressed subtrees, or hidden decoding cost. A tagged representation
of the visual constructors is also possible, with constant overhead
per node, but is not required for the resource argument.

### Size of one contraction

Each left-hand side has fixed size apart from its metavariable
subtrees. Its pattern is linear: each metavariable appears once.
Rule matching therefore requires no comparison between two arbitrary
subtrees. The duplication rule copies `z` twice; every other rule
uses each retained metavariable at most once.

For the encoding above, let `|t|` mean serialized bit length. The
duplication rule has sizes

```text
|D (D x) y z| = 8 + |x| + |y| + |z|
|x z (y z)|   = 3 + |x| + |y| + 2*|z|.
```

Consequently its output is at most twice its input length. The other
computational rules decrease length. Contracting one redex inside a
context copies that context once, so the same bound `|t'| ≤ 2*|t|`
holds for one contraction anywhere in the whole expression. The
argument counts actual copied bits; it does not assume constant-time
copying of a subtree or shared pointers.

### Finding and contracting one redex

Choose an effective strategy, such as the first matching position in
preorder. Finding a redex means finding a syntactic rule instance,
not searching for a redex whose reduction will eventually terminate.

A sequential multitape implementation can proceed as follows:

1. Validate the prefix encoding and empty leaf payloads.
2. Enumerate candidate application positions in preorder.
3. At each candidate, scan the fixed pattern, locating the boundaries
   of its metavariable subtrees with a pending-subtree counter.
4. At the first match, copy the context and the required subtree
   intervals to the output in the order specified by the rule.
5. Return the input unchanged if it is malformed or has no redex.

For each candidate, a fixed number of scans of at most `n` bits
suffices. Unary counters on work tapes give a direct implementation
of subtree scanning with linear cost per scan. There are at most
`n` candidates, giving an `O(n²)` time bound. A fixed number of
positions, counters, input copies, and an output of length at most
`2*n` use `O(n)` space in total. An implementation can re-scan rather
than storing a table of offsets for every node; such a table with
binary offsets could itself occupy `O(n log n)` bits.

This establishes an algorithmic upper bound of simultaneous
polynomial time and linear space for deterministic single-step
reduction, including redex discovery. A specified root redex requires
only a fixed number of scans and admits linear time. Tighter bounds
for a whole-expression strategy can be investigated separately.

If the chosen operational presentation requires metavariables to be
values, their syntactic value checks must also be performed. Scanning
the corresponding subtrees remains polynomial time and linear space.
The bound does not require evaluating them to values during matching.
The result is an existence argument for a Turing-machine algorithm,
not a complexity theorem for an arbitrary recursive Lean or OCaml
evaluator.

### Iteration and generated equality

Let `step` be the total endofunction just described. Every fixed
iterate belongs to the composition closure of `step`. This does not
make a uniform evaluator that reduces arbitrary terms to normal form
an admissible total function: reduction may diverge, and intermediate
terms can grow. From the one-step size estimate, `k` steps give the
upper bound `2^k * n`; no uniform linear-space bound in the initial
input follows from that estimate.

Even an explicit step count does not automatically preserve the
target for tree reduction, because intermediate and final trees can
grow. A simulation with an explicit polynomial time budget and a
linear space budget, returning a budget-exhausted state when needed,
is a different, bounded operation.

There is also a direct connection to the proposed quotient types.
For valid expression encodings `t` and `u`, the relation stating that
`u` is obtainable from `t` by one rule contraction at some position
is decidable in simultaneous polynomial time and linear space in
`|t| + |u|`: enumerate positions, form each candidate result, and
compare it with `u`, reusing storage. Its equivalence closure is
convertibility generated by these rules.

Use the full one-step relation for that quotient. The graph of one
deterministic strategy need not generate the same equivalence on all
terms, especially non-normalizing terms; replacing the full relation
would require a separate proof. This gives two related operations:
a total next-state function for execution and a decidable binary
generator for equational reasoning.

The selected resource target therefore suffices both for a Turing
machine's single transition and for a single triage-calculus
contraction. The remaining implementation choices are the expression
encoding, reduction strategy, totalization convention, and exact
CSLib resource accounting. Proving semantic preservation and the
stated bounds in Lean remains future implementation work.

[bit-tree-encoding]: ../Geb/Prototypes/Computability/BitTree/Encoding.lean
[bit-tree-bound]: ../Geb/Prototypes/Computability/BitTree/Bound.lean
[finset-topos]: ../Geb/Mathlib/CategoryTheory/FinSetSkel/ElementaryTopos.lean
[ceers]: https://invariant.org/papers/ceer.pdf
[lambek-scott]: https://www.site.uottawa.ca/~phil/papers/LS11.final.pdf
[cook-reckhow]: https://www.cs.toronto.edu/~sacook/homepage/cook_reckhow.pdf
[histories]: https://www.cs.cmu.edu/~fp/courses/flac/lectures/lecture21.html
[statman]: https://www.cs.cornell.edu/courses/cs6110/2012sp/Statman-typed-lambda-calculus.pdf
[clote]: https://bioinformatics.bc.edu/clotelab/pub/cloteHandbookRecTheory.pdf
[visual-trees]: https://olydis.medium.com/a-visual-introduction-to-tree-calculus-2f4a34ceffc2
[jay-calculi]: https://github.com/barry-jay-personal/blog/blob/main/2024-12-12-calculus-calculi.md
[triage-spec]: https://treecalcul.us/specification/
