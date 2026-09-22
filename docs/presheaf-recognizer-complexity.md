# Presheaf recognizers and categories of bounded computation

Recognition of explicit presheaf W-tree codes has a different resource
requirement from elimination of those trees. This document separates the
implemented reductions, the proposed complexity theorem, and the restrictions
on categorical and internal interpretation claims.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Checking, recursion, and evaluation](#checking-recursion-and-evaluation)
  - [Elementary recursion](#elementary-recursion)
- [The proposed recognition theorem](#the-proposed-recognition-theorem)
- [Reduction to bounded local tests](#reduction-to-bounded-local-tests)
- [Complexity classes and closure requirements](#complexity-classes-and-closure-requirements)
- [Oitavem expressions as admissible maps](#oitavem-expressions-as-admissible-maps)
- [Recognized carriers and W-elimination](#recognized-carriers-and-w-elimination)
- [Internal syntax and interpretation](#internal-syntax-and-interpretation)
- [Observing coded bitstreams](#observing-coded-bitstreams)
- [Related results](#related-results)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Checking, recursion, and evaluation

The following capabilities concern different tasks. An NNO is a
natural-numbers object; a PNNO is a parameterized natural-numbers object.
The table records mathematical context and sufficient conditions, rather than
additional formalized complexity bounds for Geb's checkers.

| Functions or categorical structure | Capability | Qualification |
| --- | --- | --- |
| Logspace | Check explicit finite proof trees or typing derivations | The representation, navigation, and local inference checks must admit logspace implementations. |
| Elementary-recursive functions; decision class `ELEMENTARY` | Construct and search finite sets and function spaces at any fixed finite order | Each program or formula has a fixed exponential-tower bound; unrestricted iteration of exponentiation can leave the class. |
| Primitive-recursive functions; a PNNO in a Cartesian category | Use functions obtained by first-order primitive recursion as steps of further primitive recursions | Each definition uses finitely many fixed stages; exact characterization by primitive recursion concerns the free Cartesian category with a PNNO. |
| Cartesian closure with an NNO | Recurse into function objects, defining functions such as Ackermann | This extends first-order primitive recursion without implying general recursion or nontermination. |
| Partial computable functions | Uniformly evaluate arbitrary encoded programs, including the evaluator's own code | Evaluation may fail to terminate; there is no total computable universal evaluator for all total computable functions. |

For the logspace row, let `n` be the entire certificate's encoded length.
For a fixed calculus, if structural validity, premise references, and each
local inference are checkable in logspace, a scanner can check every position
using `O(log n)` workspace. Explicit intermediate expressions and witnesses
for individual reduction steps can replace computation of normal forms by
local verification. Avoiding self-evaluation alone does not establish this
bound: the local rules and their encoding must satisfy these conditions.
The certificate may be much larger than the statement it proves.

This permits a separation between the checker and the theory it checks.
A finite proof can concern noncomputable functions or uncountable sets of
functions in ZFC. Its verification concerns the formal derivation, without
evaluating those functions or deciding arbitrary statements of the theory.
Finite bitstrings encode formulas and proofs; they do not individually name
every member of an uncountable semantic collection.

[Metamath's specification, section 4.1.4][metamath], describes proof checking
by substitutions and expression comparisons, with hypothesis, scope, and
disjoint-variable conditions. A logspace bound for its standard proof formats
has not been established here. A checker for a more explicit certificate
format would need its own representation and local-rule analysis.

### Elementary recursion

Write `E_0(n) = n` and `E_{k+1}(n) = 2^(E_k(n))`. The decision class
`ELEMENTARY` is the union of `DTIME(E_k(n^c))` over fixed natural numbers
`k` and `c`, where `n` is input length. Its function counterpart,
`FELEMENTARY`, consists of the elementary-recursive functions. Each function
has its own fixed tower-height bound; there is no common height for the
whole class. See [Nguyên, section 1.1][typed-conversion].

Ramification and function-type order are distinct parameters.
[Leivant's first-order characterization][leivant-first-order] gives polynomial
time over binary words and linear space for the corresponding numeric
functions over the unary algebra. It already permits arbitrarily many tiers:
two tiers suffice to define the same functions. Consequently, adding tiers
alone does not yield elementary recursion in that system.
[His higher-type characterization][leivant-elementary] extends ramified
recurrence to finite function types and obtains exactly elementary-time
functions over each free algebra. Oitavem's normal/safe distinction is a
tiering of word arguments, not a hierarchy of function types. Removing
ramification from first-order primitive recursion gives primitive-recursive
functions; removing it from higher-type recursion permits still more,
as the Cartesian-closure row indicates.

The descriptive characterization concerns fixed formulas interpreted on
finite structures: the union of higher-order logics of all finite orders
captures `ELEMENTARY`, for example on the usual ordered structures encoding
input words. See [Hella and Turull-Torres][higher-order-logic]. The size
calculation explains the exponential growth: an `r`-ary relation on an
`N`-element domain has `2^(N^r)` possible values, and relations on relations
repeat this construction. Each fixed formula fixes its order, arities, and
quantifiers, so exhaustive evaluation has an elementary bound. This is a
statement about truth in a supplied finite structure, not about deciding
validity over arbitrary or infinite structures.

There is also an exact arithmetic formulation of the proposed extension of
logspace. [Prunescu, Sauras-Altuzarra and Shunia, Corollary 1][elementary-basis],
arXiv `2505.23787v2`, prove that addition, remainder, and `x ↦ 2^x`, together
with constants and projections, generate all elementary-recursive numeric
functions by composition alone. Their total remainder convention is
`x mod 0 = x`. Addition and remainder on binary integers are in `FLOGSPACE`;
for remainder, use `x mod y = x - y * floor(x/y)` when `y > 0` and
[Hesse, Allender and Barrington's uniform `TC^0` arithmetic][division],
which lies within logspace. Thus, for numeric functions with binary
input and output,

```text
closure_under_composition(FLOGSPACE ∪ {x ↦ 2^x}) = FELEMENTARY.
```

The basis theorem gives one inclusion; the other follows because logspace
functions and exponentiation are elementary, and elementary functions are
closed under composition. This uses ordinary composition of denoted
functions; an extension of Oitavem's tiered syntax needs its own rules and
soundness argument.

To express numerical exponentiation on words, fix the encoding first. If
`w` represents `x` in ordinary positional binary notation, `binary(2^x)`
is a `1` followed by `x` zeroes when written most significant bit first. For the
repository's [Oitavem word bijection][word-coding], the compatible definition
is instead

```text
exp₂(w) = unrank (2 ^ rank w).
```

Here lists are least significant bit first. `rank w` reads `w ++ [true]`
as a binary number and subtracts one; conversely,
`unrank n = (n + 1).bits.dropLast`. Thus `rank [] = 0` and
`exp₂ [] = [false]`; for
`x = rank w > 0`, the output is `[true]` followed by `x - 1` false bits.
These conventions are interconvertible with ordinary binary numerals in
logspace. Using the word length as the exponent instead computes a different
function: the ordinary binary output for `2^length(w)` has only
`length(w) + 1` bits and is logspace-computable.

The hardware analogy therefore requires arbitrary precision and an
unbounded shift count. Although numerically `2^x = 1 << x`, its ordinary
binary output has `x + 1` bits, exponentially many in the binary input
length in the worst case. A fixed-width shift cannot produce those outputs;
an arbitrary-precision implementation must account for their storage and
emission. A compact symbolic representation of the shift has a different
output contract from the explicit words considered here.

These results suggest a connection through a fixed finite number of
exponential expansions, with the bound determined by the program or formula.
Under dense bitset coding, `code(S) = sum(2^a for a in S)`, numerical
exponentiation even constructs the code of a singleton: `code({x}) = 2^x`.
Function spaces and power sets introduce exponential cardinalities as well.
The representation matters: a sparse list can represent a singleton cheaply.
Neither higher-order syntax nor set formation alone determines a complexity
class; the permitted constructions, encodings, and iteration rules do.

For compilers, the finite basis supplies a recursion-free arithmetic target
language for every elementary numeric function. This is an expressibility
result; it does not itself guarantee an efficient translation or small
intermediate integers. The higher-order characterizations also support
evaluation of fixed finite-order queries and normalization with an explicit
bound on type complexity. In the simply typed
lambda calculus, a fixed bound on the degrees of redex types gives an
elementary normalization bound; allowing arbitrary input terms removes that
fixed bound, and deciding beta-convertibility is `TOWER`-complete and hence
nonelementary. See [Nguyên, Theorems 1.1 and 2.4][typed-conversion]. Thus a
compiler may use a syntactically restricted fragment or an explicit resource
bound to justify elementary evaluation. The cost of that evaluation remains
separate from checking explicit derivations, as in the logspace row.

For foundations, elementary function arithmetic supplies bounded induction,
exponentiation, and elementary bounded recursion. It supports coded finite
sets, finite functions, and finite power sets, while its bounds on provable
totality exclude input-height exponential towers. [Avigad, section 2 and
Theorem 2.2][elementary-arithmetic], develops these constructions. This
provides a setting for finitary constructions with elementary bounds.
Unrestricted iteration of exponentiation, and therefore the unrestricted
elimination principle discussed [below](#recognized-carriers-and-w-elimination),
still exceeds those bounds.

## The proposed recognition theorem

Fix a coded finitary presheaf polynomial endofunctor and a finite base
category. Require logspace implementations of the operations on codes used by
the checker: shape validation, direction cardinality and indexing, slice
indices and their equality, direction restriction, shape restriction, and
arity reindexing. Require a canonical explicit tree encoding with logspace
navigation and equality of subtree spans. These are requirements on encoded
operations, not on the cardinalities of the shape or slice-index types.

Under these conditions, the proposed theorem is that hereditary naturality,
and hence presheaf W-membership after the tree and slice checks, is decidable
in logspace. The algorithmic argument below supports this statement. The
complete construction of the local Oitavem expression from these operations
is not yet formalized.

The finite direction sets need effective presentations. A Lean family
`B : A → Type` is not itself a word function. Presenting its fibers by
`Fin (arity a)` replaces it computationally by arity, validity, and conversion
operations. Binary direction indices let the scanner count the children
actually present. An arity larger than the input's node count is rejected
without enumerating that many directions. Finiteness without effective
presentations supplies neither this behavior nor a complexity bound.

The functor and its parameter programs are fixed in this theorem. Equivalently,
a compiler may accept expression witnesses for the parameters and produce a
recognizer expression for that particular signature. This is not one logspace
program that interprets arbitrary parameter programs supplied as part of its
input. Constants and polynomial degrees may depend on the fixed signature.

## Reduction to bounded local tests

The native checker compares, at each node and each applicable direction and
base morphism, a selected child `t` with a restricted child `restrict(g,u)`.
The repository's restriction changes only the root of `u`. Write
`u = sup(a,f)` and `t = sup(a',f')`. Equality is equivalent to:

1. `a' = shapeRestr(g,a)`;
2. for every direction `b` of `a'`,
   `f'(b) = f(reindex(g,a,b))`, with transport along the root equality.

The equalities in the second step compare original input subtrees. Their
canonical encodings can be compared by scanning their spans. There is no need
to unfold a succession of restrictions or construct a transformed tree.
After root equality succeeds, the directions of the restricted root are
exactly those of the candidate root already in the input. This avoids
enumerating an arbitrarily large restricted arity on a rejected input.

A scanner enumerates node positions, applicable directions and morphisms,
and positions within the compared spans. These are fixed-depth loops with
input-bounded counters; a fixed finite category contributes constant data.
Each local operation can be recomputed when a bit of its output is needed.
Logspace composition is justified by this recomputation argument, not by
storing intermediate words. See [Cenzer et al., Theorem 1 and
Corollary 1(i)][cenzer].

[PresheafScan.lean][presheaf-scan] formalizes the mathematical reduction:

- `native_eq_scan` equates the native checker on every raw tree with the
  conjunction of its local tests over the tree's occurrences.
- `scan_eq_true_iff` identifies acceptance with hereditary naturality on
  slice-valid trees.
- `restrictedEq_eq_true_iff` verifies the root comparison using an arbitrary
  correct equality test on original subtrees.
- `positions_eq_native` transfers any sound and complete enumeration of nodes
  by input suffixes, with a correct local test, to the native checker.

The list `occurrences` specifies the scan. Materializing it is not the
proposed logspace implementation.

## Complexity classes and closure requirements

Identity and composition suffice for the admissible submonoid used by
`Typechecker`. They do not suffice for the recognizer construction. Even the
submonoid containing only the identity meets those axioms, without containing
Boolean constants on bitstrings. Recognition also needs encoded structural
operations, Boolean tests, and bounded universal quantification.

If a local position test takes time `T(n)` and workspace `S(n)`, the outer
scan uses polynomially many calls and workspace `O(log n + S(n))`, allowing
repeated access to the original input. Fixed-depth nested loops and the
simulation of input views add polynomial time overhead. This statement
concerns scanning; deriving `T` and `S` from
signature operations must account for the sizes of their intermediate codes.

The following consequences are algorithmic arguments, not formal machine
bounds for the implemented presheaf checker:

| Operations and representation assumptions | Recognition bound |
| --- | --- |
| All code operations in `FLOGSPACE`, logspace navigation | `FLOGSPACE` |
| All code operations in polynomial time | Polynomial time |
| Polynomial time and linear workspace, with linearly bounded intermediate codes | Polynomial time and linear workspace |
| Elementary time for the code operations | Elementary time |
| Space `s(n)`, polynomially bounded intermediate codes | Space `O(log n + s(n^k))` for some fixed `k`, with suitable monotonicity |

For the last row, the polynomial accounts for finitely many compositions;
closure under polynomial changes of input length determines whether the
output class can have the same name as the input class. A workspace bound
alone does not in general bound output length by a polynomial. The linear
output convention selected for `FPOLYTIMELINSPACE` in
[the metalogic discussion][resource-target] therefore matters.

The [counterexample family][counterexample] supplies a lower bound in the
other direction: hereditary naturality on its designated slice-valid trees
is exactly the arbitrary predicate put into direction restriction. Restricting
that operation's complexity cannot compensate for unrestricted complexity
in other signature operations. When all other operations and navigation are
logspace, bounding direction restriction gives the corresponding local-test
bound above.

## Oitavem expressions as admissible maps

[BoundedQuantification.lean][quantification] constructs constants, normalized
Boolean tests, and `Expr.allSuffixes` directly in the existing Oitavem algebra.
The scan carries one Boolean verdict; its rank is at most two, so a constant
two-bit recursion bound preserves it. `Expr.eval_allSuffixes` proves the
finite-universal-quantification equation.

[Typechecker/Oitavem.lean][oitavem-category] instantiates the existing category:

- `definableSubmonoid` consists exactly of unary expression denotations.
- `Expr.admissible` supplies an endomorphism with its syntax witness.
- `Expr.decisionProblem` normalizes a word-valued test to the truth values
  `[true]` and `[]`.
- `Expr.scanProblem` implements universal position checking.
- `Expr.presheafScan_pass_iff` proves that a correct local position expression
  yields a decision problem agreeing with native hereditary naturality.

The last theorem takes the local expression, the node-position reader's
coverage proofs, and the local correctness equation as explicit arguments.
It does not construct that expression from shape and direction operations.
The required tree navigation, primitive code operations, and replacement of
the existing Kristiansen expressions remain implementation obligations.

These theorems require no axiom identifying Oitavem's syntax with a machine
class. They concern the defined algebra and its interpreter. Formal machine
soundness and completeness are separate obligations recorded in
[the Oitavem soundness discussion][soundness].

## Recognized carriers and W-elimination

A decision procedure for a carrier does not establish an initial-algebra
universal property in a category of resource-bounded maps. The algebra map
may be admissible while its unique set-theoretic fold is not.

The implemented `squareFold` gives a counterexample on explicitly encoded
word-shaped unary trees. Its base is the constant word `[true,true]`. At each
unary constructor it applies the Oitavem expression `squareWord`, replacing
a word of length `m` by one of length `m²`. The fold has output length
`2^(2^n)` on a tree of depth `n`, proved by `length_squareFold`.
`no_squareFold` uses the algebra's polynomial output-length theorem to prove
that no unary Oitavem expression computes this fold.

This obstructs the standard word carrier with its constructors from supplying
unrestricted word-tree elimination in the Oitavem decision-problem category.
It is not a nonexistence theorem for every possible resource-sensitive
presentation of inductive data. A bounded, safe, or otherwise restricted
elimination principle needs its own categorical formulation.

For `ELEMENTARY`, repeated squaring is still elementary, so this particular
counterexample does not separate it. Unrestricted iteration of an elementary
exponentiation operation instead produces towers whose height depends on the
input; it has the same conceptual problem at that larger class. This latter
claim is not formalized here.

Primitive recursion admits further first-order primitive recursion using
previously defined functions as its fixed base and step. The Grzegorczyk
classes exhaust the primitive-recursive functions: a new definition remains
at some finite level, although it need not remain at the level of its step
function or strictly increase that level. For example, `T(0) = 1` and
`T(n+1) = 2^(T(n))` define a primitive-recursive, non-elementary function.
See [Bournez and Hainry, section 3][hierarchy].

The numerical functions represented in the free Cartesian category with a
PNNO are exactly the primitive-recursive functions. In a general Cartesian
category, a PNNO supplies the recursion principle without imposing this
upper bound on all other arrows. Cartesian closure additionally supplies
function objects as elimination targets; recursion into `N → N` permits
Ackermann's function. This differs from choosing an already defined numerical
function as the fixed step of another first-order recursion. See [Buchholtz
and Schipp von Branitz, section 2 and Theorem 2.1][primitive-recursion],
arXiv `2404.01011`.

## Internal syntax and interpretation

The implemented Oitavem expressions are already a slice W-type indexed by
normal and safe arities. Their denoted functions identify multiple expression
trees, so syntax and the extensional collection of denotations are different
objects. Slice syntax can also be viewed over a discrete index category.
That category has infinitely many arity objects, but only identity morphisms;
the slice syntax checker does not need the finite-category presheaf theorem.

Recognizing object and arrow syntax is compatible with the proposed model.
Recognizing arbitrary representatives of semantic arrows requires more:
the `Typechecker` representative carries a proof that it preserves acceptance
on every valid input. A syntactic presentation can enforce this by constructors
or explicit certificates. Tree well-formedness alone does not decide that
semantic preservation condition or equality of quotient morphisms.

Nor can the same total algebra contain an unrestricted interpreter for all
of its encoded tests. `no_universal_decider` proves this even when the
interpreter only returns acceptance, assuming admissible diagonal pairing.
It also excludes a full-output interpreter. The general categorical version
for full outputs is `DecisionProblem.exists_fixed_point_of_evaluation` in
`Typechecker/Exponentials.lean`. Thus checking that a word
encodes an object is different from uniformly running every encoded object's
membership procedure. Fixed checkers, syntax checkers, and evaluators with
explicit resource budgets remain distinct constructions.

The obstruction applies beyond logspace. If a total class admits
`d(x) = U(x,x) + 1` whenever it admits `U`, a universal evaluator `U` for
that same class would give `d` a code `e` and imply
`d(e) = U(e,e) + 1 = d(e) + 1`. In particular, no total computable evaluator
covers all total computable unary functions. A stronger total class can
evaluate a weaker one: primitive-recursive programs have a total computable
evaluator, which is not primitive recursive.

The partial computable functions do admit a universal partial computable
evaluator. At its diagonal program's own code, execution diverges, so the
argument produces no contradictory numerical equality. This remains within
ordinary Turing computability; it relaxes guaranteed termination.
[Avigad's notes, section 2.7, Theorems 2.7.5 and 2.7.6][universal-evaluation],
give the universal partial evaluator and the total diagonal obstruction.

These statements concern uniform evaluation from ordinary numerical or
bitstring codes with the operations needed for diagonalization. Typed
self-interpretation can use representations that exclude that construction.
[Brown and Palsberg's self-interpreter for the strongly normalizing
System F-omega][typed-self-interpreter], DOI `10.1145/2837614.2837623`, has
this property; it does not supply the unrestricted evaluator considered here.

## Observing coded bitstreams

[Oitavem-coded bitstreams][coded-bitstreams] represent a stream by an
expression of one normal and no safe argument, its value at the all-zero
word of length `n` read as the stream's entry at depth `n`. Recognizing
the codes is in `FLOGSPACE`, by that directory's recognizer, and the
syntactic tail, composition with a successor, is a fixed rewrite of the
spelling. Observing a coded stream is another matter: reading the entry
at a depth is the universal function of Oitavem's algebra restricted to
unary inputs, and [`not_recognizes_diagonal`][counterexample] at the
constant test function shows that no expression of the algebra computes
the entry at depth zero from the code. Under the paper's Theorem 3.4 the
observation therefore lies outside `FLOGSPACE`.

The class of the observation depends on what it returns. The decision
problem, the bit at a depth or termination there, is in `EXPSPACE`:
Oitavem's logspace simulation recomputes each intermediate word bit by
bit and keeps one counter per recursion of size the logarithm of the
largest intermediate word, so its workspace is linear in the code's size
times that logarithm; and the largest intermediate word of a code of `s`
nodes at depth `n` has length at most `(n + 2) ^ 2 ^ s`
([`Expr.length_le_pow`][size]), a bound whose exponent's exponent is
attained up to a constant factor by iterated squaring, so the logarithm
is exponential in the code's size and the simulation is not a
polynomial-space one. The time of such a machine follows from its space
by counting configurations,
[`Machine.computes_expspace`][space-time]: a halting transducer in space
`c * 2 ^ ((n + 1) ^ d)` runs in time `C * 2 ^ 2 ^ ((n + 1) ^ D)`. The
machine itself is not constructed here. `EXPSPACE` is closed under
composition of its decision procedures, so observing streams one entry
at a time forces no larger class. Whether the observation is
`EXPSPACE`-hard is open here.

The word-valued evaluator, returning the whole value at a depth, is
different. Iterating a unary squaring `k` times over a two-bit constant
is a code of size linear in `k` whose value has length `2 ^ 2 ^ k`, and
composing such evaluations iterates the exponential further, the
phenomenon of § Elementary recursion. `ELEMENTARY` is therefore the
closure of word-valued evaluation under composition, and `EXPSPACE` the
class of entry-wise observation.

## Related results

[Cockett, Díaz-Boïls, Gallagher and Hrubeš, *Timed Sets, Functional Complexity,
and Computability*][timed-sets], DOI `10.1016/j.entcs.2012.08.009`, supplies
closely related categorical infrastructure. Proposition 3.1 obtains
restriction-category structure under additive complexity-order hypotheses.
Corollaries 6.3 and 6.4 identify PTIME and LOGSPACE as the total maps of
particular Turing categories. Their construction includes partial maps and
resource-sensitive objects; it is not an identification with Geb's current
decision-problem category or a total universal evaluator on standard-sized
bitstrings.

[Cockett and Redmond, *A Categorical Setting for Lower Complexity*][polarized],
DOI `10.1016/j.entcs.2010.08.017`, uses polarized strong categories to support
inductive data with restricted computational behavior. Its introduction
explains the difficulty caused by unrestricted recursion at lower complexity;
its sized-set model controls output growth rather than establishing the
presheaf recognition bound here.

[Dal Lago and Hofmann, *Realizability Models and Implicit Complexity*][realizability],
DOI `10.1016/j.tcs.2010.12.025`, supplies a resource-monoid realizability
framework for elementary affine logic, LFPL, and soft affine logic. Its
extension of LFPL supports internal inductive datatypes. It provides a further
candidate framework for the elimination question, not a proof about Geb's
hereditary-naturality checker.

These sources establish relevant closure and categorical constructions.
The verified local root-restriction reduction still needs an implementation
of its word operations and navigation in Oitavem's algebra.

[cenzer]: https://people.clas.ufl.edu/cenzer/files/n84.pdf
[timed-sets]: https://users.math.cas.cz/~hrubes/PDFs/TimedSet.pdf
[polarized]: https://doi.org/10.1016/j.entcs.2010.08.017
[realizability]: https://doi.org/10.1016/j.tcs.2010.12.025
[metamath]: https://us.metamath.org/downloads/metamath.pdf#page=132
[leivant-first-order]: https://doi.org/10.1007/978-1-4612-2566-9_11
[leivant-elementary]: https://doi.org/10.1016/S0168-0072(98)00040-2
[higher-order-logic]: https://doi.org/10.1016/j.tcs.2006.01.009
[elementary-basis]: https://arxiv.org/html/2505.23787v2#S2
[division]: https://people.cs.rutgers.edu/~allender/papers/division.pdf
[typed-conversion]: https://lmcs.episciences.org/14215/pdf
[elementary-arithmetic]: https://www.andrew.cmu.edu/user/avigad/Papers/elementary.pdf#page=3
[word-coding]: ../Geb/Prototypes/Computability/Oitavem/Word.lean
[hierarchy]: https://members.loria.fr/EHainry/papers/tcs05.pdf#page=5
[primitive-recursion]: https://arxiv.org/html/2404.01011v1#S2
[universal-evaluation]: https://www.andrew.cmu.edu/user/avigad/Teaching/candi_notes.pdf#page=46
[typed-self-interpreter]: https://popl16.sigplan.org/details/POPL-2016-papers/52/Breaking-Through-the-Normalization-Barrier-A-Self-Interpreter-for-F-omega
[presheaf-scan]: ../Geb/Prototypes/Computability/PresheafScan.lean
[counterexample]: ../Geb/Prototypes/Computability/Oitavem/PresheafCounterexample.lean
[coded-bitstreams]: ../Geb/Prototypes/BitStream/Oitavem.lean
[size]: ../Geb/Prototypes/Computability/Oitavem/Size.lean
[space-time]: ../Geb/Prototypes/Computability/Oitavem/Machine/SpaceTime.lean
[quantification]: ../Geb/Prototypes/Computability/Oitavem/BoundedQuantification.lean
[oitavem-category]: ../Geb/Prototypes/Typechecker/Oitavem.lean
[resource-target]: bitstring-metalogic.md#selected-resource-target
[soundness]: oitavem-logspace-soundness.md
