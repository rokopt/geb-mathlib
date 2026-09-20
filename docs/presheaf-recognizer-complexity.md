# Presheaf recognizers and categories of bounded computation

Recognition of explicit presheaf W-tree codes has a different resource
requirement from elimination of those trees. This document separates the
implemented reductions, the proposed complexity theorem, and the restrictions
on categorical and internal interpretation claims.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [The proposed recognition theorem](#the-proposed-recognition-theorem)
- [Reduction to bounded local tests](#reduction-to-bounded-local-tests)
- [Complexity classes and closure requirements](#complexity-classes-and-closure-requirements)
- [Oitavem expressions as admissible maps](#oitavem-expressions-as-admissible-maps)
- [Recognized carriers and W-elimination](#recognized-carriers-and-w-elimination)
- [Internal syntax and interpretation](#internal-syntax-and-interpretation)
- [Related results](#related-results)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

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
[presheaf-scan]: ../Geb/Prototypes/Computability/PresheafScan.lean
[counterexample]: ../Geb/Prototypes/Computability/Oitavem/PresheafCounterexample.lean
[quantification]: ../Geb/Prototypes/Computability/Oitavem/BoundedQuantification.lean
[oitavem-category]: ../Geb/Prototypes/Typechecker/Oitavem.lean
[resource-target]: bitstring-metalogic.md#selected-resource-target
[soundness]: oitavem-logspace-soundness.md
