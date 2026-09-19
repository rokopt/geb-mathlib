/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import VersoManual
public import GebManual.Bibliography
import Geb.Prototypes.Typechecker.Instances

/-! # Universal properties of decision problems

A catalogue of sufficient conditions, necessary conditions, and obstructions
for the universal properties in the elementary-topos interface.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open GebProto.EndomorphismCategory
open GebProto.EndomorphismCategory.DecisionProblem

#doc (Manual) "Universal properties of decision problems" =>

The construction {name}`DecisionProblem` starts with a base type `B`,
distinct truth values `t` and `f`, and a submonoid `S` of endomorphisms
of `B`. Thus identity and composition are admissible. An object is an
admissible checker returning only `t` or `f`; its {name}`Fiber` is the
set of inputs on which it returns `t`. A morphism is an admissible
endomorphism preserving acceptance, with representatives identified
when they agree on the source's accepted fiber. Values outside that
fiber do not affect morphism equality.

The checkers are two-valued; morphism representatives need not be.
The quotient identifies morphisms, not elements of objects. In
particular, two different function codes or certificate trees remain
different accepted elements, even when their interpretations agree.

This chapter follows the chosen data in
{name}`CategoryTheory.ElementaryTopos`. The abstract constructions
and the named necessity theorems below are checked by Lean.
Applications to machine complexity classes are informal deductions:
the corresponding transducer and computation-history encodings have
not been instantiated in Lean. Sufficient conditions are not presented
as necessary unless a theorem establishes that direction.

# Terminal objects

An admissible checker accepting exactly `t` suffices:
{name}`HasTrueSingletonChecker` gives {name}`terminalCone` and the
{name}`hasTerminal` instance. From any object, its own checker sends
every accepted input to `t`. Every map into that singleton agrees
there, giving uniqueness after quotienting.

More generally, a singleton `{a}` is terminal when its checker is
admissible and an admissible endomorphism sends `t` to `a`;
{name}`terminalConeOfSingleton` packages this construction. When the
constant-true checker is admissible,
{name}`unique_to_singleton_iff_constant_mem` characterizes terminality
of a singleton by admissibility of the constant function at its point.

Having two distinct base values alone does not supply a singleton
checker. Nor is the constant-true checker terminal: it accepts all of
`B`, so its fiber is the full base, with distinguishable endomorphisms.
This failure is proved by {name}`not_unique_to_constant`.

Singleton tests and constants are available among total regular
string functions and among full logspace functions. Decision
completeness can supply the singleton test without supplying every
output-producing function.

# Initial objects

The constant-false checker accepts nothing. Its admissibility is
{name}`HasFalseChecker`; {name}`rejectAll`, {name}`initialCocone`, and
{name}`hasInitial` give the object and categorical interface. Identity
represents a map from the empty fiber to any target, and all such
maps are equal on that fiber.

{name}`exists_empty_iff_hasFalseChecker` identifies the existence of
an empty accepted fiber with admissibility of constant false.
Under that admissibility assumption, {name}`unique_from_iff_empty`
characterizes initial objects as exactly those with empty fibers.
The assumption matters: with only Boolean identity admissible, the
resulting one-object category has an initial object whose fiber is
nonempty. Constant false is a useful sufficient condition, not an
unconditional necessary one for initiality.

All-constant algebras satisfy the condition, including the
size-bounded algebras investigated here.

# Binary products

{name}`ProductCoding` supplies pair encoding, admissible projections,
closure under pairing the outputs of any two admissible functions,
a checker for valid pair codes, and conjunction of decision checkers.
The product accepts exactly valid codes whose two components pass
their respective checkers. The validity test is needed when some base
values are not pair codes: projection followed by reconstruction must
recover every accepted product element.

{name}`binaryProductCone` proves the universal property;
{name}`hasBinaryProducts` registers existence. Together with the
terminal construction, {name}`cartesianMonoidalCategory` supplies the
topos interface's cartesian field.

A necessary condition comes from the full-base object `U`, when
constant true is admissible. If `U` has a product with itself,
{name}`exists_injective_not_surjective` produces an admissible
injection of `B` into itself that is not surjective. The unary
size-bounded algebras have a uniform additive output-size bound for
each function. Their admissible injections must be surjective;
{name}`not_hasBinaryProducts_of_sizeBounded` therefore rules out
binary products. This is a restriction on output functions, even
when the algebra is complete for a substantial decision class.

For bitstrings, total regular functions already suffice. Escape each
bit using `00` or `01`, separate the components with `11`, and reject
malformed encodings. Regular functions support the required decoding,
tests, composition, and pointwise concatenation
{citep AlurFreilichRaghothaman2014}[Section III]. Full logspace
functions also suffice; logspace composition and pairing are discussed
in {citep CenzerDowneyRemmelUddin2008}[Section 2 and page 12]. These
are upper bounds on what suffices, not minimality theorems.

# Binary coproducts

{name}`CoproductCoding` supplies tagged injections, a checker for
valid tagged elements, and admissible branch selection. The accepted
fiber is the disjoint union of the two accepted fibers.
{name}`binaryCoproductCocone` and {name}`hasBinaryCoproducts` package
the universal property and existence.

Pair coding can implement tags, but the complete condition also needs
distinguishable tags, singleton tag tests, and case analysis.
{name}`DecisionConditionals` and {name}`CoproductCoding.ofProducts`
make those additional assumptions explicit. Pairing alone does not
assert them. Total regular string functions and full logspace
functions provide these operations.

The same necessary injection condition applies when `U` has a
coproduct with itself:
{name}`exists_injective_not_surjective_of_copairing`.
Consequently {name}`not_hasBinaryCoproducts_of_sizeBounded` excludes
binary coproducts for the size-bounded unary algebras admitting `U`.

# Equalizers

{name}`EqualizerCheckers` asks for an admissible checker accepting
exactly those `x` accepted by the source for which `r(x) = s(x)`.
The equalizer inclusion is identity on these values. A map equalizing
`r` and `s` already lands in that fiber, so the same admissible
function supplies its factorization. The construction is independent
of the representatives of the two morphisms.

{name}`equalizerCone` and {name}`hasEqualizers` provide the interface.
{name}`EqualizerCheckers.ofProducts` gives another sufficient route:
pair the two outputs and test equality of the decoded components.
Pairing is convenient for that route, but is not required by the
basic agreement-filtering condition. No converse for arbitrary
equalizers has been proved.

For logspace functions, output equality can be tested by recomputing
output symbols with logarithmic counters. Thus logspace soundness
for the admissible functions, together with completeness for the
relevant logspace decision checkers, suffices for agreement filtering.
Unlike products, this does not demand a larger encoded pair as output.
The metalanguage equality proofs establish the universal property;
no runtime proof-tree representation is needed.

# Coequalizers

{name}`CoequalizerRel` is the equivalence relation generated on the
target fiber by `r(x) ∼ s(x)` for accepted source values. A
{name}`ClassNormalizer` is an admissible function choosing a member
of each class and assigning the same result to the generating pairs.
It follows that normalization is constant on whole classes and
idempotent. Agreement filtering recognizes its fixed points; these
form the coequalizer object, with normalization as the projection.

{name}`CoequalizerNormalForms` supplies normalizers for all parallel
pairs. Together with {name}`EqualizerCheckers`, it gives
{name}`coequalizerCocone` and {name}`hasCoequalizers`. This is a
sufficient condition: an arbitrary categorical coequalizer need not
have an admissible section selecting representatives in the original
target.

The necessary statement is {name}`coequalizer_kernel_iff`: two target
values have the same projection exactly when every admissible
coequalizing map identifies them. Without further separation
assumptions, this is not automatically equality in the generated
equivalence relation.

For explicitly presented finite undirected graphs, logspace
connectivity {citep Reingold2008}[] allows selection of the least
vertex of a component. Applying this to a family of string-valued
diagrams needs uniformly accessible finite graph presentations of
suitable size, with compatible representative labels. Finite classes
alone do not suffice.

In fact, full logspace and even all total computable functions do
not supply all coequalizers on bitstrings. Let the source accept
valid halting histories with input `e`, and let the parallel maps
output `(e, 0)` and `(e, 1)`. These endpoints must be identified
when `e` halts. For a nonhalting `e`, the singleton indicator of
`(e, 0)` coequalizes the diagram and separates the endpoints, so
the necessary kernel theorem forces their projections to differ.
Equality of projection outputs would decide halting. The generated
classes have at most two members, as in the relation used in
{citep GaoGerdes2010}[the proof of Proposition 7.6]. The application
to computation histories here remains informal.

An indexed W-type can describe finite equivalence derivations.
Checking a proposed derivation does not decide whether one exists,
nor produce a canonical representative. Quotienting morphisms does
not identify two accepted proof trees as elements of an object.

# Exponentials

{name}`ExponentialCoding` provides an admissible language of function
codes, admissible evaluation, admissible parameter abstraction, and
extensionality: accepted codes agreeing on every accepted argument
are equal as base values. The last condition supplies uniqueness of
currying. Merely encoding each admissible function with an external
interpretation does not supply these operations or this uniqueness.

{name}`ExponentialCoding.homEquiv` gives the currying bijection.
{name}`closedOfCoding` packages the right adjoint to product with a
fixed object; {name}`monoidalClosed` supplies the topos interface's
closed field. The singleton-argument case is constructed by
{name}`singletonExponentialCoding`, with codes given by output values.
For a fixed finite argument fiber, finite output tables also give an
informal logspace construction with suitable encodings.

The general obstruction is stronger than a complexity bound.
{name}`exists_fixed_point_of_evaluation` proves that an admissible
evaluator representing every admissible endomorphism forces each
admissible endomorphism to have a fixed point. Diagonalize by mapping
`x` to `a(eval(pair(x, x)))`. A code for that function produces a
fixed point of `a`. This is the diagonal mechanism of
{citep Lawvere1969}[Sections 1–2]. Existence of codes is already
enough for the obstruction; uniqueness is not needed.

{name}`exists_fixed_point_of_exponential` derives such evaluation
from any proposed exponential `U^U`, where `U` accepts every base
value. {name}`not_closed` and {name}`not_monoidalClosed` turn an
admissible function without fixed points into a categorical
obstruction over the chosen product structure.

On bitstrings, prepending one bit has no fixed point. Consequently
full regular functions, full logspace functions, all total computable
functions, and even all set-theoretic endomorphisms fail to provide
all exponentials in this fixed-base category. Raising the resource
bound cannot solve that problem.

# Subobject classifier

An image test alone supplies only part of the required structure.
{name}`MonoImage` records a checker for the image of a monomorphism
and an admissible total function that recovers a preimage on that
image. Its behavior elsewhere is unrestricted. The inverse is needed
to construct the factorization in the classifier's pullback square.

{name}`ClassifierData` assumes all constants are admissible, a
singleton checker for `{t}`, a checker for `{t, f}`, and such image
data for every monomorphism. The truth map includes `t` into the
two-value object. A mono's image checker is its characteristic map;
the inverse supplies pullback lifts, and two-valuedness supplies
uniqueness of the characteristic map.
{name}`ClassifierData.classifier` has exactly the type of the
{name}`CategoryTheory.ElementaryTopos.classifier` field, and
{name}`hasSubobjectClassifier` registers existence.

There is also a necessary result that does not assume the classifier
has two values. With all constants admissible, monomorphisms are
exactly injections on accepted fibers, by
{name}`GebProto.EndomorphismCategory.DecisionProblem.mono_iff_injective`.
If some object has an accepted point,
{name}`exists_image_test_of_classifier` says every mono image, on
accepted target inputs, must be of the form `r(y) = v` for an
admissible endomorphism `r` and a fixed base value `v`. The proof
uses constant maps to test the pullback at individual points.
This necessity is weaker than the sufficient package: it does not
assert an admissible two-valued image checker or an image inverse.

For bitstrings, this rules out a classifier even with all total
computable functions. Accept canonical complete halting histories of
a fixed deterministic universal machine, and map each history to its
input. Require unique configuration encodings, the specified initial
configuration, and termination at the first halt. Each halting input
then has exactly one accepted history, so this map is an injection.
Its image in `U` is the halting set. An admissible image test, followed
by equality with a fixed string, would decide that set.

Validation of a supplied history and extraction of its input can be
done in logspace in the supplied history's length, by rescanning
adjacent configurations. The length of a history is not bounded by
the input's length. Thus the obstruction already applies to full
logspace functions, and to computable submonoids containing these
operations and all constants. The machine-encoding argument is an
informal deduction from the formal image-test theorem. Unique
certificates still do not make certificate existence decidable.

Arbitrary set-theoretic functions behave differently: classically,
image indicators and inverses of injections on their images can be
extended to total functions using a default base value. They satisfy
the sufficient classifier condition. The tests give a constructive
finite example by exhaustive Boolean search: the Boolean-base
category has a classifier even though it has no binary products.

# Collecting the conditions

{name}`elementaryTopos` assembles the conditions into the actual
{name}`CategoryTheory.ElementaryTopos` structure: classifier data,
pair coding, coproduct coding, agreement checkers, class normalizers,
and exponential coding for every pair of objects. Its classifier
data already supplies the singleton terminal checker and constant
false for the initial object. This is a conditional assembly of
chosen data, not an assertion that a familiar function class meets
all the conditions simultaneously.

There is a stronger incompatibility for these particular packages.
{name}`ClassifierData.exists_fixed_point_free` constructs a function
without fixed points from the image checker of the false singleton:
it sends `f` to `t` and every other value to `f`.
Consequently {name}`not_monoidalClosed_of_classifierData` proves
that classifier data together with pair coding rules out cartesian
closure. The collected sufficient packages therefore cannot all be
inhabited at once. This theorem concerns the specified two-valued
classifier package; it is not a claim that classifiers and
exponentials are incompatible in arbitrary categories.

For the goal of finding a small familiar function class, the current
results therefore give a boundary rather than a candidate topos.
Regular functions already suffice for the first four constructions;
full logspace also supplies equalizers. Unrestricted coequalizers
and classifiers encounter undecidable existence questions, while
exponentials encounter a diagonal obstruction even beyond
computability. No class of total computable bitstring functions
containing all logspace functions can meet the whole topos interface
in this category. Even taking every set-theoretic endomorphism does
not give a topos, because `U^U` is unavailable.

The sufficient closure conditions concern all functions in `S`.
Mere inclusion of a benchmark class in a larger submonoid does not
automatically establish pairing or abstraction closure for its extra
functions. Likewise, decision completeness alone does not supply
admissible output-producing operations. No globally minimal class
or equivalence between every sufficient package and the corresponding
universal property is claimed.
