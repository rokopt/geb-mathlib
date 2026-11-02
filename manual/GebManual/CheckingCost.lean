/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import VersoManual
public import GebManual.Bibliography
import Geb.Prototypes.Kernel
import Geb.Prototypes.FreeTopos

/-! # Checking-cost chapter

Where the time of the bootstrap's slowest checks goes, the factors that compose it, how the
architecture of the metalogic's checker bears on them, and the changes that remove each factor.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The cost of checking" =>
%%%
tag := "checking-cost"
%%%

This chapter states where the time of the bootstrap's slowest checks
goes, the factors that compose it, how the architecture of the
metalogic's checker bears on them, and the changes that remove each
factor, in the order of their effect against their cost. Its figures
are those that {ref "logic"}[The logic] and
{ref "the-next-phase"}[The next phase] record, those of the runs of
`slow-checks.yml` on GitHub's hosted runners, whose limit on a job's
time is six hours, and those of {ref "measurements"}[The measurements]
at its end.

# The checks

:::table +header
*
  * Check
  * Time
  * What it computes
*
  * The loading in the mode `proof`
  * Under two minutes
  * The kernel's check of a proof of each step of the loading of the
    metalogic's program from the equations of {name}`Geb.Kernel.infer`
    at the definition's nodes, and the comparison of the denotation it
    states with the definition's mirror
*
  * The search of `datatype-app`
  * More than six hours
  * The compiled prover's search for the development's derivations
*
  * The search of `datatype-list`
  * Two and a half hours
  * The same, for its development
*
  * The other searches
  * From 8 to 71 minutes each
  * The same, for their developments
*
  * The check of the certificate `datatype-list`
  * Four and a half hours
  * Lean's evaluator's check of the certificate `datatype-list`
:::

The search of `datatype-app` does not complete within the limit. The
table's figures are those of a run of the hosted runners without the
second change below or those after it; {ref "measurements"}[The
measurements] give the times with them.

# The factors

## Computation as deduction

The base checker of the internal language computes no reduction. A
β-step, the unfolding of a definition, the computation of a fold and
each step of the arithmetic of numerals are nodes of a derivation
({name}`Geb.FreeTopos.Internal.Rule`), and the checker recomputes, by
substitution, the term each node rewrites to. A proof about a program
by its symbolic evaluation therefore has the size of the evaluation's
trace. At the measurement of the next phase, 99 in 100 of the stored
derivations' nodes lay in rewritings and 69 in 100 were compositions,
congruences and identities; the terms the rules name, counted as trees,
had ten times the derivations' nodes; and one step of conversion in
place of each rewriting leaves about one node in ninety. At numerals of
six decimal digits the base checker takes 27.1 seconds on the prover's
derivation of a product, and the step of evaluation at literals from
0.03 to 0.05 milliseconds.

A type theory with a conversion rule decides such equations by
computing. The equality of two terms up to reduction is a judgment its
checker decides, and a proof records the steps of reasoning alone, which
{citet BarendregtBarendsen2002}[] state as the Poincaré principle.
Reflection {citep Boutin1997}[] applies the principle to a decision
procedure, whose run in the checker replaces the proof it would emit, and
{citet GregoireLeroy2002}[] compile the reduction the checker performs.

## Syntax as numerals

The objects of the proofs about the compiler's components, kernel terms,
types and contexts, are rose trees with natural-number labels, and the
translation sends a label to the bitstring of its index
({name}`Geb.FreeTopos.Translation.numeral`). A case analysis of a term's
kind is then a test of a numeral, decided by splitting the label's bits:
the weakening proof of {ref "goedel-t"}[Gödel's T] splits them to a
depth of five, and the case analyses of bits, the unfoldings of the
library's arithmetic and the computations of its folds are its steps.
Over a datatype whose constructors are distinct operations, the same
case analysis is one computation of a fold at a constructor.

## Interpretation within interpretation

The proofs about the compiler's components are proofs about
interpreters. The statement of weakening equates two applications of the
kernel's type checker written in Geb, and the soundness of the datatype
language's typing relates the stage-1 compiler's typing and resolution
to the kernel's evaluation. The prover reduces the translation of the
interpreter at a symbolic term, so that each step the interpreter takes
on a concrete term is a sequence of steps of the internal language, each
a node of the derivation.

## The reduction

The prover's reduction ({name}`Geb.FreeTopos.Internal.eval`) tries, at
each node it visits, a list of rules in order
({name}`Geb.FreeTopos.Internal.rootRewrite`), substitutes by traversal
for a β-step and for the step of a fold
({name}`Geb.FreeTopos.Internal.Term.subst`), and builds the derivation
of every rewriting it performs, those of the attempts a tactic discards
for another proof included. A term, a type and a derivation are each a
W-type whose nodes hold their children as a function from their
positions ({name}`Geb.RoseTree`), so that a traversal tabulates each
node's children as a list, two terms are compared by traversing both,
and no subterm is shared. An environment machine {citep Landin1964}[],
which binds a variable to its value in place of substituting it, and
normalization by evaluation {citep BergerSchwichtenberg1991}[] avoid the
repeated traversals of substitution; hash-consing
{citep FilliatreConchon2006}[] shares equal subterms and compares two
terms by their identities. The conversion checker's step `machine`
reduces by an environment machine
({name}`Geb.FreeTopos.Internal.machineReduce`) that evaluates lazily and
computes each delayed value once {citep Launchbury1993}[], the library's
definitions being written for a reduction that reduces a conditional's
selected branch alone; its values are trees of the same W-type, and its
reading back of a value is a term to which the evaluated term rewrites
by the base checker's rules
({name}`Geb.FreeTopos.Internal.machineReduce_reaches`).

## Evaluation by the interpreter

A stored certificate is checked by `evaluation_axiom`, which evaluates
the check at elaboration by `Lean.Meta.evalExpr`. The evaluator
interprets the intermediate representation of a definition whose
compiled code no shared library loaded into Lean holds, and calls the
compiled code of one that it holds. The library `Geb` is compiled into
a shared library that Lake loads into every module importing it from
another library (Lake's option `precompileLibrary`), so that the
checker runs compiled; the definitions of the test library, among them
the reading of the certificate's text, are interpreted. Checked so, the
checks take from a fifth to a sixth of their interpreted time, and from
the interpreted time to the compiled time is a factor of 9 to 12
({ref "measurements"}[The measurements]).

## The loading in the mode `proof`

Each step of the loading is a theorem whose proof applies, at each node
of the definition, the equation of the checker-evaluator
{name}`Geb.Kernel.infer` at the node's form, at the types and
denotations its children's equations state
(`Geb/Prototypes/Kernel/LoadCommand.lean`). The kernel checks each
equation's instance, compares the types by their constructors, each
global's type being stored as a type tree, reaches a referenced global
in the list of the globals reversed, in as many steps as it is from the
last, and compares the denotation the proof states with the
definition's mirror. Its time is that of the size of the definitions
and of the distance of the globals they refer to, rather than of the
reduction of {name}`Geb.Kernel.infer`, which decides each equality of
types inside a denotation by evaluating it. Each list of globals and
each global is declared at the height above its body's, as the
elaborator declares a definition, so that the kernel, which unfolds the
higher of two definitions first, unfolds a list of globals to the append
that builds it rather than evaluating the append.

## The contexts of congruences and type inference
%%%
tag := "contexts-typing"
%%%

A congruence that rewrites an abstraction's body or a fold's step
rewrites it in the context the binder extends
({name}`Geb.FreeTopos.Internal.childCtxs`): each hypothesis is weakened
past the bound variables, by a traversal of the formula, and the type of
a fold's start or datum is inferred. The checker as compiled
({name}`Geb.FreeTopos.Internal.checkFast`) weakens a hypothesis where a
rewriting by it reads it instead, so that a traversal of every
hypothesis at each congruence under a binder becomes a traversal of one
hypothesis at each rewriting by a hypothesis. The prover's reduction
enters the same contexts at each abstraction and fold it reduces under
({name}`Geb.FreeTopos.Internal.deepStep`), and as compiled
({name}`Geb.FreeTopos.Internal.evalFast`) weakens a hypothesis where a
rule reads it likewise. The application of a theorem
infers the type of each term it substitutes
({name}`Geb.FreeTopos.Internal.instOk`), and propositional and
functional extensionality, a cut and a conversion from a formula infer
the type of a formula or a function. The base checker infers a type by
a fold that computes the type alone
({name}`Geb.FreeTopos.Internal.typeOf`), proved to be the type the
term's compilation to the combinators computes
({name}`Geb.FreeTopos.Internal.typeOf_eq_compile`); a compilation
builds the arrow of each node, from the product of the context's types,
and finds a fold's parameters by testing which variables its start or
step mentions. As compiled, the inference reads the parts of a product,
a coproduct, an exponential, a list object or a rose-tree object from
the label of its former
({name}`Geb.FreeTopos.Internal.prodParts_eq_prodPartsFast` and its
analogues) rather than by comparing the type with the former at its
children, a comparison of the size of the type at each application and
projection; it tests a type by a fold that does not rebuild its subtrees
({name}`Geb.FreeTopos.Internal.isTy_eq_isTyFast`); and it decides the
equality of two trees, types and terms alike, by comparing the children
of two nodes of one shape by their indices
({name}`Geb.PartialHorn.instDecidableEq_eq_decEqFast`) rather than over
a list of the indices built at each node. In the development of `datatype-list` the weakening of
the hypotheses at each congruence is most of the time of
{name}`Geb.FreeTopos.Internal.check` evaluated as it is defined
({ref "measurements"}[The measurements]).

## Their composition

The factors are independent, and each multiplies the cost the others
leave. The size of a derivation is the length of a trace, the first and
third factors; the encoding of syntax lengthens the trace, the second;
each step of the trace costs a traversal of the reduction, the fourth;
each operation of the check costs the interpreter's overhead, the
fifth; and each congruence under a binder costs a traversal of every
hypothesis, the seventh. The ratio of the base checker's time to the step of evaluation at
literals, about five times ten to the fifth, is the first two together. No one
factor accounts for the distance between a check of seconds and one that
exceeds the hosted runners' limit.

# Equality as a sort

The equality of the metalogic's theory is a judgment at both sorts,
established by a certificate the checker checks
({ref "presentation"}[The presentation]). Three forms of equality bear
on the cost of checking:

:::table +header
*
  * Form
  * A proof records
  * The checker
*
  * A judgment, established by a certificate
  * Every step, the steps of computation among them
  * Checks each step
*
  * A third sort, of proofs of equations
  * Every step, as a term of that sort
  * Checks the term's sort
*
  * A judgment decided by conversion
  * The steps of reasoning alone
  * Computes the steps of computation
:::

A presentation with a third sort, whose operations are reflexivity,
symmetry, transitivity, congruence and the instances of the axioms, makes
a proof a term of the theory. Such a term records the steps a
certificate records, so it changes neither the size of a proof nor the
time to check it, and terms of that sort that prove one equation are
distinct unless further equations identify them. The cost is in the
steps of computation that the first two forms record and the third
leaves to the checker.

The choice between the fibered and the indexed presentation
({citet Kovacs2022}[], Section 4.7) bears on a different cost. In the
fibered presentation the definedness of a composite is an equation
between objects, which a certificate of the combinators proves; of those
certificates' nodes, 89 in 100 repeated terms, and 78 in 100 after the
definitional extension ({ref "definitional-extensions"}[Definitional
extensions and shared certificates]), until the checker's inference of
definedness and canonical objects, which the indexed presentation states
as typing. The Mitchell–Bénabou language, whose typing is syntactic, is
the language the proofs about programs are written in, and its
derivations are those the first factor enlarges.

# The prover and the checker

An untrusted prover whose output a small trusted checker checks is the
architecture of Lean, whose elaborator and tactics are untrusted and
whose kernel checks the terms they construct, and of the metalogic's
prover and checker; the soundness of a result rests on the checker
alone. Three properties of the form it takes here bear on the cost.

* The checker computes no conversion, so a certificate carries the
  computation that a checker with a conversion rule performs.
* Certificates are stored artifacts that searches generate, and
  `ci.yml` and `scripts/pre-push.sh` repeat a search and compare its
  output with the committed certificate byte for byte where the search's
  inputs differ from those of its last passing run, so that a search's
  time is the time of a check after each change to them.
* The prover, its tactics and the combinator prover are written in Lean
  and in Geb, with proofs that the two construct the same certificates
  (`GebTests/Prototypes/FreeTopos/Agreement/`). The soundness of a
  development rests on the checker, and the prover's public contract is
  any checked certificate ({ref "compatibility-contract"}[The
  compatibility contract]), so the agreement of the provers adds to the
  work and not to what is established.

Milawa's checkers {citep Davis2009}[] form a sequence of increasing
strength, each proved sound with the checker before it, and its large
proofs are checked by the later checkers. The bootstrap has checked its
proofs about the compiler's components with the base checker, and
admits the first stronger checker after them
({ref "conversion-continuation"}[Completing the checker with a step of
conversion]).

# The changes

The changes below remove the factors, in the order of their effect
against their cost.

1. The checks evaluated by compiled code, which removes the fifth
   factor; what is trusted gains the C compiler that compiles Lean's
   intermediate representation, which the interpreter executes
   directly. The library `Geb` is compiled for the evaluator of its
   importers. The shared library is built from those of the libraries
   it imports, each whole: a build without the GitHub cache compiles
   the C of every module of mathlib, which the mathlib cache holds, and
   elaborates the modules of CSLib that `Geb` does not import, in seven
   minutes on sixteen cores.
2. The hypotheses weakened past a binder where a rewriting reads one,
   rather than at each congruence under the binder. A rewriting adds no
   hypothesis, so that within one every hypothesis is weakened past the
   same binders: the compiled checker
   ({name}`Geb.FreeTopos.Internal.checkFast`) rewrites under the
   hypotheses as they were stated with the number of the binders, a
   delayed renaming in the manner of explicit substitutions
   {citep AbadiCardelliCurienLevy1991}[], and weakens a hypothesis where
   it rewrites by it. It is proved equal to the checker
   ({name}`Geb.FreeTopos.Internal.check_eq_checkFast`), which the
   compiler replaces by it. It removes the seventh factor. The searches'
   time is not in it ({ref "measurements"}[The measurements]). The
   conversion checker as compiled
   ({name}`Geb.FreeTopos.Internal.convCheckFast`) takes it at its steps
   `base`. Neither it nor the inference of a type alone is in the
   checker written in Geb
   ({ref "base-checker-evaluation"}[The base checker's evaluation]).
3. The prover's reduction weakening the hypotheses where a rule reads
   one, as the compiled checker does, trying at a node only the rules
   whose left side's root may have the node's label, and comparing a
   term with an equation among the hypotheses by a fold of the
   equation's left side computed once rather than by building its
   weakening. The reduction as compiled
   ({name}`Geb.FreeTopos.Internal.evalFast`) is proved equal to
   {name}`Geb.FreeTopos.Internal.eval`
   ({name}`Geb.FreeTopos.Internal.eval_eq_evalFast`), which the compiler
   replaces by it, so a search constructs the certificates it
   constructed. It removes most of the searches' time, which was the
   weakening of every hypothesis at each binder the reduction entered
   ({ref "measurements"}[The measurements]).
4. A search run where its inputs differ from those of its last passing
   run, on every push. `ci.yml` keys a passing run by the bytes of the
   executable `geb-certify` and by the committed certificates, and runs a
   search at a key with no record of one, and `scripts/pre-push.sh`
   records the same inputs at its last passing run of the searches
   (`docs/rules/ci-and-workflow.md` § Certificates). The executable
   changes with the compiled code of every module it imports, so a
   change to the prover or to a program it reasons about runs every
   search; content identity ({ref "content-identity"}[Content identity])
   would name the definitions each search reads.
5. A proof of each step of the loading from the equations of the
   checker-evaluator at each form of term, of the size of the definition
   rather than of its reduction, which brings the mode `proof` within
   minutes ({ref "measurements"}[The measurements]), and so the mode
   `proof` is the default of every build and workflow, which removes the
   axioms of the loading from them.
6. Conversion computed by the checker by a reduction of another method,
   proved sound against the base checker's rules rather than equal to
   the prover's reduction. The conversion checker's steps `norm` and
   `eval` compute the prover's reduction's result alone, without its
   derivation, which removes the first factor from the certificates'
   size and leaves the time of a step the reduction's own; the step
   `machine` reduces by the environment machine, at numerals of six
   decimal digits from 3.5 times faster than the step `eval` at their
   equality to 105 times at their product
   ({ref "measurements"}[The measurements]), which removes the
   fourth factor at the terms it reduces. It reads a fold's step back
   unreduced. A translation of the stored developments' derivations
   into steps of it shortens their certificates and leaves their checks
   as costly; it replaces only the joins whose rewritings cite neither
   a theorem nor a hypothesis, which the machine does not apply.
7. The datatypes of the proofs as datatypes of the metalogic: the
   translation of a datatype of the datatype language to the initial
   algebra of its declaration, rather than to rose trees over
   bitstrings, which removes the second factor.
8. Each untrusted component written once, the agreement proved for the
   checker and the translation, which are trusted.

# The measurements
%%%
tag := "measurements"
%%%

The stored certificates of weakening, of substitution and of the
expansion's identity on programs of kernel forms are checked by the
modules of `GebTests/Prototypes/FreeTopos/Certified/`, whose builds
Lean's evaluator's checks dominate, with the library `Geb` interpreted
and compiled, and by compiled code in
`GebBench/Prototypes/FreeTopos/Certified.lean`, the least of three runs:

:::table +header
*
  * Certificate
  * The module's build, interpreted
  * The module's build, `Geb` compiled
  * Compiled
*
  * Weakening
  * 57 seconds
  * 9.0 seconds
  * 5.4 seconds
*
  * Substitution
  * 97 seconds
  * 20 seconds
  * 11.2 seconds
*
  * Expansion
  * 95 seconds
  * 16 seconds
  * 7.8 seconds
:::

The module checking the certificate `datatype-list`
(`GebTests/Prototypes/FreeTopos/Certified/DatatypeList.lean`) builds
in 32.5 minutes with `Geb` compiled, on sixteen cores, where the slow
checks' run on GitHub's hosted runners took four and a half hours with
it interpreted.

The conversion checker's steps `norm` and `eval` compute the prover's
reductions' results alone ({name}`Geb.FreeTopos.Internal.normalizeR`,
{name}`Geb.FreeTopos.Internal.evalR`), each proved to be the projection
of the reduction that computes a derivation
({name}`Geb.FreeTopos.Internal.normalizeR_eq`,
{name}`Geb.FreeTopos.Internal.evalR_eq`), so that a step is sound as
before, by the soundness of the base checker at the derivation it does
not build; the step `machine` reduces by the environment machine, sound
by the base checker's soundness at a derivation it does not build
either. `GebBench/Prototypes/FreeTopos/Literals.lean` proves the
equation of the library's arithmetic at numerals and its value's numeral
by the base checker on the prover's derivation, by the prover's reduction
of each side computing its derivation, by the step `eval`, by a step of
evaluation, and by the step `machine` at each side. At numerals of six
decimal digits, in one run:

:::table +header
*
  * Definition
  * Base checker
  * Reduction with its derivation
  * Step `eval`
  * Step of evaluation
  * Step `machine`
*
  * Addition
  * 136 milliseconds
  * 171 milliseconds
  * 172 milliseconds
  * 0.035 milliseconds
  * 4.5 milliseconds
*
  * Multiplication
  * 27.1 seconds
  * 22.3 seconds
  * 18.8 seconds
  * 0.053 milliseconds
  * 179 milliseconds
*
  * Truncated difference
  * 235 milliseconds
  * 265 milliseconds
  * 234 milliseconds
  * 0.035 milliseconds
  * 6.1 milliseconds
:::

At the other definitions and sizes measured, the step `eval` and the
reduction computing its derivation take the same time within the
variation between runs. The derivation is therefore not where the
reduction's time goes: computing the result alone removes the
derivation's nodes from a certificate and leaves the time of the
reduction, its rewriting by substitution and its trial of the rules at
each node, to the method of the reduction. The step `machine` reduces by
another method, and at numerals of six decimal digits is faster than the
step `eval` by factors from 3.5, at equality, to 105, at the product. The
step of
evaluation, which computes by the arithmetic of the natural numbers, is
faster than the first three on the product by factors from 350000 to
510000, the first two factors together, and than the step `machine` by
a factor of 3400 there, the second factor, which the machine leaves.

`GebBench/Prototypes/FreeTopos/Profile.lean` divides the base checker's
time on a stored development among its derivations' rules: each node's
time less its children's is the rule's own, and probes repeat and time
apart the contexts of a congruence's children, the
test of a theorem's instance, which infers the types of the terms it
substitutes, and the inference of the types of formulas. On the
development of `datatype-list` after those of `datatype-base` and
`datatype-atom`, with type inference by compilation, in one run without
the probes, the check took 24.8
minutes, its theorem of index 360 alone 18.5, and the congruences'
own time was 59 in 100 of it. On its theorem of index 348, of 333682
nodes, with type inference by compilation, in one run with the probes,
which repeat what they time:

:::table +header
*
  * Computation
  * Seconds
*
  * The contexts of congruences
  * 66.1
*
  * The congruences' own time less their contexts
  * 29.7
*
  * The tests of theorems' instances
  * 7.7
*
  * The inference of the types of formulas
  * 1.4
*
  * β-steps
  * 0.95
*
  * Rewriting by hypotheses
  * 0.07
*
  * The theorem, with the probes
  * 186
:::

Without the probes the theorem takes 80.7 seconds. On the development
of substitution, in one run without the probes, of 13.1 seconds, the
β-steps' own time is 5.3, the compositions' 1.7, the rewritings by
theorems' 1.3 and the rewritings by hypotheses' 0.02.

With type inference by {name}`Geb.FreeTopos.Internal.typeOf`, in one
run with the probes, on the theorem of index 348 the tests of
theorems' instances take 2.1 seconds, the inference of the types of
formulas 0.38 and the contexts of congruences 59.0. Its congruences
that weaken the hypotheses past a binder are 5205, and weaken 363667
hypotheses of 174537590 nodes in all. The compiled checks of weakening,
of substitution and of the expansion's identity take 5.4, 10.8 and 3.2
seconds, and the module checking the certificate `datatype-list` builds
in 19.0 minutes.

With the hypotheses weakened where a rewriting reads them
({name}`Geb.FreeTopos.Internal.checkFast`), in one run with the probes,
the theorem of index 348 takes 8.9 seconds: the congruences' own time
is 0.11 seconds and their contexts' 0.02, and the largest parts left are the rewritings by
theorems, 2.3 seconds, and the tests of their instances, 1.9. The
compiled checks of weakening, of substitution and of the expansion's
identity take 5.1, 10.3 and 3.1 seconds, and the module checking the
certificate `datatype-list` builds in 176 seconds.

The checks with the changes above but the third, on sixteen cores, in
one run, the searches six at a time:

:::table +header
*
  * Check
  * Time
*
  * The loading in the mode `proof`
  * 100 seconds for the six layers, `Checker`, `Translation`, `Prover`,
    `Tactics`, `Combinator` and `Printer`, each importing the one before,
    40, 8.1, 9.0, 13, 20 and 9.9 seconds, and 105 for the test of their
    agreement
*
  * The loading in the mode `native`
  * 12 seconds for the six layers, and 106 for the test of their
    agreement
*
  * The search of `datatype-app`
  * 5.5 hours
*
  * The search of `datatype-list`
  * 2.0 hours
*
  * The other searches
  * From 17 seconds to 46 minutes each
*
  * The modules of the certificate `datatype-list` and of the
    interaction-net compiler's graph reduction
  * 176 and 585 seconds
:::

The searches longer than twenty minutes take from 0.6 to 1.2 times their
time in the hosted runners' run of {ref "checking-cost"}[the table of
checks], which includes the build, so their time is the prover's rather
than the checker's.

With the third change, and the inference of types compiled as the fold of
the children's types alone
({name}`Geb.FreeTopos.Internal.typeOf_eq_typeOfFast`), in one run on
sixteen cores, the searches three at a time, the search of
`datatype-atom` takes 25.5 seconds, against 300 without them in the same
run; that of `datatype-list` 402 seconds, against 64 minutes in another
run; and that of `datatype-app` 10.6 minutes. The certificates they write
are the committed ones byte for byte. Of the search of `datatype-atom`
before the third change, 73 in 100 was the renaming of terms, most of it
the weakening of the hypotheses at the binders the reduction entered.
Of the search of `datatype-app` after it, about two fifths is the
inference of types: by the checker, which checks each theorem a search
finds, at the instances of theorems, and in the reduction's contexts of
folds.

With the parts of types read from their labels, the test of types as a
fold and the equality of trees decided over the indices of the children
({ref "contexts-typing"}[The contexts of congruences and type
inference]), in one run of every search in turn, the searches of
`datatype-list`, `datatype-app` and `decode-case`, the longest, take
277, 391 and 495 seconds, against 469, 638 and 824 without them, and
every search in turn 2601 seconds; the certificates are the committed
ones byte for byte. Of the search of `datatype-app` they halve the
inference of types, by the checker and in the reduction's contexts of
folds. The search of `datatype-app` reaches 7.2 gigabytes of resident
memory.

With them, `scripts/pre-push.sh` with its build up to date, on sixteen
cores, in one run, the searches four at a time, each in a process of its
own reading the committed certificates, takes 40.0 minutes: the searches
20.0 and the check of the bootstrap's fixed points 17.3. The searches'
times sum to 48 minutes, against 43 in turn; `decode-case`, the longest
at 589 seconds, begins among the last, as it is listed, and ends the
searches. No process exceeds 4.8 gigabytes of resident memory.

# The searches' remaining time
%%%
tag := "searches-remaining"
%%%

With the changes above, in one run of the search of `datatype-app` with
probes, which take its time from 391 to 495 seconds, the prover's
reduction takes 210 seconds and the check of each declaration as it is
stored (`checkAfter` in `GebTests/Prototypes/FreeTopos/DatatypeBase.lean`)
175. Of the reduction, the inference of types in the contexts of folds
takes 46 seconds and substitution 7; the remainder, about 155 seconds, is
the matching of rules and the reduction's own traversal, which the probes
do not divide. Of the check, the tests of theorems' instances
({name}`Geb.FreeTopos.Internal.instOk`) take 68 seconds, nearly all of it
the inference of the types of the terms they substitute, which are the
hypotheses' formulas of the logic's deductions; the inference of the
types of 1538 formulas, about 30 milliseconds each, 47 seconds;
substitution 14 and renaming 11.

The trees a check types share almost no structure, a tree's nodes being
about as many as its distinct subtrees, so a table of types by subtree
saves no traversal. Looking up a definition among the globals in an
array rather than a list changes the search's time by less than 1 in
100.

Two measurements locate the next change: the division of the
reduction's remainder among the matching of a rule's left side, the
choice of the rules tried at a node and the traversal; and, in the
check, how often the same formula's type is inferred at successive
instances of theorems. The check as stored is the only check of the
certificates that no module of `GebTests/Prototypes/FreeTopos/Certified/`
reads (`docs/rules/ci-and-workflow.md` § Certificates),
so it stays in the search until such modules check them.
