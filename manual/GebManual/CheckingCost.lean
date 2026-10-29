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
  * The loading in the mode `rfl`
  * More than six hours
  * The kernel's reduction of {name}`Geb.Kernel.infer` on each
    definition of the metalogic's program, and the comparison of the
    denotation it computes with the definition's mirror
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
  * `GebSlow`
  * Four and a half hours
  * Lean's evaluator's check of the certificate `datatype-list`
:::

The first two do not complete within the limit.

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
six decimal digits the base checker takes 28.7 seconds on the prover's
derivation of a product, and the step of evaluation at literals from 0.2
to 0.4 milliseconds.

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

## The loading in the mode `rfl`

Each step of the loading is a theorem proved by reflexivity: the
checker-evaluator, applied to a definition's tree in the globals before
it, gives those globals extended by the definition's computed type and
its mirror, cast to the type's denotation
(`Geb/Prototypes/Kernel/LoadCommand.lean`). The kernel decides it by
reducing {name}`Geb.Kernel.infer`, a type checker whose result carries a
denotation of the type it computes, through the casts that compare the
computed type with the mirror's, in the environment of every global
before the definition. Its time grows faster than the program
({ref "improvements"}[Improvements]).

## Their composition

The factors are independent, and each multiplies the cost the others
leave. The size of a derivation is the length of a trace, the first and
third factors; the encoding of syntax lengthens the trace, the second;
each step of the trace costs a traversal of the reduction, the fourth;
and each operation of the check costs the interpreter's overhead, the
fifth. The ratio of the base checker's time to the step of evaluation at
literals, about ten to the fifth, is the first two together. No one
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
  `slow-checks.yml` repeats each search and compares its output with the
  committed certificate byte for byte, so that a search's time is the
  time of a check.
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
2. The searches out of the daily checks: the committed certificates
   checked, and a search run when the sources it reads change, which
   content identity ({ref "content-identity"}[Content identity])
   determines.
3. The mode `native` as the loading's policy, with the mode `rfl` run on
   demand or replaced by a proof of each step from the equations of the
   checker-evaluator at each form of term, of the size of the definition
   rather than of its reduction.
4. Conversion computed by the checker by a reduction of another method,
   proved sound against the base checker's rules rather than equal to
   the prover's reduction. The conversion checker's steps `norm` and
   `eval` compute the prover's reduction's result alone, without its
   derivation, which removes the first factor from the certificates'
   size and leaves the time of a step the reduction's own; the step
   `machine` reduces by the environment machine, at numerals of six
   decimal digits from 3 times faster than the step `eval` at their
   equality to 160 times at their product
   ({ref "measurements"}[The measurements]), which removes the
   fourth factor at the terms it reduces. It reads a closure and a
   fold's step back unreduced, and no tactic yet emits it.
5. The datatypes of the proofs as datatypes of the metalogic: the
   translation of a datatype of the datatype language to the initial
   algebra of its declaration, rather than to rose trees over
   bitstrings, which removes the second factor.
6. Each untrusted component written once, the agreement proved for the
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

The module of `GebSlow` checking the certificate `datatype-list` builds
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
  * 224 milliseconds
  * 212 milliseconds
  * 205 milliseconds
  * 0.32 milliseconds
  * 5.8 milliseconds
*
  * Multiplication
  * 37.5 seconds
  * 39.6 seconds
  * 32.2 seconds
  * 0.38 milliseconds
  * 197 milliseconds
*
  * Truncated difference
  * 201 milliseconds
  * 262 milliseconds
  * 268 milliseconds
  * 0.31 milliseconds
  * 7.4 milliseconds
:::

At the other definitions and sizes measured, the step `eval` and the
reduction computing its derivation take the same time within the
variation between runs. The derivation is therefore not where the
reduction's time goes: computing the result alone removes the
derivation's nodes from a certificate and leaves the time of the
reduction, its rewriting by substitution and its trial of the rules at
each node, to the method of the reduction. The step `machine` reduces by
another method, and at numerals of six decimal digits is faster than the
step `eval` by factors from 3, at equality, to 160, at the product. The
step of
evaluation, which computes by the arithmetic of the natural numbers, is
faster than the first three on the product by factors from 80000 to
110000, the first two factors together, and than the step `machine` by
a factor of 500 there, the second factor, which the machine leaves.
