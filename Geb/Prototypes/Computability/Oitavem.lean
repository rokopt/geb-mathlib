/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Word
public import Geb.Prototypes.Computability.Oitavem.Subtraction
public import Geb.Prototypes.Computability.Oitavem.Addition
public import Geb.Prototypes.Computability.Oitavem.Basic
public import Geb.Prototypes.Computability.Oitavem.Syntax
public import Geb.Prototypes.Computability.Oitavem.Truncation
public import Geb.Prototypes.Computability.Oitavem.Length
public import Geb.Prototypes.Computability.Oitavem.Size
public import Geb.Prototypes.Computability.Oitavem.Recursion
public import Geb.Prototypes.Computability.Oitavem.Derived
public import Geb.Prototypes.Computability.Oitavem.BoundedQuantification
public import Geb.Prototypes.Computability.Oitavem.PresheafCounterexample
public import Geb.Prototypes.Computability.Oitavem.Machine.SpaceTime
public import Geb.Prototypes.Computability.Oitavem.Machine.Read
public import Geb.Prototypes.Computability.Oitavem.Machine.While
public import Geb.Prototypes.Computability.Oitavem.Machine.CountOutput
public import Geb.Prototypes.Computability.Oitavem.Machine.ReadOutput
public import Geb.Prototypes.Computability.Oitavem.Machine.Generated
public import Geb.Prototypes.Computability.Oitavem.Machine.Allocate
public import Geb.Prototypes.Computability.Oitavem.Machine.Reader
public import Geb.Prototypes.Computability.Oitavem.Machine.Repeat
public import Geb.Prototypes.Computability.Oitavem.Machine.Compose
public import Geb.Prototypes.Computability.Oitavem.Machine.Realizer
public import Geb.Prototypes.Computability.Oitavem.Machine.Realizer.Reader
public import Geb.Prototypes.Computability.Oitavem.Machine.Realizer.Initial
public import Geb.Prototypes.Computability.Oitavem.Machine.Realizer.Compile
public import Geb.Prototypes.Computability.Oitavem.Machine.Realizer.Loop
public import Geb.Prototypes.Computability.Oitavem.Machine.Realizer.Retained
public import Geb.Prototypes.Computability.Oitavem.Machine.Realizer.Recursion
public import Geb.Prototypes.Computability.Oitavem.Machine.Counter
public import Geb.Prototypes.Computability.Oitavem.Machine.Segment
public import Geb.Prototypes.Computability.Oitavem.Machine.Subtraction
public import Geb.Prototypes.Computability.Oitavem.Machine.MapOutput
public import Geb.Prototypes.Computability.Oitavem.Machine.Initial
public import Geb.Prototypes.Computability.Oitavem.Machine.Capture
public import Geb.Prototypes.Computability.Oitavem.Machine.Recursion
public import Geb.Prototypes.Computability.Oitavem.Machine.RecursiveLength
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Oitavem's Logs algebra

The syntactic algebra of {cite}`Oitavem2010` Definition 3.1, its interpretation,
the safe-input truncation lemma, polynomial output length, its double
exponential bound uniform in the expression's size, and correctness and
logarithmic representation size of capped recursion states. Only logarithmically
many initial output digits are needed to obtain each such state. An indexed loop
can retain these output prefixes directly, with its equivalence to safe recursion
proved. The bounded-recursion scheme used in Lemma 3.2 is a derived constructor.

These results concern word functions and their representations. They do not assert
the existence of a polynomial-time, logarithmic-space Turing machine for every
expression. Such a theorem additionally requires a transducer implementation that
recomputes intermediate words instead of storing them on work tapes.

{name}`Geb.Oitavem.Machine.computes_polytime_logspace` supplies the time-bound
part of that construction: a halting transducer with a logarithmic work-space
bound has a simultaneous polynomial time bound, on the same machine. It does not
construct a machine for an expression.

The machine layer also supplies reusable physical-input and stored-word readers,
loops that emit output, and a one-work-tape transducer for {name}`Geb.Oitavem.squareWord`.
{name}`Geb.Oitavem.Machine.computableInTimeAndSpace_squareWord` proves simultaneous
quadratic time and logarithmic space for that example.
{name}`Geb.Oitavem.Machine.countOutput_runsTo` converts an emitter into a length
reader with one additional binary counter. Applied to the square machine, it
counts the generated quadratic word using two logarithmic work tapes.
{name}`Geb.Oitavem.Machine.computableInTimeAndSpace_length_squareWord` gives a
complete machine bound for numerical length composed with the square expression.
{name}`Geb.Oitavem.Machine.readOutput_runsTo` converts an emitter into a digit reader
with two extra tapes, a runtime query countdown and a one-bit result.
{name}`Geb.Oitavem.Machine.squareDigit_runsTo` verifies queries into the quadratic
word, including the first out-of-range position, in cubic time and logarithmic space.
Finite-state output transformations implement string predecessor, last-digit extraction,
and numerical successor and predecessor without additional work tapes. Generated length
and product constructors use binary counters; segment readers implement iterated predecessor.
Conditional generators select and run one branch after testing a generated word's length.
{name}`Geb.Oitavem.shortlexSub_eq_numericSub` verifies a digitwise subtraction algorithm
against the existing word encoding. {name}`Geb.Oitavem.Machine.numericSubGenerator_emitsIn`
implements it through virtual length and sentinel-digit readers: two scans determine
the sign and significant length, then emit the result with all working ports cleared.
{name}`Geb.Oitavem.shortlexAdd_eq_unrank_add` verifies bounded-carry addition for
log-transition, without decoding the long normal word's rank.
{name}`Geb.Oitavem.Expr.eval_transitionOffset` supplies an alternative using only
initial functions and normal composition, and {name}`Geb.Oitavem.Expr.eval_logTransitionNormal`
verifies the complete safe-to-normal substitution.
{name}`Geb.Oitavem.Machine.generatedPrefix_transformsIn` retains a bounded output
prefix while preserving the old saved value throughout the generator call.
{name}`Geb.Oitavem.Machine.retainedLoop_transformsIn` realizes an indexed saved-word
invariant with two reusable extra tapes.
{name}`Geb.Oitavem.Machine.squareRecLengthMachine_computes` verifies the saved-prefix
implementation of {name}`Geb.Oitavem.lengthByRec` over the generated square, with
simultaneous polynomial time and logarithmic space on eight work tapes.
{name}`Geb.Oitavem.Machine.concatRecGenerator_emitsIn` streams concatenation-recursion
step digits before its base result, from indexed child contracts.
{name}`Geb.Oitavem.Machine.Generator` supplies a common protected environment,
private restoring calls, and uniform logarithmic workspace bounds.
{name}`Geb.Oitavem.Initial.realize` combines independently compiled argument
generators through every initial function. Generated length and digit readers
return answers to caller registers and restore their shared private workspace.
{name}`Geb.Oitavem.Expr.realized` closes this interface under every Logs constructor,
including both recursion schemes and log-transition. Safe recursion captures a
logarithmic prefix at each intermediate step and emits the full final output.
{name}`Geb.Oitavem.Expr.computable_polytime_logspace` proves direct machine soundness:
every fixed expression with one normal input and no safe inputs has a finite
transducer with simultaneous polynomial time and logarithmic work space.

## References

* {cite}`Oitavem2010`
-/
