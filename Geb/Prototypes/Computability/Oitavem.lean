/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Word
public import Geb.Prototypes.Computability.Oitavem.Basic
public import Geb.Prototypes.Computability.Oitavem.Syntax
public import Geb.Prototypes.Computability.Oitavem.Truncation
public import Geb.Prototypes.Computability.Oitavem.Length
public import Geb.Prototypes.Computability.Oitavem.Recursion
public import Geb.Prototypes.Computability.Oitavem.Derived
public import Geb.Prototypes.Computability.Oitavem.BoundedQuantification
public import Geb.Prototypes.Computability.Oitavem.PresheafCounterexample
public import Geb.Prototypes.Computability.Oitavem.Machine.SpaceTime
public import Geb.Prototypes.Computability.Oitavem.Machine.Read
public import Geb.Prototypes.Computability.Oitavem.Machine.While
public import Geb.Prototypes.Computability.Oitavem.Machine.CountOutput
public import Geb.Prototypes.Computability.Oitavem.Machine.ReadOutput
public import Geb.Prototypes.Computability.Oitavem.Machine.Repeat
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Oitavem's Logs algebra

The syntactic algebra of {cite}`Oitavem2010` Definition 3.1, its interpretation,
the safe-input truncation lemma, polynomial output length, and correctness and
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
General reader substitution and the retained-prefix recursion machine remain open.

## References

* {cite}`Oitavem2010`
-/
