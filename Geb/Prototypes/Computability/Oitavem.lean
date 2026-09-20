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

## References

* {cite}`Oitavem2010`
-/
