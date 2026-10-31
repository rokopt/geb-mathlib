/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebBench.Prototypes.FreeTopos.TranslationProofs
public import GebTests.Prototypes.FreeTopos.Certified.Expansion
public import GebTests.Prototypes.FreeTopos.Certified.Substitution
public import GebTests.Prototypes.FreeTopos.Certified.Weakening

set_option doc.verso true in
/-!
# The stored certificates, checked by compiled code

The checks that the modules of {lit}`GebTests.Prototypes.FreeTopos.Certified` state by
{lit}`evaluation_axiom`, which Lean's evaluator decides when the modules are elaborated, decided
here by the compiled checker: for each of the certificates of weakening, of substitution and of
the expansion's identity on programs of kernel forms, its number of declarations and the least of
three times its check takes, the program read and translated, in milliseconds.

## Main definitions

* {lit}`run` — the measurements.

## Tags

internal language, certificate, compiled evaluation, measurement, benchmark
-/

set_option doc.verso true

@[expose] public section

namespace GebBench.Prototypes.FreeTopos.Certified

open Geb Geb.FreeTopos
open GebTests.Prototypes.FreeTopos GebTests.Prototypes.FreeTopos.Certified
open GebBench.Prototypes.FreeTopos.TranslationProofs (timeUs)

set_option compiler.extract_closed false in
/-- The measurement of one certificate's check, printed, and an error where it fails. -/
def report (name : String) (decls : List Internal.Decl) (check : Unit → Bool) : IO Unit := do
  let (ok, t) ← timeUs check
  if !ok then throw (IO.userError s!"{name}: the check fails")
  IO.println s!"{name},{decls.length},{t / 1000}"

set_option compiler.extract_closed false in
/-- The measurements. Closed terms are not extracted, so that each check runs when it is timed
rather than when the program starts. -/
def run : IO Unit := do
  IO.println "certificate,declarations,check_milliseconds"
  report "weakening" Weakening.decls fun _ ↦
    provedIn GebTests.Prototypes.FreeTopos.Weakening.program
      GebTests.Prototypes.FreeTopos.Weakening.Prog.G Weakening.decls
      GebTests.Prototypes.FreeTopos.Weakening.weakening
  report "substitution" Substitution.decls fun _ ↦
    provedIn GebTests.Prototypes.FreeTopos.Substitution.program
      GebTests.Prototypes.FreeTopos.Weakening.Prog.G Substitution.decls
      GebTests.Prototypes.FreeTopos.Substitution.substitution
  report "expansion" Expansion.decls fun _ ↦
    provedIn GebTests.Prototypes.FreeTopos.Expansion.program
      GebTests.Prototypes.FreeTopos.Weakening.Prog.G Expansion.decls
      GebTests.Prototypes.FreeTopos.Expansion.expansion

end GebBench.Prototypes.FreeTopos.Certified

end
