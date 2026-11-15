/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Literals
public import GebTests.Prototypes.FreeTopos.Agreement.Conversion

set_option doc.verso true in
/-!
# The environment machine written in Geb beside the machine in Lean

For products of numerals of growing sizes, in the development of
{lit}`GebTests.Prototypes.FreeTopos.Literals`, the time the conversion checker takes to accept a
step of the environment machine at each side of the equation of the product and its value's
numeral: by the checker in Lean ({name}`Geb.FreeTopos.Internal.convCheck`), whose machine delays a
value and computes it when it is first read, and by the checker written in Geb
({lit}`bootstrap/free-topos/conversion.geb`), in the Lean the bootstrap compiler emits, whose
machine computes a delayed value where it builds the node. The two machines are one function of
the term reduced, so the checkers accept the same certificates; the table measures what computing
each delayed value costs. The measurements stop after the first product at which the checker
written in Geb takes longer than a bound.

## Main definitions

* {lit}`byMachineAt` — the certificate of an equation by a step of the machine at each side,
  within a depth of recursion.
* {lit}`provesLean`, {lit}`provesGeb` — whether the checker in Lean, and the checker written in
  Geb, accepts that certificate for an equation of closed terms.
* {lit}`sizes` — the factors measured.
* {lit}`run` — the measurements.

## Tags

internal language, abstract machine, lazy evaluation, mirror, measurement, benchmark
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebBench.Prototypes.FreeTopos.MachineMirror

open Geb Geb.Kernel Geb.FreeTopos
open GebTests.Prototypes.FreeTopos.Agreement.Encode
  GebTests.Prototypes.FreeTopos.Agreement.Conversion
open GebTests.Prototypes.FreeTopos.Literals (G entries bin lit)
open Internal (Term)

/-- The certificate of an equation by a step of the machine at each side within a depth of
recursion, every definition of the library unfolded. -/
def byMachineAt (fuel : ℕ) : Internal.ConvDeriv :=
  RoseTree.node (.base .join)
    [RoseTree.node (.machine fuel Translation.lib.length [] 0 1 []) [],
      RoseTree.node (.machine fuel Translation.lib.length [] 0 1 []) []]

/-- Whether the checker in Lean accepts a step of the machine at each side of an equation of
closed terms, within a depth of recursion. -/
def provesLean (fuel : ℕ) (t u : Term) : Bool :=
  (⟨0, [], [], Term.eq t u⟩ : Internal.Thm).convChecks G entries [] (byMachineAt fuel)

/-- Whether the checker written in Geb accepts a step of the machine at each side of an equation
of closed terms, within a depth of recursion. -/
def provesGeb (fuel : ℕ) (t u : Term) : Bool :=
  («Conversion.thmConvChecks» (encGlobals G) (entries.toList.map encEntry) []
    (encThm ⟨0, [], [], Term.eq t u⟩) (encConv (byMachineAt fuel))).label != 0

/-- The factors measured, each multiplied by itself: the numbers one less than the powers of
two, of one bit more at each. -/
def sizes : List ℕ := (List.range 12).map fun i ↦ 2 ^ (i + 1) - 1

/-- The time to evaluate a Boolean once, in microseconds, with its value. -/
def timeOnce (f : Unit → Bool) : IO (Bool × ℕ) := do
  let t₀ ← IO.monoNanosNow
  let b ← IO.lazyPure fun _ ↦ f ()
  let t₁ ← IO.monoNanosNow
  pure (b, (t₁ - t₀) / 1000)

set_option compiler.extract_closed false in
/-- The measurements: each row the factor, whether the checkers accept, and the times of the two
checkers, in microseconds, at a depth of recursion of the machine, until the checker written in
Geb takes longer than a bound, in microseconds; an error where the checkers differ. Closed terms
are not extracted, so that each check runs when it is timed rather than when the program
starts. -/
def run (fuel : ℕ := 256) (bound : ℕ := 2000000) : IO Unit := do
  IO.println "factor,accepted,lean_machine_microseconds,geb_machine_microseconds"
  (← IO.getStdout).flush
  let mut go := true
  for a in sizes do
    if go then
      let t := bin .mul a a
      let u := lit (a * a)
      let (okL, tL) ← timeOnce fun _ ↦ provesLean fuel t u
      let (okG, tG) ← timeOnce fun _ ↦ provesGeb fuel t u
      if okL != okG then throw (IO.userError s!"mul {a} {a}: the checkers differ ({okL} {okG})")
      IO.println (",".intercalate ([toString a, toString okL, toString tL, toString tG]))
      (← IO.getStdout).flush
      if tG > bound then go := false

end GebBench.Prototypes.FreeTopos.MachineMirror

end
