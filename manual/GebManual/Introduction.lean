/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import VersoManual

/-! # Introduction chapter -/

open Verso.Genre Manual

#doc (Manual) "Introduction" =>

Geb is a programming language whose first-class notions include
"programming language" itself. Its specification, interpreter, and
compiler are developed as formal mathematics; this repository
develops that mathematics in Lean 4 against mathlib.

Two disciplines shape the development. The first is constructive:
no `noncomputable` definitions, with `Classical` reasoning
minimised and tracked module by module. The second is
upstream-directed: content is authored to be plausibly
upstreamable, with `Geb/Mathlib/` targeting mathlib4,
`Geb/Cslib/` targeting CSLib, `GebLang/` targeting mathlib4 or
CSLib per module's own import closure, and `Geb/Internal/`
holding the downstream-only remainder.

The chapters that follow present the implemented mathematics one
area at a time, in dependency order, with type-checked references
into the source.
