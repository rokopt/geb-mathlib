/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.ReadableSExpr  -- shake: keep; #guard needs it
public meta import Geb.Prototypes.ReadableSExpr  -- shake: keep; #guard needs it
public import GebTests.Prototypes.ConcreteSyntax  -- shake: keep; #guard needs it
public meta import GebTests.Prototypes.ConcreteSyntax  -- shake: keep; #guard needs it
public import Mathlib.Data.Fin.VecNotation

/-!
# Tests for the readable rose-tree spelling

`Rsexp.parse_print` constrains the parser only on the printer's output, so
every rejection path is unexercised by it, and no theorem evaluates
`Rsexp.print`'s spelling — the `@[simp]` lemmas `Rsexp.print_zero` and
`Rsexp.print_succ` pin it only up to unfolding. The assertions below check
the printer's spelling at a concrete tree; evaluate the round trip
`Rsexp.parse_print` states but does not run; evaluate the `Ast` composites
`Rsexp.printViaRose` and `Rsexp.parseViaRose` at `sampleAst`, reused from
`GebTests.Prototypes.ConcreteSyntax`, whose round trip
`Rsexp.parseViaRose_printViaRose` states but does not run; exercise three
families of input the parser admits but the printer never emits —
whitespace variants, a parenthesized childless node, and the decimal
layer's laxity on leading zeros, including the reinterpretation of a
parenthesized single-child node `(0 1)` as the childless node `1`;
evaluate the formatter `Geb.format` at this syntax, which
`Rsexp.format_idem` states idempotent without running it; and exercise
the rejection paths, including the two distinct routes to `none` at
empty and at whitespace-only input.

Inputs are `List Char`; core's `String.toList` depends on
`Classical.choice`, which
[CONTRIBUTING.md § Constructive-only](../../CONTRIBUTING.md) requires be
minimised. `String.ofList` is choice-free and is used to compare printed
output against a string literal. A `#guard` is not a declaration, so
`GebMeta.detectNonstandardAxiom` would not catch a leak there.

## Main definitions

* `sampleRose` — the tree the assertions run on: a node of six children,
  the third itself a node.

## Tags

concrete syntax, s-expression, parser, retraction, rose tree, test
-/

@[expose] public section

open Geb

/-- A node of six children, third of them itself a node. -/
def sampleRose : Rose 8 :=
  Rose.node 0 ![Rose.node 1 ![], Rose.node 2 ![],
    Rose.node 3 ![Rose.node 4 ![]], Rose.node 5 ![], Rose.node 6 ![],
    Rose.node 7 ![]]

/-! ## The printer's spelling, which no theorem evaluates -/

#guard String.ofList (Rsexp.print sampleRose) == "(0 1 2 (3 4) 5 6 7)"

/-! ## The round trip, evaluated -/

#guard Rsexp.parse 8 (Rsexp.print sampleRose) == some sampleRose

/-! ## The `Ast` composites, evaluated

`Rsexp.printViaRose` and `Rsexp.parseViaRose` compose `Rsexp.print` and
`Rsexp.parse` with the rose bijection; `Rsexp.parseViaRose_printViaRose`
states their round trip but does not run it. `sampleAst` is reused from
`GebTests.Prototypes.ConcreteSyntax`, so the spelling can be compared
against the one that module pins for the same tree. -/

#guard String.ofList (Rsexp.printViaRose sampleAst) == "(0 (1 2))"
#guard Rsexp.parseViaRose 3 (Rsexp.printViaRose sampleAst) == some sampleAst

/-! ## Inputs the parser accepts but the printer never emits -/

-- pin that each compared input parses: every assertion below is an
-- equality of two `parse` calls, which two `none`s would satisfy
#guard (Rsexp.parse 8 ['(', '0', ' ', '1', ')']).isSome

-- whitespace variants the printer never emits
#guard Rsexp.parse 8 ['(', '0', ' ', ' ', '1', ')'] == Rsexp.parse 8 ['(', '0', ' ', '1', ')']
#guard Rsexp.parse 8 ['(', '0', ' ', '1', ' ', ')'] == Rsexp.parse 8 ['(', '0', ' ', '1', ')']
#guard Rsexp.parse 8 ['(', '0', '\t', '1', '\r', ')'] == Rsexp.parse 8 ['(', '0', ' ', '1', ')']
#guard (Rsexp.parse 8 ['(', '0', ' ', '(', '1', ')', ')']).isSome
#guard Rsexp.parse 8 ['(', '0', '(', '1', ')', ')']
    == Rsexp.parse 8 ['(', '0', ' ', '(', '1', ')', ')']
#guard Rsexp.parse 8 ['(', ' ', '0', ' ', '1', ' ', ')'] == Rsexp.parse 8 ['(', '0', ' ', '1', ')']
#guard Rsexp.parse 8 [' ', '(', '0', ' ', '1', ')', '\n'] == Rsexp.parse 8 ['(', '0', ' ', '1', ')']

-- a parenthesized childless node
#guard (Rsexp.parse 8 ['6']).isSome
#guard Rsexp.parse 8 ['(', '6', ')'] == Rsexp.parse 8 ['6']

-- leading zeros, which `Csexp.digitsVal` already accepts
#guard (Rsexp.parse 8 ['7']).isSome
#guard Rsexp.parse 8 ['0', '0', '7'] == Rsexp.parse 8 ['7']

-- `(01)` is a reinterpretation, not a rejection: the childless node 1
#guard (Rsexp.parse 8 ['1']).isSome
#guard Rsexp.parse 8 ['(', '0', '1', ')'] == Rsexp.parse 8 ['1']

/-! ## The formatter

`Geb.format` returns an `Option (List Char)`; the rewrite is checked as an
equality of `Option String`, mapping `String.ofList` over the result. The
input parenthesizes the sixth child, `(6)`, where the printer would write
the bare numeral `6`; `Rsexp.format_idem` states the result is a fixed
point without running it. -/

#guard (format (Rsexp.parse 8) Rsexp.print
    ['(', '0', ' ', '1', ' ', '2', ' ', '(', '3', ' ', '4', ')', ' ', '5',
      ' ', '(', '6', ')', ' ', '7', ')']).map String.ofList
    == some "(0 1 2 (3 4) 5 6 7)"

/-! ## Rejection paths -/

#guard Rsexp.parse 8 ['(', '0', ' ', '1'] == none          -- unterminated
#guard Rsexp.parse 3 ['9'] == none                          -- label ≥ k
#guard Rsexp.parse 8 [')'] == none                          -- unopened
#guard Rsexp.parse 8 ['0', ' ', 'x'] == none                -- trailing input
#guard Rsexp.parse 8 ['(', ')'] == none                     -- no head numeral
#guard Rsexp.parse 8 ['(', '(', ')', ')'] == none           -- no head numeral
#guard Rsexp.parse 8 ([] : List Char) == none               -- entry at zero fuel
#guard Rsexp.parse 8 [' ', ' '] == none                     -- empty-input branch

-- The last two are distinct paths: empty input exercises the entry point
-- at zero fuel, whitespace-only input reaches `parseStep`'s empty-input
-- branch at positive fuel.
