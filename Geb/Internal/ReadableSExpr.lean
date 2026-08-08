/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.ConcreteSyntax

/-!
# A readable spelling of the rose syntax

`Geb.Csexp.print` and `Geb.Ast.printViaRose` are both [RFC9804]
canonical: length-prefixed and whitespace-free, so neither has a
readable form. This module spells the same `Rose k` as parenthesized
text, a node's label followed by its children, so that
`fork (leaf 0) (fork (leaf 1) (leaf 2))` reads as `(0 (1 2))`.

The fragment lies inside [R7RS] `<datum>`: a reader conforming to that
grammar accepts it without new code, and tools operating on
parenthesized text apply to it directly. Labels are decimal numerals,
which the [RFC9804] advanced form cannot spell as tokens — § 4.3
requires a token not begin with a digit — where [R7RS] and [EDN] read a
digit-initial token as a number.

## Main definitions

* `Rsexp.print` — the readable spelling of a `Rose k`.
* `Rsexp.parse` — the parser matching it, built from `Rsexp.parseStep`,
  `Rsexp.parseAux` and the shared `Rose.parseChildren`.
* `Rsexp.skipWs` — the whitespace skip the stripping discipline runs.
* `Rsexp.printViaRose`, `Rsexp.parseViaRose` — the composites with the
  rose bijection, spelling an `Ast k`.

## Main statements

* `Rsexp.parse_print`, `Rsexp.parseViaRose_printViaRose` — the
  retraction law, on `Rose` and on `Ast`, with `Rsexp.format_idem` and
  `Rsexp.print_injective` instantiating the generic corollaries.

## Implementation notes

The parser strips whitespace on return rather than on entry:
`parseStep` is called on stripped input and returns a stripped
remainder. That discipline is what lets `Rose.parseChildren` be reused
verbatim — the loop tests its input's head against `')'` immediately,
so it must be called on already-stripped input — and what lets `parse`
match `some (r, [])` syntactically rather than testing a remainder for
whitespace.

A childless node prints as a bare numeral, so a printed tree can end in
a digit and `parseAux_print` carries a delimiting side condition on the
caller's remainder. Always parenthesizing would remove the obligation
and the spelling; `Csexp.readDigits_append` carries the same condition
for the same reason.

## References

* [R7RS] §§ 4.1.3, 7.1.1, 7.1.2 — the datum grammar this fragment lies
  inside.
* [EDN] — the second readable format the spelling agrees with.
* [RFC9804] §§ 4.3, 6, 8 — the token rule that rules out the advanced
  form, and the conformance of declining it.
* [RFC8259] § 2 — the `ws` production this whitespace class matches.

## Tags

concrete syntax, s-expression, parser, retraction, rose tree
-/

@[expose] public section

namespace Geb
namespace Rsexp

/-! ## Whitespace -/

/-- The whitespace class this syntax admits: space, horizontal tab,
carriage return and line feed. It is a subset of the class [R7RS]
§ 7.1.1 fixes, and admits the same four characters as [RFC8259]
§ 2's `ws`. -/
def isWs (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\r' || c = '\n'

/-- Drop a leading run of whitespace. Carried by `List.rec` rather than
by structural recursion, per the recursor rule. -/
def skipWs : List Char → List Char :=
  List.rec [] fun c cs ih ↦ if isWs c then ih else c :: cs

@[simp] theorem skipWs_nil : skipWs [] = [] := rfl

theorem skipWs_cons (c : Char) (cs : List Char) :
    skipWs (c :: cs) = if isWs c then skipWs cs else c :: cs := rfl

/-! ## Printer -/

/-- The readable spelling: a childless node is its label, a node with
children is its label and their spellings, parenthesized and each
preceded by one space. The uniform space is what makes every element of
the child block a cons, which the arity bound and the whitespace skip
both use. -/
def print {k : Nat} : Rose k → List Char :=
  WType.elim (List Char) fun x ↦
    match x with
    | ⟨(i, 0), _⟩ => Csexp.decOf i.val
    | ⟨(i, _ + 1), ch⟩ =>
      '(' :: (Csexp.decOf i.val
        ++ (((List.ofFn ch).map (fun s ↦ ' ' :: s)).flatten ++ [')']))

@[simp] theorem print_zero {k : Nat} (i : Fin k) (f : Fin 0 → Rose k) :
    print (Rose.node i f) = Csexp.decOf i.val := rfl

theorem print_succ {k n : Nat} (i : Fin k) (f : Fin (n + 1) → Rose k) :
    print (Rose.node i f)
      = '(' :: (Csexp.decOf i.val
          ++ (((List.ofFn f).map (fun t ↦ ' ' :: print t)).flatten
              ++ [')'])) := by
  unfold print Rose.node
  rw [WType.elim_mk]
  simp only []
  rw [List.map_ofFn, List.map_ofFn]
  rfl

end Rsexp
end Geb
