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

/-! ## Character facts -/

/-- The two parentheses are distinct characters. -/
theorem open_ne_close : ('(' : Char) ≠ ')' := by decide

/-- An opening parenthesis is not whitespace, so the whitespace skip
stops at the head of a parenthesized spelling. -/
theorem open_not_ws : isWs '(' = false := by decide

/-- A closing parenthesis is not whitespace, so the whitespace skip
stops at a child block's terminator. -/
theorem close_not_ws : isWs ')' = false := by decide

/-- A space is whitespace, so the whitespace skip consumes the separator
the printer emits before each child. -/
theorem space_is_ws : isWs ' ' = true := by decide

/-! ## The decimal layer -/

/-- A printed numeral reads back whole, and leaves exactly what followed
it. The delimiting hypothesis on the remainder is what a
non-parenthesizing spelling of a childless node costs; it is the same
condition `Csexp.readDigits_append` carries. -/
theorem readNat_append (n : Nat) (rest : List Char)
    (h : ∀ c cs, rest = c :: cs → Csexp.charDigit c = none) :
    Csexp.readNat (Csexp.decOf n ++ rest) = some (n, rest) := by
  unfold Csexp.readNat
  rw [Csexp.readDigits_append _ _ (Csexp.decOf_all_digits n) h]
  simp [Csexp.decOf_ne_nil n, Csexp.digitsVal_decOf, List.isEmpty_iff]

/-- A digit is not whitespace. The conclusion is `isWs c = false` rather
than a disequality because the whitespace class has four members. -/
theorem digit_not_ws {c : Char} (h : (Csexp.charDigit c).isSome) :
    isWs c = false := by
  unfold isWs
  have h1 : ¬ c = ' ' := by rintro rfl; exact absurd h (by decide)
  have h2 : ¬ c = '\t' := by rintro rfl; exact absurd h (by decide)
  have h3 : ¬ c = '\r' := by rintro rfl; exact absurd h (by decide)
  have h4 : ¬ c = '\n' := by rintro rfl; exact absurd h (by decide)
  simp [h1, h2, h3, h4]

/-- A digit is not an opening parenthesis. -/
theorem digit_not_open {c : Char} (h : (Csexp.charDigit c).isSome) :
    c ≠ '(' := by
  rintro rfl
  exact absurd h (by decide)

/-- A digit is not a closing parenthesis. -/
theorem digit_not_close {c : Char} (h : (Csexp.charDigit c).isSome) :
    c ≠ ')' := by
  rintro rfl
  exact absurd h (by decide)

/-- `Csexp.decOf_ne_nil` in the form its consumers use: a shortest-form
decimal has a head. -/
theorem decOf_eq_cons (n : Nat) : ∃ c cs, Csexp.decOf n = c :: cs :=
  List.exists_cons_of_ne_nil (Csexp.decOf_ne_nil n)

/-- The head of a shortest-form decimal is a digit. -/
theorem decOf_head_digit (n : Nat) :
    ∀ c cs, Csexp.decOf n = c :: cs → (Csexp.charDigit c).isSome := by
  intro c cs hc
  refine Csexp.decOf_all_digits n c ?_
  rw [hc]
  simp

/-- A numeral is already stripped: the whitespace skip is the identity on
a printed decimal and whatever follows it. -/
theorem skipWs_decOf_append (n : Nat) (rest : List Char) :
    skipWs (Csexp.decOf n ++ rest) = Csexp.decOf n ++ rest := by
  obtain ⟨c, cs, hc⟩ := decOf_eq_cons n
  rw [hc, List.cons_append, skipWs_cons,
    if_neg (by simp [digit_not_ws (decOf_head_digit n c cs hc)])]

/-! ## The head of a spelling -/

/-- Every spelling begins with an opening parenthesis or with a digit,
according to whether the node has children. This is the readable
counterpart of `Rose.exists_print_eq_cons`, which has only the
parenthesized case. -/
theorem print_head {k : Nat} (r : Rose k) :
    ∃ c cs, print r = c :: cs ∧ (c = '(' ∨ (Csexp.charDigit c).isSome) := by
  obtain ⟨⟨i, n⟩, f⟩ := r
  cases n with
  | zero =>
    obtain ⟨c, cs, hc⟩ := decOf_eq_cons i.val
    exact ⟨c, cs, (print_zero i f).trans hc, Or.inr (decOf_head_digit i.val c cs hc)⟩
  | succ n => exact ⟨'(', _, print_succ i f, Or.inl rfl⟩

/-- A spelling is already stripped: neither possible head is whitespace,
so the skip is the identity on a spelling followed by anything. -/
theorem skipWs_print_append {k : Nat} (r : Rose k) (rest : List Char) :
    skipWs (print r ++ rest) = print r ++ rest := by
  obtain ⟨c, cs, hc, hd⟩ := print_head r
  have hw : isWs c = false := by
    rcases hd with rfl | hd
    · exact open_not_ws
    · exact digit_not_ws hd
  rw [hc, List.cons_append, skipWs_cons, if_neg (by simp [hw])]

/-- The `rest = []` instance of `skipWs_print_append`, which is the form
the entry point uses. -/
theorem skipWs_print {k : Nat} (r : Rose k) : skipWs (print r) = print r := by
  have h := skipWs_print_append r []
  rwa [List.append_nil] at h

/-- A child block with its terminator never begins with a digit: it
begins with the terminator when empty and with a separating space
otherwise. Stating it over the terminated block is what makes the empty
case true. -/
theorem block_append_head_not_digit {k : Nat} (ts : List (Rose k))
    (rest : List Char) :
    ∀ c cs, (ts.map (fun t ↦ ' ' :: print t)).flatten ++ ')' :: rest
        = c :: cs → Csexp.charDigit c = none := by
  intro c cs h
  cases ts with
  | nil =>
    simp only [List.map_nil, List.flatten_nil, List.nil_append] at h
    injection h with h1 _
    subst h1
    decide
  | cons t ts =>
    simp only [List.map_cons, List.flatten_cons, List.cons_append] at h
    injection h with h1 _
    subst h1
    decide

end Rsexp
end Geb
