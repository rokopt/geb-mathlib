# Readable S-expressions for the rose syntax

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Status](#status)
- [Problem](#problem)
- [Roadmap position](#roadmap-position)
- [Survey of readable S-expression formats](#survey-of-readable-s-expression-formats)
  - [How far the formats agree](#how-far-the-formats-agree)
  - [Why not the RFC 9804 advanced form](#why-not-the-rfc-9804-advanced-form)
  - [Why not sexplib's grammar](#why-not-sexplibs-grammar)
- [The syntax](#the-syntax)
  - [Shape](#shape)
  - [Grammar](#grammar)
  - [Printer](#printer)
  - [Where the decoder is laxer than the printer](#where-the-decoder-is-laxer-than-the-printer)
- [Proof obligations](#proof-obligations)
  - [The delimiting hypothesis cannot be dropped](#the-delimiting-hypothesis-cannot-be-dropped)
  - [What the decimal layer supplies](#what-the-decimal-layer-supplies)
  - [The child loop is reused](#the-child-loop-is-reused)
  - [Alternatives considered](#alternatives-considered)
- [Lean shape](#lean-shape)
- [Persistent documentation](#persistent-documentation)
- [Deferred](#deferred)
- [Recorded consequences](#recorded-consequences)
- [References](#references)

<!-- END doctoc -->

## Status

Design agreed; not implemented. Transient per
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape: this
file is removed in the final commits of the topic branch.

## Problem

The bare tree already has two canonical spellings, both proved.
`Geb.Csexp.print` spells the tree `fork (leaf 0) (fork (leaf 1) (leaf
2))` from `Ast` directly as
`(4:fork(4:leaf1:0)(4:fork(4:leaf1:1)(4:leaf1:2)))`, and
`Geb.Ast.printViaRose` spells it through the rose bijection as
`(1:0(1:1(1:2)))`; `GebTests/Internal/CanonicalSExpr.lean` pins both
and asserts they differ. Both are [RFC9804] canonical: length-prefixed
and whitespace-free by construction, so neither has a readable form.

The readable fragment specified below lies inside [R7RS] `<datum>`,
so a reader conforming to that grammar accepts it without new code,
and tools that operate on parenthesized text rather than through a
library binding — paredit, parinfer — apply to it directly. The
library side is current: `janestreet/sexplib` and `janestreet/sexp`
were last pushed 2026-07-10 under MIT, where `zv/sexpr` was last
pushed 2017-05-31.
§ Canonical S-expressions (RFC 9804) of
[docs/concrete-syntaxes.md](../../concrete-syntaxes.md) records that
the canonical encoding's ecosystem is instead "concentrated in the
SPKI/PGP niche".

§ The bootstrap set states a condition for this work, in its switch
thresholds:

> Add the csexp advanced form ahead of both if the textual form is
> read and written by hand often enough for the canonical form's
> unreadability to cost more than the second parser.

That condition is quantitative, and no count has been taken against
it.

This stage is therefore scheduled ahead of any measured need, on the
ground that the readable form is intended to become the form in which
trees are written and the canonical form cannot become that; waiting
for the frequency to be measurable would mean accumulating
hand-written trees in the bootstrap syntax, which § Canonical
S-expressions (RFC 9804) records as "designed for hashing and
signing". That is an
argument from anticipated use, not from the threshold, and the
threshold is recorded as the condition it is: this spec does not claim
to have met it.

The grammar adopted also differs from the one the threshold names, for
the reason in § Why not the RFC 9804 advanced form.

## Roadmap position

This is stage 1a′, inserted before stage 1b, which it delays but does
not remove.

§ The bootstrap set of
[docs/concrete-syntaxes.md](../../concrete-syntaxes.md) fixes
data-model diversity as the purpose of
writing more than one syntax, and this stage supplies no new data
model for the abstract syntax: it is one `Rose k` spelled twice. (Its
host model does differ from csexp's, which § Why not the RFC 9804
advanced form sets out — but that difference yields a spelling,
not
a second model to test the architecture against.) It therefore does
not validate syntax independence and does not discharge stage 1b; the
JSON core profile still carries that obligation. What it validates
is a different property, that one abstract syntax supports two
spellings differing in readability and in available tooling,
and it is scheduled on that ground alone.

§ Roadmap's stage table gains a row between 1a and 1b, taking the
`next` status that 1b holds, which becomes `after 1a′`:

| Stage | Content | Status |
| --- | --- | --- |
| 1a′ | readable S-expressions, bare tree, retraction proved | next |

## Survey of readable S-expression formats

Three tiers, distinguished by what there is to cite against.

**Specified independently of an implementation.** None of the three is
on a standards track. [RFC9804] is Informational on the IETF stream.
[R7RS] is not itself a standards-body document: it issues from the
Scheme Steering Committee's process and grants free copying, while its
ancestor R4RS "became the basis for the IEEE Standard for the Scheme
Programming Language in 1991". [EDN] carries productions for integers
and floating-point numbers and specifies the rest in prose, describing
itself as "casual, as we gather feedback from implementors. A more
rigorous e.g. BNF will follow". [R7RS] § 7.1.2 gives the `<datum>`
grammar as
`<simple datum> | <compound datum> | <label> = <datum> | <label> #`,
the last two being the notation for shared and circular structure;
`<list>` is `(<datum>*)` or `(<datum>+ . <datum>)`, and
`<simple datum>` covers booleans, numbers, characters, strings,
symbols and bytevectors. [EDN] specifies lists as "zero or more
elements enclosed in parentheses" and integers as an optional sign
followed by a digit, or by a nonzero digit and further digits — the
production that enforces its no-leading-zeros rule. [RFC9804] § 7.1
gives the advanced-form ABNF; its
status is Informational, § 6 marks the advanced representation
OPTIONAL against a mandatory canonical and basic transport, and § 8
provides for restricted profiles, its list opening with "no advanced
representations (only canonical and basic)".

**Implementation as specification.** Jane Street's `sexplib` has no
specification independent of its implementation: its `README.org`
carries sections headed "Lexical conventions of s-expression",
"Comments" and "Grammar of s-expressions". Those three state the
syntax, deferring string escapes to OCaml's own conventions rather
than stating them; § Examples exhibits the result. The data model is
`Sexp.t`, which the README writes
`type sexp = Atom of string | List of sexp list`.
Its atom rule, per § Lexical conventions of s-expression, is that
"[a]ll characters other than double quotes, left and right
parentheses, whitespace, carriage return, and comment-introducing
characters or sequences (see next paragraph) are considered part of a
contiguous string"; the same section gives its whitespace as "the
space, newline, horizontal tab, and form feed characters". Quoting
follows OCaml's string conventions. Real World OCaml describes the
format without claiming standardization for it. The
`query_semantics.md` document in `janestreet/sexp` is a
denotational semantics for a query language over S-expressions, not a
grammar for the syntax.

**Not formats.** parinfer and paredit are editor behaviours; the
paredit distribution is `paredit.el` and `paredit-beta.el`, for Emacs.
parinfer has two modes: Indent Mode infers close-parens from
indentation, Paren Mode infers indentation from parens. Its stated
properties are stated as desiderata — "We wish to define properties
that each Parinfer mode should exhibit" — and are that Paren Mode
should never change the AST (`R(x) = R(y)`) and should be idempotent,
that Indent Mode should be idempotent and should never change the
result of Paren Mode, and — the one stated at full strength, and the
one that constrains use here — that Indent Mode "may change the AST
(by design)". The page adds that "Formal descriptions of the actual
operations performed by the modes are pending, but informal ones
follow in their
respective sections below". The page also states that
"single-line files are okay".
`zv/sexpr` is a Rust parser whose README says it "can be configured to
read almost any s-expression variant including" Standard, Advanced and
Canonical formats, and names option paths under a `ParseConfig`. That
type name appears in the README only, not in the crate source. It is
evidence that one engine can serve canonical and readable forms, and
no more: it ships no licence file, its
`Cargo.toml` declaring `MIT/Apache-2.0`, and its README's list of
predefined configurations does not match its own configuration table,
so which ones exist was not established.

### How far the formats agree

On the spellings this printer emits, [R7RS], [EDN] and `sexplib`
denote the same tree shape: `(0 1 2 (3 4) 5 6 7)` reads as one list of
seven elements, the fourth itself a list, under all three.

The parser accepts more than the printer emits, and three
disagreements concern constructs this grammar must either accept or
reject, recorded rather than elided:

- Leading zeros. [R7RS] `<uinteger R> → <digit R>+` admits `007` and
  reads it as 7; [EDN] forbids it, "No integer other than 0 may begin
  with 0". § Where the decoder is laxer than the printer states which
  side this grammar takes.
- Commas. [EDN] counts `,` as whitespace — "Commas `,` are also
  considered whitespace, other than within strings" — so `(0, 1, 2)`
  is idiomatic EDN that this grammar rejects.
- Which characters are whitespace. `sexplib` counts form feed where
  [R7RS] does not, so `(0\f1)` is two elements under `sexplib` and
  unreadable under [R7RS]; [R7RS]'s `<line ending>` admits a bare
  return, where `sexplib`'s lexer accepts it neither as whitespace nor
  inside an atom and fails outright. § Grammar states which side this
  grammar takes.

The remaining disagreements concern constructs the bare tree does not
use: string escaping, numeric towers beyond non-negative integers,
dotted pairs, vector syntax, quotation abbreviations, comments,
keywords, and the datum labels in the `<datum>` production above.

### Why not the RFC 9804 advanced form

[RFC9804] § 4.3 requires that an octet-string given directly as a
token "does not begin with a digit", the leading digit being reserved
for a length prefix. Every label in the bare tree is a decimal
numeral, so the advanced form cannot spell one as a token: labels
would be written `"0"` or `1:0`.

The cause is the data-model thinness that § The bootstrap set credits
the canonical encoding for. [R7RS] and [EDN] also forbid a digit
initial in their unquoted identifier syntax — R7RS admits `|0|` as a
symbol under the vertical-line notation — and are unaffected because
a bare digit-initial token reads as a number instead. [RFC9804]'s
model is octet-strings only, so it has no number datum to read one as,
and must reject.

§ Canonical S-expressions (RFC 9804) records the same rule
constraining that document too: it lists two "consequences
constrain[ing] how the examples may be written", the second being
that "`(leaf 0)` is ill-formed" and
that labels "must be written as quoted strings `(leaf "0")` or
verbatim atoms `(leaf 1:0)`".

Declining the advanced form is conformant rather than a deviation:
§ 6 makes it OPTIONAL, and § 8 lists "no advanced representations
(only canonical and basic)" as a restriction an application may adopt.

### Why not sexplib's grammar

`sexplib` already reads this grammar's output: digits are ordinary
atom characters under the rule quoted above, so `(0 1 2 (3 4) 5 6 7)`
is a well-formed `sexp` and the Jane Street `sexp` query tool applies
to it as printed. What adopting `sexplib`'s atom rule in full would
buy is acceptance of its full atom syntax on input as well.

That is not adopted now on two grounds. There is no specification of
it independent of the implementation, so there is nothing to
transcribe against; and OCaml-style quoting and escaping is proof work
that the bare tree has no use for, since its atoms are `[0-9]+`
throughout. Adopting it later widens the atom production rather than
replacing the grammar.

## The syntax

### Shape

A rose node is spelled as its label followed by its children. A node
with no children is spelled as the bare label; a node with children is
parenthesized. Writing the sample of six children:

```text
(0 1 2 (3 4) 5 6 7)
```

This is the node labelled `0` with six children: the childless nodes
`1`, `2`, `5`, `6` and `7`, and, third among the six, the node
labelled `3` with the single childless child `4`.

`leaf` and `fork` do not appear. They name the constructors of the
binary presentation, and the rose presentation has neither: a label
standing alone is a constant and a parenthesized list is an
application. § Applicative-calculus reading of
[docs/concrete-syntaxes.md](../../concrete-syntaxes.md) states the
correspondence this rests on, that `μX. (k + X²)` is the raw term
syntax of an untyped applicative combinator calculus with `k`
constants, in which
"leaves are the constants and each internal node is an application".

The spelling coincides with [R7RS] and [EDN] datum syntax, and the
head-first reading with [R7RS] § 4.1.3, where "[a] procedure call is
written by enclosing in parentheses an expression for the procedure to
be called followed by expressions for the arguments to be passed to
it". [EDN] supplies no evaluation semantics and gives a list's first
element no special role — "edn is a system for the conveyance of
values. It is not a type system, and has no schemas" — so the
agreement with it is over spelling only.

### Grammar

The grammar is two-level, because what separates two adjacent numerals
is a lexical property and not a phrase production.

Lexical layer: a `numeral` is a maximal run of `DIGIT`. This is the
whole of the separation requirement. It is why `(0 1)` is the node `0`
with one child `1` while `(01)` is the childless node `1`, and why no
phrase production below mentions mandatory whitespace.

Phrase layer:

```abnf
document = *ws tree *ws
tree     = numeral / list
list     = "(" *ws numeral *( *ws tree ) *ws ")"
ws       = SP / HTAB / CR / LF
```

Whitespace is optional everywhere at this layer, which is [R7RS]'s and
[EDN]'s rule: `(` and `)` are themselves delimiters there, so `(0(1))`
and `(0 (1))` are both well-formed and denote the same tree.

`document` admits surrounding whitespace so that a file with a leading
indent or a trailing newline parses.

This whitespace class is a subset of [R7RS]'s, whose `<line ending>`
includes a bare return. It is not a subset of `sexplib`'s, which by
its § Lexical conventions of s-expression excludes carriage return and
includes form feed.

### Printer

By `WType.elim` over `Rose k`, writing `decOf` for the shortest
decimal spelling that
[Geb/Internal/ConcreteSyntax.lean](../../../Geb/Internal/ConcreteSyntax.lean)
already defines. The recursor supplies the children as a function
`ch : Rose.Arity (i, n) → List Char`, so the clause reads over
`List.ofFn ch`:

```text
node i ch, n = 0  ↦  decOf i.val
node i ch, n > 0  ↦  '(' :: (decOf i.val
                       ++ (((List.ofFn ch).map (fun s ↦ ' ' :: s)).flatten
                           ++ [')']))
```

A single space precedes every child, including one that is itself
parenthesized. What the uniformity yields is that every element of the
flattened block is a cons by construction, which is what § What the
decimal layer supplies uses for the arity bound and what the
whitespace skip steps past; a printer suppressing the space before a
parenthesized child would need a case split per child at both sites.

The arity-zero spelling equation holds by `rfl`. The other does not,
in the form the retraction proof consumes. `WType.elim` hands the step
function the children already recursed, so the clause yields
`List.ofFn (fun j ↦ print (ch j))`, while `parseChildren_print` is
stated over a `List (Rose k)` and so needs the block as
`(List.ofFn ch).map (fun t ↦ ' ' :: print t)`. Those are not
definitionally equal; the connecting lemma is core's `List.map_ofFn`,
needed on both sides — the `WType.elim` side and the `List (Rose k)` side — so
the second equation is a `rfl` step, an `if_neg` discharging the arity
split, two rewrites, and a closing `rfl`.

### Where the decoder is laxer than the printer

Three families the parser accepts and the printer never emits:

- Whitespace variants. Every optional `*ws` in the grammar above is a
  spelling the printer does not produce: `(0  1)`, `(0 1 )`, `(0(1))`,
  `( 0 1 )`, and any leading or trailing whitespace on the document.
  This is the largest of the three families and the one the tests
  exercise most.
- A childless node parenthesized: `(6)` and `6` denote the same tree,
  and the printer emits `6`.
- A numeral with leading zeros, which `Csexp.digitsVal` already
  accepts. This follows [R7RS] rather than [EDN], which rejects them.

The divergence runs the other way once: `numeral` above is any maximal
digit run, while the parser rejects a label at or above `k`, since a
`Rose k` has no such node. So `9` parses at `k = 10` and not at
`k = 3`. That is the one respect in which the parser accepts less than
§ Grammar describes, and it is a property of the alphabet rather than
of the syntax.

All three are legitimate under the retraction law, which constrains
only the composite. § Canonical S-expressions (RFC 9804) records the
same asymmetry for the canonical encoding and the same justification.
Injectivity of `print` is unaffected either way: it is derived from
the retraction by the existing `Geb.print_injective`, exactly as
`Geb.Rose.print_injective` derives it.

The composite that rewrites `( 6 )` to `6` and `007` to `7` is
`Geb.format`, defined in
[Geb/Internal/ConcreteSyntax.lean](../../../Geb/Internal/ConcreteSyntax.lean)
as `(parse c).map print`. `Geb.format_idem` states that its output is
a fixed point.

## Proof obligations

The parser has three layers beneath its entry point. Two of them
recurse through `Nat.rec` on the fuel — `parseChildren` and `parseAux`
— and `parseStep` performs no recursion at all, being a case analysis
on its input, as `Geb.Rose.parseStep` is. No definition calls itself.
There is also a whitespace skip. `skipWs` recurses on its
input rather than on fuel, and is carried by a recursor as
§ Recursion and induction through recursors of
[docs/rules/lean-coding.md](../../rules/lean-coding.md) requires;
`List.rec` here.

- `parseChildren` — `Geb.Rose.parseChildren`, reused unchanged. See
  § The child loop is reused.
- `parseStep` — one layer of recursive descent, and the layer that
  maintains the stripping invariant. A tree is either a bare numeral
  or a parenthesized list, so this branches on whether the first
  character is `(`. It strips at four sites: after `(`, after the
  label in each of the two branches, and after the child list. The
  strip after the parenthesized branch's label is the one the grammar
  makes least obvious and the one whose omission breaks the retraction —
  `Rose.parseChildren` tests its input's head against `')'`
  immediately, so it must be called on `skipWs cs1`, or `(0 1 2)`
  fails at its first child. The canonical form has neither the branch
  nor the strips.
- `parseAux` — `Nat.rec` over the fuel, undecremented as the child
  loop's bound and decremented as the child parser's fuel, as in
  `Geb.Rose.parseAux`.
- `parse` — the entry point, carrying no recursion of its own:
  `parseAux k cs.length (skipWs cs)`, matched as `Geb.Rose.parse`
  matches it, `some (r, []) ↦ some r`. The leading strip and the
  invariant together are the `document` production; without them a
  file with a leading indent or a trailing newline is rejected. The
  fuel is `cs.length` by construction, so at `parse_print` it is
  `(print r).length`. Separately, `skipWs (print r) = print r`, which
  is what makes the input `parseAux` receives equal `print r`.

The printer branches too, on whether the arity is zero, where
`Geb.Rose.print_node` is uniform. Both the spelling equations and the
retraction proof therefore acquire a case split the canonical
development does not have. The childless branch needs
`Rose.node ⟨i.val, h⟩ Fin.elim0 = Rose.node i ch` for
`ch : Fin 0 → Rose k` if `parseStep` builds the node directly, which
is `congrArg (Rose.node i) (funext fun j ↦ j.elim0)`; or
`Rose.ofList i [] = Rose.node i ch`, by `List.ofFn_zero` and then
`Geb.Rose.ofList_ofFn`, if it builds through `ofList` for uniformity
with the list branch. The plan picks one; the second is not a
requirement of the design.

### The delimiting hypothesis cannot be dropped

The canonical form's atoms are self-delimiting: a length prefix says
where each ends, which is why `Csexp.readVerbatim_append` holds for
every atom with no hypothesis on what follows. A readable numeral is
delimited only by the next character not being a digit, and
`readDigits` takes the longest decimal prefix, so the retraction lemma
is false without that hypothesis. At `k = 100`,
`r = Rose.node 5 ![]` and `rest = ['5']`, the printed form is `"5"`,
the input is `"55"`, and the parser returns the node `55` having
consumed the remainder.

So the analogue of `Geb.Rose.parseAux_print` carries the side
condition. It is not optional for a parser that reads characters; a
lexical pre-pass would confine it elsewhere, which § Alternatives
considered records.

The conclusion also has to account for the stripping discipline. On
`print r ++ rest` the last thing `parseStep` does is strip, so what it
returns is `skipWs rest`, not `rest`:

```lean
theorem parseAux_print {k : Nat} (r : Rose k) :
    ∀ (f : Nat) (rest : List Char), (print r).length ≤ f →
      (∀ c cs, rest = c :: cs → charDigit c = none) →
      parseAux k f (print r ++ rest) = some (r, skipWs rest)
```

Writing `some (r, rest)` here is false, and the delimiting hypothesis
does not save it: at `k = 10`, `r = Rose.node 5 ![]` and
`rest = [' ']`, the space is not a digit, `print r` is `"5"`, and
`parseAux 10 1 "5 "` returns `some (r, [])`.

The `parseChildren_print` analogue changes in two ways. Its
`childParse` premise gains the delimiting hypothesis and returns
`skipWs r`. Its own input is skipped, since `parseStep` strips the
printer's leading space before calling the loop — but its conclusion
is `rest` rather than `skipWs rest`, because the loop returns what
follows the closing parenthesis without stripping it.

The delimiting hypothesis has three discharge sites, not two:

- A child, followed by `' '` or by `')'`.
- The node's own label in the parenthesized branch, followed by `' '`
  at arity `≥ 1`.
- `parse_print`, which instantiates `rest = []`, where the hypothesis
  is vacuous and `skipWs [] = []`.

The hypothesis is a cost of the spelling § Shape fixes, and the
direction of that implication is worth stating precisely. A printer
that always parenthesized would emit strings opening with `(` and
closing with `)`, so no
printed numeral could abut the caller's remainder and `parseAux_print`
would need no side condition at all. Printing a childless node as a
bare numeral is what exposes a numeral at the end of a printed tree,
and so what creates the obligation. The case split does not discharge
it — `')'` is a non-digit exactly as `' '` is — it is what makes it
necessary.

### What the decimal layer supplies

`Csexp.readDigits_append` is stated with exactly that hypothesis at
[Geb/Internal/ConcreteSyntax.lean](../../../Geb/Internal/ConcreteSyntax.lean):

```lean
theorem readDigits_append : ∀ ds rest : List Char,
    (∀ c ∈ ds, (charDigit c).isSome) →
    (∀ c cs, rest = c :: cs → charDigit c = none) →
    readDigits (ds ++ rest) = (ds, rest)
```

`decOf`, `digitsVal`, `readDigits` and `digitsVal_decOf` are taken
unchanged. One lemma is new rather than reused: the parser calls
`readNat`, not `readDigits`, and there is no `readNat_append` — the
only consumer of `readNat` is `readVerbatim`, whose append lemma
inlines the fact as a local `have` instead of factoring it. So the
module proves `readNat (decOf n ++ rest) = some (n, rest)` under the
delimiting hypothesis, from `readDigits_append`, `digitsVal_decOf`,
and that `decOf` is non-empty and all digits.

Three further facts are new for the same reason. Two are consumed
where `parseStep` strips after a label:
`skipWs (decOf n ++ rest) = decOf n ++ rest`, and beneath it that a
digit character is not whitespace. The third is consumed in the
arity-zero branch of `parseAux_print`, which must show `parseStep`'s
`c = '('` test fails on `decOf i ++ rest` — that a digit character is
not `'('`. A fourth is its sibling, that a digit character is not
`')'`, which the child loop needs where a printed child begins with a
digit; the canonical development never needed it, having no such
child. None is stated anywhere yet, and the replacement head lemma
below covers none of them, being about `print r` rather than
`decOf n`. So the decimal layer is reused but extended by five
lemmas, and the module carries six more that the count of five does
not include: `decOf`'s head is a digit, two `decide`s about `(`, one
that `)` is not whitespace and one that the space is, and that the
flattened child block followed by `')' :: rest` never begins with a
digit — stated over the block with its terminator, which is what makes
it true when the block is empty. The two about `)`
and the space are reached through the child-loop induction at every
node's last child, not only at arity zero.

The canonical `Geb.Rose.exists_print_eq_cons` says every printed tree
begins with `(`. Its readable replacement is that every printed tree
is non-empty and begins with `(` or a digit, and it has two consumers.
`parseChildren` needs the head to be neither `)` nor whitespace, so
that the whitespace skip does not consume into the child and the loop
does not mistake a child for the terminator. `parse` needs
`skipWs (print r) = print r`, since the entry point skips before
running `parseAux`, and that is the same head fact at the top level.

The canonical proof takes a second fact from the same lemma, that a
printed child is non-empty, and uses it to bound a node's arity by the
length of the flattened child block. That use does not arise here.
Each block element is `' ' :: print t`, a cons by construction, so
`List.length_cons` replaces the appeal to `Rose.exists_print_eq_cons`
in the positivity side condition; the bound itself is
`L = 2 + |decOf i| + Σⱼ(1 + Lⱼ)` with `|decOf i| ≥ 0`, and needs
`List.length_flatten` and the sum bound as the canonical proof does.
`Csexp.decOf_ne_nil` and `decOf_all_digits` establish that `decOf n`'s
head is a digit, which is what the head lemma and
`skipWs (decOf n ++ rest) = decOf n ++ rest` consume;
`Csexp.decOf_ne_nil` is separately consumed by `readNat_append`,
through `readNat`'s emptiness guard, as `readVerbatim_append` consumes
it today. The
child's own fuel obligation, `Lⱼ ≤ g`, is the second of the two
inequalities and comes from the child's spelling being a sublist of
the flattened block.

### The child loop is reused

The parser strips whitespace on return rather than on entry.
`parseStep` is called on stripped input and returns a stripped
remainder, stripping at the four sites § Proof obligations names:
after `(`, after the label in each of the two branches, and after the
child list. `parseChildren` is called on stripped input and returns whatever
follows the closing parenthesis, unstripped — its terminating branch
is `if c = ')' then some ([], cs')`, and `cs'` is stripped by
`parseStep`. The invariant is therefore about `parseStep`, not
about every layer.

Under that discipline `Geb.Rose.parseChildren` is reused verbatim. Its
body mentions no syntax-specific construct but `')'`, which both
spellings close with, and both its equation lemmas come with it
unchanged,
`parseChildren_succ_close` still `@[simp]` and still `rfl`. There is
no skip parameter, no unfolding equation over a skipped input, and no
restated equation lemma.

The discipline also restores the canonical entry point. Because the
remainder is already stripped, `parse` has `Geb.Rose.parse`'s shape,
matching `some (r, [])` syntactically rather than testing a remainder
for whitespace, and `(0 1 )`, `( 0 1 )` and a trailing newline all
parse.

Four details the implementation meets that the shape of the proof does
not predict. The three digit-versus-character facts cannot be
closed by `omega` after substituting a literal, since it does not
evaluate `Char.toNat`; they need `decide` or `simp` on the
character.
`parseStep` needs an equation lemma per non-empty branch — the
parenthesized one by `rfl`, the other by `if_neg`; the empty-input
branch is reached by the whitespace-only test — because
`simp only [parseStep, …]`, the form the canonical `parseAux_print`
uses, does not reduce past the
`c = '('` test when the scrutinee is `readNat (skipWs cs)`; and after
rewriting with `readNat_append` a bare `simp only []` is still needed
to reduce the exposed `match`, as `Csexp.parseAst_printAst` already
does. And `linter.style.show`, a
member of `mathlibStandardSet`, rejects `show` used to change a goal,
so the remaining branch reductions are `change`.

`Geb.Rose.parseChildren` and its two equation lemmas move from
`Geb/Internal/CanonicalSExpr.lean` into
`Geb/Internal/ConcreteSyntax.lean`, unchanged, in a re-opened
`namespace Rose` block — that file already opens `Rose` twice and
`Ast` four times, and this adds a third `Rose` block. The move is what
lets the readable module reuse them without importing the `CSexp`
development. Each syntax proves its own
`parseChildren_print`, since the two differ in the child spelling and
in the delimiting hypothesis, which is precisely what a shared
statement would have to abstract over.

### Alternatives considered

The arrangements below were considered. They vary along dimensions
worth naming, but the dimensions do not yield a closure argument, and
this section does not claim one: the list is what was considered, not
what exists.

- **Where whitespace is consumed.** The entry point, the tree parser's
  head, its tail, the child loop — or nowhere, or a pass run before
  the parser. A design chooses a *subset*, not a value: the chosen one
  strips at the entry point and at the tail, and § Proof obligations
  names four sites within the latter.
- **What happens to `Geb.Rose.parseChildren`.** Reused where it
  stands, relocated and reused, generalised over a parameter, edited
  in place, or duplicated. The chosen design relocates.
- **The parser's input type**, `List Char` or `List Token`, free only
  under a pre-pass.
- **The printer.** § Printer's spelling is held fixed below, but it is
  not forced. Always parenthesizing removes the delimiting hypothesis
  outright, as § The delimiting hypothesis cannot be dropped states,
  and suppressing the space before a parenthesized child changes the
  cons-ness the arity bound uses. Those alternatives are recorded
  there and in § Recorded consequences rather than here.

The accepted language is not a further dimension; it is what the first
two determine, and it is the observable each arrangement is judged on.
None is costed numerically: a transient document cannot carry a
measurement its reader cannot reproduce. The plan settles the choice
and records which was taken.

- **Strip at the tree parser's head, in the child parser.** The loop
  delegates the printer's leading space to the child parser, which
  then meets `)`, so `(0 1 )` and `( 0 1 )` are rejected. That is a
  smaller accepted language than § Grammar fixes, so the rejection is
  a trade against the language, not a correctness argument.
- **Generalise the loop over a skip parameter.** Moves the obligation
  to every call site. With the skip and the child spelling concrete,
  the head and delimiting facts are provable inside a specialised
  `parseChildren_print` — which is what the canonical proof already
  does, deriving its head fact from `Rose.exists_print_eq_cons` in its
  own cons step. Generalised, both `parseAux_print` proofs supply four
  hypotheses instead, and the shared statement acquires a delimiting
  notion in terms of `Csexp.charDigit`, on which the canonical loop
  has no dependency.
- **Put the skip inside the shared loop, concretely.**
  `Geb.Rose.parseChildren` matches on `skipWs cs` outright. Then
  `parseStep` needs one strip, after `(`, and the canonical
  `parseChildren_print` gains only
  `skipWs (print t ++ r) = print t ++ r`, immediate from
  `Rose.exists_print_eq_cons` — no call site supplies anything, so the
  objection above does not reach it. Its costs are three: editing a
  proved shared declaration, where `parseChildren_succ_cons` acquires
  a whitespace hypothesis and stops being `if_neg`, though
  `parseChildren_succ_close` is still `rfl`; widening the canonical
  parser's accepted language to whitespace that syntax never emits;
  and giving up the syntactic `some (r, [])` match at the entry point,
  since the remainder must then be tested modulo whitespace.
- **Put the skip inside a duplicated loop.** The combination of the
  previous two, and the cell at which the previous bullet's first two
  costs vanish: nothing shared is edited and the canonical language
  does not widen. It costs a duplicated definition and two equation
  lemmas instead, and still tests the remainder modulo whitespace.
- **Reuse the loop where it stands.** The readable module imports
  `Geb.Internal.CanonicalSExpr` and uses `Rose.parseChildren` in
  place, so nothing moves, nothing is duplicated, and the docstring
  edits and inter-module census shift § Persistent documentation
  charges to the move do not arise. Its cost is the import closure:
  the readable module would pull in the `CSexp` family,
  `Mathlib.Data.Fin.VecNotation` and the whole canonical development
  for one loop, and would depend on a sibling spelling it otherwise
  has nothing to do with.
- **Define the loop again in the readable module, strip unchanged.** A
  short definition and two equation lemmas proved by `rfl` and
  `if_neg`, against leaving `Geb/Internal/CanonicalSExpr.lean`
  untouched. The move is the sole cause of the inter-module census
  shift § Persistent documentation records — a third module falsifies
  the counts either way — so this accepts duplication in exchange for
  not disturbing two proved modules.
- **Accept exactly what the printer emits.** The retraction law
  constrains only the composite, so nothing forces the parser to
  accept `( 0 1 )`. A printer-exact parser needs no `skipWs` at all:
  the child parser consumes the separator space, and
  `Geb.Rose.parseChildren` is reused verbatim. That removes `isWs`,
  `skipWs` and its equations, two of the five decimal lemmas — the one
  about `skipWs` over `decOf` and digit-is-not-whitespace, the other
  three surviving because the step still branches on `(` and the loop
  still tests `)` — the `skipWs rest` conclusion, and the stripping
  discipline of § The child loop is reused, though not that section's
  module move, which the reuse still needs.
  It costs `parseStep` an optional-leading-space case, since the
  printer emits a space before every child but not before the
  top-level tree, which splits the step into a body and a wrapper with
  an equation lemma each — and that optional case is itself what
  admits an omitted separator, so `(0(1))` parses. Its language is the
  printer's output, plus omitted separators, plus the two lax families
  no whitespace discipline touches: a parenthesized childless node and
  leading zeros.
- **Printer-exact interior, document-level strip.** The previous cell
  with `skipWs` at the entry point only. A leading indent parses, and
  `(0(1))` still parses. A trailing newline does not, unless this cell
  also tests the remainder modulo whitespace rather than matching
  `[]` — the same cost charged above to putting the skip in the shared
  loop. What it gives up against § Grammar is `( 0 1 )`, `(0  1)`,
  `(0 1 )`, and every separator that is not a literal space, so every
  multi-line spelling § Deferred contemplates a formatter for. The
  indent, at least, follows from the entry point's discipline rather
  than from the printer-exact interior.
- **A pre-pass over `List Char`.** Normalise whitespace to the
  printer's spelling, then run the printer-exact parser. It reuses the
  loop verbatim and keeps the input type, so the objection to the
  token-level pre-pass below does not reach it. The normaliser is not
  a deletion: `(0(1))` must be accepted while the printer-exact parser
  demands a space before each child, so the map inserts as well as
  collapses, which makes it a lexer in all but name and leaves a
  fixed-point lemma `norm (print r) = print r` whose induction meets
  the same junction facts.
- **A pre-pass over `List Token`.** § Grammar is two-level, and a
  parser could be too: `lex : List Char → List Token`, then a parser
  over `List Token`. Its token-level `parseAux_print` and
  `parseChildren_print` carry no `skipWs` and no side condition. What
  it does not yield is reuse: `Geb.Rose.parseChildren` is monomorphic
  in `List Char` and tests its head against `')'`, so a token-level
  loop is a second loop or a generalised one. Nor does the delimiting
  condition disappear; it relocates, with the same side condition and
  the same discharge sites, into
  `lex (decOf n ++ rest) = numeral n :: lex rest`, which is false as
  stated without it. The step to the tree level is a further
  induction, `lex (print r ++ rest) = tokens r ++ lex rest`, carrying
  that condition. A maximal-munch `List.rec` lexer also needs
  lookahead into its tail, since the fold runs right to left and would
  otherwise merge numerals across a separator.

## Lean shape

A new module `Geb/Internal/ReadableSExpr.lean`, importing
`Geb.Internal.ConcreteSyntax` for `Rose`, the decimal layer and the
`Retraction` skeleton. It does not import
`Geb.Internal.CanonicalSExpr`. Four existing files change:
`Geb/Internal.lean` and `GebTests/Internal.lean` each gain an import,
which is what § Repo structure of
[CONTRIBUTING.md](../../../CONTRIBUTING.md) requires with its
one-indexing-file-per-directory rule, and
`Geb/Internal/CanonicalSExpr.lean` gives up `Rose.parseChildren` and
its two equation lemmas to
`Geb/Internal/ConcreteSyntax.lean`, which receives them. No existing
proof changes: the three declarations move unedited, and nothing
consuming them is
restated. § Persistent documentation lists the docstrings that the
move and the new module make inaccurate.

It does not route through `CSexp`. That intermediate exists to state
`Csexp.print_eq_render_toCSexp`, which says the printer's output is a
canonical S-expression for the ASCII-atom trees at hand — a
conformance statement the local retraction law does not give, as the
canonical module's docstring says. A [R7RS] `<datum>` datatype would
be the corresponding intermediate here, and the reason not to build
one is that no stage of the roadmap turns on the readable output being
a `<datum>` as against being what this printer emits. § Problem's
interoperation argument is discharged by the grammar's shape, which is
checkable against [R7RS] §§ 7.1.1–7.1.2 by reading it, and needs no
Lean theorem. Skipping it costs nothing in proof
either — `CSexp.render_list_eq_flatten` exists only because
`CSexp.render` folds with `Fin.foldr` while the parser produces a
`List`, and a directly-defined readable printer over `List.ofFn ch`
gets one spelling equation by `rfl` and the other by two rewrites
with core's `List.map_ofFn`, where the intermediate would need a
locally proved lemma.

Declarations in a namespace `Geb.Rsexp`. `Geb.Csexp` is the parallel
for the module's shape, not for `print`'s type: `Geb.Csexp.print` goes
from `Ast k`, and the declaration `Rsexp.print` parallels is
`Geb.Rose.print`.

- `print : Rose k → List Char` and
  `parse : Nat → List Char → Option (Rose k)`, with `isWs`, `skipWs`,
  `parseStep` and `parseAux` beneath them. `isWs : Char → Bool` is
  where § Grammar's `ws` class is pinned in Lean, and it is what the
  digit-is-not-whitespace lemma is stated against. The child loop is
  `Geb.Rose.parseChildren` and is not redefined; `parseChildren_print`
  is proved here, against this printer's child spelling and its
  delimiting hypothesis.
- `parse_print`, then `retraction`, `format_idem` and
  `print_injective` by the existing skeleton.
- `printViaRose : Ast k → List Char` and `parseViaRose`, composing
  with the rose bijection, and their retraction from
  `Ast.ofRose_toRose`. The names follow
  `Geb.Ast.printViaRose`/`parseViaRose`, the canonical module's
  composites through the same bijection; `Geb.Csexp.printAst` is a
  direct printer, so `printAst` here would invert the established
  meaning.

There is no direct `Ast` printer. Dropping `leaf` and `fork` removes
the only thing one would have expressed.

Tests in `GebTests/Internal/ReadableSExpr.lean`, following the
existing test modules, with three constraints those modules already
meet. `#guard` runs its argument in the interpreter, so the module
needs a `public meta import` of the module under test beside the
ordinary one, each carrying `-- shake: keep` as both existing test
modules do, per § Lean 4 module system and § Lake / build workflow of
[docs/rules/lean-coding.md](../../rules/lean-coding.md). `![…]`
notation for a node's children comes from
`Mathlib.Data.Fin.VecNotation`, which reaches the canonical test
module only through `Geb.Internal.CanonicalSExpr`; a module importing
only the readable one imports it directly or builds children with
`Fin.cons`. Reusing `sexp` adds an import of
`GebTests.Internal.ConcreteSyntax`, where it is defined. And inputs
are `List Char` literals or fixtures, since
core's `String.toList` depends on `Classical.choice`, which
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Constructive-only
requires be minimised and `GebMeta.detectNonstandardAxiom` rejects
outside its allowlist. The canonical atom fixtures are specific to the
length-prefixed form; `sexp`, which only parenthesizes a body, is
reusable as it stands.

The assertions themselves: the printed spelling at a concrete tree,
the round trip evaluated, the three lax families above — whitespace
variants including `(0(1))`, `( 0 1 )` and a trailing newline; the
parenthesized childless node; leading zeros — the formatter rewriting
`(0 1 2 (3 4) 5 (6) 7)` to `(0 1 2 (3 4) 5 6 7)`, and the rejection
paths: an unterminated list, a label at or above `k`, a `)` with no
opening, trailing non-whitespace input, and the rejections peculiar to
this grammar — `()` and `(())`, which pin that a list must have a head
numeral, together with empty input, which exercises the entry point
at zero fuel, and whitespace-only input, which reaches `parseStep`'s
empty-input branch at positive fuel.

`(01)` is not a rejection path. It parses as the childless node `1`,
which § Grammar states; it is a reinterpretation, and belongs with the
lax families rather than the rejections.

## Persistent documentation

- [docs/concrete-syntaxes.md](../../concrete-syntaxes.md): the survey
  above condensed into § Format-by-format evaluation, the stage row
  in § Roadmap, the profile decisions beside the canonical form's, and
  a statement in § The bootstrap set, where the switch thresholds
  are, that the condition is recorded uncounted and the stage
  scheduled anyway, with a grammar other than the one it names.
- [docs/references.bib](../../references.bib): entries for [R7RS] and
  [EDN]. [RFC9804] is already present.
- [docs/references.md](../../references.md): library and URL pointers
  for `sexplib`, `janestreet/sexp`, Real World OCaml's
  data-serialization chapter, parinfer, paredit and `zv/sexpr`, which
  are tooling and exposition rather than citable literature.
- [docs/index.md](../../index.md): beyond naming the new module, it
  carries per-module theorem censuses with axiom breakdowns — "Of the
  module's 52 theorems, 11 …" and "Of the module's 20 theorems, 4
  depend on no axioms …" — and names `Rose.parseChildren` as
  distinguishing the canonical parser. Moving two theorems between the
  counted modules falsifies both censuses and both breakdowns.
- [TODO.md](../../../TODO.md): the module and its follow-on work.
- `Geb/Internal/CanonicalSExpr.lean`'s module docstring, at two sites,
  both naming the moved loop: `## Main definitions` calls the parsers
  "built from `Rose.parseChildren`", and the implementation notes open
  "A rose node's arity is unbounded, so `Rose.parseChildren` reads
  until the closing parenthesis".
- `Geb/Internal/ConcreteSyntax.lean`'s `## Main definitions`, which
  gains `Rose.parseChildren`.
- `Geb/Internal/ConcreteSyntax.lean`'s `Rose.Arity` docstring and its
  module docstring's § Implementation notes: both enumerate the proofs
  that need the family reducible, naming two here and
  `Rose.parseAux_print` as the third downstream. The readable
  `parseAux_print` performs the same `Fin n` against
  `Rose.Arity (i, n)` transport, so both enumerations become
  undercounts.
- `Geb/Internal/ConcreteSyntax.lean`'s § Choice-free finite
  enumerations section comment, which says the `#guard`s in "the two
  `GebTests` syntax modules" decide equality at `Ast k`, at
  `Tree k Ann` and at `Rose k`, and `Rose.instFinEnumArity`'s
  docstring, which says "Both `GebTests` syntax modules decide it".
  The readable test module's assertions compare `Option (Rose k)`
  values through the same instance, so both become undercounts.
- `docs/concrete-syntaxes.md` § The canonical grammar as a data type:
  it calls the rose spelling "the one place in this development where
  those two obligations are discharged", the obligations being the
  unbounded-arity loop and the `List`-to-W transport. The readable
  module discharges both a second time.
- `docs/concrete-syntaxes.md` § Relation to existing repository
  content: it states that "four proofs destructure `Rose.Shape`, there
  being no `Rose.ind`" and names them, two of which are the canonical
  parser's. The readable parser's head lemma and `parseAux_print`
  destructure it too, so the count and the list are undercounts.
- `docs/concrete-syntaxes.md` § Local verification: it names the two
  library modules and their two test modules and counts "52 theorems"
  and "20 more", repeated at three further points in the file. Adding
  a third library module and its test module falsifies both module
  lists and every count, and moving the child loop moves theorems
  between the two counted modules.
- `docs/concrete-syntaxes.md` § Status: it names the same four modules
  and describes `CanonicalSExpr` as "a second retraction over the same
  grammar"; this stage adds a third.

## Deferred

- **Indentation.** The printer emits one line, which is deterministic and
  needs no layout rule; a multi-line discipline is a formatter
  refinement over the same grammar. parinfer is not the reason to
  defer it — the page states that "single-line files are okay", and
  Paren Mode is the mode that would supply indentation. What any later
  formatter must respect is that Indent Mode is permitted to change
  the AST by design, so only Paren Mode composes with a retraction
  law.
- **Atom quoting and escaping.** Stage 2, when `Ann`'s `Option String`
  and `List String` enter the syntax. Until then every atom is
  `[0-9]+`.
- **Named labels.** Labels are `Fin k` and print as numerals. A label
  type carrying names would let one printer serve a syntax with
  constructor names, and is a change to the rose layer with its own
  concern.
- **Comments.** [R7RS], [EDN] and `sexplib` all provide them; nothing
  in the bare tree consumes one, and § Lexical comments are not
  durable already records why they are not part of the durable model.
- **Commas as whitespace.** Admitting them would widen the accepted
  language to cover idiomatic [EDN]; no tree needs it.

## Recorded consequences

- The rose presentation can annotate no more positions than the binary
  one, and strictly fewer as soon as the tree contains a fork —
  § Which occurrences the rose presentation can name states this, and
  states that it rests on a claim the development does not formalize.
  It applies to the readable syntax as to the canonical rose spelling,
  and binds at stage 2, when annotations acquire positions.
- The readable syntax is a second spelling over one data model, so
  § The bootstrap set's argument for stage 1b is untouched by it.
- The child loop is reused unchanged, and only its
  `parseChildren_print` is proved twice, once per child spelling.
  § The child loop is reused states the stripping discipline that
  makes the reuse possible; § Alternatives considered gives the four
  dimensions the arrangements vary along and the ten others
  considered.
- `docs/concrete-syntaxes.md` goes stale in three ways: its two
  enumerations of the syntax modules, its theorem censuses, which stop
  covering the whole development, and two claims of uniqueness — one
  that the rose spelling is the only place two obligations are
  discharged, one counting the proofs that destructure `Rose.Shape`.
- Printing a childless node as a bare numeral is what obliges the
  retraction lemma to carry a delimiting hypothesis. Always
  parenthesizing would remove the obligation and the spelling.
- Accepting whitespace the printer never emits is what obliges the
  parser to carry `skipWs`, the stripping discipline and the
  `skipWs rest` conclusion. Accepting exactly the printer's output
  would remove all three, and with them a leading indent, a trailing
  newline and `( 0 1 )`. § Alternatives considered states the trade.
- The switch threshold's frequency condition is uncounted. The stage
  rests on anticipated use, as § Problem states.

## References

- [R7RS] — Shinn, Cowan and Gleckler (eds.), *Revised⁷ Report on the
  Algorithmic Language Scheme*, 2013; productions checked against the
  errata-corrected edition dated 19 December 2022. § 4.1.3 procedure
  calls, § 7.1.1 lexical structure, § 7.1.2 external representations.
  <https://standards.scheme.org/corrected-r7rs/r7rs.html>
- [EDN] — *extensible data notation*.
  <https://github.com/edn-format/edn>
- [RFC9804] — Rivest and Eastlake, *Simple Public Key Infrastructure
  (SPKI) S-Expressions*, RFC Editor, June 2025, Informational.
  § 4.3 token representation, § 6 representation types, § 7.1 advanced
  ABNF, § 8 restricted S-expressions.
  <https://www.rfc-editor.org/rfc/rfc9804.html>
- `sexplib` — <https://github.com/janestreet/sexplib>
- `janestreet/sexp` — <https://github.com/janestreet/sexp>, query
  semantics at `doc/query_semantics.md`
- Real World OCaml, data serialization —
  <https://dev.realworldocaml.org/data-serialization.html>
- parinfer — <https://shaunlebron.github.io/parinfer/>
- paredit — <https://paredit.org/>
- `zv/sexpr` — <https://github.com/zv/sexpr>
- [docs/concrete-syntaxes.md](../../concrete-syntaxes.md) — the survey
  this stage extends.
