# Extensions of the tree recognizers

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Status](#status)
- [Questions](#questions)
- [Answers, in brief](#answers-in-brief)
- [The ranked alphabet and its term algebra](#the-ranked-alphabet-and-its-term-algebra)
- [The encoding](#the-encoding)
- [The scan combinator](#the-scan-combinator)
- [The state layout](#the-state-layout)
  - [Candidates](#candidates)
  - [Deciding factors](#deciding-factors)
  - [Choice](#choice)
  - [The alternative encoding](#the-alternative-encoding)
- [The fold](#the-fold)
- [The cost bound](#the-cost-bound)
- [Scope and branches](#scope-and-branches)
- [Deferred](#deferred)
- [Verification performed](#verification-performed)
- [Reference status](#reference-status)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Status

Transient per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape.

## Questions

`Cobham.isTree` (`Geb/Mathlib/Computability/Cobham/Tree.lean`) decides
`BinTree.Valid` and lies in the subalgebra `SmashFree` names, so by
[Strahm2003] Theorem 1(2) the decision is computable simultaneously in
polynomial time and linear space. Four extensions were asked about:

1. Leaves labelled from a finite alphabet.
2. A generic iterator over a recognized encoding — a fold or paramorphism
   in the sense of [Meertens1992] — with whatever restriction on the
   configurable part keeps the result in the subalgebra.
3. A bound on the recognizer's cost sharper than that membership gives.
4. Trees over a ranked alphabet, each label carrying its own arity.

## Answers, in brief

Question 1 is the two-arity case of question 4, and both are settled by one
construction. Question 2 is settled by the same construction with a payload
attached to each stack cell. The construction imposes two conditions on the
scan it is given, and at a finite carrier both are discharged from
finiteness alone, so the iterator's configurable part carries no restriction
of its own. Question 3 is settled against a machine model, the algebra
carrying no cost semantics of its own.

The unifying object is a right-to-left scan whose state is a bitstring
holding one stack cell per pending subterm. The present recognizer is that
scan at code width one with an empty payload; it is not analogous to the
general construction but an instance of it.

## The ranked alphabet and its term algebra

A ranked alphabet is a finitary polynomial functor whose shape type is
`Fin card`, so the term algebra is that functor's W-type, as `BinTree` is
the W-type of `BinTree.Direction`.

```lean
structure Ranked where
  card : ℕ
  width : ℕ
  card_le : card ≤ 2 ^ width
  ar : Fin card → ℕ

@[expose] def Ranked.Term (R : Ranked) : Type :=
  WType fun i : Fin R.card ↦ Fin (R.ar i)
```

`width` is the number of bits spelling one symbol and `card_le` admits
alphabets whose size is not a power of two, at the price of a block that
decodes to `card` or beyond spelling no symbol and being rejected. At
`width = 1` and `card = 2` the condition is vacuous, which is why the
present recognizer carries no such test.

The present encoding is `R = ⟨2, 1, _, ![0, 2]⟩`: code `0` is the symbol of
arity zero, code `1` the symbol of arity two.

## The encoding

```lean
@[expose] def spell (R : Ranked) : R.Term → List Bool :=
  WType.elim _ fun ⟨i, ch⟩ ↦ code R i ++ (List.ofFn ch).flatten
```

At the present alphabet this is `BinTree.print` itself: `code node ++
print l ++ print r` is `true :: (print l ++ print r)`, and `code leaf` is
`[false]`.

The processing order of a `boundedRec` is the reverse of the list order —
`evalRec` peels the head last — so a symbol's block is read before the
blocks of its children, and a symbol is applied after them. The encoding is
prefix notation in list order and postfix in processing order.

Validity is no longer the conjunction `ok w = true ∧ depth w = 1` that
`BinTree.Valid` is, because the fold now carries an incomplete block:

```lean
structure Scan where
  buf : List Bool
  depth : ℕ
  live : Bool

@[expose] def Valid (R : Ranked) (w : List Bool) : Prop :=
  w.foldr (scanStep R) ⟨[], 0, true⟩ = ⟨[], 1, true⟩
```

At `width = 1` the buffer is empty between steps, and `Valid` splits back
into the two conditions, so `Preorder.lean`'s statements are recovered as
specializations rather than replaced. The bijection `Valid w ↔ ∃ t, spell R
t = w` is proved through a fuel-bounded recursive descent, as
`BinTree.valid_iff_exists_print` is.

## The scan combinator

```lean
structure Scanner where
  step : COf 2
  base : COf 0
  growth : ℕ
  step_smashFree : SmashFree step.1
  base_smashFree : SmashFree base.1
  length_le : ∀ w, (w.foldr stepSem (baseSem ![])).length ≤
    growth * w.length + (baseSem ![]).length

def Scanner.run (S : Scanner) : COf 1

theorem Scanner.run_sem (S : Scanner) (w : List Bool) :
    runSem S ![w] = w.foldr S.stepSem S.baseSem
theorem Scanner.run_smashFree (S : Scanner) : SmashFree S.run.1
```

`Scanner.run` is a single `boundedRec` node whose bound child is the
`growth`-fold `concat` of the recursion variable with itself, of length
`growth * |y|`, followed by as many `succ` nodes as the base state is long.
`concat` is in [Strahm2003]'s operator list, so the bound is smash-free at
every `growth`.

This is the answer to question 2 in the recognizer direction: the
restriction on the configurable part is exactly two conditions — the step
lies in the subalgebra, and the state grows by a constant per bit read.
Admissibility is discharged once, for every instance.

The instances are the present recognizer, the labelled recognizer, the
ranked recognizer and the fold. Acceptance is a constant-size `cond` test
composed onto `run`; `isTree` is `accept ∘ run`.

`Scanner` also meets the condition recorded in `TODO.md` § The
Bellantoni-Cook tree recognizer for extracting the unfolding and
environment lemmas into their own module, that a second function need them.

## The state layout

The state must hold a liveness flag, the information of an incomplete
symbol block, the count of pending subterms, and, for the fold, a
fixed-width value per pending subterm.

One constraint governs the choice. The algebra is cheap at the head alone:
`cond` tests the head, `pred` is `List.tail`, `succ` is `List.cons`. A field
at distance `δ` from the head costs `δ` applications of `pred`, so `δ` is
constant; every field but the stack sits within a constant distance of the
head, and the stack is touched at its top, which is adjacent to that
region.

### Candidates

- **Unary prefix.** `List.replicate j false ++ List.replicate (d + 1) true`,
  with `[false]` for the failed state. Carries a count and no bit values, so
  it serves a label-skip phase or a pending arity but not a block whose
  value determines an arity. Growth one; bound `S₁`, as at present.
- **Escape-marked buffer.** The buffered bits each preceded by a `false`
  marker, then the counter. Carries bit values; the marker is what tells the
  buffer from the counter. Growth two. This is an escape code, the device by
  which a variable-length field becomes readable from one end.
- **Fixed-width header.** A header of constant width holding the flags, the
  buffer and the phase, then the counter, which therefore begins at a fixed
  offset. Admits no ambiguity, and states the layout as a product of fields.
  Each unfolding lemma case-splits over the header's values, and the step's
  conditionals reduce only once the scrutinee is in constructor form to the
  header's depth.
- **Merged frame stack.** One cell of a marker and `p` payload bits per
  pending subterm, the count implicit as the number of cells. The arity
  guard is a head-region test; a pop of `r` cells is `(p + 1) * r`
  applications of `pred`. Growth `p + 1`.
- **Bottom sentinel.** A terminator at the stack's bottom. Rejected: the
  bottom is the far end, and reaching it is a scan rather than a constant
  number of head operations.
- **Binary counter.** The count in binary rather than unary, of length
  logarithmic in the word length. Rejected: the comparison against an arity
  and the subtraction of one propagate carries, so neither is a constant-size
  expression, and the step is no longer constant.

### Deciding factors

In the order in which they decide:

1. Whether counts suffice or bit values are needed.
2. The size of the proofs, set by the depth of case analysis a step's
   conditionals require before they reduce. The existing
   `combSem_cons_true` already matches four constructor layers deep because
   its guard applies `pred` twice.
3. Whether the present recognizer is the layout's own instance, which
   decides whether `combSem_eq` is reused or reproved.
4. The growth constant, which sets the number of `concat` nodes in the
   bound. Every candidate is smash-free, so this decides little.
5. Bit economy, which decides nothing here: no statement of this workstream
   is a bit count.

### Choice

The escape-marked buffer and the merged frame stack are one layout under two
parameters, a code width and a payload width:

| Parameters | Instance |
| --- | --- |
| width one, payload zero | the present recognizer, unchanged |
| width one, payload zero, skip phase | labelled leaves |
| width `c`, payload zero | the ranked alphabet |
| width `c`, payload `p` | the fold |

At width one a block completes as it is read, so the buffer is empty between
steps and the state is `List.replicate (d + 1) true`, which is what `comb`
computes. Factor 3 is therefore met without a further argument.

`Scanner`'s interface takes the fixed-width header's virtue without its
cost: it is stated over an encoding and a decoding of an abstract state
with one obligation, that distinct abstract states have distinct
bitstrings, discharged once; each instance chooses its concrete layout.
That obligation is what the layout determines.

### The alternative encoding

[BenoitDemaineMunroRamanRamanRao2005] § 3 writes "the unary degree sequence
of each node but in a depth-first traversal of the tree", the depth-first
unary degree sequence, and its Theorem 3.1 gives a balanced parenthesis
string of length `2n` for an ordinal tree on `n` nodes, the
information-theoretic bound; its cardinal-tree bound is
`(⌈lg k⌉ + 2) n + o(n)` bits. That representation is the Łukasiewicz word
with each arity spelled in unary.

Spelling the arity in unary collapses the buffer to a pending-arity count,
so the unary-prefix layout serves the whole ranked case. It is not adopted
here: the arity is a function of the label, so a labelled alphabet spells
the label in any case and a unary arity beside it is redundant, and a
binary node's spelling would become three bits where the present encoding
spells it in one, which would forfeit the reduction of factor 3. It is the
representation to adopt if unbounded arity is ever required, the regime in
which it is optimal.

## The fold

```lean
structure Fold (R : Ranked) (p : ℕ) where
  step : (i : Fin R.card) → (Fin (R.ar i) → Fin (2 ^ p)) → Fin (2 ^ p)

def Fold.toScanner (F : Fold R p) : Scanner

theorem Fold.run_spell (F : Fold R p) (t : R.Term) :
    foldSem F ![spell R t] = WType.elim _ F.step t
```

`Fold.run_spell` states that `WType.elim`, the map out of the initial
algebra, is realized inside the subalgebra, transported along the encoding.

The step is a function between finite types, so it is bounded and a
constant-size tree of `cond` nodes computes it. The restriction question 2
anticipates therefore does not arise at a finite carrier: finiteness
supplies what a bound would otherwise have to. A restriction returns at an
infinite carrier, where a value bounded by a polynomial requires the
`smash` generator and leaves the subalgebra.

A paramorphism whose additional argument is a finite function of the
subterm is a fold into a product and is covered. A paramorphism whose step
receives a subterm's spelling is not: the spellings are of unbounded
length, so locating a cell boundary costs a scan of the stack at each step.
That is a property of the scheme rather than of a cost model.

[DalLagoMartiniZorzi2010] is the reference for what unbounded branching
recursion costs. Its Theorem 1 covers tiered recursion over an arbitrary
signature, and the extension of [Leivant1999]'s word-algebra result to
branching algebras holds for terms represented as graphs, so that shared
subterms are computed once. Bounded recursion on notation does not depend
on that, the bound being a side condition rather than a consequence of a
type discipline.

## The cost bound

`isTree_smashFree` with [Strahm2003] Theorem 1(2) is the only statement
about cost, and it is a class membership. The algebra carries no cost
semantics, so a sharper bound is stated against a machine model.

Measuring the algebra term instead gives a worse answer than the algorithm
deserves. `pred` and `cond` are `boundedRec` nodes rather than generators,
so under a strict reading each costs one unit per bit of its scrutinee, and
the scrutinee at each step is the state, of length `depth + 1`. The total is
the sum of the stack depths over the word: quadratic in the word length on a
left comb, linear on a right comb.

The bound is therefore stated over Cslib's `MultiTapeTM`, whose
`ComputesFunInTimeAndSpace` measures time and space together and carries an
embedding of the input alphabet into the machine alphabet, so that one
work-tape symbol holds a whole stack cell. One work tape holds the stack,
the input is consumed right to left, and each input symbol costs a constant
number of steps.

```lean
theorem decideValid_computableInTimeAndSpace (R : Ranked) :
    ComputableInTimeAndSpace (decideValid R) (fun n ↦ a * n + b) (fun n ↦ n + b)
```

Two constraints fix where this lives. `Geb/Mathlib/` may not import
`Cslib.*` and `Geb/Cslib/` may not import `Geb.Mathlib.*`, so a statement
naming both `Cslib` and `Ranked.Valid` is confined to `Geb/Internal/`. And
`DecidableInTimeAndSpace` is stated through `indicator`, which is
`noncomputable` and depends on `Classical.choice`; the statement is made
over `ComputableInTimeAndSpace` applied to a computable decision function
instead, `Valid` being decidable, so the module needs no entry in
`GebMeta.classicalAllowedModules`.

This resumes the route that
`docs/superpowers/specs/2026-08-08-tree-recognizer-linear-space-design.md`
named Route A and deferred.

## Scope and branches

| Branch | Content | Depends on |
| --- | --- | --- |
| B1 | `Geb/Mathlib/Data/Tree/Ranked/` — the alphabet, the term algebra, `spell`, the descent, `Valid`, the bijection, the equivalence with `BinTree`, and the width-one specializations | — |
| B2 | `Geb/Mathlib/Computability/Cobham/Scan.lean` — `Scanner`, the ranked recognizer, and `isTree` re-expressed as the width-one instance | B1 |
| B3 | `Geb/Mathlib/Computability/Cobham/Fold.lean` — the fold and `Fold.run_spell` | B2 |
| B4 | `BinTree` absorbed into `Ranked.Term`, and the duplication removed | B1, B2 |
| B5 | `Geb/Internal/` — the time and space bound against Cslib's `MultiTapeTM` | B2 |

B2 carries `Scanner` together with two of its instances: a combinator
introduced with one consumer would be generality without a return, and the
ranked recognizer is what the combinator is for.

Each branch adds its entries to [docs/index.md](../../index.md) per
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Each phase produces an
artifact.

B5 differs in kind from B1 to B4, which extend constructions the repository
already carries, and it is the item whose difficulty the prototypes do not
bound. B1 to B4 stand without it.

## Deferred

- The Bellantoni-Cook recognizer's port of `Scanner`, with the labelled and
  ranked variants and the `safeRec` tree recursor recorded under `TODO.md`
  § The Bellantoni-Cook tree recognizer folded into it. The signature there
  is over arities in normal and safe position, so the port is a branch and
  not a transcription.
- The paramorphism whose step receives a subterm's spelling.
- A fold at an infinite carrier, which needs the `smash` generator.
- The depth-first unary degree sequence encoding, whose condition for
  adoption is unbounded arity.

## Verification performed

Both language-level claims were checked by exhaustive evaluation before
this specification was written.

- Labelled leaves, four labels of two bits: over every word of length at
  most eleven, the scan accepts exactly the spellings, of which there are
  148 within that length, and each spelling is distinct.
- A ranked alphabet of four symbols of arities zero to three, code width
  two: over every word of length at most twelve, the scan agrees with a
  fuel-bounded recursive descent at every word.
- The cost profile: the sum of the stack depths quadruples as the word
  length doubles on a left comb and doubles on a right comb.

## Reference status

[BarringtonCorbett1989] is cited from secondary sources only. Its volume
and pages are unconfirmed, the publisher's record having refused retrieval,
so it is verified against the article itself before it enters
[docs/references.bib](../../references.bib).

The other works added by this specification —
[BenoitDemaineMunroRamanRamanRao2005], [Mehlhorn1980] and
[BraunmuhlVerbeek1983] — are confirmed: the first from the article's own
text, the other two from their published venues.

## References

- [BarringtonCorbett1989] — one-sided Dyck languages, structured
  context-free languages and bracketed context-free languages in
  DLOGTIME-uniform TC⁰, which places the recognized language far below
  linear space and records that linear space is a property of the one-pass
  method rather than of the problem.
- [BenoitDemaineMunroRamanRamanRao2005] — the depth-first unary degree
  sequence, the alternative encoding.
- [BraunmuhlVerbeek1983] — input-driven languages recognized in logarithmic
  space.
- [DalLagoMartiniZorzi2010] — what unbounded branching recursion costs.
- [Leivant1999] — ramified recurrence over word algebras.
- [Meertens1992] — paramorphisms.
- [Mehlhorn1980] — input-driven pushdown automata.
- [Strahm2003] — the subalgebra and its containment in the functions
  computable simultaneously in polynomial time and linear space.
