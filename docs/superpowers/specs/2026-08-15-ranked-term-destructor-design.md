# The ranked term algebra's destructor in the fold's language — design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [What exists](#what-exists)
- [Deliverables](#deliverables)
  - [D4. The destructor's expressions](#d4-the-destructors-expressions)
  - [D5. The inverse laws](#d5-the-inverse-laws)
  - [D6. The paramorphism at this representation](#d6-the-paramorphism-at-this-representation)
- [Why the fold reaches a subterm's boundary](#why-the-fold-reaches-a-subterms-boundary)
- [Transcription or novel](#transcription-or-novel)
- [What is verified and what is not](#what-is-verified-and-what-is-not)
- [Risks](#risks)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope

This branch adds the inverse of the initial algebra's structure map, as
expressions of Cobham's class, and the paramorphism at the same
representation. Together with
`Geb/Internal/Computability/CobhamFoldProto/Initial.lean`, on which it
depends, it lets a term of `RankedAlphabet.Term` be constructed, destructed
and recursed over inside the class, with the representation fixed by
`RankedAlphabet.spell`.

Work lands in `Geb/Internal/Computability/CobhamFoldProto/Destruct.lean` with
its `docs/index.md` entry, its indexing-file line, and a test module carrying
the samples `Boundary.lean` holds now.
Every declaration is `Classical.choice`-free, which
`GebMeta.detectNonstandardAxiom` enforces through `lake lint` for `Geb` and
`lake lint -- GebTests` for the mirror.

This document is transient under
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape: the branch is
ordered spec and plan, then implementation, then their removal. The semantic
content it delivers is currently in
`GebTests/Internal/Computability/CobhamFoldProto/Boundary.lean`, which the
branch moves into `Destruct.lean`, removing that module once the constructor
branch has taken its own half.

## What exists

`Geb/Mathlib/Data/Tree/Ranked/` supplies `Term.mk`, `Term.induction`, `code`,
`spell` with `spell_mk`, and the bijection between the valid words and the
terms: `parse`, `parse_spell`, `parse_eq_some_iff`, `spell_injective` and
`valid_iff_exists_spell`.

`Mathlib.Data.W.Basic`, which `Ranked/Basic.lean` already imports, supplies
the destructor `WType.toSigma` with `WType.ofSigma`, the laws
`WType.ofSigma_toSigma` and `WType.toSigma_ofSigma`, and `WType.equivSigma`.

`Geb/Mathlib/Data/W/Basic.lean` supplies the paramorphism itself:
`WType.para`, obtained from `elim` at the product carrier so that no new
recursion is introduced, with its computation rule `WType.para_mk`, cited to
[Meertens1992].

`Geb/Mathlib/Computability/Cobham/` supplies the class, with `isRankedOf` and
`acceptTest` in `RankedTree.lean`.

This branch adds one lemma to `SelfDelim.lean` beside its two halves, one to
`Fold.lean` — that every value on the scan's stack is one the algebra
produced, which the restricted growth condition needs — and the arity-one
composition lemma `semAt_comp1Of` to `Bound.lean`, beside the rest of the
`semAt` family and beside the constructor branch's general-arity
`semAt_compOf`, which is a different statement. It drops the `private` marker
from `SelfDelim.lean`'s `take_succ_append_take_one`, so that the truncation
split this branch needs is derived from it rather than re-proved. It
also widens in place, rather than restating, the fold-scan lemmas of
`Variable.lean` whose existing forms are too narrow for `algCh`. The
potential argument is generalised: its growth condition is restricted to the
values the scan's stack holds, and each existing form is re-derived from its
generalisation, so nothing there is duplicated and no consumer changes. The
stack-reading lemmas gain forms tolerating a trailing remainder past the
entries, stated beside the existing totals rather than replacing them:
neither is an instance of the other, the remainder-bearing forms needing
`k ≤ st.length` where the totals are total, so both stand. The rest of the
work is new modules.

`Geb/Internal/Computability/CobhamFoldProto/` supplies the fold and its
primitives: `Term.fold`, `foldOut` with `foldOut_eq` in `Fold.lean`;
`foldOutExprV` with `foldOutSemV_eq` and `outWordV` in `Variable.lean`;
`potential_foldScanStep_le` there, the shape the linearity proof follows; and
in `SelfDelim.lean` the self-delimiting primitives `entryWord`,
`takeEntryOf`, `dropEntryOf`, `dropEntriesOf` and `entryOf`, with
`takeEntrySem_entryWord`, `dropEntrySem_entryWord`,
`takeEntrySem_replicate`, `dropEntrySem_replicate` and
`length_dropEntrySem_le`. `SmashFree.lean` supplies the smash-freeness
lemmas.

## Deliverables

### D4. The destructor's expressions

The block reader needs no dispatch: a constant unary prefix turns the word
into a self-delimiting entry whose payload is the leading block.

```text
codeOf R     = comp1Of takeEntryOf (prependOf (List.replicate R.width true ++ [false]) idOf)
dropCodeOf R = comp1Of dropEntryOf (prependOf (List.replicate R.width true ++ [false]) idOf)
```

with `stepWord (codeOf R) w = w.take R.width` and
`stepWord (dropCodeOf R) w = w.drop R.width`.

The children come from a second fold, at the delimited-children algebra:

```text
algCh R i f = entryWord ((List.ofFn fun d ↦ entryWord (dropEntrySem ![f d])).flatten)
                ++ (R.code i ++ (List.ofFn fun d ↦ dropEntrySem ![f d]).flatten)
```

whose value carries the children's spellings, each delimited, followed by the
term's own spelling. `childOf R j` is `entryOf j` of `takeEntryOf` of that
fold's output, and `algChOf` is the expression computing `algCh`.

Acceptance, for `t : R.Term`, `i : Fin R.card`, `ch : Fin (R.arity i) → R.Term`
and `j : ℕ`:

```text
dropEntrySem ![Term.fold R (algCh R) t] = R.spell t
takeEntrySem ![Term.fold R (algCh R) (Term.mk R i ch)]
  = (List.ofFn fun d ↦ entryWord (R.spell (ch d))).flatten
stepWord (codeOf R) (R.spell (Term.mk R i ch)) = R.code i
stepWord (childOf R j) (R.spell (Term.mk R i ch)) = R.spell (ch ⟨j, h⟩)
```

the last under `h : j < R.arity i`. `childOf` is total: at `j ≥ R.arity i`
`entryOf` runs past the entries and yields the empty word, which is a
statement to prove rather than a convention to assume.

`foldOutExprV`'s readout emits `outWordV`, which prefixes a presence marker.
The marker is absorbed into the entry's unary prefix rather than left beside
it, so one further bit is read from what follows the entry. Each equation is
therefore stated in the "entries followed by an arbitrary remainder" form,
which `takeEntrySem` at an `entryWord` tolerates, and the `j ≥ R.arity i` case
is proved against that extra bit rather than in its absence.

D4 carries the same four obligations as the constructor branch's `mkOf`, for
`algChOf`: its `semAt` lemma, the linearity hypothesis, a multiplier, and
smash-freeness from `smashFreeBool_entryWordOf`, `smashFreeBool_dropEntryOf`,
`smashFreeBool_concatCompOf`, `smashFreeBool_prependOf`,
`smashFreeBool_projOf`, `smashFreeBool_compOf`, `smashFreeBool_flattenOf`
and `smashFreeBool_comp1Of`, the last lifting the arity-one primitives into
an arity-`R.arity i` expression.

`algCh` does not meet the per-symbol growth condition, and not because
`dropEntrySem` fails to shrink: `length_dropEntrySem_le` bounds its result by
its argument. The reason is that `algCh` duplicates its children's payloads,
delimited and plain, so `|algCh R i f|` is bounded by a multiple of
`Σ_d |f d|` rather than by that sum plus a constant.
`stackSize_le_of_growth` therefore does not apply.

A multiplicative growth condition alone would not give the linearity
hypothesis either — a fold whose values multiply at every level is
exponential in depth. The proof goes through a property of `algCh`'s outputs:
every value `v` it produces satisfies
`5 * (dropEntrySem ![v]).length + 1 ≤ v.length + 4 * R.width`, which needs no
induction hypothesis, holding at arbitrary arguments and with equality at a
nullary symbol. A potential argument over it gives the bound, charging each
input bit at most the constant and so needing no assumption about how the
pending subterms are laid out. Read as a per-step growth constant in
`potential_foldScanStep_le`'s shape the same invariant gives
`4 * R.maxArity * R.width + R.maxArity + R.width + 1`, attained at a symbol of
maximum arity whose children are all nullary.

### D5. The inverse laws

The term-algebra half needs no new definition. `WType.toSigma` at `R.Term`
inhabits

```text
R.Term → Σ i : Fin R.card, (Fin (R.arity i) → R.Term)
```

and `WType.toSigma (Term.mk R i ch) = ⟨i, ch⟩` holds by `rfl`. That is the one
statement D5 adds at that layer, bridging `Term.mk`, which mathlib does not
know; the other law is `WType.ofSigma_toSigma`, cited rather than restated.

Its expression-layer counterparts are the content: that `mkOf` at the
children's spellings is the spelling of the constructed term, which is the
constructor branch's `semAt_mkOf` composed with `spell_mk`; that `codeOf` and
`childOf` recover the symbol and the children's spellings, which is D4; and
the round trip

```text
semAt (R.arity i) (mkOf R i).1.1 (mkOf R i).2
  (fun d ↦ stepWord (childOf R d) w) = w
```

under `R.parse w = some (Term.mk R i ch)`, with `i` given rather than read, so
no dispatch over the block is needed; a single expression destructing an
unknown symbol would need one, and is not a deliverable. It is stated under
that hypothesis rather than guarded, since `childOf` and `mkOf` are total and
return an unspecified word off the recognized language. A guarded total form
is available by composing `Cobham.isRankedOf`; the branch records it in
`TODO.md` rather than building it.

Under the preorder encoding the structure map is the identity on
representations, `spell_mk` stating that a symbol's block followed by its
children's spellings is the spelling of the term they build. The content of
the inverse laws is therefore that a valid word determines the symbol and the
children's spellings, which `parse_eq_some_iff` and `spell_injective` give
semantically; D4 supplies the expressions that compute them.

### D6. The paramorphism at this representation

`WType.para` already exists, so D6 introduces no recursion scheme. What it
adds is that scheme computed at the bitstring representation, by generalising
D4's algebra:

```text
algPara R phi i f = entryWord (phi i fun d ↦ (dropEntrySem ![f d], takeEntrySem ![f d]))
                     ++ (R.code i ++ (List.ofFn fun d ↦ dropEntrySem ![f d]).flatten)
```

at a step `phi i : (Fin (R.arity i) → List Bool × List Bool) → List Bool`.
Acceptance:

```text
dropEntrySem ![Term.fold R (algPara R phi) t] = R.spell t
takeEntrySem ![Term.fold R (algPara R phi) (Term.mk R i ch)]
  = phi i fun d ↦ (R.spell (ch d), takeEntrySem ![Term.fold R (algPara R phi) (ch d)])
takeEntrySem ![Term.fold R (algPara R phi) t]
  = WType.para (List Bool) (fun x ↦ phi x.1 fun d ↦ (R.spell (x.2 d).1, (x.2 d).2)) t
```

the third identifying the construction with `WType.para` at the step that
sees each child's spelling in place of the subtree. The fold is nevertheless
built at `List Bool` because `foldOutExprV` consumes a `Term.fold` at a
`List Bool` algebra, and because the step must see a spelling rather than a
subtree if it is to be an expression of the class.

`algCh` is the instance at the step returning the children's spellings, each
delimited:

```text
algCh R = algPara R (fun _ g ↦ (List.ofFn fun d ↦ entryWord (g d).1).flatten)
```

which holds by `rfl`, so D4's two laws are corollaries of D6's. The linearity
obligation is the one D4 and D6 do not share: `algCh`'s step has length
`2 * Σ_d |(g d).1| + R.arity i`, which no constant bounds in terms of
`Σ_d |(g d).2|`, so D4's proof runs through its own invariant. For a general
step the potential argument needs `|phi i g| ≤ (Σ_d |(g d).2|) + c_phi`, and
then `c = 2 * c_phi + R.width + 1`, attained at a nullary symbol. That
constant rests on
`2 * (takeEntrySem ![w]).length + (dropEntrySem ![w]).length ≤ w.length` at
arbitrary `w`, since the growth hypothesis quantifies over arbitrary
arguments rather than over fold values. `SelfDelim.lean` has the two halves
separately, so this branch adds the combination there as
`two_mul_length_takeEntrySem_add_length_dropEntrySem_le`, making the constant
unconditional. A step whose
values are merely bounded by the subterm's size does not suffice.

D6 is semantic at the expression layer: `algParaOf` exists only once a step's
own expression is given, so the branch delivers `algChOf` and leaves the
general expression to the caller. What it does deliver for that caller is the
constant above and the lemma it rests on, so no obligation is left implicit.

`TODO.md` § Deferred items from the tree recognizers records the paramorphism
"whose step receives a subterm's spelling, which the head-locality of the
state layout admits only at quadratic cost". `algPara` carries the spelling in
the fold's carrier rather than reading it from the state, so the head-locality
that estimate rests on does not bind. What the carrier costs is a value linear
in the subterm, which is unproved at a symbolic alphabet; nothing here
measures reduction steps, so D6 replaces the estimate's premise rather than
its arithmetic.

## Why the fold reaches a subterm's boundary

A fold that carried each subterm's length beside its payload, and whose
children's values carried theirs, would grow exponentially in the term's
depth: an entry is `2 * |u| + 1` bits. `algPara` avoids that by not nesting.
Each level reads only the spelling half of a child's value, discarding the
delimited half, so the value is linear in the subterm's size.

What the expression-layer construction requires is `foldOutExprV`'s `hsize`,
that the pending values' total stays linear in the input, and the per-symbol
growth condition is one sufficient route to it rather than the requirement.
`algCh` fails the growth condition; that it satisfies `hsize` is what D4 has
to prove.

## Transcription or novel

Under [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature when
transcribing:

- D5's term-algebra half is mathlib's `WType.toSigma` with its laws,
  instantiated at the alphabet's shape and direction families; nothing is
  defined for it here.
- The paramorphism is [Meertens1992], already transcribed in this repository
  as `WType.para`. D6 defines no recursion scheme; `algPara` and `ParaStep`
  are the encoding at which it is computed, and are novel.
- `algCh`, `algChOf`, `childSem`, `childOf`, `codeOf` and `dropCodeOf` are
  novel constructions. No source is claimed for them; the class is
  [Cobham1965], and the subalgebra membership they are checked against is the
  left-to-right inclusion of [Strahm2003] Theorem 1(2).

## What is verified and what is not

Established, as theorems or `#guard`s in
`GebTests/Internal/Computability/CobhamFoldProto/Boundary.lean`:

- `dropEntry_algPara` — the value's second half is the spelling, whatever the
  step, symbolically in the alphabet.
- `takeEntry_algPara` — the paramorphism's defining law, symbolically in the
  alphabet and the step.
- `algPara_eq_para` — that construction is `WType.para` at the spelling step,
  symbolically.
- `two_mul_length_takeEntrySem_add_length_dropEntrySem_le` — the bound the
  general paramorphism constant rests on, symbolically.
- `dropEntry_algCh` and `takeEntry_algCh` — those laws at the
  delimited-children instance, as corollaries.
- `binRanked.spell destSample` and `childSem` at `binRanked` — the sample's
  spelling, and both children of a term whose children differ.
- `valueBounded` at `binRanked` — the fold's value within six times the term's
  node count, on the samples exhibited.

Not established:

- the linearity hypothesis `hsize` for `algCh` at a symbolic alphabet, and so
  the constant, which the samples above bound only at `binRanked`;
- `codeOf` and `dropCodeOf` at a symbolic width;
- `childOf` at any `j` as an expression, and its semantic counterpart
  `childSem R j (Term.mk R i ch) = R.spell (ch ⟨j, h⟩)`, which follows from
  `takeEntry_algCh` and `stepWord_entryOf` but is exhibited only by two
  `#guard`s at `binRanked`;
- the totality case of D4, at `j ≥ R.arity i`;
- smash-freeness of any of D4's expressions;
- D5's `WType.toSigma (Term.mk R i ch) = ⟨i, ch⟩` and its three
  expression-layer statements.

## Risks

- `hsize` for `algCh` has no precedent of its own shape. It is a proof
  argument of `foldOutOfV`, so `childOf` cannot be defined until it is
  proved, and restricting to `binRanked` does not avoid it: the statement
  still quantifies over every word, with only the width and the maximum arity
  becoming literals. The fallback is D4 to D6 at the semantic layer alone,
  which `Boundary.lean` already exhibits, with the expression layer recorded
  in `TODO.md`.
- The expressions may not evaluate in budget, for the reason the constructor
  branch's design records, so no `#guard` against an expression's output word
  is a deliverable here either.
- `childOf j` reads the `j`-th entry of a value linear in the input, so the
  destructor's cost is a constant number of passes above the fold's. Nothing
  here measures reduction steps; this is an analysis under one cost model, as
  the modules it builds on record of their own subjects.

## References

- [Cobham1965] — the function algebra.
- [Meertens1992] — the paramorphism, as `WType.para` transcribes it.
- [Strahm2003] — the subalgebra, of which only the left-to-right inclusion of
  Theorem 1(2) is relied on; `docs/references.bib` records that the equality
  fails read literally.
- [docs/index.md](../../index.md) — the modules this design builds on.
- [TODO.md](../../../TODO.md) § The fold over recognized terms and § Deferred
  items from the tree recognizers — the obligations this design does not
  discharge, and the estimate D6 replaces.
