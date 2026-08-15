# The ranked term algebra's constructor in the fold's language — design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [What exists](#what-exists)
- [Deliverables](#deliverables)
  - [D1. The initial algebra's structure map, as a fold-algebra](#d1-the-initial-algebras-structure-map-as-a-fold-algebra)
  - [D2. Its expression, and its four obligations](#d2-its-expression-and-its-four-obligations)
  - [D3. The witness and the identity theorem](#d3-the-witness-and-the-identity-theorem)
- [Transcription or novel](#transcription-or-novel)
- [What is verified and what is not](#what-is-verified-and-what-is-not)
- [Risks](#risks)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope

`Geb/Internal/Computability/CobhamFoldProto/` computes a fold at an algebra
of a ranked alphabet as an expression of Cobham's class. This branch adds the
initial algebra's structure map: as a fold-algebra, as an expression, and as
the fold whose value is its own argument.

The destructor, the inverse laws and the paramorphism are a separate concern
and a separate branch, which depends on this one and delivers
`Geb/Internal/Computability/CobhamFoldProto/Destruct.lean`.

Work lands in `Geb/Internal/Computability/CobhamFoldProto/Initial.lean` with
its `docs/index.md` entry and its indexing-file line, except for the
composition lemma D2's arity recursion needs, which goes to `Bound.lean`
beside the rest of the `semAt` family, `SelfDelim.lean`'s `stepWord_compOf`
being re-proved as its arity-one case rather than left stating the same fact
twice. It adds no test module
of its own: its three statements are theorems rather than samples, and
§ Risks rules out the one evaluation a sample would carry. It does carry
`GebTests/Internal/Computability/CobhamFoldProto/Boundary.lean`, the
inherited evidence module named below, which the two branches dismantle
between them.
Every declaration is `Classical.choice`-free, which
`GebMeta.detectNonstandardAxiom` enforces through `lake lint` for `Geb` and
`lake lint -- GebTests` for the mirror.

This document is transient under
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape: the branch is
ordered spec and plan, then implementation, then their removal. The semantic
content this branch delivers is currently in
`GebTests/Internal/Computability/CobhamFoldProto/Boundary.lean`. The branch
moves `algMk`, `fold_algMk`, `length_algMk` and `foldOut_algMk` out of that
module into `Initial.lean`, leaving it building with its remaining half and
with `[GambinoHyland2004]` and the moved names dropped from its docstring;
the destructor branch removes what is left.

## What exists

`Geb/Mathlib/Data/Tree/Ranked/` supplies the term algebra and its encoding:
`Term.mk` with `Term.induction`; `code` with `length_code`; `spell`, defined
as `WType.elim` applied to a step concatenating a symbol's block with its
children's spellings, with `spell_mk` reading that step at a constructor; and
`parse` with `parse_eq_some_iff`.

`Geb/Mathlib/Computability/Cobham/` supplies the class: `COf`, `prependOf`
and `zeroAtOf` from `Basic.lean`. `RankedAlphabet.parseChildren`, in the
`Ranked/` directory named above, is the bare `Nat.rec` shape the arity
recursion follows.

`Geb/Internal/Computability/CobhamFoldProto/` supplies the fold:
`Term.fold` with `Term.fold_unique` and `foldOut` with `foldOut_eq` in
`Fold.lean`; `foldOutExprV` with `foldOutSemV_eq` in `Variable.lean`, whose
three obligations D2 supplies, with `smashFree_foldOutExprV` taking a fourth;
`stackSize_le_of_growth` bridging a per-symbol growth condition to the
linearity hypothesis; `concatCompOf`, `compOf` and `projOf` in `Bound.lean`;
and the smash-freeness lemmas in `SmashFree.lean`. `GebTests/Internal/Computability/CobhamFoldProto/Fold.lean`
holds `leafCountOf`, whose expression shape D2 generalises.

## Deliverables

### D1. The initial algebra's structure map, as a fold-algebra

```text
algMk R i f = R.code i ++ (List.ofFn f).flatten
```

at the carrier `List Bool`, whose elements are read as spellings. Acceptance:

```text
Term.fold R (algMk R) = R.spell
```

holds by `rfl`, `algMk` being `spell`'s own `WType.elim` step named apart from
it, so D1's content is that naming together with the equation rather than a
new computation. Factoring the step out of `spell` instead would touch the
merged `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` and is a separate concern.

`(List Bool, algMk R)` is not itself initial — the spellings are a proper
subalgebra of `List Bool` — so what the equation says is that `algMk` is the
initial algebra's structure map transported along the encoding, and that
`spell` is the unique morphism from the term algebra into it.

### D2. Its expression, and its four obligations

`mkOf R i : COf (R.arity i)`, computing `algMk R i`: a `prependOf` of the
symbol's block onto nested `concatCompOf` applications closed by `zeroAtOf`,
whose value is `R.code i ++ (f 0 ++ (f 1 ++ … ++ []))`. Because
`concatCompOf n a b` puts `b`'s value first, the nesting is in the first
argument; `leafCountOf` has that shape at a literal arity, and generalising it
needs a slot shift at each step, `compOf` composing the arity-`n` tail against
`fun i ↦ projOf (n + 1) i.succ`. It is built by `Nat.rec` on the arity, as
`parseChildren` is, so no `def` calls itself.

- `semAt_mkOf` — that `mkOf` computes `algMk`. The single unfolding step is
  definitional but the closed form is not, `List.ofFn_succ` itself not being
  `rfl`, so this is a `Nat.rec` lemma rather than an appeal to defeq.
- Growth at the constant `R.width`, exactly, discharging the linearity
  hypothesis by way of `stackSize_le_of_growth`.
- A multiplier with `2 * R.width + 2 ≤ mult`.
- Smash-freeness of `mkOf`, from `smashFreeBool_prependOf`,
  `smashFreeBool_concatCompOf`, `smashFreeBool_compOf`,
  `smashFreeBool_zeroAtOf` and `smashFreeBool_projOf`, which is
  `smashFree_foldOutExprV`'s hypothesis, together with the membership it
  gives: `smashFree_foldOutExprV` at `mkOf` and `algMk`, placing the fold
  expression in the subalgebra [Strahm2003] Theorem 1(2) contains in the
  functions computable simultaneously in polynomial time and linear space.

### D3. The witness and the identity theorem

At the semantic layer, from `foldOut_eq` and `parse_eq_some_iff`:

```text
foldOut R (algMk R) w = (R.parse w).map (fun _ ↦ w)
```

At the expression layer, `foldOutExprV` at `mkOf` and `algMk`, with its output
word characterised for every word:

```text
foldOutSemV R (mkOf R) (algMk R) semAt_mkOf mult R.width hsize hmult ![w]
  = outWordV (R.parse w |>.map fun _ ↦ w)
```

which follows from `foldOutSemV_eq` and the semantic equation without
evaluating the expression. `TODO.md` § The fold over recognized terms records
that "no expression's output word has been computed from an input word"; this
characterises the output word symbolically instead, and `TODO.md` is amended
to say so rather than treated as discharged.

The witness joins the leaf-counting algebra rather than replacing it. The leaf
count checks a computed value against a sample; the identity checks that an
algebra rebuilding its argument is carried without loss, which an algebra
discarding structure does not check.

## Transcription or novel

Under [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature when
transcribing:

- `algMk` is the initial algebra's structure map for a polynomial functor,
  standard for W-types, transported along an encoding; the formulation
  instantiates the initiality `Term.fold_unique` already carries, for which
  [GambinoHyland2004] is the reference in use.
- `mkOf`, the expression computing it, is a novel construction. No source is
  claimed for it; the class is [Cobham1965], and the subalgebra membership it
  is checked against is the left-to-right inclusion of [Strahm2003]
  Theorem 1(2).
- The identity theorem is a corollary of that initiality with the existing
  retraction `parse_eq_some_iff`; novel only as a statement about this
  encoding.

## What is verified and what is not

Established, as theorems in
`GebTests/Internal/Computability/CobhamFoldProto/Boundary.lean`:

- `fold_algMk` — `Term.fold R (algMk R) = R.spell` by `rfl`, symbolically.
- `length_algMk` — `algMk` lengthens by exactly `R.width`, symbolically.
- `foldOut_algMk` — the identity theorem, symbolically.

Not established:

- `semAt_mkOf` at a symbolic arity;
- the smash-freeness of `mkOf`, and the subalgebra membership it gives;
- D3's expression-layer equation.

## Risks

- The expressions may not evaluate in budget. `readoutWidthV binRanked = 6`,
  so the readout's dispatch has `2 ^ 6` branches, and `casesRaw` normal forms
  grow about threefold per dispatch bit; an evaluation of the readout at a
  one-entry state did not return within four minutes. D3's criterion is stated
  symbolically for that reason, and no `#guard` against an expression's output
  word is a deliverable.
- `semAt_mkOf` at a symbolic arity rests on a `Nat.rec` over a family of
  expressions. The fallback is to state it at literal arities, as
  `leafCountOf` does, which weakens D2 to the alphabets exhibited.

## References

- [Cobham1965] — the function algebra.
- [Strahm2003] — the subalgebra, of which only the left-to-right inclusion of
  Theorem 1(2) is relied on; `docs/references.bib` records that the equality
  fails read literally.
- [GambinoHyland2004] — the initiality `Term.fold_unique` instantiates.
- [docs/index.md](../../index.md) — the modules this design builds on.
- [TODO.md](../../../TODO.md) § The fold over recognized terms — the
  obligations this design does not discharge.
