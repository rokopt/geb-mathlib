# Bellantoni-Cook syntax and semantics — design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [Sources](#sources)
  - [Per-definition classification](#per-definition-classification)
  - [Deviation 1: the class is the reformulation, not the original](#deviation-1-the-class-is-the-reformulation-not-the-original)
  - [Deviation 2: `cond` argument order](#deviation-2-cond-argument-order)
  - [Deviation 3: the syntax is a slice W-type](#deviation-3-the-syntax-is-a-slice-w-type)
  - [Deviation 4: shapes carry the composition arities](#deviation-4-shapes-carry-the-composition-arities)
  - [Deviation 5: environments as functions](#deviation-5-environments-as-functions)
  - [Deviation 6: names](#deviation-6-names)
  - [The paper's `mult` is ill-formed as printed](#the-papers-mult-is-ill-formed-as-printed)
  - [Licence](#licence)
- [Design](#design)
  - [Alternatives considered](#alternatives-considered)
  - [Placement and file manifest](#placement-and-file-manifest)
  - [The index and the signature](#the-index-and-the-signature)
  - [The syntax](#the-syntax)
  - [Finiteness and decidable admissibility](#finiteness-and-decidable-admissibility)
  - [The semantics](#the-semantics)
  - [Exposure](#exposure)
  - [Reuse](#reuse)
- [Verification evidence](#verification-evidence)
- [Tests](#tests)
- [Documentation](#documentation)
- [Non-goals](#non-goals)
- [Deferred](#deferred)
- [Constraints](#constraints)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Purpose

Define in Lean the syntax of the function class `B` of
[HeraudNowak2011] § 3.2 and its interpretation.

The consumer is the translation to Cobham's class (Theorems 1
and 2), which is what makes `B` a characterization of the
polynomial-time functions. It is § Deferred item 3, and this branch
adds it to `TODO.md` together with the two items it depends on and
the four triggers of § Deferred. That consumer is the whole
justification under CONTRIBUTING.md § Code is cost; the syntax and
the semantics are the definitions its statement quantifies over,
and nothing already in the tree consumes them.

## Sources

The paper is Sylvain Héraud and David Nowak, *A Formalization of
Polytime Functions*, arXiv:1102.5495 (v2, 31 May 2011). A short
version appeared as ITP 2011, LNCS 6898, pp. 119-134,
`doi:10.1007/978-3-642-22863-6_11`. Every section and page number
here is the arXiv version's, which is the source of record; the
short version is not established to carry the same numbering.

The reference implementation is the Coq development
`github.com/davidnowak/bellantonicook` (opam
`coq-bellantonicook`), at commit
`1f03b9296104646ddc2b2b4b12e35a6619c17a99` (2018-09-13). Every
line number below is that revision's.
`src/BellantoniCook/BC.v` carries the syntax (12-19), the arity
apparatus (`Inductive Arities` 85-89, `aeq` 91-95,
`Fixpoint arities` 115-143, `arities2` 145-149), and the semantics
(`sem_rec` 380-386, `sem` 388-422).

### Per-definition classification

CONTRIBUTING.md § Cite the literature when transcribing requires
each definition to be marked transcription or novel.

| Definition | Classification |
| --- | --- |
| the seven constructor forms of `B` | transcription, § 3.2 |
| the arity relation `A` | transcription, § 3.2 |
| every semantic clause | transcription, § 3.2 (with Deviation 2) |
| `plus`, `mult` and their subterms `plusStep`, `multBase`, `multStep` (test module) | transcription, § 3.2, corrected per § The paper's `mult` is ill-formed as printed |
| `Shape`, `Direction`, `rc`, `q`, `sig` | novel |
| `BC`, `BC.arity`, `BCOf` | novel |
| `Sem`, `transport`, `evalRec`, `evalValue`, `evalStep`, `BC.eval` | novel realisations of the transcribed clauses |
| `finEnumFin`, `finEnumCompDirection`, `sigFinitary` | novel |
| `compChildren`, `branchRec`, `badRaw`, `plusOf`, `multOf`, the `Raw` bindings and the four leaf terms `predTerm`, `condTerm`, `projNTerm`, `projSTerm` (test module) | novel |

### Deviation 1: the class is the reformulation, not the original

The class defined here is not Bellantoni and Cook's. Paper p. 6:

> Reader may have noticed that our definition of Bellantoni-Cook's
> class is slightly different from the one in [6]. First, here the
> conditional `cond` distinguishes between three cases (empty, even
> or odd bitstrings), whereas in [6] the empty bitstring is treated
> as an even one. Second, here the base case for recursion is the
> empty bitstring, whereas in [6] it is any bitstring whose
> interpretation as a positive integer is 0 …

Both differences are realised here: `cond` takes four safe
arguments and branches three ways, where the original branches two
ways on parity; and `evalRec`'s base clause is `[] ↦ g`, where the
original's is every zero-valued bitstring. The module docstring
states this and cites [HeraudNowak2011] and [BellantoniCook1992].

### Deviation 2: `cond` argument order

The paper and its reference implementation disagree. Paper § 3.2
gives `cond(; ε, x, y, z) = x`, `cond(; w0, x, y, z) = y`,
`cond(; w1, x, y, z) = z` — even selects the third safe argument,
odd the fourth. `BC.v:399-404` matches on the first of four safe
arguments and gives `| nil ↦ b`, `| true :: _ ↦ c`,
`| false :: _ ↦ d` — odd selects the third, even the fourth.

This design follows the reference implementation. Rationale: the
implementation is the artifact against which the paper's theorems
were machine-checked, so its clause is the one the published
results certify; the paper's prose carries no corresponding check.
The implementation corroborates its own reading at `BC.v:455-457`,
where `cond_simpl_true` takes the hypothesis
`hd false (sem fc l1 l2) = true` and concludes with the third safe
argument. The module docstring records the discrepancy.

The bit tested is the least significant: `Bitstring.v:50-55` gives
`bs2nat (false :: v') = 2 * bs2nat v'` and
`bs2nat (true :: v') = S (2 * bs2nat v')`, so the list head is the
low bit and the paper's `w0` is `false :: w`.

### Deviation 3: the syntax is a slice W-type

The Coq syntax is an untyped `Inductive BC` whose well-formedness
is carried by a separate `arities` function, with a semantics total
on ill-formed terms: an out-of-range projection yields the empty
bitstring, and `cond` carries three further clauses for safe
environments shorter than four (`BC.v:405-416`).

Here the arity pair is an index. `docs/rules/lean-coding.md`
§ Recursion and induction through recursors forbids a
self-referential `inductive` and a self-calling `def`, so the
indexed syntax is the slice W-type of a signature functor over
`ℕ × ℕ` and the semantics is one application of its eliminator.
Consequences:

- Only terms satisfying the arity relation inhabit `BCOf n s`, so
  the reference implementation's default values are unreachable.
- The four hand-written induction principles of the reference
  implementation (`BC_ind2'` 21-57, `BC_ind2` 59-77,
  `BC_ind_inf'` 207-335, `BC_ind_inf` 337-367 — 216 lines) are
  replaced by `SlicePFunctor.W.elim` and
  `SlicePFunctor.W.induction`. Two reasons are given for them in
  the source: `BC.v:8-9`, that Coq's generated recursor ignores the
  `list BC` fields of `comp`, covers the first two; `BC.v:377`,
  that `BC_ind_inf` "makes easier dealing with arities in inductive
  proofs", covers the other two.
- The arity function is not ported as a term-level checker, so the
  paper's "polytime checker" reading is not delivered.
  `SlicePFunctor.decidableWValid` makes admissibility of a raw tree
  decidable, so a checker is recoverable from what is already here.
  Deferred.

The paper's `B_inf` (§ 3.2, final two paragraphs, running onto
p. 8; `BCI.v:4-12`) replaces the single projection with `projIn`
and `projIs` and drops the arity annotations from `proj` and
`comp`. It is not ported.

### Deviation 4: shapes carry the composition arities

`Shape.comp` carries `n s m k` where the paper's `comp^{n,s}`
carries two superscripts. In the paper `m` and `k` are determined
by `|gN|`, `|gS|` and `A(h)`; here they must appear in the shape,
because `Direction` is a function of the shape alone and the number
of subterms depends on them. The correspondence is bijective on
well-formed terms: a term of `sig.W` with root shape
`comp n s m k` has exactly `m` normal and `k` safe argument
subterms, and its head subterm has arity `(m, k)`.

### Deviation 5: environments as functions

The Coq semantics takes two `list bs` and indexes them with `nth`,
defaulting to the empty bitstring. Here an environment is a
function `Fin n → List Bool`, total by construction, and the
semantics uses `Fin.append`, `Fin.cons` and `Fin.tail`.

### Deviation 6: names

`rec` cannot name a `Shape` constructor: `Shape.rec` is the
generated recursor (`inductive Foo | a | rec` fails
with `(kernel) constant has already been declared 'Foo.rec'`). The
shape is `safeRec`, after the standard term for the scheme; the
paper writes `rec`, Bellantoni and Cook "predicative recursion on
notation". `comp` keeps the paper's name.

The semantics is `eval`, after mathlib's `Nat.Partrec.Code.eval`,
so that `e.eval` is available for `e : BC`.

### The paper's `mult` is ill-formed as printed

Page 7 prints
`mult := rec (comp^{1,0} O ⟨⟩ ⟨⟩) (comp^{1,2} plus ⟨π₁^{2,0}⟩ ⟨π₂^{2,1}⟩) (…)`
with `A(mult) = (2, 0)`. The recursion rule of p. 6 forces
`A(h_i) = (2, 1)`, so the superscripts must be `comp^{2,1}`; the
arguments confirm it independently, since `π₁^{2,0}` forces `n = 2`
and `π₂^{2,1}` forces `s = 1`. The reference implementation has
`comp^{2,1}`: `BCUnary.v:233` reads
`comp 2 1 plus_e ((proj 2 0 1) :: nil) ((proj 2 1 2) :: nil)`.
The printed step superscript coincides with `plus`'s, where
`comp^{1,2}` is correct. The printed base superscript
`comp^{1,0}` has no counterpart in `plus` and is correct as
printed.

Under this design a literal transcription of the printed term
fails `decide`: `Shape.comp 1 2 1 1` requires its normal-argument
subterm at index `(1, 0)`, while `proj 2 0 1` carries `(2, 0)`.
§ Tests transcribes the reference implementation's arities.

### Licence

The reference development ships the CeCILL Free Software Licence
Agreement v2.1, though its README and opam metadata both name
CeCILL-A. Either way it is copyleft, and this repository is
Apache-2.0. No code is taken from it: the definitions are
transcribed from the paper, and Deviation 2 quotes three match arms
of `BC.v` as evidence for a factual claim about the two sources.
The development is catalogued in `docs/references.md`, which is
where the repository records external library pointers; no
attribution notice is added to the module.

## Design

### Alternatives considered

**A `Geb/Cslib/` module over mathlib's `WType`,** targeting CSLib
instead. `Geb/Cslib/` may not import `Geb.Mathlib.*`
(`docs/rules/upstream-eligible.md:127`), so this route cannot use
the slice W-type: `WType` is unindexed, and the
index-and-admissibility fold (`Slice/W.lean:188-190`, itself a
`WType.elim`) and its decidability (`Slice/Decidable.lean:128`)
would be restated for this signature — perhaps 40 to 60 lines,
since only one signature is involved, not the 413-line general
`Slice/W.lean`. The arity relation would become a predicate to
reason about rather than the maps `q` and `rc`, and the checker of
§ Deviation 3 would be built rather than instantiated. Both routes are
upstream-eligible, so the choice is not between upstreaming and
not.

The slice-W route is chosen on those two grounds — it restates
nothing, and it makes the arity relation data, the maps `q` and
`rc`, rather than a predicate, which is what § Deviation 3's
`BCOf` and the deferred checker rest on. Its own overhead is the
`@[expose]` discipline, the `@[reducible]` calibration recorded
below, and two `FinEnum` instances existing only to feed
`decidableWValid`, which is the smaller of the two. The subtree,
and with it the upstream target, follows from that choice rather
than preceding it: the slice W-type is `Geb.Mathlib.*`, which only
`Geb/Mathlib/` may import.

**A uniform `Fin` `Direction`,** taking `Fin (1 + (m + k))` for
`comp` and splitting it with `Fin.cases` and `Fin.addCases`. That
leaves one `FinEnum` obligation instead of two, and lets every test
term's children be written with `![…]`. Against it: `rc` and
`evalValue`'s `comp` clause become index arithmetic rather than
case distinctions on a sum. The sum is kept, and § Tests pays the
cost with one `compChildren` helper.

### Placement and file manifest

| Path | Change |
| --- | --- |
| `docs/superpowers/specs/2026-08-04-bellantoni-cook-design.md` | this spec; added, then removed |
| `docs/superpowers/plans/…` | the plan; added, then removed |
| `Geb/Mathlib.lean` | one `public import` added, in the form of `:8-10` |
| `Geb/Mathlib/Computability.lean` | new; the directory index, titled `# Computability — index` after `Geb/Mathlib/Data.lean` (a title naming `Geb.Mathlib.` would fail `scripts/lint-imports.sh`'s self-prefix check) |
| `Geb/Mathlib/Computability/BellantoniCook.lean` | new; the content |
| `GebTests/Mathlib.lean` | one import added, matching that file's existing form |
| `GebTests/Mathlib/Computability.lean` | new; the test directory index, titled `# Computability tests — index` after `GebTests/Mathlib/Data.lean` |
| `GebTests/Mathlib/Computability/BellantoniCook.lean` | new; the tests |
| `docs/references.bib` | two entries added |
| `docs/references.md` | one pointer added |
| `docs/index.md` | one bullet added |
| `TODO.md` | one subsection added, plus four trigger entries; its doctoc TOC re-run in the same commit |

Commit order: the spec, then the plan, then the library module,
then the test module, then the documentation, then a final commit
removing the spec and the plan (CONTRIBUTING.md § Concern shape).

The subtree is `Geb/Mathlib/`, whose allowed imports are
`Mathlib.*`, `Batteries.*` and `Geb.Mathlib.*`
(`docs/rules/upstream-eligible.md` § Subtree import rules;
`scripts/lint-imports.sh:179-180`). The design's only non-mathlib
import, `Geb.Mathlib.Data.PFunctor.Slice.*`, is a `Geb.Mathlib.*`
module, so the placement is legal with no rule change and the
module stays upstream-eligible. `Geb/Cslib/` is excluded: it may
not import `Geb.Mathlib.*` at all
(`docs/rules/upstream-eligible.md:127`), CSLib PRs having no access
to unupstreamed mathlib-targeted content.

The upstream target is mathlib4. `Mathlib/Computability/` already
carries this artifact's construction: `Nat.Partrec.Code`
(`Mathlib/Computability/PartrecCode.lean:76`, `eval` at `:464`) is
a deep-embedded syntax with an `eval`, as `BC` and `BC.eval` are,
and `Nat.Primrec` and `Nat.Partrec` are the recursion-theoretic
material `B` sits beside. CSLib has a claim too —
`Cslib/Computability/README.md` names "complexity classes" in its
scope, where mathlib's complexity content is confined to
machine-model resource bounds (`TM2ComputableInPolyTime` and
relatives, in `TuringMachine/Computable.lean`). It is not taken,
because § Alternatives considered chooses the slice-W encoding on
technical grounds and only `Geb/Mathlib/` can host it. Were the
encoding ever revisited, the target would be open again.

`scripts/extract-pr.sh:52-62` maps `Geb/Mathlib/*` to `Mathlib/`
and so extracts this module correctly. Its own comment records
that the mapping is an over-approximation for modules targeting
Lean core or Batteries; that reservation does not reach this one.

Under § Floodgate test the branch stays ready to ship
dependency-ordered PRs: `B` ships after
`Geb/Mathlib/Data/PFunctor/Slice/`. That is ordinary here — 45
non-index modules under `Geb/Mathlib/` already import
`Geb.Mathlib.*` siblings, 24 of them from another directory, as
`CategoryTheory/FinSetSkel/Quotient.lean:8-11` does.

`Geb/Mathlib/Computability.lean` and its test counterpart are
directory index files, one per directory as the subtree's existing
`Data.lean`, `CategoryTheory.lean` and `Logic.lean` are. The
content is one module: this workstream states no lemmas, so nothing
separates a `Defs`/`Basic` split.

All library declarations sit in `namespace BellantoniCook` — a
top-level namespace in mathlib's manner (`Turing`, `Language`), and
carrying no `Geb.Mathlib.` self-prefix, which
`docs/rules/upstream-eligible.md` forbids in namespace
declarations. `arity` and `eval` are written inside that namespace
as `def BC.arity` and `def BC.eval`, so that `e.arity` and `e.eval`
resolve for `e : BC`.

Bitstrings are `List Bool` written directly. mathlib offers no
other carrier: `BitVec n` is fixed-width, `Nat.bits` cannot
distinguish
`0` from `00` (the paper's stated reason for leaving positive
integers), `FreeMonoid Bool` is `List Bool` plus unwanted
structure, and `Mathlib/Computability/Encoding.lean:94` itself uses
`List Bool`.

### The index and the signature

The index is `I := ℕ × ℕ`, the pair of normal and safe arities. All
four universe parameters are `0` and no universe annotation is
needed.

    inductive Shape
      | zero
      | proj (n s : ℕ) (i : Fin (n + s))
      | succ (b : Bool)
      | pred
      | cond
      | safeRec (n s : ℕ)
      | comp (n s m k : ℕ)

    @[expose, reducible] def Direction : Shape → Type
      | .zero => Fin 0
      | .proj _ _ _ => Fin 0
      | .succ _ => Fin 0
      | .pred => Fin 0
      | .cond => Fin 0
      | .safeRec _ _ => Fin 3
      | .comp _ _ m k => Unit ⊕ Fin m ⊕ Fin k

    @[expose, reducible] def rc : (a : Shape) → Direction a → ℕ × ℕ
      | .zero, i => i.elim0
      | .proj _ _ _, i => i.elim0
      | .succ _, i => i.elim0
      | .pred, i => i.elim0
      | .cond, i => i.elim0
      | .safeRec n s, ⟨0, _⟩ => (n, s)
      | .safeRec n s, _ => (n + 1, s + 1)
      | .comp _ _ m k, .inl () => (m, k)
      | .comp n _ _ _, .inr (.inl _) => (n, 0)
      | .comp n s _ _, .inr (.inr _) => (n, s)

    @[expose, reducible] def q : Shape → ℕ × ℕ
      | .zero => (0, 0)
      | .proj n s _ => (n, s)
      | .succ _ => (0, 1)
      | .pred => (0, 1)
      | .cond => (0, 4)
      | .safeRec n s => (n + 1, s)
      | .comp n s _ _ => (n, s)

    @[expose] def sig : SlicePFunctor (ℕ × ℕ) (ℕ × ℕ) where
      A := Shape
      B := Direction
      r := fun x ↦ rc x.1 x.2
      q := q

`Shape` is non-recursive — no field mentions `Shape` — so
§ Recursion and induction through recursors does not reach it: the
rule's subject is self-reference, which `sig.W` carries, and a
non-recursive `inductive` is exactly the shape set `A` of a
`PFunctor`. `GebTests/Mathlib/Data/PFunctor/Presheaf/Fixtures.lean:129-134`
declares `inductive Shp` in the same role, with a hand-written
choice-free `FinEnum Shp` at 137.

`Shape` carries no `deriving` clause. § Structure and typeclass
patterns' standard derivations would all apply — its fields are
`ℕ`, `Bool` and `Fin` — but nothing here consumes them, and
`DecidableEq`/`Repr` for `BC` are § Deferred item 6, which is where
a derivation on `Shape` would be introduced alongside its lift.

`q` is the paper's arity relation read as a function of the shape
and `rc` is its hypotheses. `rc`'s `safeRec` clauses match
`Fin.mk 0` first, so direction `0` is `g` and directions `1` and
`2` are `h₀` and `h₁`. `comp`'s `inr (inl i) ↦ (n, 0)` is the
paper's "the functions in `gN` only have access to normal
variables"; `safeRec`'s directions `1` and `2` at `(n+1, s+1)` are
its `n_h = n_g + 1`, `s_h = s_g + 1`.

`Direction`, `rc` and `q` carry `@[reducible]`, not
`@[implicit_reducible]`. Measured: with `implicit_reducible` every
numeral in § The semantics fails, thirteen errors of the form
`failed to synthesize instance of type class OfNat (Fin (q
(Shape.succ b)).2) 0`; `implicit_reducible` governs unification at
implicit transparency inside dependent types, which is what
`Slice/Basic.lean:83-87` documents it for, whereas `OfNat`
synthesis needs `reducible`. With `@[expose, reducible]` every
clause elaborates with no binder ascriptions.

### The syntax

    @[expose] def BC : Type := sig.W
    @[expose] def BC.arity : BC → ℕ × ℕ := sig.wIndex
    @[expose] def BCOf (n s : ℕ) : Type := { e : BC // e.arity = (n, s) }

`sig.W` is the admissibility subtype of `sig.toPFunctor.W`
(`Geb/Mathlib/Data/PFunctor/Slice/W.lean:221`), so a term of `BC`
is a raw tree together with a proof that every node's children
carry the indices `rc` prescribes. `BCOf n s` is the type of
expressions `e` with `A(e) = (n, s)`: it is what makes the arity
relation of § 3.2 a type rather than a side condition, and it is
what § Deferred item 3 quantifies over — Theorem 1 reads "for all
`f` in `B` with well defined arities `A(f)`, there exists `f'` in
`C` such that …", which is a statement about arity-indexed terms.
It is also what the deferred checker returns.

### Finiteness and decidable admissibility

`SlicePFunctor.decidableWValid`
(`Geb/Mathlib/Data/PFunctor/Slice/Decidable.lean:128`) requires
`DecidableEq I`, free for `ℕ × ℕ`, and `sig.toPFunctor.Finitary`,
which is `∀ a, FinEnum (sig.toPFunctor.B a)`
(`Geb/Mathlib/Data/PFunctor/Univariate/Finitary.lean:38`).

The mathlib `FinEnum` instances this signature would resolve
through depend on `Classical.choice` — measured for `Fin n`, for
`PEmpty` and for sums, and `TODO.md:363-366` records the same for
`FinEnum.fin` and `ULift.instFinEnum`. Resolving `sigFinitary`
through them taints the module and fails `lake lint`, whose
permitted set is `standardAxioms = {propext, Quot.sound}`
(`GebMeta.lean:46-49`, checked by `detectNonstandardAxiom` at
`:113`; run by `scripts/pre-push.sh:30,39`). Two named choice-free
instances are supplied, following `Fixtures.lean:137`:

    scoped instance finEnumFin (n : ℕ) :
        FinEnum (Fin n) where
      card := n
      equiv := Equiv.refl _
      decEq := inferInstance

    scoped instance finEnumCompDirection (m k : ℕ) :
        FinEnum (Unit ⊕ Fin m ⊕ Fin k) where
      card := 1 + (m + k)
      equiv := (Equiv.sumCongr finOneEquiv.symm finSumFinEquiv).trans finSumFinEquiv
      decEq := inferInstance

    instance sigFinitary : sig.toPFunctor.Finitary
      | .zero => inferInstanceAs (FinEnum (Fin 0))
      | .proj _ _ _ => inferInstanceAs (FinEnum (Fin 0))
      | .succ _ => inferInstanceAs (FinEnum (Fin 0))
      | .pred => inferInstanceAs (FinEnum (Fin 0))
      | .cond => inferInstanceAs (FinEnum (Fin 0))
      | .safeRec _ _ => inferInstanceAs (FinEnum (Fin 3))
      | .comp _ _ m k => inferInstanceAs (FinEnum (Unit ⊕ Fin m ⊕ Fin k))

Four points, each measured:

- `finEnumFin` and `finEnumCompDirection` are `scoped`. A bare
  `instance` in the module's `public section` is global, and
  `Geb.lean` re-exports `Geb.Mathlib`, so `finEnumFin` would
  compete with `FinEnum.fin` at the same head symbol across the
  repository: measured, `#synth FinEnum (Fin 3)` in a module
  importing `Geb` returns `BellantoniCook.finEnumFin 3` when the
  instance is bare and `FinEnum.fin` when it is `scoped`.
  `Geb/Mathlib/CategoryTheory/FinCat/Decidable.lean:70` uses
  `scoped instance` against the same pressure. Scoping costs the
  test module nothing: `sigFinitary`'s branches resolve them by
  `inferInstanceAs` from inside their own namespace, where they are
  in scope and win on declaration order.
- `sigFinitary` is an `instance`, not a `def`: as a `def` it does
  not fire for `decidableWValid`, and it draws `Definition … of
  class type is semireducible`, fatal under `weak.warningAsError`.
  As an `instance` it needs no attribute;
  `GebTests/Mathlib/Data/PFunctor/Slice/Decidable.lean:49` declares
  the analogous `finitaryTestSlice` bare.
- The branches are `inferInstanceAs`, not `inferInstance`: instance
  search stops at reducible transparency on the projection
  `sig.B a`, so a bare `inferInstance` reports
  `failed to synthesize instance of type class FinEnum (sig.B
  Shape.zero)`.
  `GebTests/Mathlib/Data/PFunctor/Slice/Decidable.lean:46-48`
  records the same for `decEq`, and does so where the signature is
  an `abbrev`, so the cause is the projection, not `sig` being a
  `def`.
- `finEnumFin` is built as a cardinality with `Equiv.refl`, the
  construction `TODO.md` § PRA functors over finite-specification
  base categories anticipates; `Geb/Mathlib/Data/FinEnum.lean:18-22`
  documents the explicit-supply mitigation, available because the
  instances are named. A trigger records that they move to
  `Geb/Mathlib/Data/FinEnum.lean` when a second consumer appears;
  moving them now would put a second concern on this branch.

`finOneEquiv` is `Mathlib/Logic/Equiv/Defs.lean:907` and
`finSumFinEquiv` is `Mathlib/Logic/Equiv/Fin/Basic.lean:228`.

### The semantics

    @[expose] def Sem : ℕ × ℕ → Type :=
      fun i ↦ (Fin i.1 → List Bool) → (Fin i.2 → List Bool) → List Bool

    @[expose] def transport {i j : ℕ × ℕ} (h : i = j) (v : Sem i) : Sem j := h ▸ v

`transport` is named rather than written inline: `evalValue` uses
it six times, and a named function fixes the motive of `▸` once
instead of leaving it to be inferred at each site.

The recursion on the bitstring `safeRec` consumes is `List.rec`, an
auto-generated recursor and so permitted:

    @[expose] def evalRec {n s : ℕ} (g : Sem (n, s))
        (h₀ h₁ : Sem (n + 1, s + 1)) : List Bool → Sem (n, s) :=
      List.rec g (fun b v ih x y ↦
        (if b then h₁ else h₀) (Fin.cons v x) (Fin.cons (ih x y) y))

`[] ↦ g` is Deviation 1's base case; `h₁` on `true` and `h₀` on
`false` is `BC.v:383-385`; the tail `v` becomes the new first
normal argument and the recursive value enters `h_b` in safe
position as `Fin.cons (ih x y) y`.

The algebra is an auxiliary taking the compatibility hypothesis
pointwise, because the `Shape` match must generalize it:

    @[expose] def evalValue : (a : Shape) → (c : Direction a → Σ i, Sem i) →
        (∀ b, (c b).1 = rc a b) → Sem (q a)
      | .zero, _, _ => fun _ _ ↦ []
      | .proj _ _ i, _, _ => fun x y ↦ Fin.append x y i
      | .succ b, _, _ => fun _ y ↦ b :: y 0
      | .pred, _, _ => fun _ y ↦ (y 0).tail
      | .cond, _, _ => fun _ y ↦
          match y 0 with
          | [] => y 1
          | true :: _ => y 2
          | false :: _ => y 3
      | .safeRec _ _, c, h => fun x y ↦
          evalRec (transport (h 0) (c 0).2) (transport (h 1) (c 1).2)
            (transport (h 2) (c 2).2) (x 0) (Fin.tail x) y
      | .comp _ _ _ _, c, h => fun x y ↦
          transport (h (.inl ())) (c (.inl ())).2
            (fun i ↦ transport (h (.inr (.inl i))) (c (.inr (.inl i))).2 x Fin.elim0)
            (fun j ↦ transport (h (.inr (.inr j))) (c (.inr (.inr j))).2 x y)

    @[expose] def evalStep :
        sig.toSliceDomPFunctor.Obj (Sigma.fst (β := Sem)) → Σ i, Sem i :=
      fun z ↦ ⟨sig.q z.1.1,
        evalValue z.1.1 z.1.2
          ((sig.toSliceDomPFunctor.compatible_iff _ z.1.1 z.1.2).mp z.2)⟩

    @[expose] def BC.eval : BC → Σ i, Sem i :=
      SlicePFunctor.W.elim sig (Σ i, Sem i) (Sigma.fst (β := Sem)) evalStep rfl

`cond`'s indexing is `y 0` the tested bitstring, `y 1` the empty
case, `y 2` the odd case and `y 3` the even case — Deviation 2's
ordering. `comp`'s head child has arity `(m, k)` and is applied to
the normal arguments' values, each evaluated in the empty safe
environment `Fin.elim0`, and to the safe arguments' values.

Returning `sig.q z.1.1` as `evalStep`'s first component makes the
eliminator's coherence obligation
`Sigma.fst ∘ evalStep = sig.obj Sigma.fst` hold by `rfl`. Note
`SlicePFunctor.W.elim sig …`, not `sig.W.elim …`: `sig.W` is a
type, not a term, so field notation does not chain through it.

For `e : BCOf n s`, `e.property` rewrites the index of
`BC.eval e.val` to `(n, s)`; `SlicePFunctor.W.comp_elim`
(`W.lean:352`) is the lemma that the value's index is the tree's.

### Exposure

The library module opens a `public section`, and the thirteen
declarations shown above with `@[expose]` carry it — every one
except `Shape` and the three instances, which do not need it —
following
`Geb/Mathlib/Data/PFunctor/Slice/W.lean:132` and the rationale at
`:118`. The test module reduces `BC.eval` applications by `rfl`
across the module boundary, which needs the bodies of `BC.eval`,
`evalStep`, `evalValue`, `evalRec` and `transport`, and discharges
`sig.WValid` by `decide`, which needs `rc`. `sigFinitary` is
resolved by instance search rather than unfolded, so it needs no
`@[expose]`; measured, the tests succeed with all three instances
unexposed.

The test module uses plain `import` and
`set_option linter.privateModule false`, following
`GebTests/Mathlib/Data/PFunctor/Slice/W.lean:25`. It opens
`BellantoniCook` for unqualified access to `sig`, `BC`, `BCOf` and
`BC.eval`. The `scoped` instances come into scope with it, but
nothing needs them to: `sigFinitary` names them from inside their
own namespace. Measured: the tests' `decide` and `rfl` both succeed with the
three instances unexposed and with no `open` at all.

### Reuse

| Coq | here |
| --- | --- |
| `if leb (S j) n then nth j vnl nil else nth (j-n) vsl nil` | `Fin.append x y i` |
| `v' :: vnl` / `tail vnl` / `nil` | `Fin.cons v x` / `Fin.tail x` / `Fin.elim0` |
| the four hand-written induction principles (216 lines) | `SlicePFunctor.W.elim`, `.induction` |
| `Arities`, `aeq`, `arities`, `arities2` | `q`, `rc`, `sig.wIndex` |
| `Fixpoint sem_rec` | `List.rec` |

## Verification evidence

Every declaration in § Design, and every test declaration named in
§ Tests, was built and elaborated against the repository toolchain
(v4.33.0-rc2) as two modules at library paths — the library with
`public section` and `@[expose]`, the tests with plain `import` and
`linter.privateModule false` — under the repository's option set
(`autoImplicit false`, `relaxedAutoImplicit false`,
`maxSynthPendingDepth 3`, `weak.linter.mathlibStandardSet true`,
`weak.linter.style.header true`, `weak.warningAsError true`,
`weak.linter.flexible true`, `pp.unicode.fun true`), with copyright
headers and module docstrings. Zero diagnostics on both. Measured:

- `sig` elaborates as `SlicePFunctor.{0, 0, 0, 0} (ℕ × ℕ) (ℕ × ℕ)`
  with no universe annotation.
- The coherence argument to `elim` is `rfl`.
- The transport is `h ▸ v`; no `Eq.mpr`, `cast`, `Subtype.ext` or
  `simp` is required, and no clause needs a binder ascription once
  `Direction`, `rc` and `q` are `@[reducible]`.
- `by decide` discharges admissibility across the module boundary
  in 13.0 ms for `plus` and 22.1 ms for `mult` (25 nodes,
  containing `plus` twice) at default `maxHeartbeats`.
- Every assertion of § Tests reduces by `rfl` across the module
  boundary. The negative control `decide (sig.WValid badRaw)`
  reduces to `false`.
- `#print axioms`: `sig` and `finEnumFin` depend on no axioms;
  `sigFinitary`, `finEnumCompDirection`, `BC.eval`, `plus`, `mult`
  and every assertion depend on `[propext, Quot.sound]`. Deleting
  the two named instances, so that `sigFinitary` resolves through
  mathlib's, yields `Classical.choice` on `sigFinitary`, `plus`,
  `mult` and every assertion — not on `BC.eval`, which does not
  depend on `sigFinitary`. Admissibility is where the taint would
  enter, not evaluation.
- The `⟨WType.mk …, by decide⟩` form does not elaborate: instance
  search fails to unify `decidableWValid`'s conclusion against a
  goal containing an inline `WType.mk` application, reporting
  `failed to synthesize Decidable (sig.WValid (WType.mk …))`. A
  type ascription does not repair it; binding the raw tree as its
  own `def` does, which is the form § Tests specifies.

Recorded property: `Fin` numerals wrap, so a mistranscribed index
elaborates rather than failing — `(1 : Fin 1) = 0` and
`(5 : Fin 3) = 2` both close by `rfl`. This affects `proj`'s
`Fin (n + s)`, `cond`'s `y 0 … y 3` at `Fin 4`, and `safeRec`'s
`c 0 … c 2` at `Fin 3` alike. Only an expected-output check
distinguishes them, which is why every assertion states an output
and why § Tests carries `branchRec`.

## Tests

`GebTests/Mathlib/Computability/BellantoniCook.lean`.

Each term is built in two steps, because the inline form does not
elaborate (§ Verification evidence): a raw tree bound as its own
`def` at type `sig.toPFunctor.W`, then the admissible term.

    def compChildren {m k : ℕ} (h : sig.toPFunctor.W)
        (gN : Fin m → sig.toPFunctor.W) (gS : Fin k → sig.toPFunctor.W) :
        Unit ⊕ Fin m ⊕ Fin k → sig.toPFunctor.W :=
      Sum.elim (fun _ ↦ h) (Sum.elim gN gS)

    def plusStepRaw : sig.toPFunctor.W :=
      WType.mk (.comp 1 2 0 1)
        (compChildren (WType.mk (.succ true) Fin.elim0) Fin.elim0
          ![WType.mk (.proj 1 2 1) Fin.elim0])
    def plusStep : BC := ⟨plusStepRaw, by decide⟩

and likewise for the rest. `m` and `k` are implicit and solved by
unification against the expected `Direction (.comp …)`, which is
`@[reducible]` and reduces to the codomain's own
`Unit ⊕ Fin m ⊕ Fin k`. The codomain is written as that sum rather
than as `Direction (.comp n s m k)`, which would leave `n` and `s`
free and fail under `autoImplicit false`.

Every term is bound this way, leaves included: the two-step form is
required wherever a `by decide` goal mentions the tree, so each of
`plusStepRaw`, `plusRaw`, `multBaseRaw`, `multStepRaw`, `multRaw`,
`branchRecRaw`, `predTermRaw`, `condTermRaw`, `projNTermRaw`,
`projSTermRaw` and `badRaw` is its own `def` at
`sig.toPFunctor.W`. Inline `WType.mk` applications are
admissible only as *children* of such a tree, never as the subject
of the `decide`.

`safeRec`'s three children are `![…]` directly,
`Direction (.safeRec n s)` being `Fin 3`. A subterm that is already
a `BC` enters a parent's raw tree as `.val`.

`plus` and `mult` are § 3.2's examples at arities `(1,1)` and
`(2,0)`, transcribed with the arities of the reference
implementation rather than the printed superscripts (§ The paper's
`mult` is ill-formed as printed):

- `plusStep`: `comp 1 2 0 1`, head `succ true`, no normal
  arguments, safe argument `proj 1 2 1`.
- `plus`: `safeRec 0 1`, children `![proj 0 1 0, plusStep, plusStep]`.
- `multBase`: `comp 1 0 0 0`, head `zero`, no arguments.
- `multStep`: `comp 2 1 1 1`, head `plus`, normal argument
  `proj 2 0 1`, safe argument `proj 2 1 2`.
- `mult`: `safeRec 1 0`, children `![multBase, multStep, multStep]`.

They compute unary arithmetic:
`plus x y = List.replicate x.length true ++ y` and
`mult x y = List.replicate (x.length * y.length) true`. The
justification is the definitions, not the reference development's
length lemmas (`plus_correct` at `BCUnary.v:172-173` and
`mult_correct` at `:236-237` state only `|plus m n| = |m| + |n|`
and `|mult m n| = |m| · |n|`, and a length equation does not
determine a value): `succ_e` is `succ true` (`BCUnary.v:116`), so
each step of `plus` (`:167-170`) prepends `true` to its safe
argument; `mult` (`:231-234`) iterates `plus` from the base
`zero_e 1 0`, which is `comp 1 0 zero nil nil` (`BC.v:1034-1035`)
and whose head `zero` evaluates to the empty bitstring
(`BC.v:390`, through the `comp` clause at `:419-421`).

`plus` takes one normal and one safe argument; `mult` takes two
normal arguments and none safe (`sem mult_e [m; n] nil`). Each
assertion names its two environments accordingly.

`plus` and `mult` both pass the same subterm as `safeRec`'s
directions 1 and 2, so neither discriminates `h₀` from `h₁`: with
those alone, transposing `c 1` and `c 2` in `evalValue` would leave
every assertion passing. `branchRec` closes this. It is
`safeRec 0 0` with children `![zero, proj 1 1 0, proj 1 1 1]`, of
arity `(1, 0)`, so that

    f [] = [],  f (b :: v) = if b then f v else v

Single-bit arguments do not discriminate: `f [false]` and
`f [true]` are both `[]` under the intended reading and under the
transposed one. The assertions are therefore at length two:
`branchRec` on `![[false, true]]` is `[true]` and on `![[true, true]]`
is `[]`. Measured: rebuilding `evalValue` with `c 1` and `c 2`
transposed fails exactly these two assertions and no others.

`badRaw` is a `sig.toPFunctor.W`, not a `BC`: `plusStepRaw` with
its safe child replaced by `WType.mk (.proj 2 0 1) Fin.elim0`,
which carries index `(2, 0)` where `rc` demands `(1, 2)`.

Four leaf terms cover what the compound terms do not: `predTerm`
and `condTerm`, `pred` and `cond` appearing in no other term; and
`projNTerm` (`proj 1 1 0`) and `projSTerm` (`proj 1 1 1`), which
separate the two halves of `Fin.append` at a single node, the
`Fin`-wraparound property above being what motivates checking them
apart. `zero` and `succ true` need no leaf term: they are the
heads of `multBase` and `plusStep`, whose outputs `eval_mult` and
`eval_plus_cons` already pin. Each leaf is a single node with
`Fin.elim0` children, admissible vacuously but still bound in two
steps.

The twelve evaluation assertions have the form
`(BC.eval e).2 env₁ env₂ = out`; the negative control, whose
environments the coverage table marks `—`, is the thirteenth and
last row. Each evaluation assertion is named `eval_<term>`, with a
suffix where one term carries several
— `eval_plus_nil`, `eval_plus_cons`, `eval_mult`,
`eval_branchRec_false`, `eval_branchRec_true`,
`eval_predTerm_nil`, `eval_predTerm_cons`,
`eval_condTerm_empty`, `eval_condTerm_odd`, `eval_condTerm_even`,
`eval_projNTerm`, `eval_projSTerm`. The negative control is
`wValid_badRaw_eq_false`, stated in the coverage table's
`decide (sig.WValid badRaw) = false` form rather than as
`¬ sig.WValid badRaw`, so that it too closes by `rfl`. Each
carries a `/-- … -/`
docstring, `docs/rules/lean-coding.md` § Comment and docstring
rules requiring one of every theorem of public interest, which the
module's `## Main statements` section makes these.

Assertions are named `theorem`s. They cannot be `def`s —
`linter.defProp` rejects a `def` whose type is a `Prop`, and
`GebTests` inherits `mathlibStandardSet` and `weak.warningAsError`
from the package-level `[leanOptions]` (`lakefile.toml:12,15`; the
library-level block at `:59-60` overrides only
`linter.hashCommand`). The raw-tree and term `def`s anchor the
module's imports for `lake shake`, as `wLeaf`/`wNode` do in
`GebTests/Mathlib/Data/PFunctor/Slice/W.lean`; where an import is
still reported removable it carries a `-- shake: keep` comment, as
`GebTests/Mathlib/CategoryTheory/FinCat/FinCategory.lean:8-10`
does.

Coverage. Each of the following is a `theorem` stating an expected
output and closing by `rfl`:

| assertion | environments | output |
| --- | --- | --- |
| `plus` | `![[]]`, `![[false]]` | `[false]` |
| `plus` | `![[true, true]]`, `![[false]]` | `[true, true, false]` |
| `mult` | `![[true, true], [true, true, true]]`, `![]` | `List.replicate 6 true` |
| `branchRec` | `![[false, true]]`, `![]` | `[true]` |
| `branchRec` | `![[true, true]]`, `![]` | `[]` |
| `predTerm` | `![]`, `![[]]` | `[]` |
| `predTerm` | `![]`, `![[true, false]]` | `[false]` |
| `condTerm` | `![]`, `![[], [false], [true], [true, true]]` | `[false]` |
| `condTerm` | `![]`, `![[true], [false], [true], [true, true]]` | `[true]` |
| `condTerm` | `![]`, `![[false], [false], [true], [true, true]]` | `[true, true]` |
| `projNTerm` | `![[true]]`, `![[false]]` | `[true]` |
| `projSTerm` | `![[true]]`, `![[false]]` | `[false]` |
| `decide (sig.WValid badRaw)` | — | `false` |

`BCOf` is exercised by two `def`s rather than `theorem`s, `BCOf n s`
being a type and not a `Prop`:
`def plusOf : BCOf 1 1 := ⟨plus, rfl⟩` and
`def multOf : BCOf 2 0 := ⟨mult, rfl⟩`. These subsume the arities:
each elaborates exactly when `BC.arity` of its term reduces to the
stated pair, so no separate `arity_plus`/`arity_mult` theorem is
carried.

## Documentation

- Module docstring: `# Title`, summary, `## Main definitions` (the
  fourteen library declarations other than the three instances,
  which mathlib's guide does not list there), `## Implementation notes` (the
  W-type encoding and the rule requiring it; the transport and why
  `evalValue` is separate; the choice-free `scoped` `FinEnum`
  instances; the `@[reducible]` requirement), `## References`
  (`[HeraudNowak2011]`, `[BellantoniCook1992]`), `## Tags`
  (`Bellantoni-Cook, polytime, implicit computational complexity,
  safe recursion, W-type, polynomial functor`). `## Main
  statements` and `## Notation` are omitted as vacuous. Every
  declaration carries a `/-- … -/` docstring; `Shape`'s seven
  constructors are documented within the type's own docstring, as
  `Fixtures.lean:127-128` documents `Shp`'s. All four new `.lean`
  files carry the standard copyright header, and the two index
  files carry a module docstring in the form of
  `Geb/Mathlib/Data.lean`'s.
- The test module carries `# Title`, a summary and `## Tags`, as
  `GebTests/Mathlib/Data/PFunctor/Slice/W.lean:11-23` does; plus
  `## References` citing `[HeraudNowak2011]`, since `plus` and
  `mult` are transcribed, and `## Main statements` for its named
  theorems. `docs/rules/lean-coding.md` § Documentation requires
  each section that has content. Its twenty-four `def`s — the
  eleven raw trees, the ten terms, `compChildren`, `plusOf` and
  `multOf` — each carry a `/-- … -/` docstring, § Comment and
  docstring rules mandating one for every `def`. A raw tree's
  states its shape and children; a term's states its arity and,
  for `plus`, `mult` and `branchRec`, the function it computes;
  `compChildren`'s states the head-then-normal-then-safe order it
  imposes; `plusOf`'s and `multOf`'s state that they exhibit their
  terms at the arities `§ Tests` claims.
- `docs/references.bib`: `HeraudNowak2011` as `@inproceedings` at
  ITP 2011 (`author = {H{\'e}raud, Sylvain and Nowak, David}`,
  `title`, `booktitle`, `series`, `volume = {6898}`,
  `pages = {119--134}`, `publisher`, `year`, `doi`) carrying
  `eprint = {1102.5495}`, `archivePrefix = {arXiv}`,
  `primaryClass = {cs.CC}`, and a `note` recording that this
  repository cites the arXiv version's section and page numbering.
  The file's entries for works existing as both preprint and
  publication are the published type with the preprint in `eprint`
  (`AllaisAtkeyChapmanMcBrideMcKinna2021`,
  `GhaniNordvallForsbergMalatesta2015`, `JohnsonYau2021`,
  `AvanziniDalLago2018`, `AltenkirchChapmanUustalu2015`), `note`
  being used only for what those fields cannot carry — as in
  `HancockMcBrideGhaniMalatestaAltenkirch2013`, which is this
  situation exactly: proceedings entry, `note` naming which
  version's numbering the repository cites. `Vistoli2008` is
  `@misc` because it has no publication, not because the preprint
  is cited. The accented surname is
  LaTeX-escaped, as `Par{\'e}` is.
  `BellantoniCook1992` as `@article`: Bellantoni and Cook, *A new
  recursion-theoretic characterization of the polytime functions*,
  Computational Complexity 2(2), 97-110, 1992,
  `doi:10.1007/BF01201998` — the field set and order of `Pare1974`.
- `docs/references.md` § Computability: a pointer to
  `github.com/davidnowak/bellantonicook` at the commit named in
  § Sources.
- `docs/index.md` § Implemented content: one bullet in the file's
  flat one-bullet-per-module form, among the other `Geb/Mathlib/`
  bullets and after those for
  `Geb/Mathlib/Data/PFunctor/Slice/`, which it depends on, reading
  to the effect of
  "`Geb/Mathlib/Computability/BellantoniCook.lean`
  — the function class `B` of [HeraudNowak2011] § 3.2: its arity
  relation as a `SlicePFunctor` over `ℕ × ℕ`, its syntax as that
  functor's slice W-type, and its semantics by the W-type's
  eliminator. Depends on `Geb.Mathlib.Data.PFunctor.Slice.W` and
  `Geb.Mathlib.Data.PFunctor.Univariate.Finitary`. Every declaration of
  the module has axioms within `propext` and `Quot.sound`; `sig` and
  `finEnumFin` have none."
  — covering the path, the concepts and the dependencies per
  docs/process.md § Documentation
  under `docs/`, and stating the axiom dependence in prose, as the
  file's existing bullets do.
- `TODO.md`: a `### Bellantoni-Cook` subsection under `## Next up`
  containing § Deferred items 1-3 with their scope, dependencies
  and return, in the neighbouring subsections' form; and items 4
  to 7 under `## Triggers (do when condition fires)`, in that
  section's `- **Bold title**: …` bullet form.

## Non-goals

Not part of the syntax and its interpretation, and not planned:
`sem_cost` (the time-complexity semantics) and `BCI`/`B_inf` with
its two translations. Neither forecloses the deferred work:
`BCLib.v`, `BC_to_Cobham.v` and `Cobham_to_BC.v` contain no
occurrence of `BCI` or of `sem_cost`, and `sem_cost` is first
defined at `BC.v:1365`, after Proposition 2 at `:1128`.

## Deferred

Items 1-3 are a dependency chain and go to `## Next up`. Items 4
to 7 are triggers, none having a consumer yet, and go to
`## Triggers (do when condition fires)` in that section's
`- **Bold title**: …` bullet form.

1. `MultiPoly`, the multivariate polynomial library. Required by
   `BC_to_Cobham.v:2`, by `Cobham_to_BC.v:2`, and by Proposition 2,
   whose statement `polymax_bounding` (`BC.v:1128`) is over
   `poly_BC` (`:1075`), built from `pcst`, `pproj`, `pplus`,
   `pmult`, `pcomp`, `pshift` and `pplusl`. Returns the polynomial
   apparatus both later items are stated over.
2. Proposition 2, the polymax bounding of `B`. Depends on 1.
   Returns the length bound that the translation of 3 requires.
3. Cobham's class and the translations of Theorems 1 and 2.
   Depends on 1 and 2. Returns the characterization of polynomial
   time, and is the consumer named in § Purpose.
4. Trigger: a workstream needs programmable building blocks for
   terms of `B`. Port the derived function library of `BCLib.v`,
   which depends only on the syntax and semantics delivered here.
5. Trigger: a second consumer of `finEnumFin` or
   `finEnumCompDirection` appears. Move them to
   `Geb/Mathlib/Data/FinEnum.lean`, the repository's home for
   choice-free `FinEnum` support.
6. Trigger: a consumer needs `DecidableEq` or `Repr` for `BC`.
   Derive them on `Shape` and lift along `sig.W`'s subtype.
7. Trigger: a workstream needs the paper's "polytime checker" as a
   term-level artifact. Add an untyped `Ast` plus
   `check : Ast → Option ((n s : ℕ) × BCOf n s)` over
   `SlicePFunctor.decidableWValid`.

## Constraints

1. No `noncomputable`. `#print axioms` on every declaration lies
   within `{propext, Quot.sound}`, measured monomorphically in the
   consuming closure and re-measured at each toolchain bump
   (`docs/rules/lean-coding.md` § Constructive-only Lean code).
   `Quot.sound` is permitted, not excluded. The `FinEnum` instances
   are the reason this is not automatic.
2. No self-referential `inductive` and no self-calling `def`;
   `Shape` is non-recursive, the syntax's recursion is `sig.W`, and
   the semantics' recursions are `SlicePFunctor.W.elim` and
   `List.rec`.
3. All four new `.lean` files declare `module`. The library module uses
   `public import` and a `public section`; the test module uses
   plain `import` with `set_option linter.privateModule false`
   (§ Exposure).
4. `scripts/pre-push.sh` clean, `lake shake`, `lake lint` and
   `scripts/lint-imports.sh` included. `lake shake` has been observed to print a
   `PANIC at Option.get!` trace from `Lake.Shake.visitModule` when
   the first module under a new `GebTests/Mathlib/<Dir>/` appears.
   It does not reproduce reliably, exits 0 when it occurs, and
   occurs equally with an unrelated control module at the same
   path, so it is a shake artifact rather than a property of this
   design. The subtree's rules bind:
   no import outside `Mathlib.*`, `Batteries.*`, `Geb.Mathlib.*`
   (and `GebTests.Mathlib.*` for the test module); no bare umbrella
   import; and no `Geb.Mathlib.` or `GebTests.Mathlib.` prefix
   outside an `^import` line, in particular not in the namespace
   declarations.
5. No `#guard`; every assertion is a `theorem` closing by `rfl`.
   `plusOf` and `multOf` are `def`s, `BCOf n s` being a type rather
   than a `Prop`. Should an assertion not reduce, the term is
   shrunk until it does; `native_decide` is forbidden by
   Constraint 1 and `#guard` by this constraint.
6. Lambda notation follows `docs/rules/lean-coding.md` § Coding
   style: `↦`, not `=>`, in `fun`.
7. Library imports: `Geb.Mathlib.Data.PFunctor.Slice.W`,
   `Geb.Mathlib.Data.PFunctor.Univariate.Finitary`,
   `Mathlib.Logic.Equiv.Fin.Basic`. The test module adds
   `Geb.Mathlib.Data.PFunctor.Slice.Decidable`, besides
   `Geb.Mathlib.Computability.BellantoniCook` itself.

   `Slice.Decidable` belongs to the tests, not the library: the
   library uses `SlicePFunctor`, `.W`, `.wIndex` and `W.elim` from
   `Slice/W.lean` and `PFunctor.Finitary` from
   `Univariate/Finitary.lean`, and nothing from
   `Slice/Decidable.lean`; `decidableWValid` is reached only by the
   tests' `by decide`. Measured:
   `lake shake --add-public --keep-implied --keep-prefix Geb
   GebTests`, the form `scripts/pre-push.sh:42` runs, exits 0 with
   no suggestion for either new file, and no `-- shake: keep`
   comment is needed. Placing `Slice.Decidable` in the library
   instead makes it exit 1, asking for `Slice.W` and
   `Univariate.Finitary` to be added and `Slice.Decidable`
   removed.

   `Mathlib.Data.Fin.Tuple.Basic` and `Mathlib.Data.Fin.VecNotation`
   are not named, though the modules apply `Fin.append`,
   `Fin.cons`, `Fin.tail` and `![…]` directly:
   `Mathlib.Logic.Equiv.Fin.Basic` imports `VecNotation`, which
   imports `Fin.Tuple.Basic`, so naming them makes plain
   `lake shake` — the form mathlib CI runs — report both modules as
   carrying a redundant import. Measured: with them named, plain
   `lake shake --add-public --keep-prefix Geb GebTests` reports 16
   `Geb/Mathlib/` and 8 `GebTests` files against a baseline of 15
   and 7; without them, the baseline is unchanged and both modules
   still build. Omitting them keeps the branch off the count in
   `TODO.md`'s `lake shake --keep-implied` trigger and keeps the
   upstream-eligible module minimal, as CONTRIBUTING.md § Floodgate
   test requires of a PR shipped with no source-code change.
