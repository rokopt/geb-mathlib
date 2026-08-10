# Definition by cases, the generic ranked recognizer, and the finite-carrier fold

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [Segments, and where each declaration lands](#segments-and-where-each-declaration-lands)
- [Transcription status of each definition](#transcription-status-of-each-definition)
- [Constraints this design is bound by](#constraints-this-design-is-bound-by)
- [Segment 1: `Cobham/Cases.lean` and the shared combinators](#segment-1-cobhamcaseslean-and-the-shared-combinators)
  - [The meaning of a tree at an arity](#the-meaning-of-a-tree-at-an-arity)
  - [The shared combinators](#the-shared-combinators)
  - [Selection by the bits of a scrutinee](#selection-by-the-bits-of-a-scrutinee)
  - [The scrutinee shift](#the-scrutinee-shift)
  - [The case tree](#the-case-tree)
  - [The combinator and its meaning](#the-combinator-and-its-meaning)
- [Segment 2: `Cobham/RankedTree.lean`](#segment-2-cobhamrankedtreelean)
  - [The state as a bitstring](#the-state-as-a-bitstring)
  - [Inverting the state word](#inverting-the-state-word)
  - [The recognizer](#the-recognizer)
  - [The verdict and the bridge](#the-verdict-and-the-bridge)
- [Segment 3: `Cobham/Fold.lean`](#segment-3-cobhamfoldlean)
  - [Interface](#interface)
  - [Construction and statements](#construction-and-statements)
- [Additions to the ranked-encoding modules](#additions-to-the-ranked-encoding-modules)
- [What is out of scope](#what-is-out-of-scope)
- [Test mirrors](#test-mirrors)
- [Documentation and commits](#documentation-and-commits)
- [What is compiled](#what-is-compiled)
- [Risks and open questions](#risks-and-open-questions)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope

Three concerns over `Geb/Mathlib/Computability/Cobham/`:

1. **Definition by cases.** A combinator selecting among `2 ^ p` expressions of
   arity one by the low `p` bits of a scrutinee, and applying the selected one
   to a second argument, together with the constant-word, iterated-predecessor
   and diagonal combinators its consumers build branches from.
2. **The generic ranked recognizer.** `RankedAlphabet.validBool`, the validity
   scan of `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean`, as an
   expression of Cobham's class, at an
   arbitrary ranked alphabet, together with the theorem identifying it at the
   two-symbol alphabet with the recognizer `Cobham/Tree.lean` already carries.
   This closes B6 of [TODO.md](../../../TODO.md) § Extensions of the tree
   recognizers.
3. **The fold at a finite carrier.** The catamorphism of the list of bits at a
   carrier admitting a `p`-bit encoding, as an instance of the scan combinator
   `Cobham.scan`. This closes B3 of the same entry.

Segment 1 exists because segment 2 needs it: the recognizer's step must resolve
`RankedAlphabet.arOf` at a completed block, whose width is a parameter rather
than a literal, so the dispatch cannot be written out.

Segment 3 is a deliverable of this workstream rather than a dependency of
anything in it, and is the output later workstreams are expected to build on.
What it delivers is `foldSem_eq`: the statement that an expression of Cobham's
class computes the encoded state of the deterministic automaton
`(α, init, step)` after reading a word, for an arbitrary carrier admitting a
bit encoding. That is not an instance of segment 2, whose state is unbounded,
and having no consumer in the repository is its expected condition on landing,
not a cost to be justified against
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost. It is sequenced
last because nothing here depends on it. Whether it is a published statement is
an open question below; it is not described as a containment of the
finite-state transductions, there being no output function and no acceptance
condition in the interface.

## Segments, and where each declaration lands

The three concerns are appended to the existing topic branch in the order
above, each with a bookmark at its boundary, so that each is submitted as its
own pull request while the graph stays linear and conflict-free.

Every shared declaration lands in segment 1, which is the segment before the
first that consumes it, so that segments 2 and 3 add only their own module,
their own statements, and what segment 2 adds to `Data/Tree/Ranked/`. Segment 3
depends on segment 1 and not on segment 2.

Segment 1 has landed; segments 2 and 3 are not started.

| Segment | New module | `Cobham/Basic.lean` | Elsewhere |
| --- | --- | --- | --- |
| 1 | `Cases.lean` | `semAt`; the `zeroAt` family; `prepend`, `constAt`, `predIter`, `diag` | `Scan.lean`, `Tree.lean` through `semAt` |
| 2 | `RankedTree.lean` | — | a definition and four statements in `Data/Tree/Ranked/` |
| 3 | `Fold.lean` | — | — |

A characterisation naming `baseWord` or `stepWord` cannot be stated in
`Cobham/Basic.lean`: both are declared in `Cobham/Scan.lean`, which imports
`Basic.lean`. Each such lemma is therefore stated in `Cases.lean`, which
imports `Scan.lean` for `liftRaw` and `stepWord` in any case.

Each of `prepend`, `constAt`, `predIter` and `diag` follows the family shape
`Cobham/Scan.lean` and `Cobham/Tree.lean` both use, so far as it needs to: a
`…Raw` tree with its `wIndexRoot`, `wValid` and `RecBounded` lemmas, the `C`
expression, and the `…Of` form. `constAt` needs no raw tree or
admissibility of its own, being a composite of two that have them; its arity is
explicit, appearing in neither an argument type nor the result type of `C`.

## Transcription status of each definition

Per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature when
transcribing, every definition below is novel. Those of segment 1 and the two
folds are assemblies of the generators `Cobham/Basic.lean` transcribes from
[HeraudNowak2011] and [Cobham1965]. `maxArity` is a derived quantity of
`RankedAlphabet`, and `bufBits`, `stateWord` and `decodeState` are a choice of
bit layout for `RankedAlphabet.Scan`; none is drawn from a source.

Two statements realized here may be published rather than novel: that an
expression of the class computes a finite automaton's encoded state, which
segment 3 realizes, and that the languages of ranked-term preorder spellings
lie in the class, which segment 2 realizes. Neither is cited to a work yet. The
search is an open question below, settled before the plan for the segment
realizing each, per [AGENTS.md](../../../AGENTS.md) § Verify agent claims: a
statement that turns out to be published is a transcription, whose interface
[docs/rules/lean-coding.md](../../rules/lean-coding.md) § Structure and
typeclass patterns fixes to its source, which can bear on the state layout
segment 2 settles.

## Constraints this design is bound by

- **No `noncomputable`, and `Classical.choice` excluded.** Every declaration
  measures `[propext, Quot.sound]`, which `lake lint` enforces. Three routes
  into `Classical.choice` are live here and are avoided by name: `omega`
  discharging an `Iff` goal pulls it in, so an equivalence is proved from its
  two implications; `DecidableEq (Fin n → Bool)` resolves through
  `Fintype.decidablePiFintype`, so every decision below is taken over
  `List Bool` after `List.ofFn`, whose `DecidableEq` depends on no axiom; and
  `RankedAlphabet.Scan` derives no `DecidableEq` at all, so a statement about
  one is stated field by field.
- **Recursion through recursors.** No `def` calls itself and no `induction`
  tactic appears; every recursion is an explicit `Nat.rec`, `List.rec` or
  `WType.elim` application.
- **`decide` discharges admissibility only at a named constant.** Instance
  search finds `Decidable (sig.WValid w)` when `w` is a constant but not when
  it is a literal `WType.mk` application, and at a free arity or a variable `p`
  nothing reduces at all. Every admissibility proof here is written out, in the
  shape `Cobham.wValid_boundRaw` and `Cobham.zeroAt` both set.
- **An unreferenced binder is an error.** `linter.unusedVariables` is an error
  under `weak.warningAsError`, so a statement carries no binder its own text
  does not mention.
- **Transport along an opaque equation does not disappear.** It disappears by
  proof irrelevance when both sides reduce to the same literal. A node's own
  arity reduces whatever its children are; a component's does not. Where the
  two forms must be identified, `Cobham.transport_transport` is the bridge.
- **The class reaches only a bounded prefix of a word.** `pred` drops the head,
  `succ` prepends, and `cond` tests the head, so an expression of bounded size
  inspects and rewrites only a bounded prefix. This determines the field order
  of segment 2's state.
- **`Nat` subtraction is truncated.** `bufBits` below has its intended length
  only under an invariant on `buf`'s length, stated as a lemma rather than
  assumed.
- **Universes are declared.** `universe u` and `variable {α : Type u}`; `Type*`
  auto-binds a `u_1`-style variable and appears nowhere in `Geb/`.

## Segment 1: `Cobham/Cases.lean` and the shared combinators

### The meaning of a tree at an arity

```lean
@[expose] def semAt (n : ℕ) (e : sig.W) (he : arity e = n) : Sem n :=
  transport ((fst_eval e).trans he) (eval e).2
```

Added to `Cobham/Basic.lean`, beside `transport`, `fst_eval`, `eval`, `arity`
and `Sem`, on which it depends. It is not new content: `boundSem`, `scanSem`,
`baseWord` and `stepWord` in `Cobham/Scan.lean` spell out the composite, and
`eqOneSem` and `isTreeSem` in `Cobham/Tree.lean` spell out its `he := rfl`
case. All six are restated through it in this segment, so that the pattern is
named once rather than repeated at each site. Restating them is refactoring
outside the subject of this segment, which
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape would ordinarily
put on its own branch; it is bundled here by decision, the alternative being to
leave a new name beside six hand-spelled copies of what it names.

The restatement was measured against a copy rather than assumed:
`scanSem_nil`, `scanSem_eq_eval`, `combSem_nil` and `isTreeSem_eq_eval` still
close by `rfl`, and `scanSem_cons`'s `change` still lands. Not measured, and
measured first in the segment: `eqOneSem_env`, `eqOneSem_eq`,
`isTreeSem_apply`, `combSem_cons_false` and `combSem_cons_true`, each of which
reads through a restated definition by `change` or `congrArg`; and
`isTree_smashFree`, whose `decide` folds over the relocated `zeroAtRaw`.

### The shared combinators

Added to `Cobham/Basic.lean` in this segment. `zeroAtRaw`, `zeroAt` and
`zeroAtOf` move there from `Cobham/Tree.lean`, unchanged: `constAt` needs a
nullary constant at an arbitrary arity, and `Cobham/Tree.lean` imports
`Cobham/Basic.lean` rather than the reverse. None of the three carries a
`decide`; `Tree.lean`'s implementation notes record that `zeroAtRaw`,
`oneAtRaw` and `falseAtRaw` "carry a free arity, at which `decide` does not
apply". The move is a relocation of unchanged text.

```lean
@[expose] def prependRaw (u : List Bool) (e : sig.toPFunctor.W) : sig.toPFunctor.W
@[expose] def prepend {n : ℕ} (u : List Bool) (e : COf n) : C
@[expose] def prependOf {n : ℕ} (u : List Bool) (e : COf n) : COf n
@[expose] def constAt (n : ℕ) (u : List Bool) : C := prepend u (zeroAtOf n)
@[expose] def constAtOf (n : ℕ) (u : List Bool) : COf n := ⟨constAt n u, rfl⟩
@[expose] def predIterRaw (k : ℕ) : sig.toPFunctor.W
@[expose] def predIter (k : ℕ) : C
@[expose] def predIterOf (k : ℕ) : COf 1
@[expose] def diagRaw (e : sig.toPFunctor.W) : sig.toPFunctor.W
@[expose] def diag (e : COf 2) : C
@[expose] def diagOf (e : COf 2) : COf 1
```

`prepend` is the chain of `succ` nodes prepending a fixed word to what `e`
computes, by `List.rec` on `u`; `predIter` is the `k`-fold predecessor, by
`Nat.rec`; `diag` is a `comp 1 2` node over `e` and two `proj 1 0` children.
`Cobham/Tree.lean`'s `predPred` is `predIter 2`, and is left as it stands, the
deferral recorded with `oneAtOf` and `falseAtOf` below.

Their characterisations name `baseWord` and `stepWord`, so they are stated in
`Cases.lean` rather than in `Basic.lean`:

```lean
theorem stepWord_prependOf (e : COf 1) (r : List Bool) :
    ∀ u : List Bool, stepWord (prependOf u e) r = u ++ stepWord e r
theorem baseWord_prependOf (e : COf 0) :
    ∀ u : List Bool, baseWord (prependOf u e) = u ++ baseWord e
theorem baseWord_constAtOf (u : List Bool) : baseWord (constAtOf u) = u
theorem stepWord_constAtOf (u r : List Bool) : stepWord (constAtOf u) r = u
theorem stepWord_predIterOf (k : ℕ) (u : List Bool) :
    stepWord (predIterOf k) u = u.drop k
theorem stepWord_diagOf (e : COf 2) (u : List Bool) :
    stepWord (diagOf e) u = semAt 2 e.1.1 e.2 ![u, u]
```

`stepWord_prependOf` is what turns segment 2's step into a prefix followed by a
drop; `stepWord_constAtOf` is the case `e := zeroAtOf n` of
`stepWord_prependOf` and does not supply `stepWord_prependOf` in turn.
`stepWord_constAtOf` carries no `{n}` binder, `stepWord` forcing its argument
to `COf 1`. `Cobham.baseWord_eq_eval` states only that `baseWord` agrees with
what the expression carries, and says nothing about the value, so it supplies
none of these.

### Selection by the bits of a scrutinee

```lean
@[expose] def bits (p : ℕ) (w : List Bool) : Fin p → Bool :=
  fun j ↦ w.getD j false

theorem bits_succ (p : ℕ) (w : List Bool) :
    bits (p + 1) w = Fin.cons (w.getD 0 false) (bits p w.tail)
theorem bits_succ_tail (p : ℕ) (w : List Bool) :
    (fun i : Fin p ↦ bits (p + 1) w i.succ) = bits p w.tail
theorem bits_ofFn {p : ℕ} (f : Fin p → Bool) : bits p (List.ofFn f) = f
theorem ofFn_bits (p : ℕ) (w : List Bool) :
    List.ofFn (bits p w) = w.take p ++ List.replicate (p - w.length) false
```

Bit `j` of the scrutinee, `false` past its end. Reading a short scrutinee as
zero-padded, rather than conditioning the semantic theorem on `p ≤ w.length`,
keeps `casesSem_eq` free of a hypothesis, and in the tree it costs nothing:
`cond`'s empty branch is directed at the same subtree as its head-`false`
branch. `bits_ofFn` is what segment 3's step consumes; `ofFn_bits` is its
converse and is what carries segment 2's `decodeState`, which reads `List.ofFn
v`, to `decodeState_stateWord_of_lt`, which supplies `bits (dispatchWidth R)
(stateWord R s)`.

### The scrutinee shift

```lean
@[expose] def shiftRaw (e : sig.toPFunctor.W) : sig.toPFunctor.W :=
  WType.mk (.comp 2 2) fun d ↦
    match d with
    | .inl () => e
    | .inr i =>
      ![WType.mk (.comp 2 1) (fun c ↦
          match c with
          | .inl () => predRaw
          | .inr _ => WType.mk (.proj 2 0) Fin.elim0),
        WType.mk (.proj 2 1) Fin.elim0] i

theorem wIndexRoot_shiftRaw (e : sig.toPFunctor.W) :
    sig.wIndexRoot (shiftRaw e) = 2
theorem wValid_shiftRaw (e : sig.toPFunctor.W) (he : sig.WValid e)
    (ha : sig.wIndexRoot e = 2) : sig.WValid (shiftRaw e)
@[expose] def shiftW (e : sig.W) (he : arity e = 2) : sig.W :=
  ⟨shiftRaw e.1, wValid_shiftRaw e.1 e.2 he⟩
theorem arity_shiftW (e : sig.W) (he : arity e = 2) : arity (shiftW e he) = 2

theorem semAt_shiftW (e : sig.W) (he : arity e = 2) (sel x : List Bool) :
    semAt 2 (shiftW e he) (arity_shiftW e he) ![sel, x] =
      semAt 2 e he ![sel.tail, x]
theorem recBounded_shiftW (e : sig.W) (he : arity e = 2) (hr : RecBounded e) :
    RecBounded (shiftW e he)
```

The scrutinee is consumed by shifting it into the recursive subtree, rather
than by scrutinising `pred ^ j` of a fixed argument at depth `j`. The prototype
forced this, and it serves two purposes:

- It makes the semantic theorem provable. At depth `j` the scrutinee is
  `pred ^ j` applied to argument zero, which is not a variable, so no case
  analysis reduces the `boundedRec` node of `cond`. Shifting leaves the
  scrutinee as argument zero itself, so `match sel with` reduces the node — the
  same case analysis `Cobham.scanSem_cons` performs by `cases b`.
- It is smaller. A chain of `pred`s at every depth is quadratic in `p`; one
  shift per level is linear.

`semAt_shiftW` is not definitional in two places. Its component zero is the
meaning of `pred`, a `boundedRec` node, which reduces only once its argument is
a constructor — hence a case analysis on `sel`, exactly as `predSem_eq`
performs. Its component one closes by `rfl`, but the two components are
assembled by `funext`, the node applying its head at `fun i : Fin 2 ↦ …` where
the statement reads `![sel.tail, x]`.

### The case tree

```lean
@[expose] def casesRaw :
    (p : ℕ) → ((Fin p → Bool) → sig.toPFunctor.W) → sig.toPFunctor.W :=
  Nat.rec (motive := fun p ↦
      ((Fin p → Bool) → sig.toPFunctor.W) → sig.toPFunctor.W)
    (fun br ↦ liftRaw (br Fin.elim0))
    (fun _ ih br ↦
      WType.mk (.comp 2 4) fun d ↦
        match d with
        | .inl () => condRaw
        | .inr i =>
          ![WType.mk (.proj 2 0) Fin.elim0,
            shiftRaw (ih (fun t ↦ br (Fin.cons false t))),
            shiftRaw (ih (fun t ↦ br (Fin.cons true t))),
            shiftRaw (ih (fun t ↦ br (Fin.cons false t)))] i)

theorem wIndexRoot_casesRaw (p : ℕ) (br : (Fin p → Bool) → sig.toPFunctor.W) :
    sig.wIndexRoot (casesRaw p br) = 2
theorem wValid_casesRaw : ∀ (p : ℕ) (br : (Fin p → Bool) → sig.toPFunctor.W),
    (∀ v, sig.WValid (br v)) → (∀ v, sig.wIndexRoot (br v) = 1) →
    sig.WValid (casesRaw p br)
theorem recBounded_casesW : ∀ (p : ℕ) (br : (Fin p → Bool) → COf 1),
    RecBounded (casesW p br)
```

The motive reindexes the branch family at each level by `Fin.cons`. `cond`'s
four arguments are the scrutinee, the branch on an empty scrutinee, the branch
on head `true` and the branch on head `false`, in that order, which is what
`condSem_eq` states. `wIndexRoot_casesRaw` is a case split on `p`, not a
recursion: at zero the tree is a `liftRaw` and at a successor a `comp` node,
and both indices reduce. The admissibility motive quantifies over the branch
family, the recursive calls applying it to reindexed families.

The subtree for a `false` head stands at two of the four child positions, so
the normal form has `3 ^ p` leaf occurrences over `2 ^ p` distinct branches.
That normal form is never materialized: `casesRaw` is a `Nat.rec`, so the
elaborated term is of constant size, and `evalRec` is a `List.rec` on the
scrutinee, so weak-head reduction follows one root-to-leaf path. The cost of a
single reduction is linear in `p`.

### The combinator and its meaning

```lean
@[expose] def casesW (p : ℕ) (br : (Fin p → Bool) → COf 1) : sig.W
theorem arity_casesW (p : ℕ) (br : (Fin p → Bool) → COf 1) :
    arity (casesW p br) = 2
@[expose] def casesSem (p : ℕ) (br : (Fin p → Bool) → COf 1) : Sem 2 :=
  semAt 2 (casesW p br) (arity_casesW p br)

theorem casesSem_eq : ∀ (p : ℕ) (br : (Fin p → Bool) → COf 1)
    (sel x : List Bool),
    casesSem p br ![sel, x] = stepWord (br (bits p sel)) x

@[expose] def cases (p : ℕ) (br : (Fin p → Bool) → COf 1) : C
@[expose] def casesOf (p : ℕ) (br : (Fin p → Bool) → COf 1) : COf 2
theorem casesSem_eq_eval (p : ℕ) (br : (Fin p → Bool) → COf 1) :
    transport (casesOf p br).2 (casesOf p br).1.eval = casesSem p br
```

`cases` and `casesOf` carry no side condition. `recBounded_casesW` discharges
it componentwise from the branches' own, by a `Nat.rec` generalizing over the
branch family exactly as `wValid_casesRaw` does: every node the recursion
introduces is a `comp`, where `RecBoundedValue` is `True`, and its children are
`proj` together with the trees underlying `cond : COf 4` and `pred : COf 1`,
which already carry their own `RecBounded` as `cond.1.2` and `pred.1.2`.
Neither is a `comp` node; what makes them free here is that their conditions
are discharged where they are defined, not that those conditions are vacuous.

`casesSem_eq_eval` is not a `rfl`, unlike the scan combinator's counterpart:
`arity_casesW` is a theorem rather than a definitional equality, so the
transport it carries is opaque and the two forms are identified by
`transport_transport`, in the shape `baseWord_eq_eval` uses.

At `p = 0` the branch family is applied at `Fin.elim0` in the tree and at
`bits 0 sel` in the statement. These are equal by `funext fun i ↦ i.elim0` and
not by `rfl`, so the base case of `casesSem_eq` rewrites by that equality
first.

The combinator is stated at arity two although every consumer here reaches it
through `diagOf`, at a scrutinee equal to the argument. The arity-two form is
the statement the construction supports, `shiftRaw` needing both slots, and
narrowing it to the diagonal would not shorten the proof.

## Segment 2: `Cobham/RankedTree.lean`

Named to parallel `Cobham/Tree.lean`, which recognizes the same shape of
language at the two-symbol alphabet. `Cobham/Ranked.lean` would read
ambiguously against the directory `Geb/Mathlib/Data/Tree/Ranked/`.

### The state as a bitstring

```lean
@[expose] def bufBits (R : RankedAlphabet) (buf : List Bool) : List Bool :=
  List.replicate (R.width - 1 - buf.length) false ++ true :: buf
@[expose] def stateWord (R : RankedAlphabet) (s : RankedAlphabet.Scan) :
    List Bool :=
  s.live :: bufBits R s.buf ++ List.replicate s.depth true
@[expose] def dispatchWidth (R : RankedAlphabet) : ℕ :=
  R.width + R.maxArity + 2

theorem length_bufBits_of_lt (R : RankedAlphabet) (buf : List Bool)
    (h : buf.length < R.width) : (bufBits R buf).length = R.width
theorem length_stateWord_of_lt (R : RankedAlphabet) (s : RankedAlphabet.Scan)
    (h : s.buf.length < R.width) :
    (stateWord R s).length = 1 + R.width + s.depth
```

`RankedAlphabet.Scan` carries an incomplete block `buf`, a count `depth` of
pending subterms, and a liveness flag. `depth` is unbounded and the other two
are not, and an expression of the class reaches only a bounded prefix, so
`depth` is the tail and the layout admits no alternative.

`buf`'s own length cannot delimit it, since the fields after it would then
stand at a position not statically known. It is stored in a slot of exactly
`R.width` bits, delimited by a `true` sentinel preceded by `false` padding:
reading head-first from offset one, the first `true` marks where `buf` begins,
unambiguously, the padding being all `false`. This costs `R.width` bits rather
than the `2 * R.width` a separate fill counter would. The slot's length is
invariant under accumulation — the padding shrinks as `buf` grows — which is
why the fields after it never move.

`length_bufBits_of_lt`'s hypothesis is not decoration. `Nat` subtraction being
truncated, a `buf` of length `R.width` or more yields a slot of length
`buf.length + 1`, and `stateWord` is then not injective: at `R.width = 2` the
states `⟨[false, true], 0, true⟩` and `⟨[false], 1, true⟩` share the word
`[true, true, false, true]`. The invariant excluding this is
`length_buf_scanFinal_lt`, in
[Additions to the ranked-encoding
modules](#additions-to-the-ranked-encoding-modules).

`depth` is unary. Binary would need a Cobham-definable truncated subtraction
for `depth - r + 1`, and `Cobham/Tree.lean`'s recognizer represents its depth
in unary already.

The dispatch reads the whole prefix, `1 + R.width` bits, together with the low
`R.maxArity + 1` bits of `depth`, giving `dispatchWidth R` in total. Those bits
give `min depth (R.maxArity + 1)`, which decides `r ≤ depth` for every symbol:
if `depth ≥ R.maxArity + 1` then `r ≤ R.maxArity < depth`, and otherwise those
bits are `depth` itself. The `depth` slot is all `true`, and the zero-padding
convention reads `false` past its end, so `cond`'s three-way split locates
where the slot ends.

### Inverting the state word

```lean
@[expose] def decodeState (R : RankedAlphabet)
    (v : Fin (dispatchWidth R) → Bool) : RankedAlphabet.Scan
theorem decodeState_stateWord_of_lt (R : RankedAlphabet)
    (s : RankedAlphabet.Scan) (h : s.buf.length < R.width) :
    decodeState R (bits (dispatchWidth R) (stateWord R s)) =
      { s with depth := min s.depth (R.maxArity + 1) }
```

The branch family's domain is `Fin (dispatchWidth R) → Bool` at a symbolic
width, so recovering the fields index by index would carry a bound proof at
every step. `decodeState` avoids that by passing through
`List.ofFn v : List Bool` and reading the fields with the `List` API: the
liveness flag is `headD`; the slot is `take R.width` of the tail, whose padding
is removed by `dropWhile (· == false)` and whose sentinel by `tail`; the capped
depth is the length of `takeWhile id` of what follows the slot. Every operation
is structural, so no `Fin` arithmetic and no `Fintype`-derived decidability
arises, and the definition depends on no axiom.

It returns a `RankedAlphabet.Scan` rather than a tuple, that record being
exactly the three fields. Since `Scan` derives no `DecidableEq`,
`decodeState_stateWord_of_lt` is swept field by field in the mirror rather than
as one equation.

### The recognizer

```lean
@[expose] def nextPrefix (R : RankedAlphabet) (b : Bool)
    (s : RankedAlphabet.Scan) : List Bool
@[expose] def dropCount (R : RankedAlphabet) (b : Bool)
    (s : RankedAlphabet.Scan) : ℕ
@[expose] def rankedStep (R : RankedAlphabet) (b : Bool) : COf 1 :=
  diagOf (casesOf (dispatchWidth R) fun v ↦
    prependOf (nextPrefix R b (decodeState R v))
      (predIterOf (dropCount R b (decodeState R v))))
@[expose] def rankedSem (R : RankedAlphabet) : Sem 1 :=
  scanSem (constAtOf (stateWord R ⟨[], 0, true⟩)) (rankedStep R false)
    (rankedStep R true) (R.width + 1)
theorem rankedSem_def (R : RankedAlphabet) :
    rankedSem R = scanSem (constAtOf (stateWord R ⟨[], 0, true⟩))
      (rankedStep R false) (rankedStep R true) (R.width + 1)

theorem dropCount_min_depth (R : RankedAlphabet) (b : Bool)
    (s : RankedAlphabet.Scan) :
    dropCount R b { s with depth := min s.depth (R.maxArity + 1) } = dropCount R b s
theorem nextPrefix_min_depth (R : RankedAlphabet) (b : Bool)
    (s : RankedAlphabet.Scan) :
    nextPrefix R b { s with depth := min s.depth (R.maxArity + 1) } = nextPrefix R b s
theorem stateWord_scanStep_of_lt (R : RankedAlphabet) (b : Bool)
    (s : RankedAlphabet.Scan) (h : s.buf.length < R.width) :
    stateWord R (R.scanStep b s) =
      nextPrefix R b s ++ (stateWord R s).drop (dropCount R b s)
theorem rankedSem_eq (R : RankedAlphabet) (w : List Bool) :
    rankedSem R ![w] = stateWord R (R.scanFinal w)
theorem length_rankedSem_le (R : RankedAlphabet) (w : List Bool) :
    (scanSem (constAtOf (stateWord R ⟨[], 0, true⟩)) (rankedStep R false)
      (rankedStep R true) (R.width + 1) ![w]).length ≤ w.length + R.width + 1
@[expose] def ranked (R : RankedAlphabet) : C
@[expose] def rankedOf (R : RankedAlphabet) : COf 1
theorem rankedSem_eq_eval (R : RankedAlphabet) :
    transport (rankedOf R).2 (rankedOf R).1.eval = rankedSem R
```

Every branch has one shape: drop a statically known number of bits, and prepend
a statically known word. `dropCount R b s` is `1 + R.width` in four of
`RankedAlphabet.scanStep`'s five clauses — dead-absorb, accumulate,
`arOf = none` and `r > depth` all leave `depth` untouched — and
`1 + R.width + r` in the fifth, where a symbol of arity `r` pops.
`nextPrefix R b s` is the rebuilt liveness flag and block slot: on the
dead-absorb clause it is `false :: bufBits R s.buf`, `scanStep` returning the
state unchanged there, buffer included; on the two failure clauses it is
`false :: bufBits R []`, both returning `⟨[], _, false⟩`; on the accumulate
clause `true :: bufBits R (b :: s.buf)`; and on the pop
`true :: bufBits R [] ++ [true]`, the trailing bit being the pushed subterm.

`dropCount_min_depth` and `nextPrefix_min_depth` are what let the step lemma
compose with the decoder. `decodeState_stateWord_of_lt` recovers the state only
up to capping `depth` at `R.maxArity + 1`, while `stateWord_scanStep_of_lt` is
stated at `s`; the two agree because the only depth-dependence in either is the
`r ≤ s.depth` test of `scanStep`, and `le_maxArity_of_arOf_eq_some` gives
`r ≤ R.maxArity < R.maxArity + 1`. That is what that lemma is for.

`stateWord_scanStep_of_lt` is the step lemma the module rests on, and
`rankedSem_eq` is its `List.rec` over `w` through `scanSem_eq`, with
`length_buf_scanFinal_lt` supplying the hypothesis at each state,
`decodeState_stateWord_of_lt` carrying it to the bit family the branch is
selected by, the two capping lemmas closing the gap, and `stepWord_prependOf`
with `stepWord_predIterOf` turning the selected branch into the prefix-and-drop
the step lemma states.

`length_rankedSem_le` follows: `length_stateWord_of_lt` gives
`1 + R.width + s.depth`, and `depth_scanFinal_le_length` gives `depth ≤ |w|`.
The sharper `depth ≤ ⌊|w| / R.width⌋` is true but needs the block-alignment
lemma on top of it, and the bound consumed does not require it. At the empty
word the bound is `R.width + 1 ≤ 0 + R.width + 1`, tight. It is stated at
`scanSem`, which is the form `Cobham.scan` consumes and the form `Tree.lean`
states `length_combSem_le` in; `rankedSem_def` bridges the two, as
`combSem_def` does there.

### The verdict and the bridge

```lean
@[expose] def acceptWord (R : RankedAlphabet) : List Bool :=
  stateWord R ⟨[], 1, true⟩
@[expose] def acceptTestRaw (R : RankedAlphabet) : sig.toPFunctor.W
@[expose] def acceptTest (R : RankedAlphabet) : COf 1
@[expose] def isRankedRaw (R : RankedAlphabet) : sig.toPFunctor.W
@[expose] def isRanked (R : RankedAlphabet) : C
@[expose] def isRankedOf (R : RankedAlphabet) : COf 1
@[expose] def isRankedSem (R : RankedAlphabet) : Sem 1
theorem isRankedSem_eq_eval (R : RankedAlphabet) :
    transport (isRankedOf R).2 (isRankedOf R).1.eval = isRankedSem R
theorem isRankedSem_apply (R : RankedAlphabet) (w : List Bool) :
    isRankedSem R ![w] = stepWord (acceptTest R) (rankedSem R ![w])

theorem isRankedSem_eq_ite (R : RankedAlphabet) (w : List Bool) :
    isRankedSem R ![w] = if R.Valid w then [true] else []
theorem isRankedSem_eq_singleton_iff_valid (R : RankedAlphabet)
    (w : List Bool) : isRankedSem R ![w] = [true] ↔ R.Valid w
theorem isRankedSem_binRanked_eq_singleton_iff_isTreeSem (w : List Bool) :
    isRankedSem RankedAlphabet.Binary.binRanked ![w] = [true] ↔
      isTreeSem ![w] = [true]
```

`RankedAlphabet.validBool` asks that the scan end live, with an empty
incomplete block and exactly one pending subterm, so the accepting state is
`⟨[], 1, true⟩` and `acceptWord R` is `stateWord R` of it, of length
`R.width + 2`. The test `acceptTest R` is `diagOf` of `casesOf` at
`R.width + 3` bits — one past the accepting word, so that a `depth` above one
is rejected — whose branch at `v` is `constAtOf [true]` where
`List.ofFn v = acceptWord R ++ [false]` and `constAtOf []` otherwise. The
decision is taken on `List Bool`, whose `DecidableEq` depends on no axiom,
rather than on `Fin (R.width + 3) → Bool`, whose instance routes through
`Fintype.decidablePiFintype` and `Classical.choice`.

`isRankedRaw` composes that test with `ranked R` through a `comp 1 1` node, as
`Cobham/Tree.lean`'s `isTreeRaw` composes `eqOneRaw` with `combRaw`.
`isRankedSem_apply` states the composition's value, and is not a `rfl` for the
reason `Cobham/Tree.lean`'s `## Implementation notes` record for
`isTreeSem_apply`: `pred` in the composition is a `boundedRec` node, so the
proof rewrites to the composition's own application, generalizes the scan's
value, and matches on it.

`isRankedSem_eq_ite` pins the value on the rejecting branch as well as the
accepting one, for the reason `Cobham/Tree.lean`'s module docstring records for
`isTreeSem_eq_ite`: the `iff` alone
admits a recognizer returning `[false]` on a rejected word, so correctness as a
function is not implied by correctness of the accepted set. Both `iff`
statements are proved from their two implications rather than by `omega`, which
pulls `Classical.choice` on an `Iff` goal.

The bridge chains `isRankedSem_eq_singleton_iff_valid` at `binRanked`,
`RankedAlphabet.Binary.valid_iff` and `isTreeSem_eq_singleton_iff_valid`. Every
link relates semantic predicates on `List Bool`, so neither `binRanked`'s
`width` and `maxArity` nor the two recognizers' differing failure conventions
need reconciling. `Cobham/Tree.lean` keeps `comb` and `isTree`, so
`isTree_smashFree` and the [Strahm2003] Theorem 1(2) reasoning keep their
subject.

## Segment 3: `Cobham/Fold.lean`

### Interface

```lean
universe u
variable {α : Type u} {p : ℕ} (enc : α → Fin p → Bool)
         (dec : (Fin p → Bool) → α) (init : α) (step : Bool → α → α)
```

The carrier is arbitrary, and its finiteness enters only through the existence
of the `p`-bit encoding. `dec` is total and unconstrained off the image of
`enc`, the fold's state never being anything but an encoded carrier value.
Neither `Fintype` nor `FinEnum` appears, which keeps the module clear of the
ordered-algebra and `Finset` instances the axiom rules warn about.

The retraction hypothesis `hdec : ∀ a, dec (enc a) = a` is not a section
variable. Lean includes a section variable only where the statement mentions
it, so a hypothesis used only inside a proof would be out of scope there; it is
written as an explicit binder on the one theorem that needs it.

### Construction and statements

```lean
@[expose] def foldStep (b : Bool) : COf 1 :=
  diagOf (casesOf p fun v ↦ constAtOf (List.ofFn (enc (step b (dec v)))))
@[expose] def foldSem : Sem 1 :=
  scanSem (constAtOf (List.ofFn (enc init))) (foldStep enc dec step false)
    (foldStep enc dec step true) p
theorem foldSem_def : foldSem enc dec init step =
  scanSem (constAtOf (List.ofFn (enc init))) (foldStep enc dec step false)
    (foldStep enc dec step true) p

theorem length_foldSem_le (w : List Bool) :
    (scanSem (constAtOf (List.ofFn (enc init))) (foldStep enc dec step false)
      (foldStep enc dec step true) p ![w]).length ≤ w.length + p
@[expose] def fold : C
@[expose] def foldOf : COf 1
theorem foldSem_eq_eval :
    transport (foldOf enc dec init step).2 (foldOf enc dec init step).1.eval =
      foldSem enc dec init step

theorem foldSem_eq (hdec : ∀ a, dec (enc a) = a) (w : List Bool) :
    foldSem enc dec init step ![w] = List.ofFn (enc (w.foldr step init))
```

Neither the encoding-to-word nor the carrier-level fold is named: they are
`List.ofFn (enc a)` and `w.foldr step init`, spelled at the length a name would
cost, and `List` supplies both. This revises the note in
[TODO.md](../../../TODO.md) § Extensions of the tree recognizers, which records
that the encoding "must be named"; naming it is unnecessary once it is
`List.ofFn ∘ enc`, and the type distinction the note is about survives,
`foldSem … ![w]` being a `List Bool` and `w.foldr step init` an `α`.

`foldr` is the fold `Cobham.scanSem_eq` presents the scan as, and the direction
`Cobham.evalRec` recurses in: `evalRec` peels the list's head, which is the
word's last bit, and the recursive value it passes alongside is the fold of the
remainder. The statement is over the Lean list on both sides, so no convention
about which end of the word the list's head denotes enters it.

`length_foldSem_le` does not take `hdec`: every state the scan produces is a
`List.ofFn` of an `enc` value — the base by `baseWord_constAtOf`, each step by
`stepWord_constAtOf` — so its length is `p` whatever `dec` does, and
`List.length_ofFn` gives `p ≤ w.length + p`, tight at the empty word, with
`growth = p`. Consequently `fold`, `foldOf` and `foldSem_eq_eval` take no
retraction hypothesis either.

`foldSem_eq` is the module's content, and is where `hdec` enters. Its two sides
inhabit different types before `List.ofFn ∘ enc` is applied, so the encoding is
applied rather than the two equated. The proof is `List.rec` over `w` through
`scanSem_eq`; the step needs `bits_ofFn`, and then `dec (enc a) = a` identifies
the branch the case tree selects with `step b a`.

## Additions to the ranked-encoding modules

A definition and four statements segment 2 consumes that
`Geb/Mathlib/Data/Tree/Ranked/` does not carry. Each is added to the module
whose subject it is, in segment 2, and each is written unprefixed inside that
module's existing `namespace RankedAlphabet` block, an explicit prefix inside
it elaborating to a doubled name.

In `Ranked/Basic.lean`:

```lean
@[expose] def maxArity (R : RankedAlphabet) : ℕ :=
  (List.ofFn R.arity).foldr max 0
theorem arity_le_maxArity (R : RankedAlphabet) (i : Fin R.card) :
    R.arity i ≤ R.maxArity
```

Derived rather than a new field. The `foldr`-over-`List.ofFn` form is used in
place of `Finset.sup`, and the bound is established through `Nat.le_max_left`
and `Nat.le_max_right` inside a `List.rec` rather than through the
ordered-algebra API, which is the discipline `size_le_sum_ofFn` in the same
module records.

In `Ranked/Code.lean`, which is where `arOf` lives and which imports
`Basic.lean`:

```lean
theorem le_maxArity_of_arOf_eq_some (R : RankedAlphabet) {v r : ℕ}
    (h : R.arOf v = some r) : r ≤ R.maxArity
```

`arOf` returns `some (R.arity ⟨v, h⟩)` when `v < R.card` and `none` otherwise,
so every arity it yields lies in the image of `R.arity`. This is what makes
`dispatchWidth`'s `R.maxArity + 1` depth window sufficient, and it is consumed
by `dropCount_min_depth` and `nextPrefix_min_depth`.

In `Ranked/Preorder.lean`:

```lean
theorem length_buf_scanFinal_lt (R : RankedAlphabet) (w : List Bool) :
    (R.scanFinal w).buf.length < R.width
theorem depth_scanFinal_le_length (R : RankedAlphabet) (w : List Bool) :
    (R.scanFinal w).depth ≤ w.length
```

`length_buf_scanFinal_of_live` gives the first for a live scan already, as
`w.length % R.width`; the unconditional statement additionally needs that a
dead scan carries `buf = []`, which holds because both failure clauses of
`scanStep` return `⟨[], _, false⟩` and a dead state absorbs.
`depth_scanFinal_le_length` is a `List.rec`: every clause leaves `depth` alone
except the pop, which yields `depth - r + 1 ≤ depth + 1`.

## What is out of scope

- **`SmashFree (ranked R)` and `SmashFree (isRanked R)`.** `Cobham/Tree.lean`
  carries `isTree_smashFree`, and with [Strahm2003] Theorem 1(2) that places
  `isTree` in the functions computable in polynomial time and linear space. The
  generic recognizer gets no such statement here: `smashFreeBool` is a
  `WType.elim` over the whole tree, so at a symbolic `R` it is not
  `decide`-dischargeable and needs a recursion mirroring `wValid_casesRaw`, and
  at a concrete `R` it forces every node. Nothing in this design uses `smash`,
  so the statement is expected to hold; it is left to the branch that needs it.
- **B4**, absorbing `BinTree` into `RankedAlphabet.Term`, and **B5**, the
  linear time and space bound against Cslib's `MultiTapeTM`.
- The duplications against the new combinators — `oneAtOf` and `falseAtOf`
  against `constAtOf`, and `predPred` against `predIter 2` — recorded as
  deferrals in [TODO.md](../../../TODO.md). Whether substituting them preserves
  the `rfl` proofs `Cobham/Tree.lean` reads through them is unmeasured, and
  this branch takes nothing from measuring it.

## Test mirrors

Under `GebTests/Mathlib/Computability/Cobham/`, each naming a `def` value built
from the module under test rather than asserting inside an anonymous `example`,
since `lake shake` infers imports from the constants an olean references and
reports an import used only by an `example` as removable. Each carries a module
docstring, `docs/rules/lean-coding.md` § Comment and docstring rules exempting
no `.lean` file.

- **`Cases.lean`** — `casesSem` at a literal `p` against an explicitly
  tabulated branch family, with a scrutinee shorter than `p` to pin the
  zero-padding convention and one longer than `p` to pin that the high bits are
  ignored; and the four combinators' semantic lemmas at literal arguments.
- **`RankedTree.lean`** — `isRankedSem` against `RankedAlphabet.validBool` at
  `RankedAlphabet.Binary.binRanked` and at `narrowAlphabet`, whose
  `card < 2 ^ width` makes a block spell no symbol so that the `arOf = none`
  branch is reached; `decodeState_stateWord_of_lt` at each reachable `buf`
length, swept field by field since `Scan` derives no `DecidableEq`; and
`bufBits` at a `buf` of length `R.width` to pin that `length_bufBits_of_lt`'s
hypothesis is consumed rather than decorative.
- **`Fold.lean`** — a carrier whose `dec` is not injective off the image of
  `enc`, so that the retraction hypothesis is exercised rather than trivially
  satisfied.

Sweep length is set by measurement rather than by the length-eight convention
the earlier mirrors use: a dispatch at `p = 6` is not free, and `wordsUpTo 8`
is 511 words totalling 3586 scan steps, each a dispatch plus a `prepend` chain,
a `predIter` chain and the `scanRaw` layer, in elaboration and again in the
kernel. Each mirror sweeps to whatever length keeps its module within the build
budget the rest of `GebTests` sets, and records the length reached.
`set_option maxRecDepth` is valid in tactic position; `native_decide` is
forbidden, carrying a compiler-trust axiom.

## Documentation and commits

Each segment carries a `docs/index.md` entry and a `TODO.md` revision, in the
shape B1 and B2 use; `TODO.md` § Extensions of the tree recognizers records B6
and B3 as done in the segments completing them, gains the `oneAtOf`,
`falseAtOf` and `predPred` deferrals, and has its B3 note on naming the
encoding revised.

The index modules `Geb/Mathlib/Computability/Cobham.lean` and
`GebTests/Mathlib/Computability/Cobham.lean` gain an import of each new module
in its segment; without both, the new modules are not built.

Segment 2's additions to
`Geb/Mathlib/Data/Tree/Ranked/{Basic,Code,Preorder}.lean` carry their own
mirrors in `GebTests/Mathlib/Data/Tree/Ranked/`, which already exist, and their
own `docs/index.md` revisions. `docs/index.md`'s entry for `Cobham/Basic.lean`
is revised in segment 1 for `semAt`, the combinator families and the `zeroAt`
family arriving.

Each new module, source and mirror alike, carries the module docstring sections
[docs/rules/lean-coding.md](../../rules/lean-coding.md) § Documentation
mandates, in order and non-vacuously, and a `/-- … -/` docstring on every `def`
and on every theorem of public interest. Every modified module's own docstring
is updated in the segment modifying it: `Cobham/Basic.lean` for `semAt` and the
combinator families, `Cobham/Scan.lean` and `Cobham/Tree.lean` for the
restatement through `semAt` and for the `zeroAt` family leaving `Tree.lean`'s
`## Main definitions` and `## Implementation notes`, and each of
`Ranked/{Basic,Code,Preorder}.lean` for the statements it gains.

The `## Implementation notes` sections carry the decisions recorded here that
outlive this document: the scrutinee shift, the `bufBits` sentinel, the unary
`depth`, `decodeState`'s route through `List.ofFn`, the three
`Classical.choice` routes avoided, and the reason `length_foldSem_le` precedes
the retraction hypothesis and does not take it.

Commit subjects follow
[docs/rules/ci-and-workflow.md](../../rules/ci-and-workflow.md)
§ Commit-message convention — imperative present, no capital, no trailing
period, and a type from the list. This document is transient: it is removed in
the final commits of the last segment needing it, per
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape.

## What is compiled

`Geb/Internal/CasesSpike.lean` is in the working tree and compiles `bits`,
`semAt`, `shiftRaw`, `wIndexRoot_shiftRaw`, `wValid_shiftRaw`, `shiftW`,
`arity_shiftW`, `semAt_shiftW`, `casesRaw`, `wIndexRoot_casesRaw`,
`wValid_casesRaw`, `casesW`, `arity_casesW`, `casesSem`, `bits_succ` and
`casesSem_eq`. It declares `namespace Cobham` under the same names the real
module will, is absent from `Geb/Internal.lean` while it sits there — the build
reaches it through `lakefile.toml`'s `Geb.*` glob — and is deleted before
`Cobham/Cases.lean` lands. Established there:

- `Nat.rec` at the motive
  `((Fin p → Bool) → sig.toPFunctor.W) → sig.toPFunctor.W` elaborates, and the
  reindexing by `Fin.cons` in the recursive calls is accepted.
- `wValid_casesRaw`, `semAt_shiftW` and `casesSem_eq` each measure
  `[propext, Quot.sound]`.
- `casesSem (p + 1) br ![b :: t, x]` is definitionally the shifted subtree's
  meaning, so the successor step of `casesSem_eq` needs no `change`; it opens
  by rewriting with `bits_succ`, and the base case by the `Fin.elim0` equality.

Established against throwaway modules since deleted, and rebuilt as each
segment's plan is written rather than taken on trust: the `semAt` restatement
preserving `scanSem_nil`, `scanSem_eq_eval`, `combSem_nil`,
`isTreeSem_eq_eval` and `scanSem_cons`'s `change`; `decodeState` via
`List.ofFn` inverting `bufBits` and returning the capped depth, at no axiom;
`dropCount`, `nextPrefix` and the decomposition `stateWord_scanStep_of_lt` at
`narrowAlphabet` over every reachable state and both bits;
`dropCount_min_depth` and `nextPrefix_min_depth` likewise; the `R.width + 3`
verdict window separating every non-accepting reachable state; `maxArity`,
`dispatchWidth`, `List.ofFn` and `Matrix.vecCons` reducing in the kernel at
`narrowAlphabet`'s shape; `length_buf_scanFinal_lt`,
`depth_scanFinal_le_length`, `maxArity`, `arity_le_maxArity`,
`le_maxArity_of_arOf_eq_some` and `bits_ofFn` at symbolic `R`; the `constAtOf`
word lemmas with no constraint on `dec`; `diagOf` and `predIterOf` with their
semantic lemmas; `acceptWord R = stateWord R ⟨[], 1, true⟩` by `rfl`; and a
reduction of `casesSem` at `p = 7` against a branch family varying in every
bit, closing by `rfl` in well under a second. The three `Classical.choice`
claims in § Constraints were each measured.

**Segment 1 has landed.** It is in the tree at `feat/cobham-cases`, not in a
prototype: `Cobham/Cases.lean` with its mirror, and the `semAt`, `zeroAt`,
`predIter`, `prepend`, `constAt` and `diag` families in `Cobham/Basic.lean`.
`lake build`, `lake test`, `lake lint`, `lake lint -- GebTests` and
`scripts/pre-push.sh` all pass over it. § Segment 1 below is therefore a record
of what was built rather than a specification of what to build; the segments
still to build are 2 and 3.

While segment 1 was a prototype under `Geb/Internal/`, its axioms had to be
measured declaration by declaration: `lake lint` lints the `Geb` umbrella's
import closure, `Geb/Internal.lean` did not import the prototype, and
`scripts/tests/test-lint-driver.sh` reported it as escaping the linter. That
consideration applies to segment 2's and segment 3's prototypes in turn.

`ofFn_bits` proved through `List.ext_getElem` and `omega` measured
`[propext, Classical.choice, Quot.sound]`; the structural induction over the
width that replaces it is clean. That is the `omega` route § Constraints names,
observed rather than predicted.

Not built: `isRankedRaw`, `acceptTestRaw` and `acceptTest`; `decodeState`,
`nextPrefix` and `dropCount` as functions of a bit family at symbolic width;
`rankedSem_eq`, `foldSem_eq` and segments 2 and 3's `…_eq_eval`. What was built
of the verdict is the `R.width + 3` window's separating property at
`narrowAlphabet`, not any expression computing it.

## Risks and open questions

| Risk | Effect | Response |
| --- | --- | --- |
| `decodeState`, `nextPrefix` and `dropCount` are built only at `narrowAlphabet` | Segment 2's step may not generalize to symbolic `R` | Prototype at symbolic `R` before segment 2's plan, as segment 1 was; the `List.ofFn` route removes the `Fin` bound-threading that made it hard |
| Elaboration and kernel cost of the sweeps | A mirror that does not build inside the project's budget | Sweep to a measured length rather than a conventional one; `maxArity` and `dispatchWidth` are known to reduce to numerals |
| `stateWord` is injective only under `length_buf_scanFinal_lt` | A step lemma false off the reachable states | The invariant is a named lemma consumed by `length_bufBits_of_lt` and `length_stateWord_of_lt`, and a mirror pins a state violating it |
| Whether the two statements are published | A missing citation, or a wrongly claimed novelty | Search with `theoremsearch` and `arxiv-mcp-server` for both before either module docstring is written; record any key found in `docs/references.bib` |
| The `oneAtOf`, `falseAtOf` and `predPred` deferrals | Duplications carried for no reason | Measured, not argued, by whichever branch takes them up: substitute and see whether `combSem_nil` and `isTreeSem_eq_eval` still close by `rfl` |

## References

- [Cobham1965] — the class and the arity relation of bounded recursion on
  notation.
- [HeraudNowak2011] — the `Rec` form `Cobham/Basic.lean` transcribes for `pred`
  and `cond`.
- [Strahm2003] — Theorem 1(2), the polynomial-time and linear-space containment
  of the `smash`-free subalgebra, which the bridge preserves for `isTree`.
