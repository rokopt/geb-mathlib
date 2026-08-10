# Definition by cases, the finite-carrier fold, and the generic ranked recognizer

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [Segments, and where each declaration lands](#segments-and-where-each-declaration-lands)
- [Transcription status of each definition](#transcription-status-of-each-definition)
- [Constraints this design is bound by](#constraints-this-design-is-bound-by)
- [The meaning of a tree at an arity](#the-meaning-of-a-tree-at-an-arity)
- [Concern 1: `Cobham/Cases.lean`](#concern-1-cobhamcaseslean)
  - [Selection by the bits of a scrutinee](#selection-by-the-bits-of-a-scrutinee)
  - [The scrutinee shift](#the-scrutinee-shift)
  - [The case tree](#the-case-tree)
  - [The combinator and its meaning](#the-combinator-and-its-meaning)
- [Concern 2: `Cobham/Fold.lean`](#concern-2-cobhamfoldlean)
  - [Additions to `Cobham/Basic.lean` in this segment](#additions-to-cobhambasiclean-in-this-segment)
  - [Interface](#interface)
  - [Construction and statements](#construction-and-statements)
- [Concern 3: `Cobham/RankedTree.lean`](#concern-3-cobhamrankedtreelean)
  - [The state as a bitstring](#the-state-as-a-bitstring)
  - [Inverting the state word](#inverting-the-state-word)
  - [The recognizer](#the-recognizer)
  - [The verdict and the bridge](#the-verdict-and-the-bridge)
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
   to a second argument. It imposes no condition on the expressions it selects
   among.
2. **The fold at a finite carrier.** The catamorphism of the list of bits at a
   carrier admitting a `p`-bit encoding, as an instance of the scan combinator
   `Cobham.scan`.
3. **The generic ranked recognizer.** The validity scan of
   `RankedAlphabet.Preorder` as an expression of Cobham's class, at an
   arbitrary ranked alphabet, together with the theorem identifying it at the
   two-symbol alphabet with the recognizer `Cobham/Tree.lean` already carries.

Concern 1 exists because concern 3 needs it: the recognizer's step must resolve
`RankedAlphabet.arOf` at a completed block, whose width is a parameter rather
than a literal, so the dispatch cannot be written out.

Concern 2's return is mathematical rather than structural: `foldSem_eq` is the
containment of the finite-state transductions in Cobham's class, and that is
not an instance of concern 3, whose state is unbounded. It is not needed to
justify concern 1, and it has no consumer in the repository; the containment is
what it delivers.

## Segments, and where each declaration lands

The three concerns are appended to the existing topic branch in the order
above, each with a bookmark at its boundary, so that each is submitted as its
own pull request while the graph stays linear and conflict-free. Order is a
choice about conflicts, not a dependency chain: concern 3 does not depend on
concern 2, `Cobham/Fold.lean`'s carrier having to admit a `p`-bit encoding
while `RankedAlphabet.Scan.depth` is unbounded.

Each shared declaration lands in the segment that first consumes it, so that no
pull request presents unused interface. `Cobham/Basic.lean` is edited by all
three.

| Segment | New module | Added to `Cobham/Basic.lean` | Elsewhere |
| --- | --- | --- | --- |
| 1 | `Cases.lean` | `semAt` | `Scan.lean` and `Tree.lean` restated through `semAt` |
| 2 | `Fold.lean` | `zeroAt` family moved in; `prependWord`, `constAt`, `diagOf` | — |
| 3 | `RankedTree.lean` | `predIterOf` | four statements added to `Data/Tree/Ranked/` |

A characterisation naming `baseWord` or `stepWord` cannot be stated in
`Cobham/Basic.lean`: both are declared in `Cobham/Scan.lean`, which imports
`Basic.lean`. Each such lemma is therefore stated in the module that consumes
it — `Fold.lean` or `RankedTree.lean` — while the definition it characterises
sits in `Basic.lean`.

Each of `prependWord`, `constAt`, `diagOf` and `predIterOf` is a family in the
shape `Cobham/Scan.lean` and `Cobham/Tree.lean` both use, not a single
declaration: a `…Raw` tree, its `wIndexRoot` and `wValid` lemmas, its
`RecBounded` lemma, the `COf n` expression, and its semantic lemma. Six
declarations each is the realistic figure.

## Transcription status of each definition

Per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature when
transcribing, every definition below is novel — an assembly of the generators
`Cobham/Basic.lean` transcribes from [HeraudNowak2011] and [Cobham1965].

Two containments realized here may be published statements rather than novel
ones: that finite-state transductions lie in Cobham's class, which concern 2
realizes, and that the languages of ranked-term preorder spellings do, which
concern 3 realizes. Neither is cited to a work yet. The search is an open
question below, settled before either module docstring is written, per
[AGENTS.md](../../../AGENTS.md) § Verify agent claims.

## Constraints this design is bound by

- **No `noncomputable`, and `Classical.choice` excluded.** Every declaration
  measures `[propext, Quot.sound]`, which `lake lint` enforces. Two routes into
  `Classical.choice` are live here and are avoided by name: `omega` discharging
  an `Iff` goal pulls it in, so an equivalence is proved from the two
  implications; and `DecidableEq (Fin n → Bool)` resolves through
  `Fintype.decidablePiFintype`, so every decision below is taken over
  `List Bool` after `List.ofFn`, whose `DecidableEq` is structural.
- **Recursion through recursors.** No `def` calls itself and no `induction`
  tactic appears; every recursion is an explicit `Nat.rec`, `List.rec` or
  `WType.elim` application.
- **`decide` discharges admissibility only at a named constant.** Instance
  search finds `Decidable (sig.WValid w)` when `w` is a constant but not when
  it is a literal `WType.mk` application, and at a free arity or a variable `p`
  nothing reduces at all. Every admissibility proof here is written out, in the
  shape `Cobham.wValid_boundRaw` and `Cobham.zeroAt` both set.
- **Transport along an opaque equation does not disappear.** It disappears by
  proof irrelevance when both sides reduce to the same literal. A node's own
  arity reduces whatever its children are; a component's does not. Where the
  two forms must be identified, `Cobham.transport_transport` is the bridge.
- **The class reaches only a bounded prefix of a word.** `pred` drops the head,
  `succ` prepends, and `cond` tests the head, so an expression of bounded size
  inspects and rewrites only a bounded prefix. This determines the field order
  of concern 3's state.
- **`Nat` subtraction is truncated.** `bufBits` below has its intended length
  only under an invariant on `buf`'s length, stated as a lemma rather than
  assumed.
- **Universes are declared.** `universe u` and `variable {α : Type u}`; `Type*`
  auto-binds a `u_1`-style variable and appears nowhere in `Geb/`.

## The meaning of a tree at an arity

```lean
@[expose] def semAt (n : ℕ) (e : sig.W) (he : arity e = n) : Sem n :=
  transport ((fst_eval e).trans he) (eval e).2
```

Added to `Cobham/Basic.lean` in segment 1, beside `transport` and `fst_eval`,
on which alone it depends. It is not new content: `boundSem`, `scanSem`,
`baseWord` and `stepWord` in `Cobham/Scan.lean`, and `eqOneSem` and
`isTreeSem` in `Cobham/Tree.lean`, each spell it out. Those are restated
through it in the same segment, so that the pattern is named once rather than a
seventh time. The definitions are unchanged in meaning and `semAt` is
`@[expose]`, so the `rfl` proofs downstream of them are expected to survive;
that expectation is a risk recorded below, not an assumption.

## Concern 1: `Cobham/Cases.lean`

Every declaration in this section other than `cases`, `casesOf` and
`casesSem_eq_eval` is compiled; see [What is compiled](#what-is-compiled).

### Selection by the bits of a scrutinee

```lean
@[expose] def bits (p : ℕ) (w : List Bool) : Fin p → Bool :=
  fun j ↦ w.getD j false
```

Bit `j` of the scrutinee, `false` past its end. Reading a short scrutinee as
zero-padded, rather than conditioning the semantic theorem on `p ≤ w.length`,
keeps `casesSem_eq` free of a hypothesis, and in the tree it costs nothing:
`cond`'s empty branch is directed at the same subtree as its head-`false`
branch.

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
single reduction is linear in `p`, measured below.

### The combinator and its meaning

```lean
@[expose] def casesW (p : ℕ) (br : (Fin p → Bool) → COf 1) : sig.W
theorem arity_casesW (p : ℕ) (br : (Fin p → Bool) → COf 1) :
    arity (casesW p br) = 2
@[expose] def casesSem (p : ℕ) (br : (Fin p → Bool) → COf 1) : Sem 2 :=
  semAt 2 (casesW p br) (arity_casesW p br)

theorem bits_succ (p : ℕ) (w : List Bool) :
    bits (p + 1) w = Fin.cons (w.getD 0 false) (bits p w.tail)

theorem casesSem_eq : ∀ (p : ℕ) (br : (Fin p → Bool) → COf 1)
    (sel x : List Bool),
    casesSem p br ![sel, x] = stepWord (br (bits p sel)) x

@[expose] def cases (p : ℕ) (br : (Fin p → Bool) → COf 1) : C
@[expose] def casesOf (p : ℕ) (br : (Fin p → Bool) → COf 1) : COf 2
theorem casesSem_eq_eval (p : ℕ) (br : (Fin p → Bool) → COf 1) :
    transport (casesOf p br).2 (casesOf p br).1.eval = casesSem p br
```

`cases` and `casesOf` carry no side condition. `RecBounded` is discharged
componentwise from the branches' own, by a `Nat.rec` mirroring
`wValid_casesRaw`: every node the recursion introduces is a `comp`, where
`RecBoundedValue` is `True`, and its children are `proj` together with `cond`
and `pred`, which are members of `C` and so already carry their own
`RecBounded` as `cond.1.2` and `pred.1.2`. Neither `cond` nor `pred` is a
`comp` node; what makes them free here is that their conditions are discharged
where they are defined, not that those conditions are vacuous.

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

## Concern 2: `Cobham/Fold.lean`

### Additions to `Cobham/Basic.lean` in this segment

`zeroAtRaw`, `zeroAt` and `zeroAtOf` move from `Cobham/Tree.lean`, unchanged.
`constAt` needs a nullary constant at an arbitrary arity, and `Cobham/Tree.lean`
imports `Cobham/Basic.lean` rather than the reverse, so they cannot be referred
to where they stand. None of the three carries a `decide`: `Tree.lean`'s
implementation notes record that `zeroAtRaw`, `oneAtRaw` and `falseAtRaw`
"carry a free arity, at which `decide` does not apply", and their admissibility
is written out. The move is a relocation of unchanged text.

```lean
@[expose] def prependWord {n : ℕ} (u : List Bool) (e : COf n) : COf n
@[expose] def constAt {n : ℕ} (u : List Bool) : COf n := prependWord u (zeroAtOf n)
@[expose] def diagOf (e : COf 2) : COf 1
```

`prependWord` is the chain of `succ` nodes prepending a fixed word to what `e`
computes, by `List.rec` on `u`. `diagOf` is a `comp 1 2` node over `e` and two
`proj 1 0` children. Their characterisations name `baseWord` and `stepWord`, so
they are stated in this module rather than in `Basic.lean`:

```lean
theorem baseWord_constAt (u : List Bool) : baseWord (constAt u) = u
theorem stepWord_constAt {n : ℕ} (u r : List Bool) : stepWord (constAt u) r = u
theorem stepWord_diagOf (e : COf 2) (u : List Bool) :
    stepWord (diagOf e) u = semAt 2 e.1.1 e.2 ![u, u]
```

`Cobham.baseWord_eq_eval` states only that `baseWord` agrees with what the
expression carries and says nothing about the value, so it does not supply
these.

`Cobham/Tree.lean`'s `oneAtOf` and `falseAtOf` are `constAt [true]` and
`constAt [false]` and are left as they are, recorded as a deferral in
[TODO.md](../../../TODO.md). The reason is not `decide`: it is that
`prependWord` changes the definitional unfolding, and `Tree.lean` proves
`combSem_nil` and `isTreeSem_eq_eval` by `rfl` through those constants.
Whether those `rfl` proofs survive the substitution is unmeasured, and this
line takes no return from finding out.

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
  diagOf (casesOf p fun v ↦ constAt (List.ofFn (enc (step b (dec v)))))
@[expose] def foldSem : Sem 1 :=
  scanSem (constAt (List.ofFn (enc init))) (foldStep enc dec step false)
    (foldStep enc dec step true) p
theorem foldSem_def : foldSem enc dec init step = scanSem …

theorem length_foldSem_le (w : List Bool) :
    (scanSem (constAt (List.ofFn (enc init))) (foldStep enc dec step false)
      (foldStep enc dec step true) p ![w]).length ≤ w.length + p
@[expose] def fold : C
@[expose] def foldOf : COf 1
theorem foldSem_eq_eval

theorem foldSem_eq (hdec : ∀ a, dec (enc a) = a) (w : List Bool) :
    foldSem enc dec init step ![w] = List.ofFn (enc (w.foldr step init))
```

Neither the encoding-to-word nor the carrier-level fold is named: they are
`List.ofFn (enc a)` and `w.foldr step init`, spelled at the length a name would
cost, and `List` supplies both. This revises the note in
[TODO.md](../../../TODO.md) § Extensions of the tree recognizers, which
records that the encoding "must be named"; naming the encoding is unnecessary
once it is `List.ofFn ∘ enc`, and the type distinction the note is about
survives, `foldSem … ![w]` being a `List Bool` and `w.foldr step init` an `α`.

`foldr` is the right fold because the list's head is the word's last bit, so a
right fold reads the word right-to-left, which is the direction
`Cobham.evalRec` recurses in and which `Cobham.scanSem_eq` states.

`length_foldSem_le` is stated at `scanSem` rather than at `foldSem`, which is
the form `Cobham.scan` consumes and the form `Tree.lean` states
`length_combSem_le` in; `foldSem_def` bridges the two, as `combSem_def` does
there. It does not take `hdec`: every state the scan produces is a `List.ofFn`
of an `enc` value — the base by `baseWord_constAt`, each step by
`stepWord_constAt` — so its length is `p` whatever `dec` does, and
`List.length_ofFn` gives `p ≤ w.length + p`, tight at the empty word, with
`growth = p`. Consequently `fold`, `foldOf` and `foldSem_eq_eval` take no
retraction hypothesis either.

`foldSem_eq` is the module's content, and is where `hdec` enters. Its two sides
inhabit different types before `List.ofFn ∘ enc` is applied, so the encoding is
applied rather than the two equated. The proof is `List.rec` over `w` through
`scanSem_eq`; the step needs `bits p (List.ofFn (enc a)) = enc a`, stated as
`bits_ofFn` in concern 1, and then `dec (enc a) = a` identifies the branch the
case tree selects with `step b a`.

## Concern 3: `Cobham/RankedTree.lean`

Named to parallel `Cobham/Tree.lean`, which recognizes the same shape of
language at the two-symbol alphabet. `Cobham/Ranked.lean` would read
ambiguously against the directory `Geb/Mathlib/Data/Tree/Ranked/`.

`predIterOf (k : ℕ) : COf 1`, the `k`-fold predecessor by `Nat.rec`, is added
to `Cobham/Basic.lean` in this segment, with
`stepWord_predIterOf : stepWord (predIterOf k) u = u.drop k` stated here.
`Cobham/Tree.lean` supplies only `predPred`, the case `k = 2`.

### The state as a bitstring

```lean
@[expose] def bufBits (R : RankedAlphabet) (buf : List Bool) : List Bool :=
  List.replicate (R.width - 1 - buf.length) false ++ true :: buf
@[expose] def stateWord (R : RankedAlphabet) (s : RankedAlphabet.Scan) :
    List Bool :=
  s.live :: bufBits R s.buf ++ List.replicate s.depth true
@[expose] def dispatchWidth (R : RankedAlphabet) : ℕ :=
  R.width + R.maxArity + 2
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

`bufBits` has length `R.width` only when `buf.length < R.width`. `Nat`
subtraction being truncated, a longer `buf` yields a slot of length
`buf.length + 1`, and `stateWord` is then not injective: at `R.width = 2` the
states `⟨[false, true], 0, true⟩` and `⟨[false], 1, true⟩` share the word
`[true, true, false, true]`. The invariant excluding this is
`length_buf_scanFinal`, in
[Additions to the ranked-encoding modules](#additions-to-the-ranked-encoding-modules),
and every statement below is read at a reachable state.

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
theorem decodeState_stateWord (R : RankedAlphabet) (s : RankedAlphabet.Scan)
    (hbuf : s.buf.length < R.width) :
    decodeState R (bits (dispatchWidth R) (stateWord R s)) =
      { s with depth := min s.depth (R.maxArity + 1) }
```

The branch family's domain is `Fin (dispatchWidth R) → Bool` at a symbolic
width, so recovering the fields index by index would carry a bound proof at
every step. `decodeState` avoids that entirely by passing through
`List.ofFn v : List Bool` and reading the fields with the `List` API: the
liveness flag is the head; the slot is `take R.width` of the tail, whose
padding is removed by `dropWhile (· == false)` and whose sentinel by `tail`;
the capped depth is the length of `takeWhile id` of what follows the slot.
Every operation is structural, so no `Fin` arithmetic and no
`Fintype`-derived decidability arises.

It returns a `RankedAlphabet.Scan` rather than a tuple, that record being
exactly the three fields, and `decodeState_stateWord` is its round trip.
It is concern 3's analogue of concern 2's `dec` and its retraction hypothesis,
and `rankedSem_eq` turns on it.

### The recognizer

```lean
@[expose] def nextPrefix (R : RankedAlphabet) (b : Bool)
    (s : RankedAlphabet.Scan) : List Bool
@[expose] def dropCount (R : RankedAlphabet) (b : Bool)
    (s : RankedAlphabet.Scan) : ℕ
@[expose] def rankedStep (R : RankedAlphabet) (b : Bool) : COf 1 :=
  diagOf (casesOf (dispatchWidth R) fun v ↦
    prependWord (nextPrefix R b (decodeState R v))
      (predIterOf (dropCount R b (decodeState R v))))
@[expose] def rankedSem (R : RankedAlphabet) : Sem 1 :=
  scanSem (constAt (stateWord R ⟨[], 0, true⟩)) (rankedStep R false)
    (rankedStep R true) (R.width + 1)
theorem rankedSem_def (R : RankedAlphabet) : rankedSem R = scanSem …

theorem stateWord_scanStep (R : RankedAlphabet) (b : Bool)
    (s : RankedAlphabet.Scan) (h : s.buf.length < R.width) :
    stateWord R (R.scanStep b s) =
      nextPrefix R b s ++ (stateWord R s).drop (dropCount R b s)
theorem rankedSem_eq (R : RankedAlphabet) (w : List Bool) :
    rankedSem R ![w] = stateWord R (R.scanFinal w)
theorem length_rankedSem_le (R : RankedAlphabet) (w : List Bool) :
    (scanSem … ![w]).length ≤ w.length + R.width + 1
@[expose] def ranked (R : RankedAlphabet) : C
@[expose] def rankedOf (R : RankedAlphabet) : COf 1
theorem rankedSem_eq_eval (R : RankedAlphabet)
```

Every branch has one shape: drop a statically known number of bits, and prepend
a statically known word. `dropCount R b s` is `1 + R.width` in four of
`RankedAlphabet.scanStep`'s five clauses — dead-absorb, accumulate,
`arOf = none` and `r > depth` all leave `depth` untouched — and
`1 + R.width + r` in the fifth, where a symbol of arity `r` pops.
`nextPrefix R b s` is the rebuilt liveness flag and block slot, `false`-headed
on the two failure clauses and with a single trailing `true` on the pop.

`stateWord_scanStep` is the step lemma the whole module rests on, and
`rankedSem_eq` is its `List.rec` over `w` through `scanSem_eq`, with
`length_buf_scanFinal` supplying the hypothesis at each state and
`decodeState_stateWord` carrying it from the state to the bit family the branch
is selected by.

`length_rankedSem_le` follows: `|stateWord R s| = 1 + R.width + s.depth` under
the same invariant, and `depth_scanFinal_le` gives `depth ≤ |w|`. The sharper
`depth ≤ ⌊|w| / R.width⌋` is true but needs the block-alignment lemma on top of
it, and the bound consumed does not require it. At the empty word the bound is
`R.width + 1 ≤ 0 + R.width + 1`, tight. As in concern 2 it is stated at
`scanSem`, with `rankedSem_def` bridging.

### The verdict and the bridge

```lean
@[expose] def acceptWord (R : RankedAlphabet) : List Bool :=
  stateWord R ⟨[], 1, true⟩
@[expose] def isRankedRaw (R : RankedAlphabet) : sig.toPFunctor.W
@[expose] def isRanked (R : RankedAlphabet) : C
@[expose] def isRankedOf (R : RankedAlphabet) : COf 1
@[expose] def isRankedSem (R : RankedAlphabet) : Sem 1
theorem isRankedSem_eq_eval (R : RankedAlphabet)

theorem isRankedSem_eq_ite (R : RankedAlphabet) (w : List Bool) :
    isRankedSem R ![w] = if R.Valid w then [true] else []
theorem isRankedSem_eq_singleton_iff_valid (R : RankedAlphabet)
    (w : List Bool) : isRankedSem R ![w] = [true] ↔ R.Valid w
theorem isRankedSem_binRanked_eq_singleton_iff_isTreeSem (w : List Bool) :
    isRankedSem binRanked ![w] = [true] ↔ isTreeSem ![w] = [true]
```

`RankedAlphabet.validBool` asks that the scan end live, with an empty
incomplete block and exactly one pending subterm, so the accepting state is
`⟨[], 1, true⟩` and the accepting word is `stateWord R` of it, of length
`R.width + 2`. The verdict is `casesOf` at `R.width + 3` bits — one past the
accepting word, so that a `depth` above one is rejected — reached through
`diagOf`, with the branch at `v` being `constAt [true]` where
`List.ofFn v = acceptWord R ++ [false]` and `constAt []` otherwise. The
decision is taken on `List Bool`, whose `DecidableEq` is structural, rather
than on `Fin (R.width + 3) → Bool`, whose instance routes through
`Fintype.decidablePiFintype` and `Classical.choice`.

`isRankedSem_eq_ite` pins the value on the rejecting branch as well as the
accepting one, for the reason `isTreeSem_eq_ite` records: the `iff` alone
admits a recognizer returning `[false]` on a rejected word, so correctness as a
function is not implied by correctness of the accepted set. The two `iff`
statements are proved from their implications rather than by `omega`, which
pulls `Classical.choice` on an `Iff` goal.

The bridge chains `isRankedSem_eq_singleton_iff_valid` at `binRanked`,
`RankedAlphabet.Binary.valid_iff` and `isTreeSem_eq_singleton_iff_valid`. Every
link relates semantic predicates on `List Bool`, so neither `binRanked`'s
`width` and `maxArity` nor the two recognizers' differing failure conventions
need reconciling. `Cobham/Tree.lean` keeps `comb` and `isTree`, so
`isTree_smashFree` and the [Strahm2003] Theorem 1(2) reasoning keep their
subject.

## Additions to the ranked-encoding modules

Four statements concern 3 consumes that `Geb/Mathlib/Data/Tree/Ranked/` does
not carry. Each is added to the module whose subject it is, in concern 3's
segment, and each is written unprefixed inside that module's existing
`namespace RankedAlphabet` block, an explicit prefix inside it elaborating to a
doubled name.

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
module already records.

In `Ranked/Code.lean`, which is where `arOf` lives and which imports
`Basic.lean`:

```lean
theorem le_maxArity_of_arOf_eq_some (R : RankedAlphabet) {v r : ℕ}
    (h : R.arOf v = some r) : r ≤ R.maxArity
```

`arOf` returns `some (R.arity ⟨v, h⟩)` when `v < R.card` and `none` otherwise,
so every arity it yields lies in the image of `R.arity`. This is the statement
making `dispatchWidth`'s `R.maxArity + 1` depth window sufficient.

In `Ranked/Preorder.lean`:

```lean
theorem length_buf_scanFinal (R : RankedAlphabet) (w : List Bool) :
    (R.scanFinal w).buf.length < R.width
theorem depth_scanFinal_le (R : RankedAlphabet) (w : List Bool) :
    (R.scanFinal w).depth ≤ w.length
```

`length_buf_scanFinal_of_live` gives the first for a live scan already, as
`w.length % R.width`; the unconditional statement additionally needs that a
dead scan carries `buf = []`, which holds because both failure clauses of
`scanStep` return `⟨[], _, false⟩` and a dead state absorbs.
`depth_scanFinal_le` is a `List.rec`: every clause leaves `depth` alone except
the pop, which yields `depth - r + 1 ≤ depth + 1`.

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
- The `oneAtOf` and `falseAtOf` duplication against `constAt`, recorded as a
  deferral in [TODO.md](../../../TODO.md).

## Test mirrors

Under `GebTests/Mathlib/Computability/Cobham/`, each naming a `def` value built
from the module under test rather than asserting inside an anonymous `example`,
since `lake shake` infers imports from the constants an olean references and
reports an import used only by an `example` as removable.

- **`Cases.lean`** — `casesSem` at a literal `p` against an explicitly
  tabulated branch family, with a scrutinee shorter than `p` to pin the
  zero-padding convention, and one longer than `p` to pin that the high bits
  are ignored.
- **`Fold.lean`** — a carrier whose `dec` is not injective off the image of
  `enc`, so that the retraction hypothesis is exercised rather than trivially
  satisfied.
- **`RankedTree.lean`** — `isRankedSem` against `RankedAlphabet.validBool` at
  `binRanked` and at `narrowAlphabet`, whose `card < 2 ^ width` makes a block
  spell no symbol so that the `arOf = none` branch is reached; plus
  `decodeState_stateWord` at each reachable `buf` length, and `stateWord` at a
  state with `buf.length = R.width` to pin that the invariant is consumed
  rather than decorative.

Sweep length is set by measurement, not by the length-eight convention the
earlier mirrors use. A single dispatch at `p = 6` costs about 21 ms of
elaboration and about as much again in the kernel; `wordsUpTo 8` is 511 words
totalling 3586 scan steps, each a dispatch plus a `prependWord` chain, a
`predIterOf` chain and the `scanRaw` layer, so a full length-eight sweep at one
alphabet is on the order of a minute in each of elaboration and kernel
checking. The mirrors therefore sweep to whatever length keeps the module
within the build budget the rest of `GebTests` sets, and record the length
reached. `set_option maxRecDepth` is valid in tactic position; `native_decide`
is forbidden, carrying a compiler-trust axiom.

Whether `dispatchWidth narrowAlphabet` and `maxArity` reduce to numerals
through `List.ofFn` and `Matrix.vecCons` in the kernel is load-bearing for
every sweep and is checked first.

## Documentation and commits

Each segment carries a `docs/index.md` entry and a `TODO.md` revision, in the
shape B1 and B2 use; `TODO.md` § Extensions of the tree recognizers records B3
and B6 as done in the segments completing them, gains the `oneAtOf`/`falseAtOf`
deferral, and has its B3 note on naming the encoding revised.

The index modules `Geb/Mathlib/Computability/Cobham.lean` and
`GebTests/Mathlib/Computability/Cobham.lean` gain an import of each new module
in its segment; without both, the new modules are not built.

Each of `Cases.lean`, `Fold.lean` and `RankedTree.lean` carries the module
docstring sections
[docs/rules/lean-coding.md](../../rules/lean-coding.md) § Documentation
mandates, in order and non-vacuously, and a `/-- … -/` docstring on every `def`
and on every theorem of public interest. Every modified module's own docstring
is updated in the segment modifying it: `Cobham/Basic.lean` for `semAt` and
each helper family, `Cobham/Scan.lean` and `Cobham/Tree.lean` for the
restatement through `semAt` and for the `zeroAt` family leaving `Tree.lean`'s
`## Main definitions` and `## Implementation notes`, and each of
`Ranked/{Basic,Code,Preorder}.lean` for the statement it gains.

The `## Implementation notes` sections carry the decisions recorded here that
outlive this document: the scrutinee shift, the `bufBits` sentinel, the unary
`depth`, `decodeState`'s route through `List.ofFn`, the two `Classical.choice`
routes avoided, and the reason `length_foldSem_le` precedes the retraction
hypothesis and does not take it.

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
`casesSem_eq`. It declares `namespace Cobham` and so collides with the real
module, and is deleted before `Cobham/Cases.lean` lands. Established there:

- `Nat.rec` at the motive
  `((Fin p → Bool) → sig.toPFunctor.W) → sig.toPFunctor.W` elaborates, and the
  reindexing by `Fin.cons` in the recursive calls is accepted.
- `wValid_casesRaw`, `semAt_shiftW` and `casesSem_eq` each measure
  `[propext, Quot.sound]`.
- `casesSem (p + 1) br ![b :: t, x]` is definitionally the shifted subtree's
  meaning, so the successor step of `casesSem_eq` needs no `change`: the
  statement of `semAt_shiftW` at the right instance typechecks against it
  directly.

Established by review against throwaway modules since deleted, and to be
rebuilt as each segment's plan is written rather than taken on trust:
`stateWord_scanStep` for arbitrary `R` and `b` at every state satisfying the
buffer invariant; `length_buf_scanFinal`; `depth_scanFinal_le`; `maxArity`,
`arity_le_maxArity` and `le_maxArity_of_arOf_eq_some`; `bits_ofFn`;
`baseWord_constAt` and `stepWord_constAt` with no constraint on `dec`;
`diagOf`, `predIterOf` and `constAt` with their semantic lemmas;
`acceptWord R = stateWord R ⟨[], 1, true⟩` by `rfl`; and a reduction of
`casesSem` at `p = 7` against a branch family varying in every bit, closing by
`rfl` in well under a second.

Not built at all: `cases`, `casesOf`, `casesSem_eq_eval`; `decodeState`,
`nextPrefix` and `dropCount` as functions of a bit family at symbolic width;
the verdict layer; and every `…_eq_eval`.

## Risks and open questions

| Risk | Effect | Response |
| --- | --- | --- |
| `decodeState` at symbolic width is unbuilt | Concern 3's step has a shape and no definition | The `List.ofFn` route removes the `Fin` bound-threading that made it hard; prototype it before that segment's plan, as concern 1 was |
| Restating `Scan.lean` and `Tree.lean` through `semAt` | A `rfl` proof downstream may stop closing | `semAt` is `@[expose]` and the definitions are unchanged in meaning, so the delta unfolding should be the same; measured by building segment 1 before its plan is fixed |
| Kernel and elaboration cost of the sweeps | About 21 ms per dispatch at `p = 6`, over 3586 scan steps for a length-eight sweep at one alphabet | Sweep to a measured length rather than a conventional one; check first that `maxArity` and `dispatchWidth` reduce to numerals |
| `stateWord` is injective only under `length_buf_scanFinal` | A step lemma false off the reachable states | The invariant is a named lemma, and a test pins a state violating it |
| Whether the two containments are published | A missing citation, or a wrongly claimed novelty | Search with `theoremsearch` and `arxiv-mcp-server` for both statements before either module docstring is written; record any key found in `docs/references.bib` |
| Whether the `oneAtOf`/`falseAtOf` deferral is right | A duplication carried for no reason | Measured, not argued: substitute `constAt` in a throwaway build and see whether `combSem_nil` and `isTreeSem_eq_eval` still close by `rfl` |

## References

- [Cobham1965] — the class and the arity relation of bounded recursion on
  notation.
- [HeraudNowak2011] — the `Rec` form `Cobham/Basic.lean` transcribes for `pred`
  and `cond`.
- [Strahm2003] — Theorem 1(2), the polynomial-time and linear-space containment
  of the `smash`-free subalgebra, which the bridge preserves for `isTree`.
