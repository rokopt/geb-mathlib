# Definition by cases, the finite-carrier fold, and the generic ranked recognizer

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [Dependencies and segment boundaries](#dependencies-and-segment-boundaries)
- [Transcription status of each definition](#transcription-status-of-each-definition)
- [Constraints this design is bound by](#constraints-this-design-is-bound-by)
- [Additions to `Cobham/Basic.lean`](#additions-to-cobhambasiclean)
- [Concern 1: `Cobham/Cases.lean`](#concern-1-cobhamcaseslean)
  - [Selection by the bits of a scrutinee](#selection-by-the-bits-of-a-scrutinee)
  - [The scrutinee shift](#the-scrutinee-shift)
  - [The case tree](#the-case-tree)
  - [The combinator and its meaning](#the-combinator-and-its-meaning)
- [Concern 2: `Cobham/Fold.lean`](#concern-2-cobhamfoldlean)
  - [Interface](#interface)
  - [Construction](#construction)
  - [Statements](#statements)
- [Concern 3: `Cobham/RankedTree.lean`](#concern-3-cobhamrankedtreelean)
  - [The state as a bitstring](#the-state-as-a-bitstring)
  - [Inverting the state word](#inverting-the-state-word)
  - [The recognizer](#the-recognizer)
  - [The verdict and the bridge](#the-verdict-and-the-bridge)
- [Additions to the ranked-encoding modules](#additions-to-the-ranked-encoding-modules)
- [What is out of scope](#what-is-out-of-scope)
- [Test mirrors](#test-mirrors)
- [Documentation and commits](#documentation-and-commits)
- [What the prototype has established](#what-the-prototype-has-established)
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
than a literal, so the dispatch cannot be written out. Concern 2 also consumes
it, but concern 3 alone would justify it.

Concern 2's own justification is that it is a second instantiation of the scan
combinator `Cobham/Scan.lean` introduces. That module's whole-branch review
judged the combinator earned at its core and not at its periphery, an interface
with one implementation being what
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost warns against.
Concern 3 is also such an instantiation and settles that question by itself, so
concern 2 is not load-bearing for it; concern 2 has no consumer in the
repository, and is retained as a decision recorded here rather than as a
dependency.

## Dependencies and segment boundaries

The three concerns are appended to the existing line in the order above, each
with a bookmark at its boundary, so that each is submitted as its own pull
request while the graph stays linear and conflict-free. The order is a choice
about conflicts, not a dependency chain.

- Concern 1 depends on `Cobham/Basic.lean` and on `Cobham/Scan.lean`, the
  latter for `liftRaw` and for `stepWord`, which appears in `casesSem_eq`'s
  statement. Nothing moves out of `Cobham/Scan.lean`: it is imported either
  way, so relocating `liftRaw` would be churn on a settled module.
- Concern 2 depends on concern 1, on the `Cobham/Basic.lean` additions below,
  and on `Cobham/Scan.lean`.
- Concern 3 depends on concern 1, on the same `Cobham/Basic.lean` additions, on
  `Cobham/Scan.lean`, on `Cobham/Tree.lean` for the bridge, and on
  `Geb/Mathlib/Data/Tree/Ranked/{Basic,Code,Preorder,Binary}.lean`. It does not
  depend on concern 2: `Cobham/Fold.lean`'s carrier must admit a `p`-bit
  encoding, and `RankedAlphabet.Scan.depth` is unbounded, which is why concern
  3 lays out its own state word.

## Transcription status of each definition

Per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature when
transcribing, every definition below is novel — an assembly of the generators
`Cobham/Basic.lean` transcribes from [HeraudNowak2011] and [Cobham1965].

Two containments realized here may be published statements rather than novel
ones: that finite-state transductions lie in Cobham's class, which concern 2
realizes, and that the languages of ranked-term preorder spellings do, which
concern 3 realizes. [Strahm2003] and [Clote1999] are the nearest cited works.
The search is recorded as an open question below, and is settled before either
module docstring is written, per
[AGENTS.md](../../../AGENTS.md) § Verify agent claims.

## Constraints this design is bound by

- **No `noncomputable`, and `Classical.choice` excluded.** Every declaration
  measures `[propext, Quot.sound]`, which `lake lint` enforces.
- **Recursion through recursors.** No `def` calls itself and no `induction`
  tactic appears; every recursion is an explicit `Nat.rec`, `List.rec` or
  `WType.elim` application.
- **`decide` discharges admissibility only at a named constant.** Instance
  search finds `Decidable (sig.WValid w)` when `w` is a constant but not when
  it is a literal `WType.mk` application, and at a variable `p` nothing reduces
  at all. Every admissibility proof here is written out as a `Nat.rec` or
  `List.rec`, in the shape `Cobham.wValid_boundRaw` sets.
- **Transport along an opaque equation does not disappear.** It disappears by
  proof irrelevance when both sides reduce to the same literal. A node's own
  arity reduces whatever its children are; a component's does not. Where the
  two forms must be identified, `Cobham.transport_transport` is the bridge.
- **The class reaches only a bounded prefix of a word.** `pred` drops the head,
  `succ` prepends, and `cond` tests the head, so an expression of bounded size
  inspects and rewrites only a bounded prefix. This determines the field order
  of concern 3's state.
- **`Nat` subtraction is truncated.** `bufBits` below has its intended length
  only under an invariant on `buf`'s length, and that invariant is stated as a
  lemma rather than assumed.

## Additions to `Cobham/Basic.lean`

Concerns 2 and 3 both build constant words, both drop a statically known number
of bits, and both dispatch on their own argument. Four additions, made in
concern 1's segment, together with one move.

- **`zeroAtRaw`, `zeroAt`, `zeroAtOf` move from `Cobham/Tree.lean`**,
  unchanged. `constAt` needs a nullary constant at an arbitrary arity, and
  `Cobham/Tree.lean` imports `Cobham/Basic.lean` rather than the reverse, so
  the definitions cannot be referred to where they stand. Moving them rather
  than adding a third copy leaves the `decide`-discharged proofs they carry
  intact, the definitions being unchanged by the move.
- **`prependWord {n : ℕ} (u : List Bool) (e : COf n) : COf n`** — the chain of
  `succ` nodes prepending a fixed word to what `e` computes, by `List.rec` on
  `u`, with a semantic lemma `semAt_prependWord` giving its value as
  `u ++ …`. That lemma is what concern 2's base case and every branch of
  concern 3's step consume; without it neither `foldSem_eq` nor `rankedSem_eq`
  closes.
- **`constAt {n : ℕ} (u : List Bool) : COf n := prependWord u (zeroAtOf n)`**,
  with `baseWord_constAt : baseWord (constAt u) = u` and
  `stepWord_constAt : stepWord (constAt u) r = u`, both corollaries of
  `semAt_prependWord`. `Cobham.baseWord_eq_eval` states only that `baseWord`
  agrees with what the expression carries and says nothing about the value, so
  it does not supply these.
- **`predIterOf (k : ℕ) : COf 1`** — the `k`-fold predecessor, by `Nat.rec`,
  with `stepWord_predIterOf : stepWord (predIterOf k) u = u.drop k`.
  `Cobham/Tree.lean` supplies only `predPred`, the case `k = 2`.
- **`diagOf (e : COf 2) : COf 1`** — a binary expression applied to its sole
  argument in both positions, a `comp 1 2` node over `e` and two `proj 1 0`
  children, with `stepWord_diagOf : stepWord (diagOf e) u = semAt 2 … ![u, u]`.
  Concerns 2 and 3 both dispatch on their own state, so both reach `casesOf`
  through it.

`Cobham/Tree.lean`'s `oneAt` and `falseAt` are `constAt [true]` and
`constAt [false]`, and are left as they are: they are discharged by `decide`,
as is `isTree_smashFree`, and redefining them puts a reduction that currently
works at risk for no return on this line. That duplication is recorded in
[TODO.md](../../../TODO.md) as a deferral. `zeroAt` is not among it — it is the
base `constAt` is built from, not a copy of it.

## Concern 1: `Cobham/Cases.lean`

Every signature in this section is compiled; see
[What the prototype has established](#what-the-prototype-has-established).

### Selection by the bits of a scrutinee

```lean
@[expose] def bits (p : ℕ) (w : List Bool) : Fin p → Bool :=
  fun j ↦ w.getD j false

@[expose] def semAt (n : ℕ) (e : sig.W) (he : arity e = n) : Sem n :=
  transport ((fst_eval e).trans he) (eval e).2
```

Bit `j` of the scrutinee, `false` past its end. Reading a short scrutinee as
zero-padded, rather than conditioning the semantic theorem on `p ≤ w.length`,
keeps `casesSem_eq` free of a hypothesis, and in the tree it costs nothing:
`cond`'s empty branch is directed at the same subtree as its head-`false`
branch.

`bits` carries no `…Of` suffix, which throughout `Cobham/` means the `COf n`
form of the preceding name — `concatOf`, `scanOf`, `isTreeOf`, and this
design's own `casesOf`, `foldOf`, `rankedOf`.

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
the tree unfolds to `3 ^ p` leaf occurrences over `2 ^ p` distinct branches.
Reduction does not traverse them: `evalRec` is a `List.rec` on the scrutinee,
so weak-head reduction follows one root-to-leaf path and the cost of a
reduction is linear in `p`. Elaboration shares the repeated subterm through a
`let`.

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

## Concern 2: `Cobham/Fold.lean`

### Interface

```lean
variable {α : Type*} {p : ℕ} (enc : α → Fin p → Bool)
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

### Construction

```lean
@[expose] def foldStep (b : Bool) : COf 1 :=
  diagOf (casesOf p fun v ↦ constAt (List.ofFn (enc (step b (dec v)))))
@[expose] def foldSem : Sem 1 :=
  scanSem (constAt (List.ofFn (enc init))) (foldStep enc dec step false)
    (foldStep enc dec step true) p
```

Neither the encoding-to-word nor the carrier-level fold is named: they are
`List.ofFn (enc a)` and `w.foldr step init`, spelled at the length a name would
cost, and `List` supplies both already.

`foldr` is the right fold because the list's head is the word's last bit, so a
right fold reads the word right-to-left, which is the direction
`Cobham.evalRec` recurses in and which `Cobham.scanSem_eq` states.

### Statements

```lean
theorem length_foldSem_le (w : List Bool) :
    (foldSem enc dec init step ![w]).length ≤ w.length + p
@[expose] def fold : C
@[expose] def foldOf : COf 1
theorem foldSem_eq_eval

theorem foldSem_eq (hdec : ∀ a, dec (enc a) = a) (w : List Bool) :
    foldSem enc dec init step ![w] = List.ofFn (enc (w.foldr step init))
```

`length_foldSem_le` does not take `hdec`, and is proved before `foldSem_eq`.
Every state the scan produces is a `List.ofFn` of an `enc` value — the base by
`baseWord_constAt`, each step by `stepWord_constAt` — so its length is `p`
whatever `dec` does, and `List.length_ofFn` gives `p ≤ w.length + p`, tight at
the empty word, with `growth = p`. Consequently `fold`, `foldOf` and
`foldSem_eq_eval` take no retraction hypothesis either.

`foldSem_eq` is the module's content, and is where `hdec` enters. Its two sides
inhabit different types before `List.ofFn ∘ enc` is applied, so the encoding is
applied rather than the two equated. The proof is `List.rec` over `w` through
`scanSem_eq`, which presents the scan as `List.foldr scanStepWord` from
`baseWord`; the step needs `bits p (List.ofFn (enc a)) = enc a`, a
`List.getD`-over-`List.ofFn` fact stated as `bits_ofFn`, and then
`dec (enc a) = a` identifies the branch the case tree selects with `step b a`.

Both statements are made at `scanSem`, before `fold : C` exists, `Cobham.eval`
asking only for admissibility as a `sig`-tree and not for the recursion bound —
the order `Cobham/Tree.lean` runs in `combSem_eq`, `length_combSem_le`, `comb`.

## Concern 3: `Cobham/RankedTree.lean`

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
than the `2 * R.width` a separate fill counter would.

`bufBits` has length `R.width` only when `buf.length < R.width`. `Nat`
subtraction being truncated, a longer `buf` yields a slot of length
`buf.length + 1`, which moves `depth` off its offset, and `stateWord` is then
not injective: at `R.width = 2` the states `⟨[false, true], 0, true⟩` and
`⟨[false], 1, true⟩` share the word `[true, true, false, true]`. The invariant
excluding this is `length_buf_scanFinal`, in
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
    (v : Fin (dispatchWidth R) → Bool) : Bool × List Bool × ℕ
theorem decodeState_stateWord (R : RankedAlphabet) (s : RankedAlphabet.Scan)
    (hbuf : s.buf.length < R.width) :
    decodeState R (bits (dispatchWidth R) (stateWord R s)) =
      (s.live, s.buf, min s.depth (R.maxArity + 1))
```

The branch family has type `(Fin (dispatchWidth R) → Bool) → COf 1`, so its
body works from the raw bit family and must recover the liveness flag, the
incomplete block and the capped depth from it. `decodeState` is that inverse —
the sentinel search over the `R.width`-bit slot, and the count of leading
`true` bits in the depth window — and `decodeState_stateWord` is its round
trip. It is concern 3's analogue of concern 2's `dec` and its retraction
hypothesis, and `rankedSem_eq` turns on it.

### The recognizer

```lean
@[expose] def nextPrefix (R : RankedAlphabet) (b : Bool)
    (v : Fin (dispatchWidth R) → Bool) : List Bool
@[expose] def dropCount (R : RankedAlphabet) (b : Bool)
    (v : Fin (dispatchWidth R) → Bool) : ℕ
@[expose] def rankedStep (R : RankedAlphabet) (b : Bool) : COf 1 :=
  diagOf (casesOf (dispatchWidth R) fun v ↦
    prependWord (nextPrefix R b v) (predIterOf (dropCount R b v)))
@[expose] def rankedSem (R : RankedAlphabet) : Sem 1 :=
  scanSem (constAt (stateWord R ⟨[], 0, true⟩)) (rankedStep R false)
    (rankedStep R true) (R.width + 1)

theorem rankedSem_eq (R : RankedAlphabet) (w : List Bool) :
    rankedSem R ![w] = stateWord R (R.scanFinal w)
theorem length_rankedSem_le (R : RankedAlphabet) (w : List Bool) :
    (rankedSem R ![w]).length ≤ w.length + R.width + 1
@[expose] def ranked (R : RankedAlphabet) : C
@[expose] def rankedOf (R : RankedAlphabet) : COf 1
theorem rankedSem_eq_eval (R : RankedAlphabet)
```

Every branch has one shape: drop a statically known number of bits, and prepend
a statically known word. `dropCount R b v` is `1 + R.width` where the block is
incomplete or the state is dead, and `1 + R.width + r` where a symbol of arity
`r` pops; `nextPrefix R b v` is the rebuilt liveness flag and block slot,
followed by the single `true` a completed symbol pushes. Both are plain Lean
functions of `decodeState R v` and `b`, and the five clauses of
`RankedAlphabet.scanStep` — dead-absorb, accumulate, `arOf = none`, `r > depth`
and `r ≤ depth` — are their five cases.

`rankedSem_eq` is the module's content: the expression's state word is that of
the state `RankedAlphabet.scanFinal` computes. It is a `List.rec` over `w`
through `scanSem_eq`, its step matching `casesSem_eq`'s branch selection
against `scanStep`'s clauses through `decodeState_stateWord`, whose hypothesis
`length_buf_scanFinal` supplies.

`length_rankedSem_le` follows from `rankedSem_eq`:
`|stateWord R s| = 1 + R.width + s.depth` under the same invariant, and
`depth_scanFinal_le` gives `depth ≤ |w|`. The sharper
`depth ≤ ⌊|w| / R.width⌋` is true but needs the block-alignment lemma on top of
it, and the bound consumed does not require it. At the empty word the bound is
`R.width + 1 ≤ 0 + R.width + 1`, tight.

### The verdict and the bridge

```lean
@[expose] def acceptWord (R : RankedAlphabet) : List Bool :=
  true :: bufBits R [] ++ [true]
@[expose] def isRankedRaw (R : RankedAlphabet) : sig.toPFunctor.W
@[expose] def isRanked (R : RankedAlphabet) : C
@[expose] def isRankedOf (R : RankedAlphabet) : COf 1
@[expose] def isRankedSem (R : RankedAlphabet) : Sem 1
theorem isRankedSem_eq_eval (R : RankedAlphabet)

theorem isRankedSem_eq_ite (R : RankedAlphabet) (w : List Bool) :
    isRankedSem R ![w] = if R.Valid w then [true] else []
theorem isRankedSem_eq_singleton_iff_valid (R : RankedAlphabet)
    (w : List Bool) : isRankedSem R ![w] = [true] ↔ R.Valid w
theorem isRankedSem_binRanked_iff_isTreeSem (w : List Bool) :
    isRankedSem binRanked ![w] = [true] ↔ isTreeSem ![w] = [true]
```

`RankedAlphabet.validBool` asks that the scan end live, with an empty
incomplete block and exactly one pending subterm, so the accepting state word
is the single constant `acceptWord R`. The verdict is a case over
`R.width + 3` bits of the final state — one past `acceptWord R`, so that a
`depth` above one is rejected — with constant branches, which is `casesOf`
again, reached through `diagOf`.

`isRankedSem_eq_ite` pins the value on the rejecting branch as well as the
accepting one, for the reason `isTreeSem_eq_ite` records: the `iff` alone
admits a recognizer returning `[false]` on a rejected word, so correctness as a
function is not implied by correctness of the accepted set.

The bridge chains `isRankedSem_eq_singleton_iff_valid` at `binRanked`,
`RankedAlphabet.Binary.valid_iff` and `isTreeSem_eq_singleton_iff_valid`. Every
link relates semantic predicates on `List Bool`, so neither `binRanked`'s
`width` and `maxArity` nor the two recognizers' differing failure conventions
need reconciling. `Cobham/Tree.lean` is not edited beyond the move of the
`zeroAt` family: `comb` and `isTree` keep their definitions, so
`isTree_smashFree` and the [Strahm2003] Theorem 1(2) reasoning keep their
subject.

## Additions to the ranked-encoding modules

Four statements concern 3 consumes that `Geb/Mathlib/Data/Tree/Ranked/` does
not carry. Each is added to the module whose subject it is, in concern 3's
segment, and each is written unprefixed inside the existing
`namespace RankedAlphabet` block — `Ranked/Basic.lean:75-123` opens it already,
so an explicit `RankedAlphabet.` prefix would elaborate to a doubled name.

In `Ranked/Basic.lean`:

```lean
@[expose] def maxArity (R : RankedAlphabet) : ℕ :=
  (List.ofFn R.arity).foldr max 0
theorem arity_le_maxArity (R : RankedAlphabet) (i : Fin R.card) :
    R.arity i ≤ R.maxArity
```

Derived rather than a new field. The `foldr`-over-`List.ofFn` form is used in
place of `Finset.sup` to keep the module clear of the ordered-algebra
instances.

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
  `decide`-dischargeable and needs a `Nat.rec` mirroring `wValid_casesRaw`, and
  at a concrete `R` it forces every node. Nothing in this design uses `smash`,
  so the statement is expected to hold; it is left to the branch that needs it.
- **B4**, absorbing `BinTree` into `RankedAlphabet.Term`, and **B5**, the
  linear time and space bound against Cslib's `MultiTapeTM`.
- The `oneAt` and `falseAt` duplication against `constAt`, recorded as a
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
  satisfied, swept against `w.foldr step init` over every word up to length
  eight.
- **`RankedTree.lean`** — `isRankedSem` swept against
  `RankedAlphabet.validBool` over every word up to length eight, at `binRanked`
  for the bridge and at `narrowAlphabet`, whose `card < 2 ^ width` makes a
  block spell no symbol so that the `arOf = none` branch is reached. Also
  `decodeState_stateWord` at each reachable `buf` length, and `stateWord` at a
  state with `buf.length = R.width` to pin that the invariant is consumed
  rather than decorative.

`sampleAlphabet` has `arity = ![0, 1, 2, 3]`, so its `maxArity` is three and
its `dispatchWidth` seven; `narrowAlphabet` has `arity = ![0, 1, 2]`, so its
`dispatchWidth` is six. Sweep budgets are per-computation and are measured
rather than predicted; `set_option maxRecDepth` is valid in tactic position.
`native_decide` is forbidden, carrying a compiler-trust axiom.

## Documentation and commits

Each segment carries a `docs/index.md` entry and a `TODO.md` revision, in the
shape B1 and B2 use; `TODO.md` § Extensions of the tree recognizers records B3
and B6 as done in the segments completing them, and gains the `oneAt` and
`falseAt` deferral.

Each of `Cases.lean`, `Fold.lean` and `RankedTree.lean` carries the module
docstring sections
[docs/rules/lean-coding.md](../../rules/lean-coding.md) § Documentation
mandates, in order and non-vacuously, and a `/-- … -/` docstring on every `def`
and on every theorem of public interest. The `## Implementation notes` sections
carry the decisions recorded here that outlive this document: the scrutinee
shift, the `bufBits` sentinel, the unary `depth`, and the reason
`length_foldSem_le` precedes the retraction hypothesis and does not take it.

Commit subjects follow
[docs/rules/ci-and-workflow.md](../../rules/ci-and-workflow.md)
§ Commit-message convention — imperative present, no capital, no trailing
period, and a type from the list. This document is transient: it is removed in
the final commits of the last segment needing it, per
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape.

## What the prototype has established

`Geb/Internal/CasesSpike.lean` compiles the whole of concern 1 through
`casesSem_eq`, and is deleted before `Cobham/Cases.lean` lands, carrying
`open Cobham` and names colliding with the real module. Established there
rather than argued:

- `Nat.rec` at the motive
  `((Fin p → Bool) → sig.toPFunctor.W) → sig.toPFunctor.W` elaborates, and the
  reindexing by `Fin.cons` in the recursive calls is accepted.
- `wValid_casesRaw`, `semAt_shiftW` and `casesSem_eq` each measure
  `[propext, Quot.sound]`.
- `casesSem (p + 1) br ![b :: t, x]` is definitionally the shifted subtree's
  meaning, so the successor step of `casesSem_eq` needs no `change`: the
  statement of `semAt_shiftW` at the right instance typechecks against it
  directly.
- Reduction of the case tree follows one path. `casesSem p br ![sel, x]` closes
  by `rfl` at `p` up to seven against a branch family that varies, in under a
  second.
- The scrutinee-shift formulation replaced one scrutinising `pred ^ j` of a
  fixed argument at depth `j`. That form does not reduce under case analysis,
  the scrutinee not being a variable.

Not prototyped, and so written into the plan only as it comes to carry compiled
code: `cases` and `casesOf`'s `RecBounded` component, `casesSem_eq_eval`, the
`Cobham/Basic.lean` additions, and the whole of concerns 2 and 3. Concern 3's
`decodeState`, `nextPrefix` and `dropCount` are the largest unbuilt piece, and
are prototyped first within that segment.

## Risks and open questions

| Risk | Effect | Response |
| --- | --- | --- |
| `decodeState` and its round trip are unbuilt | Concern 3's step has a shape and no definition | Prototype it before that segment's plan is written, as concern 1 was |
| Kernel reduction of a sweep at a concrete alphabet | `dispatchWidth` is seven at `sampleAlphabet` and six at `narrowAlphabet`, and the tree carries `3 ^ p` leaf occurrences | Reduction follows one path, measured at `p = 7` in under a second; sweep at `narrowAlphabet` and `binRanked`, and measure rather than predict |
| `stateWord` is injective only under `length_buf_scanFinal` | A step lemma false off the reachable states | The invariant is a named lemma consumed by `decodeState_stateWord`, and a test pins a state violating it |
| `bufBits`'s storage order against `decodeBits` | A recognizer correct on no word | `decodeState` is written as the inverse of `bufBits`, and `decodeState_stateWord` is the round trip; the sweep confirms rather than establishes it |
| Whether the two containments are published | A missing citation, or a wrongly claimed novelty | Search with `theoremsearch` and `arxiv-mcp-server` for both concern 2's and concern 3's statement before either module docstring is written; record any key found in `docs/references.bib` |

## References

- [Cobham1965] — the class and the arity relation of bounded recursion on
  notation.
- [HeraudNowak2011] — the `Rec` form `Cobham/Basic.lean` transcribes for `pred`
  and `cond`.
- [Strahm2003] — Theorem 1(2), the polynomial-time and linear-space containment
  of the `smash`-free subalgebra, which the bridge preserves for `isTree`.
- [Clote1999] — a nearest cited work for the containment question above.
