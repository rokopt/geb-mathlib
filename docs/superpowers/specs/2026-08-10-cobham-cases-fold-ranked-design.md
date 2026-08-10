# Definition by cases, the finite-carrier fold, and the generic ranked recognizer

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [Dependencies and segment boundaries](#dependencies-and-segment-boundaries)
- [Transcription status of each definition](#transcription-status-of-each-definition)
- [Constraints this design is bound by](#constraints-this-design-is-bound-by)
- [Content moved into `Cobham/Basic.lean`](#content-moved-into-cobhambasiclean)
- [Concern 1: `Cobham/Cases.lean`](#concern-1-cobhamcaseslean)
  - [Selection by the bits of a scrutinee](#selection-by-the-bits-of-a-scrutinee)
  - [The scrutinee shift](#the-scrutinee-shift)
  - [The case tree](#the-case-tree)
  - [Admissibility and arity](#admissibility-and-arity)
  - [The combinator and its meaning](#the-combinator-and-its-meaning)
- [Concern 2: `Cobham/Fold.lean`](#concern-2-cobhamfoldlean)
  - [Interface](#interface)
  - [Construction](#construction)
  - [Statements](#statements)
- [Concern 3: `Cobham/Ranked.lean`](#concern-3-cobhamrankedlean)
  - [The bound on arities](#the-bound-on-arities)
  - [The state as a bitstring](#the-state-as-a-bitstring)
  - [The recognizer](#the-recognizer)
  - [The verdict and the bridge](#the-verdict-and-the-bridge)
- [Test mirrors](#test-mirrors)
- [Documentation](#documentation)
- [What the prototype has established](#what-the-prototype-has-established)
- [Risks and open questions](#risks-and-open-questions)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope

Three concerns over `Geb/Mathlib/Computability/Cobham/`:

1. **Definition by cases.** A combinator selecting among `2 ^ p` expressions
   of arity one by the low `p` bits of a scrutinee, and applying the selected
   one to a second argument. It imposes no condition on the expressions it
   selects among.
2. **The fold at a finite carrier.** The catamorphism of the list of bits at a
   carrier admitting a `p`-bit encoding, as an instance of the scan combinator
   `Cobham.scan`. Its caller supplies a bare Lean step function and owes one
   hypothesis, that the encoding is a retraction.
3. **The generic ranked recognizer.** The validity scan of
   `RankedAlphabet.Preorder` as an expression of Cobham's class, at an
   arbitrary ranked alphabet, together with the theorem identifying it at the
   two-symbol alphabet with the recognizer `Cobham/Tree.lean` already carries.

Concern 1 exists because concerns 2 and 3 both need it: the fold's step is a
function of a `p`-bit state, and the recognizer's step must resolve
`RankedAlphabet.arOf` at a completed block, whose width is a parameter rather
than a literal. Neither dispatch can be written out.

## Dependencies and segment boundaries

The three concerns are appended to the existing line in the order above, each
with a bookmark at its boundary so that each is submitted as its own pull
request while the graph stays linear and conflict-free.

Concern 1 depends on the scan combinator only for `Cobham.liftRaw` and
`Cobham.stepWord`; concern 2 depends on concerns 1 and the scan combinator;
concern 3 depends on concerns 1 and 2, on the `Cobham/Basic.lean`
additions, on the scan combinator, and on
`Geb/Mathlib/Data/Tree/Ranked/Preorder.lean`.

## Transcription status of each definition

Per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature when
transcribing, every definition below is **novel** — an assembly of the
generators `Cobham/Basic.lean` already transcribes from [HeraudNowak2011] and
[Cobham1965] — with one qualification recorded under
[Risks and open questions](#risks-and-open-questions): the containment of
finite-state transductions in Cobham's class, which concern 2 realizes, may be
a published statement, and the branch establishes whether it is before
claiming novelty in a module docstring.

## Constraints this design is bound by

- **No `noncomputable`, and `Classical.choice` excluded.** Every declaration
  measures `[propext, Quot.sound]`, which `lake lint` enforces.
- **Recursion through recursors.** No `def` calls itself and no `induction`
  tactic appears; every recursion is an explicit `Nat.rec`, `List.rec` or
  `WType.elim` application.
- **`decide` discharges admissibility only at a named constant.** Instance
  search finds `Decidable (sig.WValid w)` when `w` is a constant but not when
  it is a literal `WType.mk` application, and at a variable `p` nothing
  reduces at all. Every admissibility proof here is therefore written out as a
  `Nat.rec`, in the shape `Cobham.wValid_boundRaw` sets.
- **Transport along an opaque equation does not disappear.** It disappears by
  proof irrelevance when both sides reduce to the same literal. A node's own
  arity reduces whatever its children are; a component's does not. Where the
  two forms must be identified, `Cobham.transport_transport` is the bridge.
- **The class reaches only a bounded prefix of a word.** `pred` drops the
  head, `succ` prepends, and `cond` tests the head, so an expression of
  bounded size inspects and rewrites only a bounded prefix. This is what fixes
  the field order of concern 3's state.

## Content moved into `Cobham/Basic.lean`

Two moves, made in concern 1's segment, both of content that two
otherwise-unrelated modules now need. Both are ordinary stacked-pull-request
refactors: the line is linear and neither segment has been pushed.

- **`liftRaw` and its lemmas** (`wIndexRoot_liftRaw`, `wValid_liftRaw`,
  `recBounded_liftRaw`) move from `Cobham/Scan.lean`. The term is the
  composition of an expression of arity one with `proj 2 1`; its docstring
  ties it to `evalRec`'s step shape, which is one use of it rather than its
  meaning, and the docstring is restated accordingly.
- **`prependWord (u : List Bool) (e : COf n) : COf n`** is added: the chain of
  `succ` nodes prepending a fixed word to what `e` computes, by `List.rec` on
  `u`. `constAt n u := prependWord u (zeroAt n)` is the constant word at arity
  `n`. Every node in the chain is a `comp` or a `succ`, so `RecBounded` is
  componentwise and no bound reasoning arises.

`Cobham/Tree.lean`'s `zeroAt`, `oneAt` and `falseAt` are instances of
`constAt`, and are **left as they are**. They are discharged by `decide`, as is
`isTree_smashFree`, and redefining them puts a reduction that currently works
at risk for no gain on this line. The duplication is recorded in
[TODO.md](../../../TODO.md) as a deferral rather than acted on.

## Concern 1: `Cobham/Cases.lean`

### Selection by the bits of a scrutinee

```lean
@[expose] def bitsOf (p : ℕ) (w : List Bool) : Fin p → Bool :=
  fun j ↦ w.getD j false
```

Bit `j` of the scrutinee, `false` past its end. Reading a short scrutinee as
zero-padded rather than conditioning the semantic theorem on `p ≤ w.length` is
what keeps `casesSem_eq` free of a hypothesis; in the tree it costs nothing,
because `cond`'s empty branch is directed at the same subtree as its
head-`false` branch.

### The scrutinee shift

```lean
@[expose] def semAt2 (e : sig.W) (he : arity e = 2) : Sem 2 :=
  transport ((fst_eval e).trans he) (eval e).2

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

theorem semAt2_shiftW (e : sig.W) (he : arity e = 2) (sel x : List Bool) :
    semAt2 (shiftW e he) (arity_shiftW e he) ![sel, x] =
      semAt2 e he ![sel.tail, x]
```

The scrutinee is consumed by shifting it into the recursive subtree rather than
by scrutinising `pred ^ j` of a fixed argument at depth `j`. This is the design
decision the prototype forced, and it is load-bearing twice over:

- **It makes the semantic theorem provable.** At depth `j` the scrutinee is
  `pred ^ j` applied to argument zero, which is not a variable, so no case
  analysis makes the `boundedRec` of `cond` reduce. Shifting leaves the
  scrutinee as argument zero itself, so `match sel with` reduces the node — the
  same manoeuvre `Cobham.scanSem_cons` makes by `cases b`.
- **It is smaller.** A chain of `pred`s at every depth is quadratic in `p`; one
  shift per level is linear.

`semAt2_shiftW` is not definitional in two places. Its component zero is the
meaning of `pred`, a `boundedRec` node, which reduces only once its argument is
a constructor — hence the case analysis on `sel`, exactly as `predSem_eq`
performs. Its component one closes by `rfl`, but the two components together
are assembled by `funext`, the node applying its head at `fun i : Fin 2 ↦ …`
where the statement reads `![sel.tail, x]`.

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
```

The motive is `((Fin p → Bool) → sig.toPFunctor.W) → sig.toPFunctor.W`, so the
recursion reindexes the branch family at each level by `Fin.cons`. `cond`'s
four arguments are the scrutinee, the branch on an empty scrutinee, the branch
on head `true`, and the branch on head `false`, in that order, which is what
`condSem_eq` states.

### Admissibility and arity

```lean
theorem wIndexRoot_casesRaw (p : ℕ) (br : (Fin p → Bool) → sig.toPFunctor.W) :
    sig.wIndexRoot (casesRaw p br) = 2

theorem wValid_casesRaw : ∀ (p : ℕ) (br : (Fin p → Bool) → sig.toPFunctor.W),
    (∀ v, sig.WValid (br v)) → (∀ v, sig.wIndexRoot (br v) = 1) →
    sig.WValid (casesRaw p br)
```

`wIndexRoot_casesRaw` is a case split on `p`, not a recursion: at zero the tree
is a `liftRaw` and at a successor a `comp` node, and both indices reduce. The
admissibility motive quantifies over the branch family, because the recursive
calls apply it to reindexed families.

### The combinator and its meaning

```lean
@[expose] def casesW (p : ℕ) (br : (Fin p → Bool) → COf 1) : sig.W
theorem arity_casesW (p : ℕ) (br : (Fin p → Bool) → COf 1) : arity (casesW p br) = 2
@[expose] def casesSem (p : ℕ) (br : (Fin p → Bool) → COf 1) : Sem 2 :=
  semAt2 (casesW p br) (arity_casesW p br)

theorem bitsOf_succ (p : ℕ) (w : List Bool) :
    bitsOf (p + 1) w = Fin.cons (w.getD 0 false) (bitsOf p w.tail)

theorem casesSem_eq : ∀ (p : ℕ) (br : (Fin p → Bool) → COf 1) (sel x : List Bool),
    casesSem p br ![sel, x] = stepWord (br (bitsOf p sel)) x

@[expose] def casesOf (p : ℕ) (br : (Fin p → Bool) → COf 1) : COf 2
theorem casesSem_eq_eval (p : ℕ) (br : (Fin p → Bool) → COf 1) :
    transport (casesOf p br).2 (casesOf p br).1.eval = casesSem p br
```

`casesOf` carries **no side condition**. Every node of the tree is a `comp`,
where `RecBoundedValue` is `True`, over `cond`, `pred` and `proj`, which are
already members of `C`; so `RecBounded` is discharged componentwise from the
branches' own by a `Nat.rec` mirroring `wValid_casesRaw`. This is why the
combinator can be described as imposing no condition on what it selects among.

`casesSem_eq_eval` is not a `rfl`, unlike the scan combinator's counterpart:
`arity_casesW` is a theorem rather than a definitional equality, so the
transport it carries is opaque and the two forms are identified by
`transport_transport`, in the shape `baseWord_eq_eval` uses.

## Concern 2: `Cobham/Fold.lean`

### Interface

```lean
variable {A : Type*} {p : ℕ} (enc : A → Fin p → Bool) (dec : (Fin p → Bool) → A)
         (hdec : ∀ a, dec (enc a) = a) (init : A) (step : Bool → A → A)
```

The carrier is arbitrary, and its finiteness enters only through the existence
of the `p`-bit encoding. `dec` is total and unconstrained off the image of
`enc`, since the fold's state is never anything but an encoded carrier value;
`hdec` states that `enc` is a split monomorphism, and is the only hypothesis
the caller owes. Neither `Fintype` nor `FinEnum` appears, which keeps the
module clear of the ordered-algebra and `Finset` instances the axiom rules warn
about.

### Construction

```lean
@[expose] def spell (a : A) : List Bool := List.ofFn (enc a)
@[expose] def foldStep (b : Bool) : COf 1
@[expose] def run (w : List Bool) : A := w.foldr step init
@[expose] def foldSem : Sem 1 :=
  scanSem (constAt 0 (spell enc init)) (foldStep false) (foldStep true) p
```

`foldStep b` is `casesOf p (fun v ↦ constAt 1 (spell enc (step b (dec v))))`
composed with `proj 1 0` in both argument positions: the fold's state is at
once the scrutinee and what the branch reads, so both of the case combinator's
arguments are the sole argument of the step.

`run` is the catamorphism in the carrier. `foldr` is the right fold because the
list's head is the word's last bit, so a right fold reads the word
right-to-left, which is the direction `Cobham.evalRec` recurses in and which
`Cobham.scanSem_eq` states.

### Statements

```lean
theorem run_spell (w : List Bool) : foldSem enc dec init step ![w] = spell enc (run step init w)
theorem length_foldSem_le (w : List Bool) : (foldSem enc dec init step ![w]).length ≤ w.length + p
@[expose] def fold : C
@[expose] def foldOf : COf 1
theorem foldSem_eq_eval
```

`run_spell` is the module's content. Its two sides inhabit different types
before `spell` is applied — `foldSem … ![w]` is a `List Bool` and `run … w` is
an `A` — so the encoding is named rather than the two equated.

The proof is `List.rec` over `w` through `scanSem_eq`, which presents the scan
as `List.foldr` of `scanStepWord` from `baseWord`. The base is
`spell enc init` by `baseWord_eq_eval` at a constant. The step is where `hdec`
enters: the incoming state is `spell enc a` for the value `a` the induction
hypothesis supplies, `bitsOf p` of it recovers `enc a`, and
`dec (enc a) = a` identifies the branch the case tree selects with
`step b a`.

`length_foldSem_le` follows from `run_spell` and `List.length_ofFn`: the state
is `p` bits at every word, so the bound `p ≤ w.length + p` holds with
`growth = p` and is tight at the empty word. Both statements are made at
`scanSem` before `fold : C` exists, `Cobham.eval` asking only for admissibility
as a `sig`-tree and not for the recursion bound — the order
`Cobham/Tree.lean` already runs in `combSem_eq`, `length_combSem_le`, `comb`.

## Concern 3: `Cobham/Ranked.lean`

### The bound on arities

```lean
@[expose] def RankedAlphabet.maxArity (R : RankedAlphabet) : ℕ :=
  (List.ofFn R.arity).foldr max 0
theorem RankedAlphabet.arity_le_maxArity (R : RankedAlphabet) (i : Fin R.card) :
    R.arity i ≤ R.maxArity
```

Added to `Geb/Mathlib/Data/Tree/Ranked/Basic.lean`, where the structure it
describes lives, by a commit in this segment; it is derived rather than a new
field. `RankedAlphabet.arOf` returns `some (R.arity ⟨v, h⟩)` when `v < R.card`
and `none` otherwise, so every arity it yields is in the image of `R.arity` and
so bounded by `maxArity`. The `foldr`-over-`List.ofFn` form is used in place of
`Finset.sup` to keep the module clear of the ordered-algebra instances.

### The state as a bitstring

```lean
@[expose] def bufField (R : RankedAlphabet) (buf : List Bool) : List Bool :=
  List.replicate (R.width - 1 - buf.length) false ++ true :: buf
@[expose] def stateWord (R : RankedAlphabet) (s : Scan) : List Bool :=
  s.live :: bufField R s.buf ++ List.replicate s.depth true
@[expose] def dispatchWidth (R : RankedAlphabet) : ℕ := R.width + R.maxArity + 2
```

`RankedAlphabet.Scan` carries an incomplete block `buf`, a count `depth` of
pending subterms, and a liveness flag. `depth` is unbounded and the other two
are not, and an expression of the class reaches only a bounded prefix, so
`depth` is the tail and there is no choice about it.

`buf` has length below `R.width`, and its own length cannot delimit it, since
the fields after it would then sit at a position not statically known. It is
therefore stored in a field of exactly `R.width` bits, delimited by a `true`
sentinel preceded by `false` padding: reading head-first, the first `true`
marks where `buf` begins. This costs `R.width` bits rather than the
`2 * R.width` a separate fill counter would, since the sentinel's position
carries the count. At `R.width = 1` the field degenerates to `[true]`, `buf`
being empty at every state.

`depth` is unary. Binary would need a Cobham-definable truncated subtraction
for `depth - r + 1`, and `Cobham/Tree.lean`'s existing recognizer already
represents its depth in unary.

The dispatch reads the whole prefix together with the low `R.maxArity + 1` bits
of `depth`. Those bits give `min (depth, R.maxArity + 1)`, which decides
`r ≤ depth` for every symbol: if `depth ≥ R.maxArity + 1` then
`r ≤ R.maxArity < depth`, and otherwise those bits are `depth` itself. `cond`'s
three-way split is what detects the end of a short `depth` field, the
zero-padding convention reading it as `false` where the field is all `true`.

### The recognizer

```lean
@[expose] def rankedStep (R : RankedAlphabet) (b : Bool) : COf 1
@[expose] def rankedSem (R : RankedAlphabet) : Sem 1 :=
  scanSem (constAt 0 (stateWord R ⟨[], 0, true⟩)) (rankedStep R false) (rankedStep R true)
    (R.width + 1)

theorem rankedSem_eq (R : RankedAlphabet) (w : List Bool) :
    rankedSem R ![w] = stateWord R (R.scanFinal w)
theorem length_rankedSem_le (R : RankedAlphabet) (w : List Bool) :
    (rankedSem R ![w]).length ≤ w.length + R.width + 1
@[expose] def ranked (R : RankedAlphabet) : C
@[expose] def rankedOf (R : RankedAlphabet) : COf 1
```

Each branch of `rankedStep b` drops the prefix by a statically known number of
`pred`s, adjusts the tail by `succ true` after `r` further `pred`s where the
block calls for a pop, and prepends the rebuilt prefix by `prependWord`. The
branch knows its whole prefix, that prefix being the index selecting it, so
rebuilding reads nothing.

`rankedSem_eq` is the content: the expression's state word is the spelling of
the state `RankedAlphabet.scanFinal` computes. It is a `List.rec` over `w`
through `scanSem_eq`, its step a case analysis matching `casesSem_eq`'s branch
selection against `RankedAlphabet.scanStep`'s clauses.

`length_rankedSem_le` follows: `|stateWord R s| = 1 + R.width + s.depth`, and
`depth` rises by at most one per completed block, so
`depth ≤ ⌊|w| / R.width⌋ ≤ |w|` by `R.width_pos`. At the empty word the bound
is `R.width + 1 ≤ 0 + R.width + 1`, tight.

### The verdict and the bridge

```lean
@[expose] def isRankedOf (R : RankedAlphabet) : COf 1
@[expose] def isRankedSem (R : RankedAlphabet) : Sem 1
theorem isRankedSem_eq_singleton_iff_valid (R : RankedAlphabet) (w : List Bool) :
    isRankedSem R ![w] = [true] ↔ R.Valid w
theorem isRankedSem_eq_ite (R : RankedAlphabet) (w : List Bool) :
    isRankedSem R ![w] = if R.Valid w then [true] else []
theorem isRankedSem_binRanked_iff (w : List Bool) :
    isRankedSem binRanked ![w] = [true] ↔ isTreeSem ![w] = [true]
```

`RankedAlphabet.validBool` asks that the scan end live, with an empty
incomplete block and exactly one pending subterm, so the accepting state word
is the single constant `true :: bufField R [] ++ [true]`. The verdict is
therefore a case over `R.width + 3` bits of the final state — one past the
accepting word, so that a `depth` exceeding one is rejected — with constant
branches, which is `casesOf` again.

`isRankedSem_eq_ite` pins the value on the rejecting branch as well as the
accepting one, for the reason `isTreeSem_eq_ite` records: the `iff` alone
admits a recognizer returning `[false]` on a rejected word, so correctness as a
function is not implied by correctness of the accepted set.

The bridge composes `RankedAlphabet.Binary.valid_iff` with
`isTreeSem_eq_singleton_iff_valid`; it is a corollary of statements B1 and the
existing recognizer already carry, not a re-proof. `Cobham/Tree.lean` is not
edited: `comb` and `isTree` keep their definitions, so `isTree_smashFree` and
the [Strahm2003] Theorem 1(2) reasoning keep their subject, and the generic
construction — which is not `decide`-dischargeable and is far larger — is not
substituted underneath them.

## Test mirrors

Under `GebTests/Mathlib/Computability/Cobham/`, each naming a `def` value built
from the module under test rather than asserting inside an anonymous `example`,
since `lake shake` infers imports from the constants an olean references and
reports an import used only by an `example` as removable.

- **`Cases.lean`** — `casesSem` at a literal `p` against an explicitly
  tabulated branch family, including a scrutinee shorter than `p` to pin the
  zero-padding convention, and a scrutinee longer than `p` to pin that the
  high bits are ignored.
- **`Fold.lean`** — a carrier with `dec` non-injective off the image of `enc`,
  so that `hdec` is exercised rather than trivially satisfied, swept against
  `run` over every word up to length eight.
- **`Ranked.lean`** — `isRankedSem` swept against `RankedAlphabet.validBool`
  over every word up to length eight, at B1's existing fixtures
  `sampleAlphabet` (`card = 2 ^ width`) and `narrowAlphabet`
  (`card < 2 ^ width`, so a block spells no symbol and the `arOf = none` branch
  is reached), and at `binRanked` for the bridge.

Sweep budgets are per-computation and are measured rather than predicted;
`set_option maxRecDepth` is valid in tactic position. `native_decide` is
forbidden, carrying a compiler-trust axiom.

## Documentation

Each segment carries its own `docs/index.md` entry and its own `TODO.md`
revision, in the shape B1 and B2 use. `TODO.md` § Extensions of the tree
recognizers records B3 and B6 as done in the segments that complete them, and
gains the `constAt` duplication in `Cobham/Tree.lean` as a deferral.

## What the prototype has established

`Geb/Internal/CasesSpike.lean` compiles the whole of concern 1 through
`casesSem_eq`, and is deleted before `Cobham/Cases.lean` lands, carrying
`open Cobham` and names that collide with the real module. Established there
rather than argued:

- `Nat.rec` at the motive `((Fin p → Bool) → sig.toPFunctor.W) → sig.toPFunctor.W`
  elaborates, and the reindexing by `Fin.cons` in the recursive calls is
  accepted.
- `wValid_casesRaw` and `casesSem_eq` both measure `[propext, Quot.sound]`.
- `casesSem (p + 1) br ![b :: t, x]` is definitionally the shifted subtree's
  meaning, so the successor step of `casesSem_eq` needs no `change`: the
  statement of `semAt2_shiftW` at the right instance typechecks against it
  directly.
- The scrutinee-shift formulation replaced an earlier one that scrutinised
  `pred ^ j` of a fixed argument at depth `j`. That form does not reduce under
  case analysis, because the scrutinee is not a variable; the failure was a
  compiler's, not an argument's.

Not yet prototyped, and so stated in the plan only to the extent the plan can
carry compiled code: `casesOf`'s `RecBounded` component, `casesSem_eq_eval`,
and the whole of concerns 2 and 3.

## Risks and open questions

| Risk | Effect | Response |
| --- | --- | --- |
| Kernel reduction of a sweep at a concrete alphabet | `dispatchWidth` is `width + maxArity + 2`, so a width-two alphabet of arities at most two dispatches on six bits | Keep the fixtures at `width ≤ 2`; measure the recursion depth rather than predict it |
| The order in which `bufField` stores `buf` against the order `decodeBits` reads a block | A recognizer correct on no word, caught only by the sweep | `decodeBits` takes the head as the least significant bit and `scanStep` prepends the incoming bit to `buf`; the sweep against `validBool` at `narrowAlphabet` is what settles it |
| `casesOf`'s `RecBounded` component | Blocks concern 1 | Componentwise from the branches', every node being a `comp` over members of `C`; the same `Nat.rec` as `wValid_casesRaw` |
| Whether finite-state containment is a published statement | A missing citation, or a wrongly claimed novelty | Search with `theoremsearch` and `arxiv-mcp-server` before the module docstring is written; record the key in `docs/references.bib` if found |

Deferred, and not part of these three concerns: the `constAt` duplication in
`Cobham/Tree.lean`; B4, absorbing `BinTree` into `RankedAlphabet.Term`; and
B5, the linear time and space bound against Cslib's `MultiTapeTM`.

## References

- [Cobham1965] — the class and the arity relation of bounded recursion on
  notation.
- [HeraudNowak2011] — the `Rec` form `Cobham/Basic.lean` transcribes for
  `pred` and `cond`.
- [Strahm2003] — Theorem 1(2), the polynomial-time and linear-space
  containment of the `smash`-free subalgebra, which the bridge preserves for
  `isTree`.
