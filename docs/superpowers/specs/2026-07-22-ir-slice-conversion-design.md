# Design: Conversions between IR codes and slice polynomial functors

## Summary

Implement the two code-level translations between small inductive-recursive
(IR) codes and slice polynomial functors (SlicePFunctor), following Section 4
of [HancockMcBrideGhaniMalatestaAltenkirch2013] (henceforth [HMGA2013]).

- **SlicePFunctor to IR** (Lemma 1): a straightforward, non-recursive
  translation producing an `IR I O` code from a `SlicePFunctor I O`.
- **IR to SlicePFunctor** (Lemma 2 / Definition 5): a recursive translation
  producing a   `SlicePFunctor I O` from an `IR I O` code, defined via the
  `IR.elimAlg` eliminator.

No semantic equivalence proofs (that the interpretations agree) are included
in this design; those are deferred to follow-up work.

## Background

### The paper's translations

[HMGA2013] Section 4 establishes that small IR and dependent polynomials
(indexed containers) define the same class of functors. The two halves:

**Lemma 1 (Poly to IR):** Given a dependent polynomial `(r, t, q)` with
`I ←r— P —t→ S —q→ O`, the IR code is:

```
Σ S (λ s →
  let Ps = fiber(t, s) in
  Π Ps (λ assign →
    Σ (∀ a, assign a ≡ r (π₀ a)) (λ _ →
      ◆ (q s))))
```

The outer `Σ` ranges over shapes `S`; the `Π` (delta) ranges over the
directions of shape `s` (the fiber `Ps ≅ B s`); the inner `Σ` is the
compatibility constraint restricting the assignment to agree with the
direction-input map `r`; the `◆` (iota) terminates at the output index `q s`.

**Lemma 2 / Definition 5 (IR to Poly):** Defined by structural recursion on
the IR code:

- `◆ o`: trivial polynomial `I ←— ∅ —→ 1 —→ O` (one shape, no directions).
- `Σ S K`: coproduct of the sub-polynomials `φ(K s)` over `s : S`.
- `Π B K`: the complex case. Shapes are `Σ_{i:B→I} shapes(K i)`, directions
  are `B ⊕ directions(K i)`, the input map is the cotuple `[i, r(K i)]`, and
  the output map is `q(K i)`.

### Our formalization

Our `SlicePFunctor.{uA, uB, uD, uC} dom cod` (`Slice/Basic.lean`) is a
`PFunctor` (shapes `A : Type uA`, directions `B : A → Type uB`) extended with:
- `r : Idx → dom` (direction-input map, where `Idx = Σ a, B a`)
- `q : A → cod` (shape-output map)

This is the indexed container `(S, P, n)` view from [HMGA2013] Definition 2,
where:
- `S j = {a : A // q a = j}` (shapes over output `j`)
- `P j s = B s.1` (directions of shape `s`)
- `n j s p = r ⟨s.1, p⟩` (input index of direction `p` of shape `s`)

Our `IR.{uA, uB, uI, uO} I O` (`IndRec/Basic.lean`) is the W-type of a
polynomial functor with three shape constructors: `iota` (constant), `sigma`
(dependent sum), and `delta` (dependent product). It has an algebra-based eliminator `IR.elimAlg`
with computation rules `IR.elim_mk`, and a dependent recursor `IR.rec`
with propositional computation rules `IR.rec_iota` / `IR.rec_sigma` /
`IR.rec_delta`.

The existing `IndRec/Container.lean` provides `contCode`, which translates a
non-indexed `PFunctor` to an `IR PUnit PUnit` code (Example 1 of [HMGA2013]).

## Design

### File location

New file: `Geb/Mathlib/Data/PFunctor/IndRec/Slice.lean`

Imports (both `public import`, re-exporting to downstream):
`Geb.Mathlib.Data.PFunctor.IndRec.Basic` and
`Geb.Mathlib.Data.PFunctor.Slice.Basic`.

Registered in `IndRec.lean`'s import list as `public import`, after
`Container.lean`.

### Module docstring

The module docstring (`/-! … -/`) includes the following sections per
`docs/rules/lean-coding.md` § Documentation:

- `# Codes for slice polynomial functors as IR codes, and back` — title
- Brief summary (the two translations and their source in
  [HMGA2013] Section 4)
- `## Main definitions` — `IR.sliceCode`, `IR.toSlicePFunctorIota`,
  `IR.toSlicePFunctorSigma`, `IR.toSlicePFunctorDelta`,
  `IR.toSlicePFunctorAlg`, `IR.toSlicePFunctor`
- `## Main statements` — `IR.toSlicePFunctor_iota`,
  `IR.toSlicePFunctor_sigma`, `IR.toSlicePFunctor_delta`
- `## Implementation notes` — the universe stabilization
  (`uA' = max uA uB uI`, `uB' = uB`), the `ULift(PLift(...))` constraint
  pattern, and the indexed-container presentation choice (see below)
- `## References` — [HancockMcBrideGhaniMalatestaAltenkirch2013]
- `## Tags` — `inductive-recursive, polynomial functor, slice category,
  container, indexed container`

### Naming

- `IR.sliceCode` — `SlicePFunctor I O → IR I O` (produces the IR code for a
  slice PFunctor; parallels `contCode` in `Container.lean`)
- `IR.toSlicePFunctorIota` — the iota case of the algebra (constant slice polynomial)
- `IR.toSlicePFunctorSigma` — the sigma case (coproduct of sub-polynomials)
- `IR.toSlicePFunctorDelta` — the delta case (shapes indexed by assignments)
- `IR.toSlicePFunctorAlg` — the `Alg` assembling the three cases
- `IR.toSlicePFunctor` — `IR I O → SlicePFunctor I O` (produces the slice
  PFunctor for an IR code)
- `IR.toSlicePFunctor_iota`, `IR.toSlicePFunctor_sigma`,
  `IR.toSlicePFunctor_delta` — computation rules derived from `IR.elim_mk`

### Translation 1: `IR.sliceCode` (SlicePFunctor to IR)

**Signature:**
```
IR.sliceCode : SlicePFunctor.{uA, uB, uI, uO} I O → IR.{uA, uB, uI, uO} I O
```

**Definition** (non-recursive, direct construction):
```
sigma A (fun a =>
  delta (B a) (fun assign =>
    sigma (ULift.{uA} (PLift (∀ b, assign b = F.rCurried a b))) (fun _ =>
      iota (F.q a))))
```

Where:
- `A = F.toPFunctor.A` — shapes
- `B = F.toPFunctor.B` — direction family
- `F.rCurried a b = F.r ⟨a, b⟩` — direction-input map (curried form)
- `F.q a` — shape-output map
- `assign : B a → I` — the delta assignment (decoding of the direction data)

**The constraint:** `∀ b, assign b = F.rCurried a b` is `Prop`-valued. It is
embedded into `Type uA` via `ULift.{uA}(PLift(...))`, matching the existing
pattern in `Hom.lean:116` (`ULift.{max uA uB uI} (PLift (o = o'))`). The
constraint forces the delta assignment to agree with the direction-input map
`r`, which is the compatibility condition of
`SliceDomPFunctor.Compatible`. This
makes the IR code's interpretation match the slice polynomial functor's
domain-restricted interpretation.

**Universe:** Output is `IR.{uA, uB, uI, uO} I O`, same universe parameters as
the input's PFunctor part. The constraint type `ULift.{uA}(PLift(...))` lives
at `Type uA` (since `PLift(Prop) : Type 0` and `ULift.{uA}(Type 0) : Type uA`
via `max 0 uA = uA`), matching the shapes `A : Type uA`.

### Translation 2: `IR.toSlicePFunctor` (IR to SlicePFunctor)

**Signature:**
```
IR.toSlicePFunctor : IR.{uA, uB, uI, uO} I O
  → SlicePFunctor.{max uA uB uI, uB, uI, uO} I O
```

**Universe stabilization:**
- Shape universe `uA' = max uA uB uI`: the delta case introduces shapes
  `Σ (i : B → I), sub-shapes` where `B → I : Type (max uB uI)`; the sigma
  case has shapes involving `A : Type uA`. So `uA' ≥ max uA uB uI`.
- Direction universe `uB' = uB`: the delta case directions are
  `Sum B sub-directions` where `B : Type uB`; with `uB' = uB`, directions stay
  at `Type uB`.

**Definition** via `IR.elimAlg` with target type
`SlicePFunctor.{max uA uB uI, uB, uI, uO} I O`:

The motive universe is
`v = max (max uA uB uI + 1) (uB + 1) uI uO`
(the universe of `SlicePFunctor.{max uA uB uI, uB, uI, uO} I O`). It is
inferred by Lean from the algebra's type.

The algebra `IR.toSlicePFunctorAlg` assembles three named functions —
`toSlicePFunctorIota`, `toSlicePFunctorSigma`, `toSlicePFunctorDelta` —
following the `interpObjIota`/`interpObjSigma`/`interpObjDelta` pattern
in `Basic.lean`. Each handles one case:

**Iota case** (`◆ o`, Definition 5 clause 1):
```
{ A := PUnit.{uA'+1}
, B := fun _ => PEmpty.{uB'+1}
, r := fun ⟨_, b⟩ => PEmpty.elim b
, q := fun _ => o }
```
One shape (unit), no directions, output index `o`.

**Sigma case** (`Σ A₀ K`, Definition 5 clause 2 — coproduct of sub-polynomials):
For each `a : A₀`, the IH gives `F_a = sub a : SlicePFunctor I O`.
```
{ A := Σ a, F_a.toPFunctor.A
, B := fun ⟨a, s⟩ => F_a.toPFunctor.B s
, r := fun ⟨⟨a, s⟩, p⟩ => F_a.r ⟨s, p⟩
, q := fun ⟨a, s⟩ => F_a.q s }
```
Shapes are indexed coproducts of sub-shapes; directions, input map, and output
map are inherited componentwise.

**Delta case** (`Π B₀ K`, Definition 5 clause 3 — the complex case):
For each assignment `i : B₀ → I`, the IH gives `F_i = sub i`.
```
{ A := Σ (i : B₀ → I), F_i.toPFunctor.A
, B := fun ⟨i, s⟩ => Sum B₀ (F_i.toPFunctor.B s)
, r := fun ⟨⟨i, s⟩, Sum.inl b⟩ => i b
       fun ⟨⟨i, s⟩, Sum.inr p⟩ => F_i.r ⟨s, p⟩
, q := fun ⟨i, s⟩ => F_i.q s }
```
Shapes are coproducts of sub-shapes indexed by assignments `B₀ → I`.
Directions are the coproduct of the arity `B₀` (a direction selecting an input
index via `i`) and the sub-directions. The input map `r` is the cotuple: on
`Sum.inl b` it gives `i b` (the assignment's prescribed index), on `Sum.inr p`
it delegates to the sub-polynomial's `r`. The output map delegates to the
sub-polynomial's `q`.

This matches the indexed container computation in the proof of Lemma 2 (the
proof's `Ŝ_{ΠPK} o = Σ_{i:B→I} Ŝ_{Ki} o`, `P̂_{ΠPK} o s₀ = B + P̂_{Ki} o s₀'`,
`n` is the cotuple `[i, n_{Ki}]`), and is also the "sum of products"
description from Section 5.

**Presentation note:** Definition 5 presents the delta-case directions in the
*dependent polynomial* form `(P × S(K i)) + P(K i)`, where the `P × S(K i)`
factor accounts for the `t` map (direction-to-shape). The spec uses the
*indexed container* form `B + P(K i)` (directions without the shape pairing),
which is what `SlicePFunctor` represents and what the proof of Lemma 2
computes. The two are equivalent via the fiber construction of Definition 2.

**Elaboration note:** The `r` field's dependent pattern match
(`match p with | Sum.inl b => ... | Sum.inr p' => ...`) on the direction type
`Sum B₀ (F_i.toPFunctor.B s)` — where `F_i` is the IH result accessed via
`sub i` — may require explicit intermediate `let` bindings to help
the elaborator track `F_i` across branches.

**Computation rules** (via `IR.elim_mk`, which holds definitionally):
```
theorem IR.toSlicePFunctor_iota (o : O) :
    IR.toSlicePFunctor (IR.iota I O o) = IR.toSlicePFunctorIota I O o
theorem IR.toSlicePFunctor_sigma (A : Type uA) (c : A → IR I O) :
    IR.toSlicePFunctor (IR.sigma I O A c) =
      IR.toSlicePFunctorSigma I O A fun a => IR.toSlicePFunctor I O (c a)
theorem IR.toSlicePFunctor_delta (B : Type uB) (c : (B → I) → IR I O) :
    IR.toSlicePFunctor (IR.delta I O B c) =
      IR.toSlicePFunctorDelta I O B fun i => IR.toSlicePFunctor I O (c i)
```

### Implementation notes

- `set_option linter.checkUnivs false` is used for declarations with the
  separated arity universes, following the pattern of `Basic.lean`.
- The whole file is `@[expose] public section`, consistent with `Basic.lean`
  and `Container.lean`, so downstream modules and tests can unfold through
  every definition.
- The `toSlicePFunctorAlg` is a named `Alg` definition so that
  `IR.elim_mk` applies, giving **definitional** computation rules (`rfl`).
  Its three components are factored into named functions
  (`toSlicePFunctorIota`, `toSlicePFunctorSigma`, `toSlicePFunctorDelta`)
  following the `interpObjIota`/`interpObjSigma`/`interpObjDelta` pattern
  in `Basic.lean`.
- The `SlicePFunctor` structures in the algebra are constructed via anonymous
  constructor notation with explicit parent field:
  `{ toPFunctor := ⟨A, B⟩, r := ..., q := ... }`.

## References

- [HancockMcBrideGhaniMalatestaAltenkirch2013] — Section 4 (Lemmas 1-2,
  Definition 5) for the translations. Section 5 for the "sum of products"
  reformulation of the delta case.
- `IndRec/Container.lean` — `contCode`, the non-indexed analogue
  (Example 1).
- `IndRec/Basic.lean` — `IR.elimAlg`, `IR.Alg`, `IR.elim_mk`,
  `IR.rec`, `IR.RecStep`, `IR.rec_mk`.
- `Slice/Basic.lean` — `SlicePFunctor`, `SliceDomPFunctor.rCurried`,
  `SliceDomPFunctor.Compatible`.
- `IndRec/Hom.lean:116` — precedent for `ULift.{u}(PLift (prop))` embedding.
