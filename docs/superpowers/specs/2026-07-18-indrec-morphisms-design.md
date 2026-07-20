# Morphisms of IR codes — design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [Closure gate result](#closure-gate-result)
- [Source and proof-route deviation](#source-and-proof-route-deviation)
- [Design](#design)
  - [FreeCoprodCompDisc additions](#freecoprodcompdisc-additions)
  - [Precomposition on codes](#precomposition-on-codes)
  - [Universe scheme](#universe-scheme)
  - [Homset (Definition 8)](#homset-definition-8)
  - [Identity (branch 2a)](#identity-branch-2a)
  - [Theorem 2.4 functoriality (branch 2b)](#theorem-24-functoriality-branch-2b)
  - [Naturality and Theorem 3 (branch 2c)](#naturality-and-theorem-3-branch-2c)
  - [Composition and the category laws (branch 2d)](#composition-and-the-category-laws-branch-2d)
  - [Semantic statements (branch 1, complete)](#semantic-statements-branch-1-complete)
  - [Placement and documentation](#placement-and-documentation)
- [Branch decomposition](#branch-decomposition)
- [Constraints](#constraints)

<!-- END doctoc generated TOC -->

## Purpose

Extend `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean` with the
category of IR codes, following
[HancockMcBrideGhaniMalatestaAltenkirch2013] from "The category of
small IR codes" through Corollary 2. Branch 1 (complete) supplied the
auxiliary semantic operations (copower, `(+i)`, the cotuple `[i, k]`),
the code operation `γ^i` (Lemma 4), and Lemmas 3 and 4. The remaining
work — the homset (Definition 8), the identity, composition, and the
category laws (Corollary 2) — is delivered in four dependency-ordered
branches (see Branch decomposition):

- 2a: the homset and the identity morphism, constructed syntactically.
- 2b: the functoriality content of Theorem 2.4 of
  [GhaniNordvallForsbergMalatesta2015] for the interpretation
  (`FreeCoprodCompDisc.Hom` identity and category laws; the `IR.rec`
  computation rule; the characterizing equations of `IR.interpMor`;
  preservation of identity and composition).
- 2c: natural transformations between interpretations and Theorem 3
  (the interpretation extended to morphisms, full and faithful).
- 2d: composition and the category laws (Corollary 2), by transfer
  through the full-and-faithful interpretation of Theorem 3.

The scope grew from the original branch-2 plan (homset plus a purely
syntactic identity, composition, and laws) after the closure gate below
established that composition does not close by syntactic induction on
codes and requires the semantic transfer of Theorem 3.

The mathlib `Category` instance, Theorem 2 (the left-Kan-extension
characterization), and Theorem 4 (the equivalence with dependent
polynomial functors) remain deferred to future workstreams.

## Closure gate result

The identity, composition, and category laws were first specified as a
single simultaneous syntactic induction on codes (no interpretation
route). A prototype of the homset and the candidate auxiliary
operations, checked against the built `Basic.lean`, established:

- The homset (Definition 8) computes definitionally at every clause,
  and the identity morphism closes syntactically — through a
  list-generalized pre-unit `Hom γ (γ^a)` whose recursion appends the
  mapped `δ`-direction to a superscript stack (so the subcode
  induction hypothesis lands at the required precomposition depth) and
  a navigation operation carrying a factorization parameter. The
  identity depends only on `propext` and `Quot.sound`.
- Composition does not close. It requires `supMor` (the action of
  precomposition on morphisms) and `sup2` (associativity of iterated
  precomposition) at the codomain code, which is a parameter rather
  than a structural subcode of the recursion; no generalization of the
  recursion variable reaches it, and the homset is domain-recursive, so
  inducting on the codomain does not decompose it either. This matches
  the source, which obtains Corollary 2 by transfer along the
  full-and-faithful interpretation (Theorem 3), not syntactically.

## Source and proof-route deviation

The paper proves Corollary 2 by transfer along the full and faithful
interpretation functor of Theorem 3; the paper exhibits no explicit
identity or composition on the homsets of Definition 8, and asserts
`γ^i` only to exist (Lemma 4). This workstream follows the paper's
transfer route for composition and the category laws (branch 2d),
constructs the identity syntactically (branch 2a), and supplies its own
constructive proofs, in the `FreeCoprodCompDisc` encoding, of the
Theorem 2.4 functoriality (branch 2b) and of Theorem 3 (branch 2c) that
the transfer consumes:

- Transcription: the homset clauses of Definition 8; the statements
  of Lemma 3, Lemma 4, the functoriality content of Theorem 2.4 of
  [GhaniNordvallForsbergMalatesta2015], Theorem 3, and Corollary 2;
  the copower and `(+i)` operations; the binary coproduct `[i, k]`
  of objects (the paper's cotuple, used by `(+i)`).
- Novel (constructed here): the concrete `γ^i` (branch 1); the
  syntactic identity, through a list-generalized pre-unit and a
  navigation operation (branch 2a); the constructive proofs of the
  Theorem 2.4 functoriality, Theorem 3, and Corollary 2 in the
  `FreeCoprodCompDisc` encoding, together with the natural-transformation
  notion between interpretations they require; the universe scheme
  below; the object-isomorphism notion and the name-lifting operation
  on `FreeCoprodCompDisc` objects.

Recorded deviations from the paper's statements: composition and the
category laws are obtained by the paper's transfer through Theorem 3
rather than by syntactic induction on codes, the closure gate having
established that the syntactic route does not reach composition;
Theorem 3's natural isomorphism is realized in the constructive,
`Classical`-free `FreeCoprodCompDisc` encoding (no mathlib `Category`);
Lemma 4's
equality of interpretations is stated as a pointwise isomorphism
(the intensional setting does not validate the paper's equality of
functors); Lemma 3's natural isomorphism is likewise stated as a
pointwise isomorphism (natural transformations between
interpretations are not yet defined; naturality is deferred with
Theorem 3); the clauses of `γ^i` and of the homset carry
`ULift` insertions forced by the universe scheme below; clause 1A
renders the paper's proposition `o ≡ o'` as the type
`PLift (o = o')`; and the homset is heterogeneous in the arity
universes where Definition 8 states one instantiation.

## Design

### FreeCoprodCompDisc additions

In `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`:

- Binary coproduct of objects (`Sum` of name types, `Sum.elim` of
  decodings), with injections and cotuple universal property.
- Copower `X ⊗ i`: `coprod X (fun _ ↦ i)` for a type `X` and an
  object `i`, with its universal property.
- `(+i)`: the object map sending `k` to the binary coproduct of a
  fixed object `i` with `k`.
- A name-lifting operation (`ULift` on the name type, decoding
  through `ULift.down`), so objects at a lower index universe can
  enter `Hom` and the coproduct constructions.
- An object-isomorphism notion: a name-type equivalence commuting
  with decodings. Chosen over a mutually inverse `Hom` pair
  because `Equiv` relates name types at different universes, which
  the lemma statements below require (`Hom` is fixed at one index
  universe).

### Precomposition on codes

`γ^i` internalizes precomposition with `(+i)` for `i : Q → I`: its
specification (Lemma 4) is `⟦γ^i⟧ k ≅ ⟦γ⟧ ((+i) k)` where the
object of `(+i)` is `⟨Q, i⟩`. Defined by `IR.elim` on `γ`:

- `(ι o)^i = ι o`; `(σ A K)^i = σ A (fun a ↦ (K a)^i)`.
- `(δ Q' K')^i`: a `σ` over `c : Q' → Q ⊕ PUnit` (classifying
  each element of the arity `Q'` as resolved immediately into `i`
  or not), then a `δ` over the subtype of unresolved arity
  elements, recursing on `K'` at the assignment merging `i ∘ c`
  with the `δ` directions.

The clauses are stated up to the `ULift` insertions the target
universe instantiation requires (for example `σ` receives the
lifted `A` and the lifted `c`-type).

### Universe scheme

The `σ` arity in the `δ` clause of `γ^i` lives at
`max uB' uB` (`Q' : Type uB'`, `Q : Type uB`), so for `i : Q → I`
with `Q : Type uB`, `γ^i` maps `IR.{uA', uB', uI, uO}` to
`IR.{max uA' uB' uB, uB', uI, uO}`, and that target instantiation
is a fixed point of the operation. Consequently:

- `IR.Hom` is heterogeneous: left code at `{uA, uB}`, right code at
  the stabilized instantiation `{max uA' uB uB', uB'}` (clause 3
  sends the right code through `γ^i`, and a single Lean definition
  cannot recurse at a changed universe instantiation).
- Identity, composition, and the laws are stated at the uniform
  stabilized instantiation `IR.{max uA uB, uB, uI, uO}`: a
  `Hom γ γ` requires the right side's `σ`-arity universe to carry
  the `max … uB` shape. The raw homset keeps the extra
  heterogeneous generality.
- The semantic lemmas are also stated at the uniform
  instantiation. `IR.interpObj` lands in `Map.{max uA uB, uI, uO}`
  and `Map` fixes one index universe for domain and codomain, so
  `⟦γ⟧ ((+i) k)` elaborates only where the coproduct's index
  universe is absorbed by the interpretation's — which the
  uniform instantiation provides (`Q : Type uB`,
  `γ : IR.{max uA uB, uB, uI, uO}`). The heterogeneous generality
  applies to the code operation and the homset, not to the
  interpretation, whose signature this workstream does not
  change.

### Homset (Definition 8)

`IR.Hom`, by `IR.elim` on the left code with an inner `IR.elim` on
the right code in the `ι` case:

- Clause 1A: `Hom (ι o) (ι o') = PLift (o = o')` (a `Type`, since
  other clauses wrap homsets in `Σ`/`Π`).
- Clause 1B: `Hom (ι o) (σ A K) = Σ a, Hom (ι o) (K a)`.
- Clause 1C: `Hom (ι o) (δ Q' K') =
  Σ e : Q' → PEmpty, Hom (ι o) (K' (PEmpty.elim ∘ e))`.
- Clause 2: `Hom (σ A K) γ' = Π a, Hom (K a) γ'`.
- Clause 3: `Hom (δ Q K) γ' = Π i : Q → I, Hom (K i) (γ'^i)`.

### Identity (branch 2a)

The homset and the identity are constructed syntactically at the
uniform instantiation, by `IR.rec` on the domain code, in named
one-step operations (each an explicit term). The construction, verified
against `Basic.lean`:

- Homset transport `homOfEq` along code equalities (the `IR.Hom`
  analogue of `FreeCoprodCompDisc.homOfEq`).
- `sigmaPush : Hom γ (K a) → Hom γ (σ A K)` — σ-injection
  postcomposition, `IR.rec` on the domain with the target `(A, K, a)`
  generalized. (Identity at a `σ` code is not componentwise
  reflexivity; clause 2 makes it a product of injections into the
  whole `σ` code.)
- `deltaEmptyPush : Hom γ (M (PEmpty.elim ∘ e)) → Hom γ (δ E M)` for an
  empty witness `e : E → PEmpty`, `IR.rec` on the domain with
  `(E, e, M)` generalized.
- A list-generalized pre-unit `preUnitStack γ L : Hom γ (γ ^^ L)`,
  where `γ ^^ L` folds precomposition over a list `L` of index
  objects. `IR.rec` on `γ` with `L` generalized: the `δ` case appends
  the mapped direction `⟨B, i⟩` to `L`, so the subcode induction
  hypothesis lands at the precomposition depth the clause-3 superscript
  demands. The navigation from that hypothesis into the superscripted
  `δ`-tower is a `deltaNav` operation carrying a factorization
  parameter `g : Bin → Bout` that tracks how a peeled classifier layer
  resolves against the outer superscript.
- `id γ := preUnitStack γ []`.

The stack generalization replaces the simultaneous superscript-generalized
induction the original branch-2 plan anticipated. For the identity every
superscript layer is generated by the domain's own directions, which the
stack captures, so the recursion is well-founded on the domain code with
the stack a parameter. The identity depends only on `propext` and
`Quot.sound`. The `List`-recursive helpers (`γ ^^ L`, the stack folds)
are committed through `List.rec`, per the recursor-only rule.

Statement: `id : Hom γ γ`.

### Theorem 2.4 functoriality (branch 2b)

The functoriality content of Theorem 2.4 of
[GhaniNordvallForsbergMalatesta2015], constructively, so that `⟦γ⟧` is a
functor and natural transformations between interpretations can be
stated:

- `FreeCoprodCompDisc.Hom` identity and the category laws (left
  identity, right identity, associativity); composition
  (`FreeCoprodCompDisc.Hom.comp`) exists from branch 1. The
  functoriality of `coprodMor` (preservation of identity and
  composition), which the functor-law proofs and branch 2c's
  naturality consume.
- The propositional computation rule of `IR.rec`, and from it the
  characterizing equations of `IR.interpMor` at `IR.iota`,
  `IR.sigma`, and `IR.delta`.
- Preservation of identity and composition by `IR.interpMor`.

Independent of branch 2a. Corresponds to the existing TODO item
"Complete Theorem 2.4 for `IndRec`" (constructive part).

### Naturality and Theorem 3 (branch 2c)

- A notion of natural transformation between interpretations
  `⟦γ⟧ ⇒ ⟦γ'⟧` (families of `FreeCoprodCompDisc.Hom` commuting with the
  morphism maps), with identity and vertical composition.
- Theorem 3: the interpretation extended to morphisms,
  `Hom γ γ' → Nat(⟦γ⟧, ⟦γ'⟧)`, full and faithful — the correspondence
  `Hom γ γ' ≅ Nat(⟦γ⟧, ⟦γ'⟧)`, by induction on the homset structure,
  using Lemmas 3 and 4 (branch 1). Fullness (the `Nat → Hom` direction)
  is what the transfer of branch 2d consumes.

Depends on branch 2b. The constructive proof of Theorem 3 in the
`FreeCoprodCompDisc` encoding — in particular staying `Classical`-free —
is this branch's closure gate: its plan derives the induction before
implementation, returning to design if it fails to close.

### Composition and the category laws (branch 2d)

By transfer through the full-and-faithful interpretation of Theorem 3
(the paper's Corollary 2):

- `comp : Hom γ γ' → Hom γ' γ'' → Hom γ γ''`, the image under fullness
  of the vertical composite of the transported natural transformations.
- Left identity, right identity, and associativity, as equalities in
  the homsets, from the corresponding laws for natural transformations
  together with faithfulness.

The auxiliary code operations the syntactic route required (`supMor`,
the action of precomposition on morphisms; `sup2`, associativity of
iterated precomposition) are subsumed: they are precomposition's
functoriality and associativity, which hold semantically through
Lemma 4 and need no separate syntactic construction. Depends on
branches 2a and 2c.

### Semantic statements (branch 1, complete)

Both at the uniform instantiation (`γ : IR.{max uA uB, uB}`,
`i : Q → I`, `Q : Type uB`), with the object-isomorphism notion
absorbing residual index-universe differences between the two
sides. Branch 2c reuses these as the semantic content of Theorem 3:

- Lemma 4: `⟦γ^i⟧ k ≅ ⟦γ⟧ ((+i) k)` pointwise, by induction on
  `γ` — the correctness proof for the constructed `γ^i`.
- Lemma 3:
  `⟦δ Q K⟧ k ≅ ∐ (i : Q → I), Hom(lift ⟨Q, i⟩, k) ⊗ ⟦K i⟧ k`
  pointwise, from the coproduct and copower machinery; `⟨Q, i⟩`
  enters `Hom` through the name-lifting operation, since its
  names live at `uB` and `k`'s at `max uA uB`.

### Placement and documentation

A requirement of this workstream is that the morphism development
precede the `Universes` and `Container` sections, so later
workstreams can extend those sections with morphism uses. The
expanded scope (homset and identity, Theorem 2.4 functoriality,
naturality and Theorem 3, composition and the laws) is large enough
that the narrow-and-deep directory structure favours sibling `IndRec`
modules over a single `IndRec/Basic.lean`; each branch's plan fixes
its file placement (a natural split is one module per branch —
`Hom`, `Functor`, `Naturality`, `Category` — with the `Universes` and
`Container` sections relocated after the morphism development). Module
docstrings (`## Main definitions`,
`## Main statements`, implementation notes) are updated in every
touched file (including `Geb/Mathlib/Logic/Equiv/Basic.lean`,
which receives generic `Equiv` combinators the constructions
factor through); every declaration transcribed from or specified
by the paper cites [HancockMcBrideGhaniMalatestaAltenkirch2013]
per the citation rules, with docstrings distinguishing
transcription from construction. Generic auxiliary machinery
(hom composition, the isomorphism notion, lifting, the `Equiv`
combinators) is not taken from the paper and carries no
citation, per the citation rules' scope. Mirrored test files
under `GebTests/` and the `docs/index.md` entry are updated in
the same branches.

## Branch decomposition

Branch 1 is complete (merged). The remaining work is four
dependency-ordered topic branches, each with its own plan:

- Branch 1 (complete): `FreeCoprodCompDisc` additions, `γ^i`,
  Lemmas 3 and 4.
- Branch 2a: the homset (Definition 8) and the identity. Depends on
  branch 1.
- Branch 2b: Theorem 2.4 functoriality. Depends on branch 1;
  independent of branch 2a.
- Branch 2c: naturality and Theorem 3 (full and faithful). Depends
  on branch 2b.
- A dedicated relocation branch (after 2b): moves the `Universes`
  and `Container` sections of `Basic.lean` into sibling modules
  following the morphism development, discharging the ordering
  requirement of Placement and documentation. Depends on branch 2b
  (which creates the module the sections must follow).
- Branch 2d: composition and the category laws (Corollary 2), by
  transfer. Depends on branches 2a and 2c.

Branches 2a and 2b are independent and may proceed in parallel. The
spec and all branch plans are removed in the final commits of the
last branch (2d), per CONTRIBUTING § Concern shape.

## Constraints

- Constructive discipline: no `noncomputable`, no `Classical`;
  axiom linter passes (`propext`, `Quot.sound` only).
- Recursor-only recursion: all definitions by recursors
  (`IR.elim`/`IR.rec`, and `List.rec` for the branch-2a stack
  helpers); no `induction` tactic, no self-referential `def`,
  no `termination_by`.
- Explicit proof terms: committed definitions and proofs are
  term-mode, with no tactic blocks. Tactics may be used during
  intermediate development to discover a proof; the committed
  form spells out the resulting term, factored into small named
  declarations (motives, step functions, auxiliary lemmas) in the
  manner of `IR.ExtMotive` and `IR.ext`, whose motive is factored
  out precisely so that the proof is an `Eq.rec` application.
  Rationale: the development is eventually to become
  self-referential — fixed points of inductive-recursive types
  that themselves describe the syntax of inductive-recursive
  definitions, including the syntax of these proofs — and tactic
  scripts obscure the proof terms that syntax must describe.
- `lake build`, `lake test`, `lake lint`,
  `scripts/lint-imports.sh` pass on each branch.
- Interface fixed by the source: the homset clauses and lemma
  statements follow the paper up to the recorded deviations
  (isomorphism for equality of interpretations; `ULift`
  insertions); implementation strategies are free.
