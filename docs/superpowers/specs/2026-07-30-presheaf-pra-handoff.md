# Handoff: write the spec from the presheaf p.r.a. prototype

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [The task](#the-task)
- [State of the branch](#state-of-the-branch)
- [What the prototype establishes](#what-the-prototype-establishes)
  - [Four facts the spec should state, each backed by a declaration](#four-facts-the-spec-should-state-each-backed-by-a-declaration)
  - [What is inference rather than elaboration](#what-is-inference-rather-than-elaboration)
- [Verified literature facts](#verified-literature-facts)
- [What to harvest from the previous spec](#what-to-harvest-from-the-previous-spec)
- [What remains open](#what-remains-open)
- [Two leads to weigh when brainstorming the codes](#two-leads-to-weigh-when-brainstorming-the-codes)
  - [Varying both sides at once, over the walking arrow](#varying-both-sides-at-once-over-the-walking-arrow)
  - [Indexed induction-recursion as the route to the code type](#indexed-induction-recursion-as-the-route-to-the-code-type)
- [Repository hazards learned the hard way](#repository-hazards-learned-the-hard-way)
- [Process notes](#process-notes)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

A transient planning document, removed with the spec and the plan. It
transfers a prototyping session to a fresh one whose task is to write the
spec.

## The task

Write the spec for a workstream on morphisms of presheaf
parametric-right-adjoint functors. The mathematics is settled and
machine-checked; what remains is code organisation and presentation.

The prototype at `Geb/Internal/PresheafIRProto/` is the source being
transcribed, in the sense that a paper usually is — except that it
compiles and is axiom-audited, so it cannot be misread, only
mis-organised. Treat it as the authority. Where this document and the
prototype disagree, the prototype is right.

`docs/superpowers/specs/2026-07-30-presheaf-pra-ir-codes-design.md` is
the previous spec. Its design content is superseded and should be
replaced wholesale, not edited: it was revised three times against
foundations that no longer exist, and each revision inherited the
previous framing's errors. Harvest from it only the items listed in
§ What to harvest.

## State of the branch

Branch `feat/presheaf-pra-ir-codes`, fifteen commits off `main`. `lake
build`, `lake lint`, `scripts/lint-imports.sh` and `lake test` all pass.

The prototype is imported from `Geb/Internal.lean`, so it is reachable
from the `Geb` root and audited by `GebMeta.detectNonstandardAxiom`. The
core is held to `{propext, Quot.sound}`; only
`Geb.Internal.PresheafIRProto.Functor` is on
`GebMeta.classicalAllowedModules`. That allowlist entry is persistent
infrastructure, not a `docs/` file, and must be removed in the same
commit that removes the prototype.

## What the prototype establishes

`Geb/Internal/PresheafIRProto/Basic.lean`, choice-free, 69 declarations
in twelve sections. `Geb/Internal/PresheafIRProto/Functor.lean`, the
allowlisted wrapper, two.

The central results, in dependency order:

| Declaration | Content |
| --- | --- |
| `shapePresheaf F : Jᵒᵖ ⥤ Type uA` | the shape presheaf, from `shapeRestr` |
| `arityPresheaf F a : Iᵒᵖ ⥤ Type uB` | the arity presheaf, from `directionRestr` |
| `ArityHom F a Z` | the unbundled presheaf hom `E(a) ⟶ Z` |
| `objEquivSigmaArityHom` | the interpretation is a coproduct of representables, at arbitrary `uZ` |
| `DomHom`, `domHomEquivNatFamily` | the representation theorem, domain level |
| `ShapeHom` | the shape map as a morphism of shape presheaves |
| `PshHom` | the full morphism type: `ShapeHom`, arity maps backward, `reindexCompat` |
| `pshHomFib_objFibRestr` | the action commutes with the `J`-restriction |
| `pshHomEquivNatFamily` | the representation theorem, in full |

The wrapper holds `arityHomEquivNatTrans` (the bundling isomorphism,
`rfl` both ways) and `objEquivSigmaHom` (the core equivalence
transported along it). The wrapper derives; it does not re-prove.

### Four facts the spec should state, each backed by a declaration

1. Natural transformations between presheaf p.r.a. functors are
   classified by shape-map-forward and arity-map-backward data. This is
   `pshHomEquivNatFamily`. Full and faithfulness is therefore
   definitional rather than a theorem to be hoped for.
2. The classification is available because a `PresheafPFunctor`'s
   interpretation is, by construction, a coproduct of representables —
   `objEquivSigmaArityHom`. It is not a property of the ambient
   category: Yoneda holds in any locally small category.
3. Unbundling buys both constructivity and universe polymorphism.
   `objEquivSigmaArityHom` holds at arbitrary `uZ`; its bundled wrapper
   is pinned to `uZ := uB`. Both restrictions came from requiring the
   arity presheaf and the input presheaf to lie in one functor category,
   which is exactly what `⟶` demands and exactly what draws in
   `Classical.choice` through `CategoryTheory.Functor.category`.
4. `PresheafPFunctorData` already *is* the familial presentation, in
   unbundled form. `shapeRestr` gives `T₁` its presheaf structure,
   `directionRestr` gives each `E(a)` its own, and `reindex` is the
   functoriality of `E` over `el(T₁)ᵒᵖ` — `ReindexNaturality` says
   exactly that `reindex g a : E(shapeRestr g a) ⟶ E(a)` is a presheaf
   morphism. Nothing needed adding; only bundling.

### What is inference rather than elaboration

The prototype's older sections carry claims marked as inferences; keep
the marking. In particular nothing relates `objPresheaf` of
`iotaPresheaf` or `iotaConst` to a constant functor — their
functoriality is elaborated, their constancy is not. `arityVaries`
elaborates its arity types; that `reindex` is non-invertible is a
marked one-step inference.

## Verified literature facts

Each was checked against the primary source during adversarial review;
several corrected an error. Sources:
`~/wingeb/positive-inductive-recursive-definitions.pdf`,
`~/wingeb/tlca13-small-induction-recursion.pdf`, Agda at
`~/git-workspaces/positiveIR/`.

- Remark 3.4 of [GhaniNordvallForsbergMalatesta2015]: results are
  "completely parametric in the choice of morphisms used; any collection
  that represents natural transformations between the codes works, as
  long as the identity morphisms and composition can be defined". The
  range runs to `Hom(x,y) = ⟦x⟧ → ⟦y⟧`, which is full and faithful "by
  definition" but forces `⟦−⟧` to be defined simultaneously with the
  codes, making the code system itself inductive-recursive.
- Section 2 of the same: its morphisms differ from those of
  [HancockMcBrideGhaniMalatestaAltenkirch2013], whose characterization
  of the `δ` interpretation as a left Kan extension fails for
  non-discrete `C`, losing full and faithfulness. Its conclusion lists
  recovering that characterization as an open problem, not an
  impossibility. Full and faithfulness over `Fam(C)` is therefore
  attainable, at the cost of the simultaneous definition above.
- Why the classification does not transfer to `Fam(C)`: Theorem 2.4
  indexes the `δ` coproduct by set maps `A → X`, whereas by
  Definition 2.2 a `Fam(C)`-morphism `(X,P) → (Y,Q)` is a pair `(h,k)`
  with `k : P ⟹ Q ∘ h`, carrying `C`-morphism data the index does not.
  So the `δ` interpretation is not a coproduct of `Fam(C)`-representables.
- Theorem 2.4 reads "Let `D` be a (possibly large) type": Dybjer–Setzer's
  index type need not be a set.
- Smallness in [HancockMcBrideGhaniMalatestaAltenkirch2013] is a
  restriction, not a generalization — "smallness refers to the size of
  the target-type", `I` and `O` "may be large types". What that paper
  adds over Dybjer–Setzer is the split of one index type into `I` and
  `O`.
- Remarks 2.3 states four properties of `Fam(C)`: fibred over `Set` with
  a standard split cleavage, the free set-indexed coproduct completion,
  cocomplete iff `C` has small connected colimits, and `Fam` a functor
  `CAT → CAT`. It says nothing about a Grothendieck construction; the
  split cleavage is the same content as the family functor.
- The shapes-forward arities-backward form is Definition 7 (morphisms of
  indexed containers). Definition 6 is the dependent-polynomial
  presentation whose `r`/`q` naming this repository follows. The
  unconstrained `A → X` coproduct index is Definition 4.
- Definition 3.1's `δ` morphism rule takes `ρ : Nat(F, G(− ∘ α))`; the
  Agda weakens `ρ` to a bare family, an admissible choice under
  Remark 3.4. The published `δ` *code* rule carries no functoriality
  witness; functoriality is the side condition that `F` be a functor.
- `docs/references.bib` has the author order of
  `GhaniNordvallForsbergMalatesta2015` wrong. The published LMCS byline
  is Ghani, Malatesta, Nordvall Forsberg; the entry and the citation key
  both encode the arXiv preprint's order. Pre-existing, used by seven
  files, deferred to its own branch per one concern per branch.

## What to harvest from the previous spec

Only these. Everything else is superseded.

- The `## References` list and every citation key, including
  `GhaniMalatestaNordvallForsberg2014Agda`, added on this branch.
- The transcription-or-novel table's shape, per
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature when
  transcribing. Its rows need rewriting against the prototype.
- The § Direction list of open questions about codes, which is still
  accurate.

## What remains open

Codes denoting these functors. The morphism side is settled, and it
determines the code-level morphism type: it mirrors `PshHom`, and the
code-level representation theorem is the analogue of
`pshHomEquivNatFamily`. What is not settled: the code type itself, how
`I` and `J` thread through the constructors, what indexes the `δ`
subcode family once the arity is a presheaf, whether every
`PresheafPFunctor` has a code, and what "denotes" means for any
incompleteness claim. Positive inductive-recursive definitions over
`Fam(C)` are not a stage of this work; if wanted they are better
recovered inside the presheaf construction than built separately.

## Two leads to weigh when brainstorming the codes

Neither is established to be needed. Both should be considered during
the brainstorming phase, and if they do not enter the implementation
they are strong candidates for tests, since each exercises a capability
the discrete system provably lacks.

### Varying both sides at once, over the walking arrow

In the endofunctor case of the existing `IR` system (`I = O = D`), the
initial algebra generates a type `A` together with a decoding
`A → D`, but `D` is fixed throughout the iteration: only one of the two
sets varies. `Fam(D)` has `D` as a parameter, so no `IR(D)` code can
move it.

A presheaf on the walking arrow category is exactly a function between
two sets — `PSh(𝟚) ≃ Set^→`, the arrow category. Iterating an
endofunctor there varies both sets and the map between them
simultaneously. That is the minimal witness that presheaf p.r.a.
functors strictly extend the discrete system, and it is the simplest
concrete instance of the observation that presheaf W-types subsume
inductive-inductive definitions: defining two types and a map between
them at once is precisely an inductive-inductive definition, and it is
precisely an initial algebra in `PSh(𝟚)`.

Two things make this immediately usable rather than aspirational. The
degeneracy direction is already understood — discrete `I` and `J`
recover the slice system — so the walking arrow is the first step off
the discrete case, not a leap. And the prototype's `arityVaries` is
already a `PresheafPFunctor (Fin 1) (Fin 2)` with `Fin 2` carrying its
preorder category, which *is* the walking arrow; the fixture for this
test partly exists.

Worth checking during brainstorming: whether the codes should be
developed against the walking arrow first, as the smallest base with a
non-identity morphism, before any general `J`. A worked example there
would exercise `shapeRestr`, `reindex` and `reindexCompat` non-trivially
while staying small enough to compute with by hand.

### Indexed induction-recursion as the route to the code type

Section 6 of [HancockMcBrideGhaniMalatestaAltenkirch2013], "Small
indexed Induction Recursion", generalises `IR` to `IIR`, whose codes are
parameterised by two *families* rather than two types:

```text
data IIR (D : I → Set) (E : J → Set) : Set₁ where
  ι : (je : ΣE)                                            → IIR D E
  σ : (S : Set)          (K : S → IIR D E)                 → IIR D E
  δ : (P : Set) (i : P → I) (K : ((p : P) → D (i p)) → IIR D E) → IIR D E
```

with a translation `⌊·⌋ : IIR D E → IR ΣD ΣE` into the unindexed system,
and Corollary 4 stating that `IIR D E` and `Poly ΣD ΣE` are equivalent.
The paper also gives the direct interpretation
`⟦·⟧IIR : IIR D E → ((i : I) → Set/(D i)) → ((j : J) → Set/(E j))`.

The lead: `D : I → Set` and `E : J → Set` are exactly the object maps of
presheaves over discrete `I` and `J`. So the step from `IIR` to a
presheaf-indexed `IIR` is the same step this repository already took
from `SlicePFunctor` to `PresheafPFunctor` — supply the functorial
actions and use them as restrictions. If that is right, `IIR`'s code
type is the template for the presheaf code type, and its `δ` rule, which
carries an extra `i : P → I` "selecting the index for each position in
`P`", is the template for how the indices thread through — which is
open question 2 of § What remains open.

Three specifics that make the lead look sound rather than merely
suggestive:

- `IIR`'s `ι` takes a point of the *total space* `ΣE`, not a point of
  an index type. The prototype's constant functors have shape type a
  total space too — `iotaConst P`'s shapes are the total space of `P`,
  and `iotaPresheaf j₀`'s are `Σ j', (j' ⟶ j₀)`, the total space of the
  representable. The shapes of the presheaf `ι` are already in the form
  `IIR`'s `ι` argument takes.
- The paper's own size remark, that `(i : I) → Set/(D i) ≅ ΣD → Set ≅
  Set/ΣD`, is the same total-space collapse that makes the translation
  to `IR` work. Whether it survives the presheaf generalisation is a
  question worth asking early: the collapse is available for discrete
  bases, and the analogue for a general base is the equivalence between
  presheaves on `el(P)` and presheaves over `P` — which does hold, but
  needs the category of elements rather than a bare `Σ`.
- `δ`'s extra `i : P → I` is precisely the labelling that the prototype
  found must acquire presheaf structure: a bare set `P` labelled by
  `i : P → I` admits no `directionRestr`, since for `f : i′ ⟶ i` the
  fibre over `i` can be inhabited while the fibre over `i′` is empty.
  So the `IIR` `δ` rule is the discrete shadow of the constructor whose
  presheaf form is already known to be required.

Worth checking during brainstorming: whether the presheaf code type
should be developed as presheaf-`IIR` directly, with the existing `IR`
recovered as the singleton-indexed case, rather than as a separate
generalisation of `IR`. The paper notes that `IR` is the fragment of
`IIR` indexed over a singleton, so that specialisation is already
established on the discrete side.

## Repository hazards learned the hard way

- `lake env lean` is forbidden; use `lake build`. A hook blocks
  redirecting stderr to `/dev/null`.
- `lake lint` reads a stale environment unless `lake build` runs first.
  A green lint immediately after an edit may describe the previous
  state.
- Anonymous `example`s are **not** audited by the axiom linter. Name
  every one. See `TODO.md` § Named examples for axiom auditing.
- `Equiv.eq_symm_apply` depends on `Classical.choice`. Use
  `(e.symm_apply_apply _).symm.trans (congrArg e.symm h)`.
- Writing `⟶` between objects of a functor category draws in
  `Classical.choice` via `CategoryTheory.Functor.category`, before any
  proof. `Type u`'s own category instance is axiom-free.
- Dependent projections block `rw`/`simp` silently, reporting the lemma
  as unused. Generalise the element first
  (`obtain ⟨p, rfl⟩ : ∃ p, e.symm p = x := ⟨_, Equiv.symm_apply_apply _ x⟩`),
  and factor sigma-level actions into non-dependent helpers. Bundling an
  index proof with its element, so laws are equalities of subtype
  elements, also works; make such a bundle `@[reducible]`.
- Homs in `Type u` are `ConcreteCategory`-wrapped: `app`-style fields
  need `↾`, `funext` often becomes tactic-mode `ext`, and `congrFun` on
  a naturality equation fails — use `NatTrans.naturality_apply` or
  `simp only [← ConcreteCategory.comp_apply]; rw [α.naturality f.op]`.
  `FunctorToTypes.naturality` is deprecated.
- `(f ≫ g).unop = g.unop ≫ f.unop`, so law applications go
  outer-factor-first.
- A bad universe ascription on a `⟶` surfaces as
  `failed to synthesize instance of type class Quiver ...`, not as a
  universe error. `example : Category (Iᵒᵖ ⥤ Type uB) := inferInstance`
  succeeding while `⟶` fails is the tell.
- `@[expose]` on a declaration already inside an `@[expose] public
  section` is a hard error.
- `PresheafPFunctor.value_objRestrElt` is `private`; the prototype
  restates it locally. The upstream version should probably drop
  `private`.

## Process notes

Per [AGENTS.md](../../../AGENTS.md) § Adversarial review, the spec goes
through fresh-context adversarial rounds until no blocker and no serious
findings, before the user reviews it. Start a new change before each
round's response commit, or the response folds into the previous round's
commit.

The five rounds run against the previous spec spent most of their value
catching claims asserted without elaboration. With the mathematics now
backed by a compiling, linted file, a reviewer's job should narrow to
whether the prose matches the Lean and whether the organisation is
right. Cite declaration names, so that it can.
