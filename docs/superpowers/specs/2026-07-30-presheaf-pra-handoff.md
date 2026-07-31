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
