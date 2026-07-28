# Spec: W2 — the `ElementaryTopos` class

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope of this document](#scope-of-this-document)
- [Decisions taken here](#decisions-taken-here)
- [Findings](#findings)
  - [What changed since the pinned findings](#what-changed-since-the-pinned-findings)
  - [A class-typed definition requires `@[instance_reducible]`](#a-class-typed-definition-requires-instance_reducible)
  - [The derived form elaborates](#the-derived-form-elaborates)
  - [The coherence field is `rfl` exactly at `mkOfTerminalΩ₀`](#the-coherence-field-is-rfl-exactly-at-mkofterminal%CF%89%E2%82%80)
  - [[Pare1974] verified against the primary source](#pare1974-verified-against-the-primary-source)
- [The class](#the-class)
- [Derived accessors and instances](#derived-accessors-and-instances)
- [The test module](#the-test-module)
- [Documentation and citations](#documentation-and-citations)
- [Deliverables](#deliverables)
- [Verification](#verification)
- [Out of scope](#out-of-scope)
- [Interaction with the other workstreams](#interaction-with-the-other-workstreams)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope of this document

This is the brainstorming-phase spec for W2 of the workstream group
`TODO.md` § FinSetSkel as an elementary topos. W2 supplies the
`ElementaryTopos` class, its derived accessors and derived `Prop`
instances, the citations, and the module docstring. It adds no part
of `FinSetSkel`: W1 through W5 are ordered by that roadmap, and W2 is
independent of W1.

The umbrella spec that produced the roadmap was added and removed on
branch `docs/finsetskel-topos-roadmap`, `jj` change
`nkwoqxwytsvrlpnsklzzlzkxtovyxkzm`. Its findings were pinned to
mathlib at Lean v4.33.0-rc1. Every finding this spec relies on was
re-verified at the revision current on `main` at the date above, by
elaborating the declarations named; § Findings records what changed.

This document is transient, per `CONTRIBUTING.md` § Concern shape:
the branch removes it in its final commits.

## Decisions taken here

The roadmap leaves three choices to W2. All three are settled below,
and each is settled against an elaborated experiment rather than a
reading of mathlib's sources.

1. **The two `Prop` fields are derived, not carried.** The class has
   seven data fields and one coherence field. `HasFiniteCoproducts`
   (row e), `HasFiniteLimits` (row j) and `HasFiniteColimits` (row k)
   become W2's one-time derived instances.
2. **The coherence mechanism of constraint 6 is an equality field**,
   `classifier_Ω₀ : classifier.Ω₀ = cartesian.tensorUnit`, oriented
   classifier-side to cartesian-side.
3. **The test module carries a witness.** Besides the resolution
   assertions, it instantiates the class at the degenerate topos
   `Discrete PUnit`, so the class is shown inhabitable before W3, W4
   and W5 build against it.

Consequence of decision 1 for the rest of the group, anticipated by
the roadmap: W3's rows e and j and W5's row k become redundant, and
W5 reduces to the `ElementaryTopos FinSetSkel` instance alone. W3 and
W4 need no amendment — the roadmap fixes that they proceed on the
field form regardless, and redundant `Prop` instances are harmless by
proof irrelevance. The operation table's row assignments are
unaffected as statements about which workstream constructs which
operation.

## Findings

### What changed since the pinned findings

| Item | Recorded in the umbrella spec | Current |
| --- | --- | --- |
| `MonoidalClosed` | `CategoryTheory/Monoidal/Closed/Basic.lean:46` | unchanged, still line 46 |
| Classifier module | `Subobject/Classifier/Defs.lean` | unchanged |
| `Cocones.ext` | not recorded | deprecated in favour of `Cocone.ext` |
| `isTerminalTensorUnit` | field of `CartesianMonoidalCategory` | field of `SemiCartesianMonoidalCategory`, which `CartesianMonoidalCategory` extends |

The umbrella spec's module paths are correct as recorded. Two forms
reachable from them have changed: `Cocones.ext` is deprecated, and
deprecation is an error under this repository's build, so the empty-
cocone bridge in § The derived form elaborates uses `Cocone.ext`; and
`isTerminalTensorUnit` is now inherited rather than declared, which
does not change how it is used but does change where it is found.

`CartesianMonoidalCategory C` supplies `HasTerminal C`,
`HasBinaryProducts C` and `HasFiniteProducts C` by instance search,
confirming the roadmap's statement that row f needs nothing beyond
the cartesian field.

### A class-typed definition requires `@[instance_reducible]`

Constraint 5 requires that W2's accessors for the data-carrying
classes be definitions rather than instances. At the current
toolchain a definition whose type is a class is rejected:

> Definition `…` of class type is semireducible. Most type class
> instances should be instance-reducible, so consider marking this
> definition with `@[instance_reducible]`.

This is an error, not a warning. The data accessors therefore carry
`@[instance_reducible]`. This is a constraint on how constraint 5 is
implemented, not a departure from it: the accessors remain
definitions, and the two routes to the data still need not agree
definitionally.

### The derived form elaborates

All three derivations of decision 1 hold with the class's data fields
as their only input, by the lemmas the umbrella spec recorded:

| Derived instance | Lemma | Supplied by |
| --- | --- | --- |
| `HasFiniteCoproducts C` | `hasFiniteCoproducts_of_has_binary_and_initial` | the initial and binary-coproduct fields |
| `HasFiniteLimits C` | `hasFiniteLimits_of_hasEqualizers_and_finite_products` | the cartesian and equalizer fields |
| `HasFiniteColimits C` | `hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts` | `HasFiniteCoproducts` above and the coequalizer field |

The four intermediate `Prop` classes — `HasInitial`,
`HasBinaryCoproducts`, `HasEqualizers`, `HasCoequalizers` — are
obtained from the corresponding fields through `HasLimit.mk` and
`HasColimit.mk` and the three `has…_of_has…_pair` lemmas.

One bridge is not mechanical. The initial field is a `ColimitCocone`
over the empty diagram, while `HasInitial` is reached through
`IsInitial.hasInitial`, whose argument is an `IsColimit` for the
cocone `asEmptyCocone`. The two cocones agree on their point and have
no components elsewhere, so the bridge is
`IsColimit.ofIsoColimit … (Cocone.ext (Iso.refl _) …)`.

### The coherence field is `rfl` exactly at `mkOfTerminalΩ₀`

Two facts fix the shape of decision 2, and the second is a
construction obligation on every instance of the class.

- A classifier built by
  `Subobject.Classifier.mkOfTerminalΩ₀ (𝟙_ C) isTerminalTensorUnit …`
  satisfies `.Ω₀ = 𝟙_ C` by `rfl`. That constructor is the one the
  roadmap already assigns to row l, so constraint 6's obligation
  costs W3 nothing.
- An arbitrary `Subobject.Classifier C` does not satisfy it. mathlib
  derives `Subobject.Classifier.isTerminalΩ₀`, so an arbitrary
  classifier's `Ω₀` is canonically isomorphic to the cartesian unit,
  but the two are not equal. The class is therefore not constructible
  from a classifier obtained some other way without first
  transporting it.

The alternative of carrying no coherence field was considered and
rejected. It would leave every statement mixing the classifier with
the cartesian structure carrying a transport along that canonical
isomorphism, where the roadmap's intent — and W3's construction — is
that the two terminals are one object. Constraint 6 stands as the
roadmap states it.

### [Pare1974] verified against the primary source

W2's standing obligation is discharged. The article was read in
facsimile at Project Euclid, which carries the *Bulletin* as open
access; the publisher's own pages returned the same access denial
recorded when the roadmap entry was written.

| Claim under obligation | Verdict |
| --- | --- |
| The `docs/references.bib` record | Confirmed as printed: volume 80, number 3, May 1974, pages 556–561, "Colimits in Topoi", by Robert Paré |
| Proof route is monadicity of the power-object functor | Confirmed. The paper's theorem is that `Ω^(-) : Eᵒᵖ ⟶ E` satisfies the hypotheses of the reflexive tripleableness theorem and is therefore tripleable |
| Priority of C. J. Mikkelsen | Confirmed, and stronger than the roadmap records |

The paper describes itself as giving a new proof of Mikkelsen's
theorem, which states that an elementary topos has all finite
colimits, and cites for it C. J. Mikkelsen, *Finite colimits in
toposes*, a talk at the category theory conference at Oberwolfach in
July 1972. It further records that Lambek and Rattray obtained the
theorem independently by a different approach.

The roadmap's sentence in `TODO.md` § Class fields — that
[Pare1974] "having first published" the result — is therefore
inaccurate and is corrected by this workstream. The result is
Mikkelsen's theorem; [Pare1974] is a published proof of it by
tripleability. This spec makes no claim about which proof appeared in
print first, the paper not settling that.

Two further statements in the paper bear on the class's design and
are recorded in the module docstring.

- The paper's own axiomatisation of an elementary topos is cartesian
  closed together with a subobject classifier, with finite limits
  *and* finite colimits both derived. Every generator this class
  carries as data is therefore a computational strengthening of the
  definition, not a mathematical necessity — which is the roadmap's
  stated rationale, now supported by the source rather than assumed.
- The route by which the colimits are derived passes through the
  power object, confirming the roadmap's complexity remark that a
  derived coequalizer routes through `P (Fin m) = Fin (2 ^ m)`,
  exponential in `m` where W4's union-find is near-linear.

## The class

Stated over `(C : Type u) [Category.{v} C]`, per constraint 3.

```lean
class ElementaryTopos (C : Type u) [Category.{v} C] where
  cartesian : CartesianMonoidalCategory C
  closed : @MonoidalClosed C _ cartesian.toMonoidalCategory
  initialCocone : ColimitCocone (Functor.empty.{0} C)
  binaryCoproductCocone : ∀ X Y : C, ColimitCocone (pair X Y)
  equalizerCone : ∀ {X Y : C} (f g : X ⟶ Y), LimitCone (parallelPair f g)
  coequalizerCocone : ∀ {X Y : C} (f g : X ⟶ Y), ColimitCocone (parallelPair f g)
  classifier : Subobject.Classifier C
  classifier_Ω₀ : classifier.Ω₀ = cartesian.tensorUnit
```

Every field type is a mathlib type, per constraint 2, so W3 and W4
produce them without importing W2. The closed field is typed relative
to the cartesian field, carrying that dependency in its own type;
the classifier's dependency on the cartesian terminal is carried by
the coherence field, for the reason recorded in § Findings.

Terminal and binary products are reached through the cartesian field
only, so the class carries one terminal object rather than two.

## Derived accessors and instances

Per constraint 5: definitions for the data-carrying classes,
instances for the `Prop` classes.

| Name | Kind | Type |
| --- | --- | --- |
| `cartesianMonoidalCategory` | `def`, `@[instance_reducible]` | `CartesianMonoidalCategory C` |
| `monoidalClosed` | `def`, `@[instance_reducible]` | `MonoidalClosed C` |
| `isInitial` | `def` | `IsInitial initialCocone.cocone.pt` |
| — | `instance` | `HasInitial C` |
| — | `instance` | `HasBinaryCoproducts C` |
| — | `instance` | `HasEqualizers C` |
| — | `instance` | `HasCoequalizers C` |
| — | `instance` | `HasFiniteCoproducts C` (row e) |
| — | `instance` | `HasFiniteLimits C` (row j) |
| — | `instance` | `HasFiniteColimits C` (row k) |

## The test module

`GebTests/Mathlib/CategoryTheory/ElementaryTopos.lean` has two parts.

The witness instantiates the class at `Discrete PUnit`, the
one-object one-morphism category, which is a degenerate elementary
topos. Its construction rests on `Unique (X ⟶ Y)` for every pair of
objects, from which every cone is a limit cone and every cocone a
colimit cone; the cartesian structure is then
`CartesianMonoidalCategory.ofChosenFiniteProducts`, the closure is a
trivial adjunction, and the classifier is `mkOfTerminalΩ₀` at the
tensor unit, whose coherence obligation is discharged by `rfl`. It
tests what W2 alone can be wrong about ahead of W5: that the class is
inhabitable, and that its fields can be met together.

The resolution assertions then confirm, through that instance, that
each of the seven `Prop` classes of § Derived accessors and instances
is found by `inferInstance`.

Neither part depends on `FinSetSkel`. `Discrete PUnit` is not
proposed as a fixture for later workstreams; it exists to exercise
this class.

## Documentation and citations

- Module docstring: constraint 3 (why `Category.{v} C` rather than
  `SmallCategory C`), constraint 5's accessor rule, the rationale for
  carrying the generators as data and deriving the finite (co)limit
  `Prop`s, and a `## References` section.
- `docs/references.bib` gains an entry for the Mikkelsen talk.
  [MacLaneMoerdijk1992] and [Pare1974] are already present, and the
  bibliographic record of the latter is confirmed as printed.
- Cited from the Lean sources: [MacLaneMoerdijk1992] for the
  definition transcribed, [Mikkelsen1972] for the finite-colimits
  theorem, and [Pare1974] for its proof by tripleability of the
  power-object functor.
- `TODO.md` § Class fields: the attribution sentence corrected per
  § Findings; the § Status row for W2; and the § Class fields
  paragraph recording that W2 took the derived-instance route, so
  that W3, W4 and W5 read an accurate roadmap.
- `docs/index.md`: the module entry.

The Mikkelsen entry cites an unpublished 1972 conference talk, which
has no searchable identifier of the kind `CONTRIBUTING.md` § Cite the
literature when transcribing requires. It is recorded with the
bibliographic detail [Pare1974] gives for it, and [Pare1974] — which
does carry a DOI — is cited alongside it wherever it appears, so the
attribution is traceable to a source that is retrievable.

## Deliverables

1. `Geb/Mathlib/CategoryTheory/ElementaryTopos.lean`.
2. `GebTests/Mathlib/CategoryTheory/ElementaryTopos.lean`.
3. Both added to `Geb/Mathlib/CategoryTheory.lean` and
   `GebTests/Mathlib/CategoryTheory.lean` respectively.
4. Both appended to `GebMeta.classicalAllowedModules`. W2 is a
   wrapper throughout, per constraint 8, having no choice-free
   counterpart beneath it.
5. `docs/references.bib`, `docs/index.md` and `TODO.md` as above.

## Verification

- `lake build` and the test target clean.
- `lake lint` clean, which runs the axiom linter: every declaration
  in the two modules depends on no axiom outside the standard set
  together with `Classical.choice`, both modules being allowlisted.
- `scripts/lint-imports.sh` clean. W2 imports only `Mathlib.*`, which
  the `Geb/Mathlib/` allow-list already admits; it needs nothing from
  the `Batteries.` admission W0 made.
- `markdownlint-cli2` and the `doctoc` check clean for the Markdown
  touched.
- No `noncomputable` and no `sorry` in either module.

The class, the accessors, the derived instances, the witness and the
resolution assertions have each been elaborated at the current
revision, as a single unit, with no error and no `sorry`. That was
done in standalone snippets; the repository uses Lean's module system
(`module`, `public import`), which the snippets did not exercise, so
the plan re-verifies inside the actual modules rather than inheriting
that result.

## Out of scope

- The `ElementaryTopos FinSetSkel` instance, and any operation-table
  row. Those are W3, W4 and W5.
- Any alternative constructor taking finite limits, exponentials and
  a classifier and building the colimits by the [Pare1974] route. The
  roadmap records that the redundancy forecloses nothing and such a
  constructor may be added later; W2 does not add it.
- Any transport of the class along an equivalence of categories.

## Interaction with the other workstreams

W2 is independent of W1 and touches no file W1 touches except
`GebMeta.classicalAllowedModules`, `TODO.md` and `docs/index.md` —
the three the roadmap's § Standing obligations already identifies as
concurrent-append points for the W1/W2 pair. These are textual
conflicts, resolved by rebasing whichever sibling merges second.

W2 introduces no `simp` lemma, so the caution about W3's and W4's
carrier-level normal forms does not apply to it.

## References

- `TODO.md` § FinSetSkel as an elementary topos — the authoritative
  roadmap.
- The umbrella spec, `jj` change
  `nkwoqxwytsvrlpnsklzzlzkxtovyxkzm` on branch
  `docs/finsetskel-topos-roadmap`.
- [CONTRIBUTING.md](CONTRIBUTING.md), [AGENTS.md](AGENTS.md),
  [docs/process.md](docs/process.md).
- Robert Paré, "Colimits in Topoi", *Bulletin of the American
  Mathematical Society* 80(3), 556–561, May 1974,
  <https://doi.org/10.1090/S0002-9904-1974-13497-X>; read in
  facsimile at
  <https://projecteuclid.org/journals/bulletin-of-the-american-mathematical-society/volume-80/issue-3/Colimits-in-Topoi/bams/1183535542.full>.
