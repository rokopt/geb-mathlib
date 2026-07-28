# Spec: W2 — the `ElementaryTopos` class

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope of this document](#scope-of-this-document)
- [Decisions taken here](#decisions-taken-here)
- [Transcription or novel](#transcription-or-novel)
- [Findings](#findings)
  - [Findings the umbrella spec does not cover](#findings-the-umbrella-spec-does-not-cover)
  - [A class-typed definition warns, and warnings are errors here](#a-class-typed-definition-warns-and-warnings-are-errors-here)
  - [The derived form elaborates](#the-derived-form-elaborates)
  - [The two terminals need no coherence field](#the-two-terminals-need-no-coherence-field)
  - [The literature, verified against the primary sources](#the-literature-verified-against-the-primary-sources)
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
instances, the citations, and the module docstring. It adds no part of
`FinSetSkel`: W1 through W5 are ordered by that roadmap, and W2 is
independent of W1.

The umbrella spec that produced the roadmap was added and removed on
branch `docs/finsetskel-topos-roadmap`, `jj` change
`nkwoqxwytsvrlpnsklzzlzkxtovyxkzm`. Its findings were pinned to mathlib
at Lean v4.33.0-rc1. Every finding this spec relies on was re-verified
on 28 July 2026, at the revision then current on `main`, by elaborating
the declarations named, through the `lean-lsp` MCP; § Findings the
umbrella spec does not cover records the additions.

This document is transient, per `CONTRIBUTING.md` § Concern shape: the
branch removes it in its final commits.

## Decisions taken here

The roadmap leaves two choices to W2, and W2 adds a third. The first two
are settled against an elaborated experiment rather than a reading of
mathlib's sources; the third is a judgement about what W2 can establish
before W5.

1. **The two `Prop` fields are derived, not carried.** The class has
   seven data fields and no others. `HasFiniteCoproducts`
   (row e), `HasFiniteLimits` (row j) and `HasFiniteColimits` (row k)
   become W2's one-time derived instances.
2. **Constraint 6 is amended: the class carries no coherence field.**
   The classifier's `Ω₀` and the cartesian unit are both terminal and
   so canonically and uniquely isomorphic; W2 exports that
   isomorphism as `tensorUnitIsoΩ₀` instead of equating the objects.
   No composite of it is exported: a consumer wanting the truth map
   over the cartesian unit writes `tensorUnitIsoΩ₀.hom ≫
   classifier.truth`, which needs no lemma of W2's to normalise.
3. **The test module carries a witness.** Besides the resolution
   assertions, it instantiates the class at the degenerate topos
   `Discrete PUnit`, so the class is shown inhabitable before W3, W4
   and W5 build against it.

Decision 1 is what `TODO.md` § Class fields offers W2, and its
consequence is what that paragraph states: rows e, j and k become W2's
one-time derivations, and W3 and W5 proceed on the field form
regardless, their rows e, j and k becoming redundant `Prop` instances,
harmless by proof irrelevance. W2 removes no obligation from any other
workstream and requires no amendment to the operation table, to the §
Workstreams bullets, or to W5's duty to remove the roadmap entry on
completion. W5 is assigned row k whichever route W2 takes.

The sentence licensing this in `TODO.md` § Class fields — rows e, j and
k "become W2's one-time derivations and leave W3's and W5's assignments"
— admits reading "leave" as either vacating or leaving alone. Leaving
alone is the reading taken, on two grounds internal to the roadmap: the
clause that redundant `Prop` instances are harmless by proof irrelevance
presupposes W3 and W5 still register them; and the § Workstreams bullet
assigns W5 row k unconditionally on W2's choice. The same paragraph
settles it outright: "W3 and W5 proceed on it regardless of W2's
eventual choice". W2's amendment to that section disambiguates the
sentence rather than leaving the next reader to re-derive it.

Decision 1 departs from constraint 1 ("Data for generators, `Prop` for
finite (co)limits") only in the way `TODO.md` § Class fields licenses:
the finite (co)limits remain `Prop`, and cease only to be fields.
Constraints 4 and 7 bind W1 and are not W2's.

## Transcription or novel

Required by `CONTRIBUTING.md` § Cite the literature when transcribing,
which obliges each workstream's brainstorming-phase spec to mark each
definition.

| Declaration | Status |
| --- | --- |
| `ElementaryTopos` | Transcription of the colimits-inclusive axiomatisation — finite limits, finite colimits, cartesian closure, subobject classifier — strengthened computationally, the generators being carried as data rather than asserted. [Pare1974] page 556 attributes that axiomatisation to [Freyd1972] and to Kock and Wraith, taking the colimits-free form itself |
| `cartesianMonoidalCategory`, `monoidalClosed`, `isInitial`, `tensorUnitIsoΩ₀` | Neither. Projections of the fields, or derived from them by terminality |
| The derived `Prop` instances | Neither. Consequences of the fields, by mathlib lemmas |
| The `Discrete PUnit` witness | Neither, and no originality is claimed. The degenerate topos is a standard example; W2 neither transcribes a statement of it nor rests on a published one, the witness proving the topos structure directly from `Unique (X ⟶ Y)` |

The redundancy of the finite colimits is literary context rather than a
transcription: W2 derives `HasFiniteColimits` from the initial object,
binary coproducts and coequalizers by mathlib lemmas, not by the theorem
of [Mikkelsen1976] or the proof of [Pare1974]. Those works are cited to
record why the redundancy is not an accident, not as the source of a
transcribed theorem.

## Findings

### Findings the umbrella spec does not cover

The mathlib pin is unchanged. `lake-manifest.json` records
`79d0395a1825a6264ad5d269e35e60537518955e`, tagged `v4.33.0-rc1`, both
on `main` today and at the umbrella spec's change, so no declaration
moved between the two documents. Re-verification confirmed what that
spec records and added two items it does not.

| Item | Umbrella spec | This spec |
| --- | --- | --- |
| `MonoidalClosed` | `CategoryTheory/Monoidal/Closed/Basic.lean:46` | confirmed, still line 46 |
| Classifier module | `Subobject/Classifier/Defs.lean` | confirmed |
| `Cocones.ext` | not recorded | deprecated in favour of `Cocone.ext` |
| `isTerminalTensorUnit` | not recorded | declared in `SemiCartesianMonoidalCategory`, which `CartesianMonoidalCategory` extends |

Both additions bear on the module. `Cocones.ext` is deprecated at this
pin, and `lakefile.toml` sets `weak.warningAsError = true`, so its use
is an error here rather than a warning; § The derived form elaborates
uses `Cocone.ext`. And `isTerminalTensorUnit` is unreachable under the
bare name and under `CategoryTheory.isTerminalTensorUnit`; the reachable
forms are `SemiCartesianMonoidalCategory.isTerminalTensorUnit` and
`CartesianMonoidalCategory.isTerminalTensorUnit`, the latter by an
explicit `export` inside the `CartesianMonoidalCategory` namespace
rather than by parent projection. This spec uses the latter.

`CartesianMonoidalCategory C` supplies `HasTerminal C`,
`HasBinaryProducts C` and `HasFiniteProducts C` by instance search,
confirming the roadmap's statement that row f needs nothing beyond the
cartesian field.

### A class-typed definition warns, and warnings are errors here

Constraint 5 requires that W2's accessors for the data-carrying classes
be definitions rather than instances. A definition whose type is a class
draws:

> Definition `…` of class type is semireducible. Most type class
> instances should be instance-reducible, so consider marking this
> definition with `@[instance_reducible]`. If it is intentionally
> semireducible, this warning can be disabled with
> `set_option warn.classDefReducibility false`.

This is a warning at the toolchain, promoted to an error by this
repository's `weak.warningAsError = true`. Two remedies exist:
`@[instance_reducible]` on the accessor, or `set_option
warn.classDefReducibility false`. W2 takes the first, which is what the
message recommends and what keeps the accessors instance-reducible for
downstream elaboration. This is a constraint on how constraint 5 is
implemented, not a departure from it: the accessors remain definitions,
and the two routes to the data still need not agree definitionally.

### The derived form elaborates

All three derivations of decision 1 hold with the class's data fields as
their only input, by the lemmas the umbrella spec recorded:

| Derived instance | Lemma | Supplied by |
| --- | --- | --- |
| `HasFiniteCoproducts C` | `hasFiniteCoproducts_of_has_binary_and_initial` | the initial and binary-coproduct fields |
| `HasFiniteLimits C` | `hasFiniteLimits_of_hasEqualizers_and_finite_products` | the cartesian and equalizer fields |
| `HasFiniteColimits C` | `hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts` | `HasFiniteCoproducts` above and the coequalizer field |

`HasBinaryCoproducts`, `HasEqualizers` and `HasCoequalizers` are not
fields, and the lemmas that supply them —
`hasBinaryCoproducts_of_hasColimit_pair`,
`hasEqualizers_of_hasLimit_parallelPair` and
`hasCoequalizers_of_hasColimit_parallelPair` — take the per-diagram
limit and colimit classes as instance arguments. The module therefore
declares three further instances by `HasLimit.mk` and `HasColimit.mk`
over the corresponding fields, for `HasColimit (pair X Y)`, `HasLimit
(parallelPair f g)` and `HasColimit (parallelPair f g)`. They are named
rather than left anonymous, so that a diagnostic or a later
declaration can refer to them; nothing downstream is obliged to, every
one of them being a `Prop` and so interchangeable with any other route
to the same class by proof irrelevance. They are listed with the
accessors below. From them,
`hasBinaryCoproducts_of_hasColimit_pair`,
`hasEqualizers_of_hasLimit_parallelPair` and
`hasCoequalizers_of_hasColimit_parallelPair` give the three
corresponding `Prop` classes; `HasInitial` is separate, below.

`Functor.empty.{0} C` pins the universe deliberately, against the
guidance in `docs/rules/lean-coding.md` to keep universes as polymorphic
as compiles. `HasInitial C` unfolds to `HasColimitsOfShape (Discrete
PEmpty.{1}) C`, and `IsInitial` is `IsColimit (asEmptyCocone _)` at the
same level, so any other level breaks the connection below. The module
docstring records this so it is not later generalised.

That connection is the one step in the module that is not mechanical.
The initial field is a `ColimitCocone` over the empty diagram, while
`HasInitial` is reached through `IsInitial.hasInitial`, whose argument
is an `IsColimit` for the cocone `asEmptyCocone`. The two cocones agree
on their point and have no components elsewhere, so
`IsColimit.ofIsoColimit … (Cocone.ext (Iso.refl _))` converts one to the
other, its remaining obligation discharged by the autoParam.

### The two terminals need no coherence field

Constraint 6 has the class enforce that the classifier field's `Ω₀` is
the cartesian field's terminal object. The premise behind that — the
umbrella spec's concern that a general `[ElementaryTopos C]` "may carry
two unrelated terminals and the classifier's universal property would
not compose with the cartesian structure" — does not hold, and decision
2 amends the constraint accordingly.

- The two objects are never unrelated. mathlib derives
  `Subobject.Classifier.isTerminalΩ₀`, and `CartesianMonoidalCategory`
  carries `isTerminalTensorUnit`, so both are terminal and therefore
  canonically isomorphic. W2 exports the isomorphism as
  `tensorUnitIsoΩ₀` by `IsTerminal.uniqueUpToIso`.
- The isomorphism is unique, in both directions, by `hom_ext` at either
  terminal. So no coherence condition arises: every diagram involving
  the comparison map commutes by terminality alone, with nothing to
  state and nothing to check.

An equality field was drafted first and rejected on two grounds.

It asserts an equality of objects, which is not invariant under
equivalence. mathlib does state such equalities where the
identification is itself the subject — `CategoryTheory.Skeletal` and
`CategoryTheory.Bicategory.Strict` both do — but not in the classes
involved here, whose idiom is to bundle an object and assert a
property of it (`isTerminalTensorUnit : IsTerminal (𝟙_ C)`).
The identification is not the subject of an elementary topos, and
`Geb/Mathlib/` is upstream-eligible under `CONTRIBUTING.md`
§ Floodgate test.

And it constrains every instance for a benefit no consumer yet needs:
an arbitrary `Subobject.Classifier C` does not satisfy the equality —
the `rfl` fails with a type mismatch — so an instance whose natural
classifier construction yields an `Ω₀` isomorphic but not equal to the
cartesian unit would have to rebuild the classifier through
`mkOfTerminalΩ₀` before it could be given at all. The rebuild is
mechanical, the pullback squares transporting along the unique
comparison, but it is a cost carried by every future instance to make
definitional a statement that terminality already supplies.

Nothing is lost at `FinSetSkel`. W3 builds row l through
`mkOfTerminalΩ₀` at its own terminal, as the operation table already
assigns, so `Ω₀` and the cartesian unit remain the same object there;
the class does not require it. `tensorUnitIsoΩ₀` is then a map between
one object and itself, equal to the identity by terminality.

### The literature, verified against the primary sources

W2's standing obligation is discharged. [Pare1974] was read in
facsimile; the article is open access and is served both by the
publisher and by Project Euclid, though which of the two answers a given
request has varied, so neither is recorded here as the source.
[Mikkelsen1976] was read at the Theory and Applications of Categories
reprint series.

| Claim under obligation | Verdict |
| --- | --- |
| The [Pare1974] bibliographic record | Author, title, volume 80, number 3, May 1974 and pages 556–561 confirmed against the scan. The DOI is not printed on the article and was confirmed separately against the Crossref record, which is also where the title's letter case was checked; `references.bib` records the title in sentence case, a BibTeX convention, where the article prints it in full caps |
| Proof route is monadicity of the power-object functor | Confirmed. The paper's main theorem is that `Ω^(-) : Eᵒᵖ ⥤ E` satisfies the hypotheses of what it calls the RTT, a modification of the Barr-Beck crude tripleableness theorem, and is therefore tripleable |
| Priority of C. J. Mikkelsen | Confirmed as to discovery, and refined |
| The source of the transcribed axiomatisation | [Pare1974] page 556 names [Freyd1972] and Kock and Wraith as assuming finite limits and colimits. [Freyd1972] confirms it directly: its section 1 defines a cartesian closed category as a finitely bicomplete one, and its section 2 adds the classifier |

The paper describes itself as giving a new proof of Mikkelsen's theorem,
which states that an elementary topos has all finite colimits, and cites
for it a talk at the category theory conference at Oberwolfach in July
1972. [Mikkelsen1976] states that theorem as its Theorem 2.3; the
author's note written for the 2022 reprint dates the talk to 23–29
July 1972.

The roadmap's sentence in `TODO.md` § Class fields — that [Pare1974]
first published the result — is amended to what the sources support,
which is less. They establish that Mikkelsen discovered the theorem and
that [Pare1974] appeared before [Mikkelsen1976]: the thesis was
published in March 1976 and its bibliography cites [Pare1974] as a 1973
Dalhousie preprint. They do not establish that no earlier publication
exists, which is what "first published" asserts; [Pare1974] positions
itself as a new proof of an existing theorem and claims no priority in
print. The amended sentence records the theorem as Mikkelsen's,
discovered and presented in July 1972, with [Pare1974] giving a
published proof by tripleability of the power-object functor.
Mikkelsen's discovery priority is what the roadmap's standing obligation
anticipated as "the reported priority of C. J. Mikkelsen", now verified
against both primary sources.

Two statements about the paper are recorded here so that the module
docstring does not repeat a misreading of them. Both stand on page 558, before the
tripleability theorem, while the finite-colimits statement they might be
taken to qualify is on page 559, after that theorem's proof. Reading
them as qualifications of the finite-colimits theorem gets the
attribution wrong. The paper's sentences "Lambek and Rattray [5] have
also obtained this theorem … but their approach is different" and
"Certain parts of this theorem were already known to Mikkelsen" both
refer to the tripleability theorem, that being "the main theorem of the
paper" as the same passage names it — not to the finite-colimits
theorem. [Pare1974] itself does not use the word "independently".

[Mikkelsen1976] supplies the detail behind the second sentence, and
settles the relation between the two proofs of the tripleability
theorem in its author's own words: "The proof of the tripleability
theorem which we are now going to establish does not differ essential
from that which was discovered independently by R. Paré, [22]". The
tripleability theorem was therefore discovered twice over, and the
later of the two sources says so. The chronology around it comes from
the author's note written for the 2022 reprint rather than from the
1976 text: Mikkelsen was asked in December 1972 whether
`P : Eᵒᵖ ⥤ E` was tripleable, dates his own proof to January 1973 and
presented it at Oberwolfach on 28 July 1973, whereas [Pare1974] was
communicated to the Bulletin on 22 September 1973. None of this bears
on the finite-colimits theorem, which is Mikkelsen's alone.

Two further statements in [Pare1974] bear on the class's design and are
recorded in the module docstring.

- The axiomatisation the paper adopts, from its reference [6], is
  cartesian closed together with a subobject classifier, with finite
  limits and finite colimits both derived, the paper noting that two of its
  references assume them "but we do not make that assumption here".
  Every generator this class carries as data is therefore a
  computational strengthening of the definition rather than a
  mathematical necessity, which is the roadmap's stated rationale,
  now supported by the source rather than assumed.
- The derivation passes through the power object. This is the source
  of the complexity remark in the removed umbrella spec — that a
  derived coequalizer routes through `P (Fin m) = Fin (2 ^ m)`,
  exponential in `m` where W4's union-find is near-linear. That
  remark is the umbrella spec's, not the roadmap's; the roadmap says
  only that a derived construction is whichever one the general proof
  yields, and that is not union-find.

## The class

Stated over `(C : Type u) [Category.{v} C]`, per constraint 3. Field
docstrings are elided here and are mandatory in the source, per
`docs/rules/lean-coding.md` § Comment and docstring rules.

```lean
class ElementaryTopos (C : Type u) [Category.{v} C] where
  cartesian : CartesianMonoidalCategory C
  closed : @MonoidalClosed C _ cartesian.toMonoidalCategory
  initialCocone : ColimitCocone (Functor.empty.{0} C)
  binaryCoproductCocone : ∀ X Y : C, ColimitCocone (pair X Y)
  equalizerCone : ∀ {X Y : C} (f g : X ⟶ Y), LimitCone (parallelPair f g)
  coequalizerCocone : ∀ {X Y : C} (f g : X ⟶ Y), ColimitCocone (parallelPair f g)
  classifier : Subobject.Classifier C
```

Every field is a mathlib type, per constraint 2, so W3 and W4 produce
them all without importing W2, and the class adds no field of its own —
constraint 2's separate admission for a coherence field goes unused.
The closed field is typed relative to the cartesian field, carrying
that dependency in its own type; the classifier needs no such
dependency, for the reason recorded in § The two terminals need no
coherence field.

Terminal and binary products are reached through the cartesian field
only, so the class carries one terminal object rather than two.

## Derived accessors and instances

Per constraint 5: definitions for the data-carrying classes, instances
for the `Prop` classes.

| Name | Kind | Type |
| --- | --- | --- |
| `cartesianMonoidalCategory` | `def`, `@[instance_reducible]` | `CartesianMonoidalCategory C` |
| `monoidalClosed` | `def`, `@[instance_reducible]` | `MonoidalClosed C` |
| `isInitial` | `def` | `IsInitial initialCocone.cocone.pt` |
| `tensorUnitIsoΩ₀` | `def` | `𝟙_ C ≅ classifier.Ω₀` |
| `hasColimit_pair` | `instance` | `HasColimit (pair X Y)` |
| `hasLimit_parallelPair` | `instance` | `HasLimit (parallelPair f g)` |
| `hasColimit_parallelPair` | `instance` | `HasColimit (parallelPair f g)` |
| — | `instance` | `HasInitial C` |
| — | `instance` | `HasBinaryCoproducts C` |
| — | `instance` | `HasEqualizers C` |
| — | `instance` | `HasCoequalizers C` |
| — | `instance` | `HasFiniteCoproducts C` (row e) |
| — | `instance` | `HasFiniteLimits C` (row j) |
| — | `instance` | `HasFiniteColimits C` (row k) |

Constraint 5 has a consequence for the ordering within the module.
Because `cartesianMonoidalCategory` is a definition and not an instance,
no `MonoidalCategory C` is in scope, and the type `MonoidalClosed C`
does not elaborate: the elaborator reports `failed to synthesize
instance of type class MonoidalCategory C`. The module therefore
declares `cartesianMonoidalCategory` first and marks it `attribute
[local instance]`, in force for the rest of the module. Three
declarations need it: `monoidalClosed`, for the reason above;
`tensorUnitIsoΩ₀`, whose type mentions `𝟙_ C` and which without it
fails to synthesize `MonoidalCategoryStruct C`; and `HasFiniteLimits`,
which without it fails to synthesize `HasFiniteProducts C`. The other
ten declarations of the table elaborate with no cartesian instance in
scope; the attribute is left in force throughout rather than scoped to
three, so that a later addition inherits it.
The alternative, spelling `monoidalClosed` at `@MonoidalClosed C _
(cartesianMonoidalCategory C).toMonoidalCategory`, also elaborates and
is not taken, the local attribute serving every later declaration rather
than one.

The same consequence applies to consumers: a downstream module holding
only `[ElementaryTopos C]` has no `CartesianMonoidalCategory C` in scope
until it applies the same local attribute. The module docstring records
this alongside constraint 5's accessor rule, since W3, W4 and W5 all
meet it.

## The test module

`GebTests/Mathlib/CategoryTheory/ElementaryTopos.lean` has two parts.

The witness instantiates the class at `Discrete PUnit`, the one-object
one-morphism category, which is the degenerate topos. That it is an
elementary topos is standard, and W2 claims no originality for it; the
witness also does not rest on the claim, proving the structure
directly. The construction rests on `Unique (X ⟶ Y)` for every pair of
objects. That
instance is not in mathlib and the module supplies it, in one line over
the `Subsingleton (X ⟶ Y)` that mathlib does provide. From it, every
cone is a limit cone and every cocone a colimit cone; the cartesian
structure is `CartesianMonoidalCategory.ofChosenFiniteProducts`, the
closure is an adjunction whose hom-equivalence is `Equiv.ofUnique`, and
the classifier is `mkOfTerminalΩ₀` at the tensor unit. The witness
declares its cartesian
and closed structures as instances rather than as definitions, so
§ A class-typed definition warns, and warnings are errors here does
not reach it; a definition form would need the same
`@[instance_reducible]`. The closed field is written at
the explicit type `@MonoidalClosed _ _ cartesian.toMonoidalCategory`
rather than `MonoidalClosed _`: no competing `MonoidalCategory (Discrete
PUnit)` instance is reachable under this module's imports — checked, and
`Discrete.monoidal` needs a `Monoid PUnit` that they do not bring — but
the explicit form costs nothing and does not depend on that remaining
true.

The resolution assertions then confirm, with that instance in scope,
that each of the seven whole-category `Prop` classes of § Derived
accessors and instances is found by `inferInstance`. The three
per-diagram instances take implicit arguments and are exercised
through those seven rather than asserted directly.

The witness is comparable in size to the module it tests, and it
establishes what nothing else in W2 can: that the seven fields can be
satisfied together. The cheaper alternative, resolution assertions under
a hypothetical `variable [ElementaryTopos C]`, cannot detect an
over-constrained class, and the two places over-constraint could arise
undetected are the closed field's dependent typing and the mutual
satisfiability of the seven fields at one category. Neither is settled
by reading the roadmap, which fixes the field types but not that any
category meets them all at once. Without the witness the
first instance of the class is W5's, at the end of the group, after W3
and W4 have built against it.

One constraint interaction follows, and is noted rather than left
implicit. Constraint 8 makes W2 "a wrapper throughout"; the witness is
the one part of W2 that is not packaging, and it is a test module,
which `TODO.md` § Standing
obligations already requires to be allowlisted alongside its wrapper.

Neither part depends on `FinSetSkel`. `Discrete PUnit` is not proposed
as a fixture for later workstreams; it exists to exercise this class.

## Documentation and citations

- Module docstring: constraint 3 (why `Category.{v} C` rather than
  `SmallCategory C`), constraint 5's accessor rule together with the
  local-instance consequence for consumers, the deliberate universe
  pinning of the empty diagram, the rationale for carrying the
  generators as data and deriving the finite (co)limit `Prop`s. Its
  sections are those `docs/rules/lean-coding.md` § Documentation makes
  mandatory where non-vacuous: `# Title` and summary,
  `## Main definitions`, `## Implementation notes` for the rationale
  above, `## References`, and `## Tags`.
- `docs/references.bib` gains [Mikkelsen1976], the licentiate thesis,
  keyed to the original 1976 Aarhus publication with the 2022
  Theory and Applications of Categories reprint recorded as the
  retrievable form. It is cited in preference to the 1972 talk, which
  has no searchable identifier of the kind `CONTRIBUTING.md` § Cite
  the literature when transcribing requires; the thesis states the
  theorem and dates the talk, so nothing is lost. It also gains
  [Freyd1972], the source [Pare1974] names for the colimits-inclusive
  axiomatisation this class transcribes. [Pare1974] is already
  present.
- Cited from the Lean sources: [Freyd1972] for the definition
  transcribed, and [Mikkelsen1976] with [Pare1974] as context for the
  redundancy of the finite colimits, per § Transcription or novel.
  [MacLaneMoerdijk1992] is not cited: an earlier draft named it as the
  source of the definition, and its own prologue gives the
  colimits-free form, finite limits with exponentials and power
  objects, constructing the colimits later.
- `TODO.md` § Class fields: the attribution sentence loses "first
  published", which the sources do not support, and records instead
  that the theorem is Mikkelsen's, discovered and presented in July
  1972, with [Pare1974] giving a published proof by tripleability of
  the power-object functor. This is a replacement, not an addition;
  see § The literature, verified against the primary sources. Also
  the § Status row for W2, the disambiguation of the "leave W3's and
  W5's assignments" sentence per § Decisions taken here, and a note
  that W2 took the derived-instance route, so that W3, W4 and W5 read
  an accurate roadmap; the note names the § Class fields table's
  finite-limits and finite-colimits rows, which a reader of that table
  alone would otherwise count as fields the class carries. Also
  § Standing obligations, whose last bullet records the [Pare1974]
  attribution as unverifiable and assigns the
  verification to W2; it is struck, the obligation being discharged
  in § The literature, verified against the primary sources.
- `TODO.md` § Class fields, classifier row: it reads
  "`Subobject.Classifier C`, with `Ω₀` the cartesian terminal", which
  states the enforcement the class no longer carries. The qualifier is
  struck, leaving the field type.
- `TODO.md` § Cross-workstream interface constraints: constraint 6 is
  amended per decision 2. It ceases to require enforcement and becomes
  a note that the classifier's `Ω₀` and the cartesian terminal are
  both terminal and so canonically and uniquely isomorphic, that W2
  exports the isomorphism, and that W3 builds row l at the cartesian
  terminal as a convenience rather than an obligation. Constraint 2's
  closing sentence, admitting "a `Prop` coherence field of W2's own
  (constraint 6)", is struck with it, no such field now existing.
- Decision 1 leaves the operation table, the § Workstreams bullets and
  W5's scope untouched; decision 2 changes W5's instance only by
  removing a field it would have discharged by `rfl`.
- `docs/index.md`: the module entry.

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
- `lake lint` and, separately, `lake lint -- GebTests`. These are two
  invocations, not one: `lakefile.toml` sets
  `lintDriverArgs = ["Geb"]`, so plain `lake lint` does not reach the
  test module. Both run the axiom linter, and every declaration in
  the two modules must depend on no axiom outside the standard set
  together with `Classical.choice`, both modules being allowlisted.
- `lake shake --add-public --keep-implied --keep-prefix Geb GebTests`
  clean, for minimised imports.
- `scripts/lint-imports.sh` clean. W2 imports nothing outside
  `Mathlib.*`, `Geb.Mathlib.*` and `GebTests.Mathlib.*` — the test
  module imports the wrapper, and the two index files gain a line
  each — all of which the allow-lists already admit; it needs nothing
  from the `Batteries.` admission W0 made.
- `markdownlint-cli2` and the `doctoc` check clean for the Markdown
  touched.
- No `noncomputable` and no `sorry` in either module.

The class, the accessors, the derived instances, the witness and the
resolution assertions have each been elaborated at the current revision,
as a single unit, with no error and no `sorry`. That was done in
standalone snippets, which did not exercise the module system, and the
plan re-verifies inside the actual modules rather than inheriting the
result. Three specifics rather than a general caveat:

- `scripts/lint-imports.sh` requires every upstream-eligible file to
  carry a `module` line, which `docs/rules/lean-coding.md` places
  after the copyright block; it is not optional, and it does not
  precede the header the style linter requires.
- Under `module`, the declarations need a `public section`.
- Definitional transparency across a module boundary needs
  `@[expose]`, per this repository's own precedent in
  `Geb/Mathlib/Data/PFunctor/Slice/Basic.lean` and
  `Geb/Mathlib/CategoryTheory/Grothendieck.lean`. It is not required
  here: a two-module build with the wrapper under a plain
  `public section` resolves every derived instance and both data
  accessors from the test module, so `@[instance_reducible]` crosses
  the boundary without it. W2 therefore does not take `@[expose]`,
  an attribute exposing every body of an upstream-eligible module not
  being added without a stated need.

## Out of scope

- The `ElementaryTopos FinSetSkel` instance, and any operation-table
  row. Those are W3, W4 and W5.
- Any alternative constructor taking finite limits, exponentials and
  a classifier and building the colimits by the [Pare1974] route. The
  removed umbrella spec records that the redundancy forecloses
  nothing and such a constructor may be added later; W2 does not add
  it.
- Any transport of the class along an equivalence of categories.

## Interaction with the other workstreams

W2 is independent of W1. The files it touches that W1 also touches are
the four the roadmap's § Standing obligations identifies as
concurrent-append points for the W1/W2 pair:
`GebMeta.classicalAllowedModules`, the § Status table, `docs/index.md`,
and any shared directory index file — the last being
`Geb/Mathlib/CategoryTheory.lean` and its `GebTests` parallel, which
deliverable 3 appends to. The roadmap fixes only that W1 through W5
place their modules under `Geb/Mathlib/`, so whether W1 appends to
those same two files is not settled there; the resolution is the same
either way. These are textual conflicts, resolved by rebasing
whichever sibling merges second.

W2 introduces no `simp` lemma, so the caution about W3's and W4's
carrier-level normal forms does not apply to it.

## References

- `TODO.md` § FinSetSkel as an elementary topos — the authoritative
  roadmap.
- The umbrella spec, `jj` change
  `nkwoqxwytsvrlpnsklzzlzkxtovyxkzm` on branch
  `docs/finsetskel-topos-roadmap`.
- `CONTRIBUTING.md`, `AGENTS.md`, `CLAUDE.md`, `docs/process.md`,
  `docs/rules/lean-coding.md`.
- [Freyd1972] Peter Freyd, "Aspects of topoi", *Bulletin of the
  Australian Mathematical Society* 7(1), 1–76, 1972,
  <https://doi.org/10.1017/S0004972700044828>.
- [Mikkelsen1976] Christian Juul Mikkelsen, *Lattice Theoretic and
  Logical Aspects of Elementary Topoi*, Various Publication Series
  No. 25, Matematisk Institut, Aarhus Universitet, March 1976;
  reprinted as *Reprints in Theory and Applications of Categories*
  No. 29, 2022, pages 1–89,
  <http://www.tac.mta.ca/tac/reprints/articles/29/tr29.pdf>.
- [Pare1974] Robert Paré, "Colimits in topoi", *Bulletin of the
  American Mathematical Society* 80(3), 556–561, May 1974,
  <https://doi.org/10.1090/S0002-9904-1974-13497-X>.
