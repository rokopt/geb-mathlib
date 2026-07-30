# FinSetSkel W5 — the elementary-topos instance and roadmap removal

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Goal](#goal)
- [Verified findings](#verified-findings)
- [Deliverable 1: the instance](#deliverable-1-the-instance)
- [Deliverable 2: the test parallel](#deliverable-2-the-test-parallel)
- [Deliverable 3: the documentation migration](#deliverable-3-the-documentation-migration)
- [Deliverable 4: the removal](#deliverable-4-the-removal)
- [Constraints](#constraints)
- [Out of scope](#out-of-scope)
- [Branch shape](#branch-shape)
- [Acceptance criteria](#acceptance-criteria)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Goal

W5 is the last workstream of the FinSetSkel elementary-topos group. It
assembles the seven fields W3 and W4 export into an
`ElementaryTopos FinSetSkel` instance, which is the whole of the
group's remaining finite-colimit obligation; and it removes the
group's roadmap entry from `TODO.md`, migrating the durable part into
the persistent documentation.

`elementaryTopos` is a transcription, in the sense of
`CONTRIBUTING.md` § Cite the literature: the proposition it inhabits —
that the category of finite sets is an elementary topos — is published
mathematics. It proves nothing new. Each of its seven fields was
constructed, and where it transcribed published mathematics cited, by
W1 through W4, and the axiomatisation it instantiates is cited to
[Freyd1972] by `Geb/Mathlib/CategoryTheory/ElementaryTopos.lean`. The
new module's `## References` names [nLabFinSet]
(`https://ncatlab.org/nlab/show/FinSet`), following
`FinSetSkel/Basic.lean`, which cites [nLabSkeletalCategory] and keeps
the textbook locator that entry attests out of the `.lean` file. The
same division applies here: the module cites the nLab entry only, and
the locator it attests — Johnstone, _Sketches of an Elephant_, example
2.1.2 — is recorded in `TODO.md` § Triggers as pending verification
against the primary source, attestation by a secondary source not
being verification. Everything Deliverable 2 declares is novel:
assertions about this development, transcribing nothing.

## Verified findings

Each was established by elaborating Lean against the tree at
`c38e3249`, at toolchain v4.33.0-rc1. Those that presuppose the new
modules were established on probe modules built in place and then
removed; the tree at `c38e3249` is unchanged.

- **The assembly typechecks with no adaptation.** All seven fields are
  accepted as written, including the `closed` field, whose type
  `@MonoidalClosed C _ cartesian.toMonoidalCategory` accepts
  `FinSetSkel.monoidalClosed` directly. W3 recorded this and deleted
  its probe; the finding is re-established here rather than assumed.
  The instance elaborates inside `namespace FinSetSkel` with every
  field written unqualified, under `@[expose] public section`, and its
  measured axioms are `propext`, `Quot.sound` and `Classical.choice`.
- **`@[expose]` is not required for the instance.** Lean core
  auto-exposes any non-`Prop` `instance`
  (`Lean/Elab/MutualDef.lean:1347-1350` at v4.33.0-rc1), and
  `ElementaryTopos` is data-carrying, so `elementaryTopos` is exposed
  either way and Deliverable 2's assertions read through its fields
  regardless. `@[expose] public section` is written for consistency
  with the five sibling wrappers, not out of necessity. The
  observation that a non-exposed `public def` does not reduce
  downstream is true of `def`s and does not transfer to instances.
- **Every one of the seven fields is pinned by `rfl`, with no
  evaluation.** For each accessor, an equation between
  `ElementaryTopos.<field>` and `FinSetSkel.<field>` holds by `rfl`,
  including for `coequalizerCocone`, whose value does not reduce, the
  union-find it computes through not reducing definitionally.
- **Four `Prop` classes are made resolvable by the instance, not one.**
  With the five field-supplying modules imported and no instance,
  `HasFiniteCoproducts`, `HasCoequalizers`, `HasInitial` and
  `HasBinaryCoproducts` at `FinSetSkel` resolve, while `HasEqualizers`,
  `HasFiniteLimits`, `HasFiniteColimits` and `HasPushouts` all fail to
  synthesize; all four resolve after it. mathlib's
  `hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts` is a
  `theorem`, not an `instance`
  (`Mathlib/CategoryTheory/Limits/Constructions/LimitsOfProductsAndEqualizers.lean:418`),
  which is why the two hypotheses resolving does not make the
  conclusion resolve. There is no construction for the finite-colimit
  obligation to write.
- **`FinSetSkel` could not have been an instantiation of
  `FintypeCat.Skeleton`.** mathlib's `SmallCategory Skeleton` instance
  fixes `Hom X Y := ULift (Fin X.len) → ULift (Fin Y.len)`
  (`Mathlib/CategoryTheory/FintypeCat.lean:181`). A type carries one
  `Category` instance, so a category with the same objects and vector
  morphisms is a distinct type. `FinSetSkel/Basic.lean:16-19` already
  records that mathlib's morphisms are functions and are comparable
  only through `Classical.choice`; the one-instance argument and the
  noncomputability below are what it does not record.
- **mathlib's finite (co)limits on `FintypeCat` are constructed
  noncomputably.** This is a fact about mathlib's other model of
  finite sets, not about `FinSetSkel`, and bears only on the
  `Skeleton.lean` item of Deliverable 3. The `Prop` instances
  `hasFiniteLimits`
  (`Mathlib/CategoryTheory/Limits/FintypeCat.lean:58`) and
  `hasFiniteColimits` (`:133`) are plain instances — being `Prop`,
  they could not be otherwise — but the constructions they are layered
  over are `noncomputable`: `finiteLimitOfFiniteDiagram` (`:40`),
  `inclusionCreatesFiniteLimits` (`:45`),
  `finiteColimitOfFiniteDiagram` (`:115`) and
  `inclusionCreatesFiniteColimits` (`:120`). Nothing transported along
  the equivalence computes.
- **A worked finite colimit is available at a shape neither the binary
  coproducts nor the coequalizers cover.** `HasPushouts FinSetSkel`
  resolves only through the derived finite colimits. Identifying the
  pushout takes two steps, not one: `IsPushout.of_hasBinaryCoproduct'`
  (`Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Basic.lean:453`)
  gives an isomorphism with the chosen-colimit coproduct
  `mk 1 ⨿ mk 1`, which does not reduce to `mk 2`; a second isomorphism
  to `binaryCoproductCocone`'s cocone point is needed before `skeletal`
  applies. The composite elaborates:

  ```lean
  theorem sampleSkelToposPushoutInitialSpan_eq :
      pushout (initial.to (mk 1 : FinSetSkel.{0})) (initial.to (mk 1))
        = mk 2 :=
    skeletal
      ⟨(IsPushout.of_hasBinaryCoproduct' (mk 1 : FinSetSkel.{0})
          (mk 1)).isoPushout.symm ≪≫
        colimit.isoColimitCocone (binaryCoproductCocone (mk 1) (mk 1))⟩
  ```

- **Every generator of `FinSetSkel`'s topos structure computes.** No
  declaration under `Geb/Mathlib/CategoryTheory/FinSetSkel/` is
  `noncomputable`, that keyword being banned repository-wide, so the
  terminal object, the binary products, the equalizers, the initial
  object, the binary coproducts, the union-find coequalizer, the
  exponentials and the classifier are all data that runs. The
  instance's seven fields are those terms unchanged.
- **What does not compute is the passage from those generators to a
  cone over an arbitrary finite diagram**, for two independent
  reasons. mathlib's `limitConeOfEqualizerAndProduct`
  (`…/LimitsOfProductsAndEqualizers.lean:102`) is `noncomputable`,
  routing through `limit.cone`; and, prior to that,
  `ElementaryTopos.lean:43-48` records that `FinCategory` carries a
  `Fintype` whose `Finset` yields a list only through the
  `noncomputable` `Finset.toList`, so an arbitrary finite diagram
  admits no computable enumeration to fold the generators over. For
  any diagram written down explicitly the limit is computable by
  iterating the chosen binary product and taking the chosen
  equalizer; it is the universally quantified statement that is not.
  This is why W2 carries `HasFiniteLimits` and `HasFiniteColimits` as
  `Prop`: they were never going to carry data, so deriving them loses
  nothing.
- **The chosen-(co)limit API is noncomputable.** `colimit`
  (`Mathlib/CategoryTheory/Limits/HasLimits.lean:703`, inside the
  `noncomputable section` opened at `:61`),
  `colimitCoconeOfCoequalizerAndCoproduct`
  (`…/LimitsOfProductsAndEqualizers.lean:379`) and `coprod`
  (`…/Shapes/BinaryProducts.lean:536`) are all `noncomputable` and all
  depend on `Classical.choice`. The worked colimit above is therefore
  an identification of objects, `FinSetSkel` being skeletal, rather
  than an evaluation.
- **Both allowlist entries are necessary.** Removing the source entry
  flags `elementaryTopos`. Removing the test entry flags every
  declaration in the test module, each routing through the instance.
- **`Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq` is a
  `deprecated_module`**; `…Pullback.IsPullback.Basic` is not.
- **`Fin.compressEquiv` has consumers.** `TODO.md:885-892` records it
  as having none besides its own module, its test parallel and its
  `docs/index.md` entry. W4's
  `Geb/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean` consumes it at
  lines 124, 130, 150, 158 and 183, and `docs/index.md:461` documents
  that consumption. The trigger's condition is void. That entry is
  also the only occurrence of a `W`-label in `TODO.md` outside the
  block this branch deletes, at `:885` and `:890`.
- **`TODO.md` § Triggers holds 21 top-level entries**
  (`TODO.md:694` through `:885`), not two.
- **`lake shake --add-public --keep-prefix Geb GebTests` reports 13
  `Geb/Mathlib/` files and 5 `GebTests` ones**, exiting 1. Dropping
  `--add-public` gives 19 and 13 instead, so the figures are
  meaningful only against a named invocation. Restoring
  `--keep-implied` is the repository's own check and exits 0.
- **The `ofFn` ban is stated but its enforcement is not.**
  `Geb/Mathlib/Data/Vector/OfFn.lean`'s module docstring states that
  choice-free modules use `ofFnC`, names the tainted lemmas, and at
  `:29-30` gives one `@[simp]` mechanism for the Batteries import it
  declines. It does not record that the lemmas the ban covers — Lean
  core's, not mathlib's — carry `@[simp]`, three of them also
  `@[grind =]`, so a bare `simp` or `grind` introduces
  `Classical.choice`; nor that the violation surfaces at `lake lint`
  rather than at elaboration. The four are `Vector.getElem_ofFn`
  (`Init/Data/Vector/OfFn.lean:27`), `Vector.getElem_range`
  (`Init/Data/Vector/Range.lean:145`) and `Vector.getElem_finRange`
  (`Init/Data/Vector/FinRange.lean:25`), all three `@[simp, grind =]`,
  and `Vector.ofFn_getElem` (`Init/Data/Vector/OfFn.lean:72`),
  `@[simp]` alone. The constructions `Vector.range` and
  `Vector.finRange`, as against their lemmas, are banned by
  `TODO.md:429` and by no other place in the tree.
- **Outside `TODO.md`, the `Nat` and `Equiv` disciplines appear only
  in `docs/index.md`.**
  `docs/index.md:500-504` and `:527-530` state them, and
  `docs/process.md` § Documentation under `docs/` defines that file as
  a reader-facing topological narrative rather than a rule file
  binding a `.lean` edit; both entries describe what one module did.
  The `Equiv` entry states only the domain half, not that codomain
  transport is choice-free and needs no replacement.
- **The `LawfulBEq (Fin n)` dependence is live, and depends on the
  import context.** With `Geb.Mathlib.CategoryTheory.FinSetSkel.`
  `Classifier.Instance` imported — one of this workstream's five
  field-supplying modules — `#synth LawfulBEq (Fin 4)` selects
  `Std.LawfulBEqOrd.lawfulBEq` and a `Decidable` membership at
  `List (Fin 4)` measures `propext`, `Classical.choice` and
  `Quot.sound`. Under the narrower closure of
  `FinSetSkel/Classifier/Core.lean`, which decides exactly such a
  membership at `:90` (`by_cases hj : j ∈ m.toVec.toList`) and is not
  allowlisted, the choice-free `instLawfulBEq` wins and the same
  measurement gives `propext` alone. So `TODO.md:465-483` binds the
  modules it says it binds, and measuring it in a narrow closure gives
  the opposite answer — the failure mode migrated rule 1 describes,
  reached in this spec's own drafting.

## Deliverable 1: the instance

`Geb/Mathlib/CategoryTheory/FinSetSkel/ElementaryTopos.lean`, named for
the class it instantiates. Naming it `Topos.lean` would lose the
Grothendieck-versus-elementary distinction the group's naming rule was
written to make.

The module carries the standard copyright header, the `module` keyword,
`public import`s of the class and the five field-supplying modules, its
docstring, then `@[expose] public section`, `universe u`, and
`open CategoryTheory Limits` — the form its siblings use
(`Shapes/Instances.lean:62`, `Classifier/Instance.lean:61`,
`Equalizer/Limits.lean:43`), not the fully qualified variant at
`Coequalizer.lean:46`. It contains exactly one declaration, inside
`namespace FinSetSkel`:

```lean
/-- `FinSetSkel` is an elementary topos. -/
instance elementaryTopos : ElementaryTopos FinSetSkel.{u} where
  cartesian := cartesianMonoidalCategory
  closed := monoidalClosed
  initialCocone := initialCocone
  binaryCoproductCocone := binaryCoproductCocone
  equalizerCone := equalizerCone
  coequalizerCocone := coequalizerCocone
  classifier := classifier
```

Its module docstring carries a title; a summary naming the four `Prop`
classes the instance makes resolvable and stating why the module is
allowlisted: it introduces no `Classical.choice` dependence of its own,
inheriting the whole of it from the seven field terms, whose own
modules each name the mathlib construct responsible. That rationale is
carried in the summary in each of
`Skeleton.lean:21`, `Equalizer/Limits.lean:17`, `Coequalizer.lean:24`
and `Shapes/Instances.lean:23`; `## Main definitions`;
`## Implementation notes`; `## References` citing [nLabFinSet] and no
textbook locator; and `## Tags`. `## Main statements` and
`## Notation` are omitted as vacuous rather than left as placeholders.

`## Implementation notes` carries two items: that nothing beyond the
instance is registered, a direct `HasFiniteColimits FinSetSkel` being a
second resolution route to a `Prop` nothing consumes; and the
across-constructions half of the data-versus-`Prop` argument
(`TODO.md:353-364`) — carrying the coequalizer as data decides which
algorithm runs, a derived construction being whichever one the general
proof yields, and that is not union-find. That argument names
union-find and so belongs here rather than in the class module, which
declares no instance of its own class.

The module is packaging throughout, so it and its test parallel are
appended to `GebMeta.classicalAllowedModules`; the test parallel's name
may be added here, the list being an inert `NameSet` in which an
unmatched name is not an error.
`Geb/Mathlib/CategoryTheory/FinSetSkel.lean` gains a `public import` in
its existing alphabetical order, between `Coequalizer` and `Equalizer`.
Without it `lake lint` does not reach the new module —
`lintDriverArgs = ["Geb"]` runs over the root's import closure — so the
allowlist entry would be inert and the axiom check would not run.
`docs/references.bib` gains `nLabFinSet` in this deliverable, the
module's `## References` citing it: the form is that of its three
sibling nLab entries, placed beside `nLabSkeletalCategory` at `:256`,
the file being unalphabetised and validated by no script.

## Deliverable 2: the test parallel

`GebTests/Mathlib/CategoryTheory/FinSetSkel/ElementaryTopos.lean`,
carrying the same obligations as any `.lean` file: copyright header,
`module` keyword, a `/-- … -/` docstring on every declaration, and
`@[expose] public section`, the form at
`GebTests/Mathlib/CategoryTheory/FinSetSkel/Coequalizer.lean:21`. Its
module docstring carries a title, a summary, `## Main statements` —
which has content, the module declaring twelve named theorems — and
`## Tags`. Its sibling test modules omit `## Main statements`; that
divergence is recorded as a § Triggers entry rather than propagated.
`GebTests/Mathlib/CategoryTheory/FinSetSkel.lean` gains its plain
`import` in this deliverable, not in Deliverable 1, so that no commit
imports a module that does not yet exist; without it `lake lint --
GebTests` does not reach the module and its allowlist entry is inert.

Its imports are three: the new source module, as a `public import`,
the form its siblings use (`Coequalizer.lean:8`); and
`Geb.Mathlib.CategoryTheory.FinSetSkel.Skeleton`, for `skeletal`, and
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic`, both
as plain `import`s, each being used only inside a proof term and so
outside the public closure. No `public meta import` is needed, this
module evaluating nothing in the interpreter, so it adds no third site
to the `scripts/extract-pr.sh` rewrite defect that `TODO.md:873-884`
records, and no `-- shake: keep` suppression.

Assertions are named theorems rather than `example`s, following the
directory's own pattern
(`GebTests/Mathlib/CategoryTheory/FinSetSkel/Coequalizer.lean:26`) and
avoiding the shake false positive an `example`-only import produces.
The four resolution assertions take the directory's own resolution
form, `snake_case` naming the class and the category as at
`Coequalizer.lean:26`'s `hasCoequalizers_finSetSkel`; none collides.
The seven field-identity assertions and the pushout theorem take the
prefix `sampleSkelTopos`, the bare `sampleSkel…` forms colliding with
`sampleSkelClassifier` at `Classifier/Instance.lean:27` and
`sampleSkelEqualizerCone` at `Equalizer/Limits.lean:31`, and
`lake lint -- GebTests` merging every test module into one
environment.

Three parts:

**Resolution.** One assertion per `Prop` class the instance makes
resolvable, and only those four: `HasEqualizers`, `HasFiniteLimits`,
`HasFiniteColimits`, `HasPushouts`. The other four resolve
independently of the instance. Each is a
`theorem … := inferInstance`, the form at `Coequalizer.lean:26`. The
other four are already asserted by
`GebTests/Mathlib/CategoryTheory/FinSetSkel/Shapes/Instances.lean:27`
and `Coequalizer.lean:26`; `inferInstance` reports no route, so
restating them here would assert nothing about this module.

**Field identity.** Seven assertions, one per field, each of the form
`(FinSetSkel.elementaryTopos).<field> … = FinSetSkel.<term> …` closed
by `rfl`, the right side naming the term Deliverable 1 assigns to that
field. The raw projections are what close: the class module's two
named accessors are unexposed `@[instance_reducible] def`s,
`ElementaryTopos.lean:91` opening a plain `public section`, so
`ElementaryTopos.cartesianMonoidalCategory … = …` is not a
definitional equality and the `monoidalClosed` counterpart does not
typecheck at all, its two sides living over different cartesian
structures.
These are a regression check rather than a discovery test: each field
of a `where`-block is definitionally the term written for it, so they
can fail only if the instance is later rewired. Their value is that
they connect the instance to each field's own sibling test module,
where that field's behaviour is exercised, so a rewiring is caught
without duplicating those tests here.

A class-typed `def … := inferInstance` is not used as a witness. Such a
definition draws the semireducibility warning unless marked
`@[instance_reducible]`, and an equation between terms tests the
wiring where a class-typed definition restates a type.

**The worked colimit.** The pushout identification above, stated
inline as printed, with no separate fixture: the span is two
applications of `initial.to`, short enough to read in the statement.

## Deliverable 3: the documentation migration

`TODO.md`'s preamble states that a completed workstream's content
merges into `docs/index.md`. Most of the group's entry is transient and
is deleted. The durable items, none of which belongs in `docs/index.md`, are
enumerated below by destination.

**Six rules → `docs/rules/lean-coding.md`
§ Constructive-only Lean code**, the section at `:399` that already
describes the axiom linter, not the `### Constructive-only` subsection
at `:241`. That the two sections overlap is pre-existing; this
workstream adds to the one carrying the axiom material and does not
reconcile them. They are added as bullet items under the existing
section, adding no heading, so that file's `doctoc` TOC does not move.
Each is one to three sentences and carries the v4.33.0-rc1 pin of any
measurement it rests on; the per-lemma name lists they are drawn from
stay where they are.

1. The monomorphic-measurement rule (`TODO.md:498-503`): take an axiom
   measurement from a monomorphic declaration at the instances used,
   and in the import closure of the module that will use them,
   `#print axioms` on a polymorphic constant reporting that constant
   and no instantiation of it. The import-closure clause is this
   workstream's addition, established by the `LawfulBEq` finding
   above.
2. The name-the-term rule (`TODO.md:505-514`): where two routes
   inhabit one class and only one is choice-free, name the term rather
   than leaving instance search to select, and where the only instance
   in scope is choice-dependent, supply one.
3. The module-split rule, constraint 8 (`TODO.md:418-427`), stated
   over a module set rather than over a workstream, `TODO.md:868-870`
   holding that a workstream cannot be referred to from persistent
   documentation: split a development's modules so that constructions
   and the content of their universal properties are choice-free over
   the underlying data and mathlib structures and `Prop` instances sit
   in a wrapper whose fields are those terms; admit only wrapper
   modules to `GebMeta.classicalAllowedModules`; a wrapper may carry
   content where that content cannot be stated choice-free.
4. The `Nat` bound rule (`TODO.md:450-463`): establish a bound on
   `Fin` or `Nat` arithmetic by `omega` over individually named
   hypotheses, or by case analysis, rather than by the single lemma
   that states it, the choice-dependent and choice-free lemmas of that
   API interleaving under no separating convention.
5. The `Equiv` transport rule (`TODO.md:485-496`): transport along an
   equivalence of a function type's codomain freely; state the domain
   transport in a choice-free module, mathlib's domain-transport
   combinators depending on `Classical.choice` where its
   codomain-transport ones do not.
6. The `LawfulBEq (Fin n)` rule (`TODO.md:465-483`): in a choice-free
   module whose closure reaches mathlib's `Fin` order API, pin the
   `LawfulBEq (Fin n)` instance to the three-line construction over
   the `DecidableEq`-derived `BEq`, instance search otherwise
   selecting `Std.LawfulBEqOrd.lawfulBEq`, which is choice-dependent
   at `Fin n`; every operation stated over the class inherits that,
   `decide (j ∈ l)` at `List (Fin n)` among them. This is an instance
   of rule 2 one level down, and is stated separately because the
   closure-dependence makes it easy to measure clean.

The same section gains the half of the `ofFn` item that names this
repository's tooling: that a violation of the ban is not an
elaboration error and surfaces at `lake lint`, which that section
already documents. That sentence stays out of the `Geb/Mathlib/`
docstring below, `scripts/extract-pr.sh` rewriting import lines only,
so a docstring naming `lake lint` would ship to mathlib unchanged.

**One rule → `docs/rules/lean-coding.md`
§ Structure and typeclass patterns** (`:337`): the registration rule,
half of constraint 5 (`TODO.md:388-398`) — register a `Prop` class as
an instance where something consumes it, redundant registrations being
harmless by proof irrelevance but not therefore warranted. It has no
constructive content, so it does not belong beside the axiom material.
`docs/index.md` attests it by example at its `Equalizer/Limits.lean`
entry and `ElementaryTopos.lean` states its proof-irrelevance half for
accessors, but neither states the rule.

**Two items → `Geb/Mathlib/Data/Vector/OfFn.lean`'s module docstring**,
which already states the ban and names the tainted lemmas: that those
lemmas carry `@[simp]`, and all but `Vector.ofFn_getElem` also
`@[grind =]`, so a bare `simp` or `grind` meeting such a term
introduces `Classical.choice`; and that the constructions
`Vector.range` and `Vector.finRange` are themselves banned in
choice-free modules, which `TODO.md:429` states and no other place
does. Placing both beside the ban avoids a second statement of it in
the rules file.

**Two items → `Geb/Mathlib/CategoryTheory/ElementaryTopos.lean` and
`Geb/Mathlib/CategoryTheory/FinSetSkel/Basic.lean`**: the two name
rationales `TODO.md:212-216` fixes. `ElementaryTopos.lean`
§ Implementation notes gains one sentence on why the class is
`ElementaryTopos` and not `Topos`: the qualifier distinguishes it from
a Grothendieck topos, and mathlib reserves `Topos` for sheaf-theoretic
material, `Mathlib/CategoryTheory/Topos/` holding `Sheaf.lean` and a
`deprecated_module` classifier shim and mathlib declaring no `Topos`
class.
`Basic.lean` gains an `## Implementation notes` section, having none,
placed between `## Main statements` and `## References`, carrying one
sentence on why the category is `FinSetSkel`, the `Skel` recording
that it is the skeletal model, parallel to `FintypeCat.Skeleton`.
Creating that section is symmetric with the `Skeleton.lean` item
below; moving the rationale paragraphs already in that module's
summary into it remains out of scope.

**One item → `Geb/Mathlib/CategoryTheory/FinSetSkel/Skeleton.lean`**,
which gains an `## Implementation notes` section, having none, placed
between `## Main statements` and `## Tags` as the mandated order
requires, that module having no `## References`. This is the one item
the branch adds rather than migrates: it answers the question a
mathlib reviewer asks of that module, which the deleted block raised
and left open. It states only what `Basic.lean:16-19` does not: that
mathlib's `SmallCategory Skeleton` fixes its morphisms to functions
and a type carries one `Category` instance, so a vector-morphism
category is a distinct type rather than an instantiation; and that
mathlib's finite (co)limits on `FintypeCat` are constructed
noncomputably.

`docs/process.md` gains one new `##` section, § Constructive-only
discipline, placed after § Illustrate only with the archetypal so that
§ Document only the persistent stays adjacent to the two sections that
open by calling themselves its corollaries. It gives the rationale for
the constructive rules in three to six sentences, including the
`#print axioms` behaviour rule 1 rests on. Its `doctoc` TOC is regenerated in
the same commit.
§ Constructive-only Lean code gains one further rule, the seventh:
re-measure the axiom dependences these rules rest on at each toolchain
bump, a lemma's axioms following its proof. That is `TODO.md:462-463`'s
obligation. It goes in a `docs/rules/` file rather than in
`docs/process.md`, which records why rules exist rather than stating
them, and rather than in § Triggers, which a bump reviewer does not
read; `docs/rules/*.md` are path-scope-loaded, so an agent editing
`.lean` files sees it.

**`docs/index.md`** gains an entry for the new module — new
documentation of a new module rather than a migrated item — appended after the
`Classifier/Instance.lean` entry, the last
of the instance's six predecessors and the file's last entry, that
file being maintained in topological order. The entry records the
instance, which `Prop` classes it makes resolvable, that the
source and test modules are listed in
`GebMeta.classicalAllowedModules`, as every sibling entry for an
allowlisted module does, and its dependencies — the five
field-supplying entries and the class — as
`docs/process.md` § Documentation under `docs/` requires of an entry. It
records no carrier: the initial object's
length and the binary coproduct's are `Shapes/Core.lean` facts and
belong to that entry if anywhere. Row letters do not appear; they were
artifacts of how the operations were referred to while the group was
planned, and were deliberately kept out of every `.lean` docstring.

Not migrated, each for its own reason:

- The object-carrier argument and the root-`Vector` cost analysis,
  carried by `FinSetSkel/Basic.lean:23-30` and `:32-47` respectively —
  the second in its `DecidableEq` and `ofFn`/`get` halves, the first by
  a different argument reaching the same conclusion.
- The [Mikkelsen1976] and [Pare1974] citations, carried by
  `ElementaryTopos.lean`.
- Constraint 9's per-lemma taint lists for `Vector.ofFn` and
  `Array.ofFn`, carried by `Geb/Mathlib/Data/Vector/OfFn.lean`'s
  docstring and by the surviving trigger at `TODO.md:818-834`; and its
  `Nat` list, whose conclusion rule 4 carries and whose enumeration
  would need re-measuring on every bump.
- The choice-taint of `Fintype.decidableForallFintype`, recorded at
  `Geb/Mathlib/Data/FinEnum.lean:20,48`.
- The note on W3's and W4's carrier-level `simp` lemmas
  (`TODO.md:516-518`), whose content — do not mark a transport lemma
  `simp` in a direction that rewrites the established carrier normal
  form — restates the normal-form principle mathlib's own style guide
  states, which `docs/rules/lean-coding.md` § Authoritative upstream
  guides already binds.
- The standing obligation that `GebMeta.classicalAllowedModules` gains
  each new wrapper module and its `GebTests` parallel
  (`TODO.md:529-531`), stated by `GebMeta.lean:56-57`; and the
  concurrent-pair conflict note (`:532-537`), the workstream
  assignments, dependency order, spec-recovery pointers, status table,
  and constraints 1, 2, 4 and 7, all transient. Constraints 3 and 6 are
  durable but already stated, at `ElementaryTopos.lean:34-37` and
  `:70-75`.

## Deliverable 4: the removal

The § Triggers amendments below are made first, while their line
anchors still hold; the deletion removes lines 181-549 and shifts every later line.

`## Triggers (do when condition fires)` gains two entries, loses one
and has four amended, leaving 22.

- Removed: the `Fin.compressEquiv` entry (`:885-892`). Its stated
  condition — that the declaration has no consumer — is false, so the
  question it poses under `CONTRIBUTING.md` § Code is cost is
  answered, and the consumption is recorded at `docs/index.md:461`. It
  is also the only surviving occurrence of a `W`-label in `TODO.md`
  outside the deleted block.
- Appended: the concrete textbook locators pending verification — Mac
  Lane p. 91 and Riehl p. 34, attested by [nLabSkeletalCategory], and
  Johnstone example 2.1.2, attested by [nLabFinSet]. The condition is
  stated per locator, so acquiring one primary source discharges that
  locator and leaves the entry standing for the others.
- Appended: the test-module docstring divergence — Deliverable 2's
  module carries `## Main statements` and its siblings do not, though
  each declares named theorems. The condition is the next occasion to
  revise those modules.
- Amended, `:705-722`, the `lake shake --keep-implied` entry: its file
  enumeration is replaced rather than incremented, its present figures
  predating W3 and W4. The implementer runs
  `lake shake --add-public --keep-prefix Geb GebTests` once the new
  modules are in the tree and records that output, naming the
  invocation: at `c38e3249` it gives 13 and 5, dropping `--add-public`
  gives 19 and 13, and the new source module will appear in it,
  `Classifier/Instance.lean:10` and `Exponential/Closed.lean:9` both
  publicly importing `Shapes.Instances` so that import is implied in
  the new module too.
- Amended, `:850`, the `mathlib-to-Batteries` entry: "outlives this
  workstream group" refers to the deleted section.
- Amended, `:835-841`, the "Choice-free `Skeletal FinSetSkel`" entry:
  it ends "There is no such use while `Skeletal` is consumed only by
  the wrapper", and Deliverable 2 makes the new test module a second
  consumer. That module is allowlisted, so the entry's condition still
  does not fire and only the wording changes.
- Amended, `:782-789`, the test-module import-visibility entry: its
  claim that every sibling test module uses plain `import` for its
  module under test is false: most use `public import`, and
  Deliverable 2 adds another. The corrected premise is stated
  qualitatively, a count going stale on the next test module. The
  entry's question stands.

Three § Triggers entries are false or unmet for reasons predating this
branch and are left alone: `:805-817`, whose extraction is not
discharged — `GebTests/Mathlib/Data/PFunctor/Presheaf/Fixtures.lean`
exists, is imported by four modules, and declares an unrelated
fixture family, while `presheafWitnessData` is still duplicated at
`GebTests/Mathlib/Data/PFunctor/Presheaf/Basic.lean:85` and
`W.lean:37`, so the extraction the entry directs is half-executed and
its completion is a multi-file change rather than a premise
correction; `:790-796`, the test-declaration privacy
discipline; and the closing lines of `:860-872`, whose claim that
`TODO.md` is where workstreams are named survives the deletion, the
preamble retaining the vocabulary.

`TODO.md` lines 181-549 — `### FinSetSkel as an elementary topos`
through the status table, ending immediately before
`### Complexity of the decidable validity checkers` at 550 — are then
deleted whole. Line 180 is blank and line 549 is blank, so the
deletion leaves exactly one blank line between the surrounding
sections. The edit is anchored on line numbers with assertions on both
bounds: an assertion on the first and last line deleted is checkable
where a title-bounded scripted edit has no such check.

`doctoc --update-only .` is re-run: `TODO.md:15-21` carries the
section's TOC entry and six sub-entries, which the deletion makes
stale.

The preamble at `TODO.md:33-34` is amended to route a completed
workstream's content to the persistent documentation rather than to
`docs/index.md` alone. Its workstream vocabulary is retained,
`CONTRIBUTING.md` § Working step 2 directing a reader to `TODO.md` to
pick one, and `TODO.md:762` using the word in an entry this branch
does not touch.

## Constraints

1. No `noncomputable` declaration; `Classical.choice` only in the two
   allowlisted modules this workstream adds.
2. The instance module `public import`s the class and the five
   field-supplying modules: the declaration's type mentions the first
   two and its body terms from each of the rest. Import visibility
   elsewhere is decided per import, per the module-system rule, and
   any import the shake check reports is reviewed before it is
   written: its output identifies a sufficient closure, not the module
   a reader should see named.
3. `lake lint` and `lake lint -- GebTests` are the axiom checks,
   running `collectAxioms` over the import closure of each root; a
   module absent from its index chain is not reached, so both index
   imports are part of the check rather than tidiness.
4. The banned `ofFn` family is a separate check that `#print axioms`
   cannot catch, the ban being on the `@[simp]` lemmas and on the
   `range` and `finRange` constructions. It is checked by grepping
   each new module against the list in
   `Geb/Mathlib/Data/Vector/OfFn.lean`'s docstring and the surviving
   trigger at `TODO.md:818-834`. Neither module of this workstream is
   expected to trip it, both being packaging.
5. Every authored `.md` file passes `markdownlint-cli2`, and committed
   Markdown with more than one `##` heading carries a `doctoc` TOC.
6. Nothing is pushed without the user's line-by-line review; the PR
   description is user-authored; tool use is disclosed and the PR
   carries the `LLM-generated` label if the code it contains warrants
   it.
7. The phase workflow of `CLAUDE.md`'s table is followed:
   `superpowers:writing-plans` to plan,
   `superpowers:subagent-driven-development` to execute, `lean4:review`
   before any Lean commit,
   `superpowers:verification-before-completion` before any completion
   claim, `superpowers:receiving-code-review` on review feedback, and
   `lean4:golf` and `pr-review-toolkit:review-pr` before a push is
   proposed.

## Out of scope

- Any construction for the finite-colimit obligation. It is derived.
- Refactoring `FinSetSkel/Basic.lean`'s module summary, several
  rationale paragraphs of which belong under `## Implementation
  notes`, and the same shortcoming in `Skeleton.lean`'s summary, which
  this branch's new `## Implementation notes` section sits beside
  without correcting. Both are W1's content and a separate concern.
- Adding `## Main statements` to the sibling test modules that lack
  it; recorded as a § Triggers entry instead.
- Amending `docs/index.md`'s `Shapes/Core.lean` entry to record the
  initial and coproduct carriers.
- Reconciling `docs/rules/lean-coding.md`'s two overlapping
  constructive-only sections.
- `scripts/extract-pr.sh`'s failure to rewrite `public meta import`
  lines. This branch adds no such line.
- Factoring the `⊗` / `prodObj` transparency idiom into a top-level
  lemma. A reviewer directed that this be done only if a later
  workstream encountered the same transparency mismatch; this one does
  not, containing no proof that projects through a tensor.
- Resolving the `lake shake --keep-implied` question itself, which its
  own trigger assigns to a separate branch. This branch corrects that
  trigger's enumeration; it does not act on it.

## Branch shape

`feat/finsetskel-w5`, off `main` at `c38e3249`, ordered as
`CONTRIBUTING.md` § Concern shape requires: the commits adding the spec
and the plan, then the implementation commits, then the commits
removing the spec and the plan. Commit subjects follow
`docs/rules/ci-and-workflow.md` § Commit-message convention —
imperative present, lower-case, no trailing period, under 72 characters
where possible, and one of the documented types.

Six orderings bind within the implementation commits. Deliverables 1
and 2 precede Deliverable 3, whose `docs/index.md` entry names the new
module. Deliverable 3 precedes Deliverable 4, so that no commit is one
at which the migrated rules are stated nowhere. Within Deliverable 4,
the § Triggers amendments precede the deletion, which shifts their
line anchors. Deliverable 1 precedes Deliverable 2, whose module imports the
source module. Each new module, its `GebMeta.classicalAllowedModules`
entry and its index import land in one commit: a module reachable from
its root without its allowlist entry fails `lake lint`, depending as it
does on `Classical.choice`. Any commit adding or removing a section in a
TOC-bearing Markdown file regenerates that file's TOC in the same
commit.

The spec and the plan each go through fresh-context adversarial review
rounds to convergence before the user reviews them, per `AGENTS.md`
§ Adversarial review.

Two reviewers proposed splitting the rules migration onto its own
branch, on the ground that it binds every `.lean` file and is
reviewable without reference to any FinSetSkel code. The user's
decision is to keep the work on one branch: the deletion is what
removes that content's only statement, so a split would produce one
branch deleting rules with no destination and another adding rules with
no stated occasion. That decision makes the user's line-by-line review
the only check on seven rules binding every `.lean` file in the
repository; the acceptance criteria below establish that each
destination was edited, not that the edit says the right thing.

## Acceptance criteria

`scripts/pre-push.sh` runs the build, the tests, `lake lint` for both
libraries, `scripts/lint-imports.sh`, the shake check,
`markdownlint-cli2` and the `doctoc` check, and builds `GebTests`
itself, so criterion 1 subsumes each of those.

1. `scripts/pre-push.sh` passes.
2. `Geb/Mathlib/CategoryTheory/FinSetSkel/ElementaryTopos.lean`
   declares `FinSetSkel.elementaryTopos : ElementaryTopos
   FinSetSkel.{u}` with the seven fields of Deliverable 1 and no other
   declaration, under `@[expose] public section`; its module docstring
   carries `## Main definitions`, `## Implementation notes`,
   `## References` naming `nLabFinSet`, and `## Tags`; and
   `Geb/Mathlib/CategoryTheory/FinSetSkel.lean` `public import`s it.
3. The test module declares the four resolution assertions, the seven
   field-identity assertions — each of the form
   `(FinSetSkel.elementaryTopos).<field> … = FinSetSkel.<term> …`, — and the
   pushout theorem of Deliverable 2; it contains no `sorry`; it is
   under `@[expose] public section` and its module docstring carries a
   title, a summary, `## Main statements` and `## Tags`; and
   `GebTests/Mathlib/CategoryTheory/FinSetSkel.lean` imports it.
4. The only additions to `GebMeta.classicalAllowedModules` are the two
   modules this workstream adds.
5. `HasEqualizers`, `HasFiniteLimits`, `HasFiniteColimits` and
   `HasPushouts` at `FinSetSkel` resolve, none having resolved at
   `c38e3249`.
6. `grep -rnE '^[[:space:]]*noncomputable[[:space:]]' Geb/ GebTests/`
   is empty, as it is at `c38e3249`; and neither new module names a
   lemma or construction from the banned `ofFn` family of constraint
   4.
7. `grep -nE '\bW[0-5]\b' TODO.md` is empty;
   `grep -rnE '\bW[0-5]\b|[Ww]orkstream' Geb/ GebTests/` is empty, as
   it is at `c38e3249`; `TODO.md` contains no
   `### FinSetSkel as an elementary topos` heading; its § Triggers
   holds 22 top-level entries, each of the four Deliverable 4 amends
   differing from `c38e3249`; its § Triggers contains `Johnstone`,
   `2.1.2`, `Mac Lane`, `Riehl` and `Main statements`, none of which it
   contains at `c38e3249`; its preamble differs from `c38e3249`; and no other part
   of `TODO.md` differs except the TOC and the deleted section.
8. Each migration destination was edited, checked by grep for a phrase
   absent from that file at `c38e3249`, and — where placement is
   load-bearing — within the section named. In
   `docs/rules/lean-coding.md` § Constructive-only Lean code:
   `monomorphic` and `import closure` (rule 1), `two routes` (rule 2),
   `underlying data` (rule 3), `omega` (rule 4), `codomain` (rule 5),
   `LawfulBEq` (rule 6), `toolchain bump` (rule 7), and
   `elaboration error` (the `ofFn` enforcement sentence); in its
   § Structure and typeclass patterns, `proof irrelevance` (the
   registration rule). In `docs/process.md`, the heading
   `Constructive-only discipline`. In
   `Geb/Mathlib/Data/Vector/OfFn.lean`, `grind` and
   `` `Vector.finRange` `` on a line that does not also name
   `getElem`. In `Geb/Mathlib/CategoryTheory/ElementaryTopos.lean`,
   `sheaf`. In `Geb/Mathlib/CategoryTheory/FinSetSkel/Basic.lean`,
   `skeletal model`. In
   `Geb/Mathlib/CategoryTheory/FinSetSkel/Skeleton.lean`,
   `## Implementation notes` and `SmallCategory`. In `docs/index.md`,
   `FinSetSkel/ElementaryTopos.lean`. In `docs/references.bib`,
   `nLabFinSet`.
9. The spec and the plan are absent from the working tree at the tip of
   the branch.
