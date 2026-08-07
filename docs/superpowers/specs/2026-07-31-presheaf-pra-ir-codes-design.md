# Codes for presheaf parametric-right-adjoint functors

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with
[DocToc](https://github.com/thlorenz/doctoc)*

- [Scope of this document](#scope-of-this-document)
- [The rules and their relation to small induction recursion](#the-rules-and-their-relation-to-small-induction-recursion)
- [Motivation](#motivation)
- [Stage 1: morphisms and the representation theorem](#stage-1-morphisms-and-the-representation-theorem)
- [Stage 2: the code system](#stage-2-the-code-system)
  - [The setting is indexed induction-recursion, not induction-recursion](#the-setting-is-indexed-induction-recursion-not-induction-recursion)
  - [The two rules and their semantics](#the-two-rules-and-their-semantics)
  - [Why `δ`'s arity varies over the output object](#why-%CE%B4s-arity-varies-over-the-output-object)
  - [The decoding-dependent continuation](#the-decoding-dependent-continuation)
  - [Why no inductive-inductive definition is needed](#why-no-inductive-inductive-definition-is-needed)
- [Definitions: transcription or novel](#definitions-transcription-or-novel)
- [Branches](#branches)
- [Proof obligations](#proof-obligations)
- [Open questions](#open-questions)
- [Non-goals](#non-goals)
- [Notes](#notes)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope of this document

This specifies a workstream on morphisms of presheaf parametric-right-adjoint
functors and on codes denoting them, in two stages. Stage 1's content is
settled and machine-checked, up to the category structure and the
natural-transformation identification recorded as obligations 2 and 3. Stage 2
is elaborated: the two rules, the code type and the
interpretation are built, and the recursion is present. Completeness is
definitional, the leaf rule injecting an arbitrary presheaf p.r.a. functor and
`interp_praCode` folding it back unchanged; what the codes leave open is the
morphism theory.

The design carries no bound on a restricted leaf. Such a bound would measure
what a generated fragment reaches, and this design has no generated fragment to
be complete over; the vocabulary that stated one is removed rather than carried
unconsumed, per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost. The
cost is recorded where it falls: § Why `δ`'s arity varies over the output
object marks *Unelaborated* the claim that an output-varying arity is
unreachable by a constant-arity rule, which no declaration ever established.

The declarations removed with it are named individually below, so that the
retained set is determined by this document rather than by inspection. There
are fifty-two: forty-one in `Codes.lean`, ten in `Basic.lean`, one in
`Functor.lean`.

| Family | Declarations | Removed because |
| --- | --- | --- |
| The bound (`Codes.lean`) | `HasBijectiveReindex`; `hasBijectiveReindex_of_isEmpty`, `not_hasBijectiveReindex_of_isEmpty`, `hasBijectiveReindex_iotaPresheaf`, `hasBijectiveReindex_iotaConst`, `hasBijectiveReindex_coprod`, `hasBijectiveReindex_adjoinArity`, `hasBijectiveReindex_adjoinArityConst`, `not_hasBijectiveReindex_arityVaries`, `not_hasBijectiveReindex_adjoinArityVarying`, `hasBijectiveReindex_unitPsh`, `hasBijectiveReindex_sigmaPsh`, `hasBijectiveReindex_deltaRec`, `not_hasBijectiveReindex_deltaVaries`, `not_hasBijectiveReindex_interp_deltaCodeVaries` — fifteen, being the definition and its fourteen theorems | the bound itself |
| The type-indexed coproduct (`Codes.lean`) | `coprodData`, `coprod` | its two consumers, `deltaRec` and `hasBijectiveReindex_coprod`, are both retired |
| The decoding-indexed `δ` (`Codes.lean`) | `deltaRec` | superseded by `delta`, which keeps the output-varying arity where `deltaRec` does not; it belonged to the bound, not to the rules |
| The constant arity (`Codes.lean`) | `ShapeArity.const`, `ShapeArity.isFunctorial_const` | their only consumers are `deltaRec` and `hasBijectiveReindex_adjoinArityConst` |
| The unit (`Codes.lean`) | `unitPshData`, `unitPsh`, `unitPshLiftData`, `unitPshLift` | a generator of the bound's fragment and the foot of `praWitnessLift`; no rule names a unit, `CodeShape` and `codeAlgOn` referencing none |
| The varying-arity `δ` (`Codes.lean`) | `arityVariesShapeArity`, `isFunctorial_arityVariesShapeArity`, `adjoinArityVarying`, `adjoinArityVarying_source_empty` | witnesses of the bound |
| The p.r.a. chain (`Codes.lean`) | `praWitnessLift`, `praWitnessLiftShapeVal`, `praWitnessLiftShapeVal_naturality`, `praWitnessLiftShapeEquiv`, `praWitnessLiftDirEquiv`, `praWitnessLiftDirEquiv_restr` | it exhibits the p.r.a. formula's data as reached by the semantic operations, which is the statement a restricted leaf would need and an unrestricted one does not |
| The slice collapse (`Codes.lean`) | `elSliceEquiv`, `elSliceEquiv_fst` | they measure what a `σ`-over-`ι` leaf reaches |
| The arity round trips (`Codes.lean`) | `DomArity.ofPresheaf`, `isFunctorial_ofPresheaf`, `dirEquivOfPresheaf`, `dirEquivOfPresheaf_restr`, `sigmaDirEquivCarrier` | the presheaf-to-arity direction and the round trips; no operation consumes them |
| The constant functor at a presheaf (`Basic.lean`) | `iotaConstData`, `subsingleton_iotaConstDirection`, `iotaConst` | a generator of the bound's fragment |
| The discrete degeneracy (`Basic.lean`) | `iotaDiscreteShapeEquiv` | it measures `ι` as a generator |
| The `arityVaries` fixture (`Basic.lean`) | `arityVariesData`, `subsingleton_arityVariesDirection`, `arityVaries`, `arityVariesData_B_zero`, `arityVariesData_B_one`, `arityVariesShapeEquiv` | the functor the bound was stated about |
| The shape-type equality (`Functor.lean`) | `iotaPresheafData_A_eq_iotaConstData_yoneda` | its statement names `iotaConstData` |

`Functor.lean` has six declarations; the five that remain are
`arityHomEquivNatTrans`, `objEquivSigmaHom`, `arityPresheafHomAtUB`,
`arityPresheafHomULifted` and `BaseArity.functor`.

Four clusters in those neighbourhoods are retained, seven declarations in all,
each having a consumer outside the removed set: `ArityB`, which
`arityVariesBase` uses for its fibres,
with `subsingleton_arityB`, whose surviving consumer is
`arityVariesBase_dir_ext` and is reached by instance search rather than by
name, so no grep finds it; `iotaPresheaf` with `iotaPresheafData` and
`subsingleton_iotaDirection`, which the worked example takes as its
continuation; `isFunctorial_of_subsingletonDirection`, whose one remaining
consumer is `iotaPresheaf`; and `DomArity.presheaf`, which `famPresheaf` uses.

Removing exactly these empties five `section` wrappers — `Degeneracy` and
`IotaConst` in `Basic.lean`, `Coprod`, `Incompleteness` and `Closure` in
`Codes.lean`. Each wrapper goes with its contents, together with the `variable`
line it scopes, which `docs/rules/lean-coding.md` § Structure and typeclass
patterns requires be removed once unused. Four imports lose their consumers in
the file that carries them.
`Functor.lean`'s
`Mathlib.CategoryTheory.Yoneda` goes with
`iotaPresheafData_A_eq_iotaConstData_yoneda`, `yoneda` occurring in that module
nowhere else and no surviving import implying it; the other three are
`Basic.lean`'s. `Mathlib.CategoryTheory.Discrete.Basic` goes outright,
`Discrete` occurring in that file only in `iotaDiscreteShapeEquiv`.
`Mathlib.CategoryTheory.Category.Preorder` and `Mathlib.Order.Fin.Basic` are
still needed, but by `Codes.lean` — `leOfHom` and the `Category (Fin 2)`
instance at `arityVariesBase`, `Cat.of (Fin 2)` at `deltaCodeVaries` — which
imports neither directly, so both move there rather than being suppressed with
`-- shake: keep`. Both move as `public import`: `arityVariesBase`'s type names
the `Category (Fin 2)` instance, so it is re-exported content, and
`scripts/pre-push.sh` runs `lake shake --add-public`, which distinguishes the
two forms. `scripts/pre-push.sh` runs `lake shake` as a blocking step,
so leaving any of the four in place fails the checklist. The three added
declarations need no import of their own: `Function.LeftInverse` and
`Function.Surjective` are already in `Codes.lean`'s closure. `Reindex` in
`Basic.lean` retains `ArityB`
and `subsingleton_arityB` and keeps its name, which names the
`PresheafPFunctorData.reindex` field rather than the bound; `VaryingWitness`
and `FusedWitness` in `Codes.lean` retain the worked example and merge into
one section named
`WorkedExample`, placed where `FusedWitness` now is, `VaryingWitness`'s four
survivors moving down past the retained `Decoding` section on which `decUnit`
depends through `PshMor`; their present names are vocabulary of the bound and
the split between them was the bound's two witnesses. `ArityB` stays an
`abbrev`: nothing turns on the attribute once its stated rationale goes, and
changing it is a second concern. `Basic.lean`'s numbered claims list is
renumbered from one — nothing references a claim by number once the retired
declarations go — and the sentence framing it as what "the generator
development tests" is rewritten, `iotaPresheaf` being the only generator left
and `Functoriality`, the other survivor, no part of the generator development.

`ShapeArity.const` is the one removal that costs an exposition rather than only
a proof. It was the prototype's only realization of an arity constant over the
output object — Section 6's `Set/I` arity — so after its removal the contrast
§ Why `δ`'s arity varies over the output object draws has no formal counterpart
on the constant side. That is consistent with the *Unelaborated* marking there:
with nothing to compare against, there is nothing the comparison could have
been proved about.

The design carries three declarations the prototype does not yet contain —
`praCodeOf`,
`leftInverse_interp_praCodeOf` and `surjective_interp`, obligation 5's content
in named form. They are the only declarations this document names that the
prototype does not
already contain; every other name cited below is present.

The trim carries its own documentation repair, which no obligation reaches:
obligation 1's clause is about a *ported* declaration's docstring, and the
prototype's module docstrings, its `/-! … -/` section docstrings and the
docstrings of declarations no branch ports are none of those. So the trim
rewrites, in the same step: all three module docstrings, as obligation 4
apportions them; the `Reindex`, `VaryingWitness` and `FusedWitness` section
docstrings; the declaration docstrings obligation 4 lists, `decVariesElt`'s
among them; `CodeShape`'s and
`interp_praCode_interp`'s, which both
assert flatly the claim § The rules and their relation to small induction
recursion marks *Unelaborated*; `ArityB`'s, whose "an `abbrev` so the
`PFunctor` projection reduces to it" describes a projection that goes with
`arityVariesData`, `ArityB`'s surviving consumer indexing by output object
instead; and two plurals that fall to one, `Basic.lean`'s title "and the `ι`
generators" and `isFunctorial_of_subsingletonDirection`'s "every constant
functor here is of that kind", `iotaPresheaf` being the only one left.
Otherwise the interval between the trim and W-b would leave dangling
`` `Foo` `` cross-references on `main` against
[docs/rules/lean-coding.md](../../rules/lean-coding.md) § Documentation.

The three added declarations sit in `Codes.lean`'s `CodeType` section after
`interp_deltaCodeVaries`, at that section's `Code.{u, v} I D` universes, each
with the `/-- … -/` docstring § Documentation requires and each entered in that
module docstring's `## Main definitions` or `## Main statements` as its kind
dictates.

The retirement, the repair and the writing of those three declarations are
assigned to no upstream branch. Obligation 4 ports the three onward to
`Geb/Mathlib/` once they exist, and ports nothing of the other two. They are
the work of the prototype's own
branch, the
one carrying this document, and land before W-a, W-b, W-d and W-e begin: the
declarations retired are ported by no obligation, so no branch's removal clause
reaches them, and obligation 4's docstring clause presupposes that the trim has
already happened. Carrying the bound's vocabulary alongside the ports would put
it on `main` unconsumed, against
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost.

The prototype at `Geb/Internal/PresheafIRProto/` is the source this document
transcribes. It compiles, is linted, and is audited by
`GebMeta.detectNonstandardAxiom`; every declaration cited below is
`Classical.choice`-free except where noted. Where this document and the
prototype's elaborated content disagree, the prototype is right; its prose
carries no such authority. Those three properties are asserted of the
prototype as it stands, so they do not yet cover `praCodeOf`,
`leftInverse_interp_praCodeOf` and `surjective_interp`; establishing them
there, `Codes.lean` not being on `GebMeta.classicalAllowedModules`, is part of
the prototype branch's acceptance. The two transient handoffs
`docs/superpowers/specs/2026-07-30-presheaf-pra-handoff.md` and
`2026-08-02-presheaf-pra-codes-handoff.md` predate this document's current
state and describe rules, obligations and branches it no longer has; where they
disagree with it, this document governs, and they are removed with it.
Claims marked *Inference, not elaborated* or
*Unelaborated* are not elaborated there; the first follows from what the
prototype elaborates, though no declaration states it, and the second is not
established here at all — asserted outright, or imported from a source that is
named but not formalized. Every other claim names the declaration
that establishes it, with three classes of exception, each flagged where it
arises: readings of a construction, backed by structure fields rather than by
theorems (§ Stage 1: morphisms and the representation theorem, fact 4);
the discrete analogues named in § Definitions: transcription or novel's
`Status` cells, no one of which is an elaborated identification;
and statements about ambient category theory or about mathlib's contents,
which are about neither this development nor the literature it transcribes —
§ Stage 1: morphisms and the representation theorem, fact 2's appeal to Yoneda
in any locally small category, § Motivation's first bullet on presheaves over
the walking arrow, § The rules and their relation to small induction
recursion's aside that `y j₀` is terminal exactly when `j₀` is, § The setting
is indexed induction-recursion, not induction-recursion's reading of a
discrete fibration as a presheaf and its naming of the mathlib composite that
obligation 6 builds from, and the same composite where obligation 6 repeats
it.

The prototype is not deliverable content. Each branch removes the part of it
that branch ports, rather than the whole surviving until the last branch. W-a
and W-b are independent in their deliverables but both edit
`Geb/Internal/PresheafIRProto/Basic.lean` and
`Geb/Internal/PresheafIRProto/Functor.lean` — W-a removing
`arityHomEquivNatTrans` and `objEquivSigmaHom` from the latter, W-b the
`BaseArity.functor` beside them — so
whichever lands second rebases over the other's edits: after W-a and W-b, what
remains is the retained derivation below. Removal alone does not leave it
buildable. Most of it names declarations the ports move and rename —
`arityPresheafHomAtUB` and
`arityPresheafHomULifted` name `arityPresheaf`; the whole domain-level warm-up
names `objEquivSigmaArityHom`, `ArityHom` and the four shared `ArityHom`
declarations — so each of W-a and W-b also rewrites the retained remainder
against the names it has just established in `Geb/Mathlib/`, and the prototype
gains imports of the new modules, which `Geb/Internal/` is permitted. Only
`SliceHom`, `sliceHomApp` and `Functoriality` stand free of both ports; the
`ObjFib` / `objFibRestr` / `objFibMap` layer is not ported either but W-a
deletes it: its consumers are the representation theorem's own chain, which
W-a restates against `objPresheaf` and `mapPresheaf`, so they go together.
`BaseArity.functor` is ported by obligation 4 into
W-b's allowlisted module. Whichever of W-d and W-e lands last removes the
remainder
together with this document, the `TODO.md` § In progress entry for this
workstream, whose markdown link and `Geb/Internal/PresheafIRProto/` path both
dangle once the prototype is gone — with the `## In progress` heading above
it, that entry being its only child, and the heading's doctoc line — the two
transient handoffs § Scope of this
document names, any plan written for a branch of this workstream, the
directory index
`Geb/Internal/PresheafIRProto.lean`, `Geb/Internal.lean` — whose sole import is
that index, leaving it empty — the `public import Geb.Internal` in `Geb.lean`,
the `Geb.Internal.PresheafIRProto.Functor` entry in
`GebMeta.classicalAllowedModules`, the `Geb/Internal/` structure bullet in
`docs/index.md`, which describes a directory that is gone — the clause naming
`GebTests/Internal/` sits inside the `GebTests/` bullet and survives — while
`CONTRIBUTING.md` § Repo structure, `docs/rules/upstream-eligible.md` and
`scripts/lint-imports.sh` state the same subtree policy and are left alone,
the policy outliving this one directory, and the two module-docstring mentions
of
`Geb.Internal` — a bullet in `Geb.lean`, a clause in `GebTests.lean` —
`GebTests/Internal/` itself surviving as the axiom-linter fixtures. That last
removal is an assignment rather than an instance of the per-branch rule above:
W-d and W-e port nothing out of the prototype, so the rule leaves them nothing
to remove, and what remains has to fall to someone. W-d
and W-e are mutually unordered, so either may land last and which does is
not determined in advance, and the removal is a condition on the last rather
than an assignment to a named branch. Carrying the
whole prototype alongside its port would define the same declarations twice on
`main`, against [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost.

It also retains steps of the derivation that the obligations do not port, and
which exist to record how the design was reached rather than to be delivered:
the domain-level warm-up (`DomHom`, `DomNatFamily`, `domHomEquivNatFamily` and
their lemmas), the `ObjFib` / `objFibRestr` / `objFibMap` layer, which
duplicates `objPresheaf` and `mapPresheaf` on the nose and is retained only
while the representation theorem is stated against it — obligation 1 restates
that chain and deletes the layer — the slice-level morphism formula (`SliceHom`,
`sliceHomApp`),
`Functoriality`, the universe-formability
demonstrations in `Functor.lean` (`arityPresheafHomAtUB`,
`arityPresheafHomULifted`), and the small computation check
`domHom_eq_pi_sigma_arityHom`. None is reachable from the code system. The
worked example is not among them: obligation 4 ports it, and states there what
it is for. Within the domain-level
warm-up, whose `DomHom`, `DomNatFamily` and `domHomEquivNatFamily` the
previous paragraph already places, the line
falls thus: `idArityHom`, `natTransOfArityHom`,
`postcompArityHom` and `map_symm_arityHom` are shared with the `PshHom` layer
and are ported by obligation 1; `idElt`, `map_idElt`,
`objEquivSigmaArityHom_idElt`, `domHomSigma`, `domHomFamily`,
`domHomFamily_symm` and `domHomEquivNatFamily` are warm-up only and are not.

## The rules and their relation to small induction recursion

The code system has two rules. What decides the count is which side is
primitive. `IR I O` is the primitive notion in
[HancockMcBrideGhaniMalatestaAltenkirch2013]: the functors it denotes are
reached only through its rules, so `ι` and `σ` have to generate the shape data,
and the correspondence with dependent polynomial functors is a theorem (its
Lemma 1). Here the functors are
the primitive notion — `PresheafPFunctor` is a structure, built and proved
functorial before any code exists — so the codes can take one as a leaf, and
the correspondence is definitional rather than earned.

| Rule | Small `IR` | Here | Status |
| --- | --- | --- | --- |
| `ι`, `σ` | generate the shape data: `ι` takes `o : O`, denoting `o' ↦ (o' = o)`; `σ` takes `S : Set` and a family `K : S → IR I O`, denoting a coproduct | absent as rules. The leaf takes a `PresheafPFunctor (el(D)) 𝔹` outright | `praCode`; `interp_praCode` folds it back unchanged |
| `δ` | takes `B : Set` and a continuation `(B → I) → IR I O`, one map serving as both the directions' labelling and their decoding | takes a `BaseArity 𝕀 𝔹` in the same directions role, with functorial output-indexing; that each `fam j` is a discrete fibration is what the Status cell records as confirmed; one subcode over `el(decPresheaf …)`, the decodings summed | Confirmed that the arity datum is a presheaf on `I`, functorially in the output: `DomArity.presheaf` and `BaseArity.functor`. That this is [nLabParametricRightAdjoint]'s two-sided discrete fibration is *Unelaborated*, the notion being that source's and formalized nowhere here; see § The setting is indexed induction-recursion, not induction-recursion. `interp_deltaCode` |

The principle governing `δ`'s generalization is the same one: replace equality
by a morphism, `Hom(x, y)` being `x = y` in a discrete category.
*Unelaborated*: that the rule therefore collapses to its small-IR counterpart
over a discrete base — no declaration bears on it and no source is offered for
it. Open question 4 leaves that degeneration open.

The leaf has three consequences, the first two of them costs.

First, the interpretation is surjective on objects by construction, so the
completeness question the generated presentation raises does not arise
(obligation 5, discharged). The mathematical content moves rather than
disappears, but not into `δ`: `delta` is a composite of `sigmaPsh` and
`adjoinArity` over `decPresheaf` and `decArity` and proves no functor law of
its own, as § The two rules and their semantics records. The content is in
`sigmaPsh` and `adjoinArity` together with the decoding layer `decPresheaf` and
`decArity`, and in their laws; what `delta`'s type adds is the
statement that they compose to an operation on presheaf p.r.a. functors — a
functor over `el(decPresheaf A hA D)`
in, one over `𝔹` out.

Second, `δ` is redundant for object coverage. `interp_praCode_interp` states it
on the nose: every code has the interpretation of a one-node code, so `δ` adds
no functor the leaf does not already supply. *Unelaborated*: that
a code therefore carries a derivation and nothing else, so that the code type
is a presentation rather than a syntax — the sentence that follows says why the
elaborated content does not reach it. What is proved is an equality of
interpretations; open question 6 records that the two codes are not known to
differ, and for a `pra` code they do not. *Inference, not elaborated*: a
category of
codes whose morphisms were defined as morphisms of interpretations would be
equivalent to the presheaf p.r.a. functors by construction, and the equivalence
would assert nothing. The prototype constructs no category of codes, so this is
a reading rather than a result; what it fixes is obligation 7's shape, which
must define its morphisms by recursion over the rules and then prove the
bijection, not adopt it as the definition.

Third, the shape of the two rules is what a restricted leaf would reuse.
Admit every presheaf p.r.a. functor and coverage is trivial; admit a restricted
class — representables, or coproducts of representables — and closure under `δ`
is a question again. This design does not pose it, and carries no vocabulary
for stating it; open question 7 records the parameterization that posing it
would need.

The reuse is of the rules' shape, not of the artifact. `CodeShape` takes no
leaf parameter: its first summand is `PresheafPFunctor (el(D)) 𝔹` outright,
so restricting the leaf replaces that summand, hence `codePFunctor`, hence
`Code` and `interp`. What carries over unchanged is the `δ` summand,
`codeAlgOn`'s `δ` case, and the fold. Making the leaf a parameter — a predicate
on `PresheafPFunctor (el(D)) 𝔹` whose subtype is the first summand, the
present system being that predicate at `True` — would let one code type carry
both, and is recorded as open question 7 rather than built, nothing yet
consuming the general form.

`iotaPresheaf`, `sigmaPsh` and `adjoinArity` sit beside the two rules without
being rules. `iotaPresheaf j₀`'s shape type is the total space
`Σ j', (j' ⟶ j₀)` of the representable. *Inference, not elaborated*: that its
shape presheaf is `y j₀`, which no declaration states. Small induction
recursion's `ι` does two jobs that a discrete base conflates — the pointed
generator, and the terminal foot a `σ` chain needs to build an arbitrary shape
set — and over a category `y j₀` need not be the terminal presheaf. (A
statement about presheaves in general, not about this development: `y j₀` is
terminal exactly when `j₀` is.) It is retained as the continuation of the
`deltaVaries` worked example and for that reading; no rule names it.

Two facts recur across the confirmations and are stated once here rather than
at each site. First, a total space costs one universe, a family of fibres
indexed by the base being larger than either: `Interp`'s shape universe is
`max u v` rather than `u`. *Inference, not elaborated*: that admitting the
representables into the leaf is what costs it, `iotaPresheaf`'s shape type
being a hom-family's total space at `max uJ vJ` where a bare output-object
index sits at `uJ`, which is read off the two shape types and stated by no
declaration. Open question 1
records what a leaf restricted below the representables would save. Second,
the boundary between the choice-free core and the
`GebMeta.classicalAllowedModules` wrapper falls in one place — writing `⟶`
between two objects of a functor category, or `⥤` into one, invokes
`CategoryTheory.Functor.category`, which depends on `Classical.choice`, where
the corresponding bare `NatTrans` or unbundled data does not. That is why
`arityHomEquivNatTrans`, `objEquivSigmaHom` and `BaseArity.functor` are in
`Functor.lean` while `reindexHom` and `ArityHom` are not.

## Motivation

The repository's existing code system, `IndRec.IR I O`, denotes functors
between free coproduct completions of discrete index types. Each functor it
denotes preserves identities and composition (`IR.interpMor_id`,
`IR.interpMor_comp`) — a statement about the denoted functors, not about the
code-level map; no `⥤` packaging of it is built. One capability it lacks, and
one property that the `Fam(C)`-based
positive inductive-recursive definitions of
[GhaniNordvallForsbergMalatesta2015] lack, motivate the generalization to
presheaf bases. `IR I O`'s own code-level interpretation is full and faithful —
Theorem 3 of [HancockMcBrideGhaniMalatestaAltenkirch2013], present here as
`IR.interpHomEquiv` — so the second point is about the `Fam(C)` generalization,
not about `IR I O`:

- A statement of ambient mathematics, per § Scope of this document's third
  exception class — the prototype constructs no initial algebras (§
  Non-goals) and no walking-arrow endofunctor. Only one of the two index sets
  varies under iteration. In the endofunctor case the initial algebra generates
  a type together with a decoding into a fixed type. A presheaf on the
  walking arrow is a function between two sets, so an endofunctor there varies
  both sets and the map between them at once — which is what an
  inductive-inductive definition is.
- *Unelaborated* — the paper asserts no impossibility; Remark 3.4
  places `Hom(x,y) = ⟦x⟧ → ⟦y⟧` at one end of a range of admissible morphism
  collections, and Section 2 records only that its own choice loses the
  property, adding that it "is not an essential property". That nothing short
  of the simultaneous definition recovers it over `Fam(C)` is this document's
  reading. The prototype argues the loss concretely rather than from Remark
  3.4: by Theorem 2.4 of [GhaniNordvallForsbergMalatesta2015] the `δ`
  interpretation's coproduct is indexed by set maps `A → X`, whereas by its
  Definition 2.2 a `Fam(C)`-morphism carries `C`-morphism data that index does
  not, so the interpretation is not a coproduct of `Fam(C)`-representables.
  Full and faithfulness of the interpretation is not available over `Fam(C)`
  without defining the interpretation simultaneously with the codes. Section 2
  of [GhaniNordvallForsbergMalatesta2015] records that the characterization of
  the `δ` interpretation as a left Kan extension fails for non-discrete `C`;
  its Conclusions and Future Work section lists recovering that
  characterization as future work, and separately records as an open problem
  whether the definable functors are closed under composition. Remark 3.4 of
  the same paper offers the alternative — morphisms `Hom(x,y) = ⟦x⟧ → ⟦y⟧`,
  full and faithful by definition — at the cost of defining `⟦−⟧`
  simultaneously with the codes.

Two maps are called an interpretation in this document, and the property lost
above attaches to only one of them. The code-level `⟦−⟧` sends a code to a
functor; the functor-level one sends a `PresheafPFunctor`'s data to the functor
`PresheafPFunctor.functor` it presents. What
[GhaniNordvallForsbergMalatesta2015] § 2 records as lost is full and
faithfulness of the code-level map, that paper's `⟦−⟧ : IR(D) → (Fam|D| →
Fam|D|)`.

Stage 1 addresses the functor level: `pshHomEquivNatFamily` classifies the
natural families between two presheaf p.r.a. functors by shapes-forward
arities-backward data, structurally, from the fact that such a functor is by
construction a coproduct of representables. Obligations 2 and 3 carry that
hom-set bijection to full and faithfulness of `PresheafPFunctor.functor`. That
is not the property § Motivation opens with; it is the input the code-level
statement needs, since a code-level hom-set bijection has to land somewhere,
and obligation 7 is where the code-level property is discharged.

## Stage 1: morphisms and the representation theorem

Settled up to the category structure and the identification recorded as
obligations 2 and 3. `Geb/Internal/PresheafIRProto/Basic.lean` carries it,
choice-free; `Functor.lean` carries what depends on `Classical.choice` through
`CategoryTheory.Functor.category` — `BaseArity.functor` among them, per
§ Stage 2: the code system. They are `arityHomEquivNatTrans` and
`objEquivSigmaHom`, which write `⟶` between objects of a presheaf category;
and the two universe-formability demonstrations `arityPresheafHomAtUB` and
`arityPresheafHomULifted`, which do the same.

| Declaration | Content |
| --- | --- |
| `shapePresheaf`, `arityPresheaf` | the shape presheaf `T₁` and each arity `E(a)`, as functors |
| `ArityHom` | the unbundled presheaf hom `E(a) ⟶ Z` |
| `objEquivSigmaArityHom` | the interpretation is a coproduct of representables, at arbitrary `uZ` |
| `DomHom`, `domHomEquivNatFamily` | the representation theorem, domain level |
| `ShapeHom`, `PshHom` | the morphism type: shape map forward, arity maps backward, `reindexCompat` |
| `idPshHom` | the identity morphism, `reindexCompat` included |
| `pshHomFib_objFibRestr` | the action commutes with the `J`-restriction |
| `pshHomEquivNatFamily` | the representation theorem in full |

Four facts follow. The first and third name the declarations that establish
them; the fourth is a reading of the construction, backed by structure fields
rather than by theorems, and the second is a statement of ambient mathematics:

1. Shape-map-forward and arity-map-backward data classify the natural families
   between presheaf p.r.a. functors: `pshHomEquivNatFamily` is a bijection
   `PshHom F F' ≃ PshNatFamily F F'`. It is not definitional: its inverse is
   `natFamilyPshHom`, whose `reindexCompat` field is discharged by
   `natFamily_generic` and `objFibMap_eq_objFibRestr_apply`; the equivalence's
   own `left_inv` rests on `natFamilyArity_pshHomFamily` and `PshHom.ext`, the
   lemma `PshHom`'s `@[ext]` attribute generates. Two
   steps separate it from full and faithfulness of the interpretation, both
   obligations rather than results: `PshNatFamily` is an unbundled proxy and is
   nowhere related to `PresheafPFunctor.functor`'s natural transformations
   (obligation 3), and fullness and faithfulness are properties of a functor,
   so they need composition on `PshHom` carried across the bijection
   (obligation 2).
2. The classification is available because the interpretation is a coproduct of
   representables (`objEquivSigmaArityHom`), not because of any property of the
   ambient category: Yoneda holds in any locally small category.
3. Unbundling yields constructivity, and universe polymorphism where the
   statement admits it. `objEquivSigmaArityHom` holds at arbitrary `uZ`; its
   bundled wrapper `objEquivSigmaHom` is pinned to `uZ := uB`. The Stage 1
   deliverable `pshHomEquivNatFamily` carries the same pinning as the bundled
   version, `PshNatFamily` quantifying only over `Z : Iᵒᵖ ⥤ Type uB`; what
   unbundling buys there is constructivity alone. `objEquivSigmaHom`'s
   restriction comes from requiring the arity presheaf and the input presheaf
   to lie in one functor category, which is what `⟶` demands and what
   introduces `Classical.choice`. `pshHomEquivNatFamily`'s comes from
   `PshNatFamily`'s own quantification and is choice-free.
4. `PresheafPFunctorData` already is the familial presentation in unbundled
   form. `shapeRestr` gives `T₁` its presheaf structure, `directionRestr` gives
   each `E(a)` its own, and `ReindexNaturality` says exactly that `reindex g a
   : E(shapeRestr g a) ⟶ E(a)` is a presheaf morphism.

## Stage 2: the code system

`Geb/Internal/PresheafIRProto/Codes.lean` carries it, choice-free.

### The setting is indexed induction-recursion, not induction-recursion

`IR I O` collapses two roles that Section 6 of
[HancockMcBrideGhaniMalatestaAltenkirch2013] keeps apart. In `IR.delta B (c :
(B → I) → IR I O)` the map `B → I` is simultaneously the arity's
index-labelling and the decoding of the recursive arguments; in that paper's
`IIR D E` the labelling `i : P → I` is fixed data and the subcodes are indexed
by the decodings `(p : P) → D (i p)`.

The presheaf setting forces the split, and what it forces the arity to be is
fixed by the ambient characterization rather than by this design.
[nLabParametricRightAdjoint] presents the p.r.a. functors between presheaf
categories as the polynomials `I ← E → K → J` in `Cat` in which the last leg `K
→ J` is a discrete fibration and the first two form a two-sided discrete
fibration, the leg into `I` being a fibration and the leg into `K` an
opfibration.

*Inference, not elaborated*: the first condition is this repository's shape
presheaf, `q : A → J` with `shapeRestr` and its two laws being a discrete
fibration over `J`; no declaration states that reading. *Inference, not
elaborated*: the second condition is the arity side, the fibration into `I`
being the presheaf structure carried at each shape and the two-sidedness the
compatibility `reindex` and `ReindexNaturality` impose between that structure
and shape restriction. Nothing here identifies the two presentations; what is
elaborated is only that the arity datum is a presheaf on `I`.

A discrete fibration over `I` is a presheaf on `I` presented by the total space
of its own fibres — not to be confused with the polynomial's `E`, the total
space of directions over shapes — and that is what `DomArity` is: `carrier`,
`proj`, and a contravariant action on the fibres of `proj`. It is the arity at
one shape, occupying the `B`-slot of `adjoinArityData`, where
`ShapeArity.fam` and `BaseArity.fam` supply the parameterization by shape and
by output object; the paper's `P` and `i : P → I` are `carrier` and `proj`, and
the decodings that `δ` turns into shapes are `PshMor`, reaching the shape
presheaf through `sigmaPsh` rather than through the arity. The total-space
presentation is what `adjoinArityData` consumes, needing one type per shape in
its `B`-slot and recovering the `I`-indexing through `r`; `DomArity.presheaf`
is the fibrewise form. The
labelling is therefore code data carrying presheaf structure, which is the
separation `IIR` makes and `IR` does not.

Only the total-space-to-fibrewise direction is retained. The converse and the
round trips stating the two agree were consumed by no operation, and a round
trip could in any case only be stated fibrewise: passing from a presheaf to an
arity raises the carrier's universe from `uB` to `max uI uB`, so the two
presheaves inhabit different functor categories and no isomorphism between them
is formable.

`δ`'s own datum is the output-indexed version: `BaseArity.isFunctorial_fam`
gives each `fam j` its two presheaf laws, `famPresheaf` names the resulting
presheaf on `I`, and `reindexHom` is the morphism of presheaves that
`reindex_naturality` supplies for each output morphism. `BaseArity.functor`
bundles the four as a functor `J ⥤ (Iᵒᵖ ⥤ Type uB)` — the output base to
discrete fibrations over the input base — whose two laws are `IsFunctorial`'s
remaining `reindex_id` and `reindex_comp` clauses.

So the presheaf system generalizes `IIR`, not `IR`: its input side is the pair
`(𝕀, D)` of a base category and a decoding presheaf, and `δ`'s continuation
depends on the decoding, which is `PshMor` — the presheaf reading of Section
6's sections `(p : P) → D (i p)`.

Throughout, `el(−)` is the category of elements in the sense of
[MacLaneMoerdijk1992] Chapter I: objects are pairs `(j, d)` with `d ∈ D(j)`,
and a morphism `(j, d) ⟶ (j', d')` is `g : j ⟶ j'` with `D(g)(d') = d`. That
is `ElObj D` on the nose, `elCategory` giving exactly those homs, so `el(D)`
names the prototype's own base and not its opposite. mathlib's `Elements` of a
presheaf lands in `𝕀ᵒᵖ`, so the corresponding mathlib term is `D.Elementsᵒᵖ`.
*Unelaborated*: that the base category whose presheaves are the
slice `PSh(𝕀)/D` is `el(D)`, which is obligation 6's deliverable and which
mathlib supplies but this development does not, and *Inference, not
elaborated*: that
`ElObj D` agrees with `D.Elementsᵒᵖ`, which nothing compares.

The semantic counterpart of that split is the
equivalence `PSh(𝕀)/D ≃ PSh(el(D))`, marked just above: `IIR D E` interprets
into `Set/ΣD →
Set/ΣE`, and the presheaf analogue of the total-space collapse needs the
category of elements rather than a bare `Σ`. Consequently a presheaf-`IIR` code
over `(𝕀, D)`, `(𝕁, E)` denotes an ordinary `PresheafPFunctor (el(D))
(el(E))`, and the code system's semantics needs no notion beyond Stage 1's.
The prototype uses the category of elements as a base category (`ElObj`,
`elCategory`) but does not construct that equivalence; in mathlib it is the
composite of `overEquivPresheafCostructuredArrow` and
`CategoryOfElements.costructuredArrowYonedaEquivalence`.

### The two rules and their semantics

`Code` is a single unindexed type, fibred over `Cat` by the projection
`codePFunctor.wIndex`; the constructor with a subcode takes an explicit
hypothesis `hK` aligning that subcode's fibre with the slot it fills. The
constructors, with the semantic operation each folds to:

| Rule | Code constructor | Semantics |
| --- | --- | --- |
| leaf | `praCode 𝔹 F` | `F` itself — an arbitrary `PresheafPFunctor (el(D)) 𝔹` at the universes `CodeShape` pins |
| `δ` | `deltaCode 𝔹 A hA K (hK : wIndex K = Cat.of (ElObj (decPresheaf A hA D)))` | `delta A hA D` — adjoin the output-varying arity `A`, the continuation depending on its decoding |

`δ`'s arity is a `BaseArity 𝕀 𝔹` over the raw input base, whose decodings into
`D` it sums. The alternative — a `BaseArity (el(D)) 𝔹` over the
interpretation's own input base, where a direction's label carries its own
decoding value and the coproduct is absorbed into the labelling rather than
appearing as shapes — is not a separate rule. *Inference, not elaborated*: that
it is `adjoinArity` at that arity's `BaseArity.pullback`, which no declaration
constructs. `adjoinArity` is
not `δ` at all: it sums over no decodings and so carries no recursion, and it
is a semantic operation for the same reason `sigmaPsh` is. (That it is
reachable through the leaf does not distinguish it, every presheaf p.r.a.
functor being so reachable, `delta` included.) That absorption is the collapse
`PSh(𝕀)/D ≃ PSh(el(D))` seen from the arity side. `CodeShape` depends on `D`
through its leaf summand, whose functors are over `el(D)`; the `δ` summand
names no `D`, `CodeNext` being where `D` enters the continuation base.

`delta` decomposes as `sigmaPsh (decPresheaf A hA D) ∘ adjoinArity`: the inner
factor adjoins the directions, and the outer takes the coproduct over the
decodings, `decPresheaf` at `b` being the decodings at `b`. That coproduct is
the shape half of [DybjerSetzer1999]'s `δ` under the regrouping
`Σ_{g : P → X} ⟦F (f
∘ g)⟧ = Σ_{d : P → D} (sections of f over d) × ⟦F d⟧`. *Unelaborated*: the
regrouping itself, which is stated here and in `delta`'s docstring and which no
declaration establishes as an equation. `adjoinArity` alone is not `δ` and
is named accordingly; it leaves the shapes untouched.

*Implementation note.* No operation's `A` field grows when a coproduct of shape
presheaves is taken, which might read as no change at all. A shape presheaf
here is a total space `A` fibred by `q` (`SlicePFunctor.Shape` is the fibre of
`q`), so a coproduct over the fibres of a discrete fibration is a re-fibring of
the same total space rather than an enlargement: `sigmaPsh` leaves `A`
untouched,
and *Unelaborated*, the declaration that carried it having been the retired
`elSliceEquiv`: that `Σ_{s ∈ S j} F.Shape ⟨j, s⟩` and `F.A` over `ElObj S` are
the same total space. A coproduct indexed by a bare type rather than by the
fibres of a
fibration would enlarge `A`; no operation here takes one.

`δ`'s continuation sits over a category of elements the arity determines, so
the rule has exactly one subcode slot and the leaf has none. The interpretation
is `interp`, the fold of `codeAlg` over the W-type; its two computation rules
`interp_praCode` and `interp_deltaCode`, one per constructor, are definitional,
as is the corollary `interp_praCode_interp` about arbitrary codes.
`interp_fst` records that a code's index is the base its interpretation lands
in.

Every operation and generator named in this document is a `PresheafPFunctor` —
that is, all seven functor laws are proved, not assumed: `iotaPresheaf`,
`sigmaPsh`, `adjoinArity` and `delta`, together with the worked example
`deltaVaries`. `delta` is a composite of the others and inherits their laws
rather than needing new ones, as `deltaVaries` inherits `delta`'s. Of all of
them only `delta` is named by a code rule; the rest are semantic operations or
the example's base.

### Why `δ`'s arity varies over the output object

Section 6 of [HancockMcBrideGhaniMalatestaAltenkirch2013] gives `δ` an arity
that is an object of `Set/I`, carrying no dependence on the output object. `δ`
here takes a `BaseArity 𝕀 𝔹`, whose fibre may differ from one output object to
the next, and `arityVariesBase` is the worked instance: over the walking arrow,
an arity inhabited over `1` and empty over `0`, so that reindexing along
`0 ⟶ 1` is the map out of the empty type.

*Unelaborated*: that this is a proper generalization — that no rule whose arity
is constant over the output object denotes such a functor. No declaration
states it. Establishing it would need a code type for the constant-arity rules,
an induction over it, and a property separating the two classes of functor,
none of which this design builds or carries. The generalization is therefore a
design decision recorded here with a worked instance, not a theorem, and
§ Scope of this document records the same.

`ShapeArity` is the form `adjoinArity` consumes: an arity varying over the
shape presheaf, carrying a family over `F.A` with a reindexing along
`shapeRestr`. *Inference, not elaborated*: that this is the unbundled data of a
functor `el(T₁) ⥤ (Iᵒᵖ ⥤ Type)`; `BaseArity.functor` bundles the
output-indexed version, and `ShapeArity` has no counterpart.

### The decoding-dependent continuation

`delta` carries an arity varying over the output object and a continuation
depending on the decoding, both by construction: the arity it takes is a
`BaseArity`, and the continuation is summed over `decPresheaf`. That both are
present at once is therefore definitional. *Unelaborated*: that
the output-varying arity stays effective once the decoding-dependent
continuation is fused onto it — that the fused rule reaches functors the
constant-arity one does not. The declaration that checked it was a
`HasBijectiveReindex` witness and is removed with that family. Three steps,
none of them a new operation:

1. The decodings of an output-varying arity form a presheaf on the output base
   (`decPresheaf`), restriction along `g : b' ⟶ b` being precomposition with
   `A.reindex g`; its functor laws are `A`'s reindexing laws.
2. Over `ElObj (decPresheaf A hA D)` every object carries its own decoding, so
   the adjoined arity is an ordinary `BaseArity` there (`decArity`,
   `isFunctorial_decArity`), and `BaseArity.pullback` turns it into the
   shape-indexed arity `adjoinArity` consumes.
3. `sigmaPsh` pushes the result forward to the output base.

`deltaVaries` is `delta` at that arity, its continuation the constant functor
at a representable; `deltaCodeVaries` is a code whose interpretation is that
functor, and `interp_deltaCodeVaries`, itself definitional, is the check that
the rule and its code compute. *Inference, not elaborated*: that every fibre of
`termPsh` is a singleton, so that `decUnit` is the only decoding into it —
`termPsh.obj` is `PUnit` definitionally and `PshMor`'s only data field is
`app`, so it follows and no declaration states it. The example does not rest
on it.

### Why no inductive-inductive definition is needed

A code's `δ` cannot mention its subcode's shapes, so its arity is indexed by
output objects (`BaseArity`) and pulled back along the shape-output map
(`BaseArity.pullback`, `BaseArity.isFunctorial_pullback`). The transport that
the pullback carries is the reason `ShapeArity` is indexed by shapes rather
than by output objects: `adjoinArityData` is then free of it.

Nor does the recursion force mutuality. That `δ` has a single subcode slot at
a base its arity determines is elaborated — `CodeDir` gives its direction type
as `PUnit`, `CodeNext` the base, and `deltaCode` takes the one subcode. That a
continuation so presented is equivalent to a family of codes indexed by
decodings is the collapse of § The setting is indexed induction-recursion, not
induction-recursion again, and carries that section's *Unelaborated* mark.

The code type is the W-type of a slice polynomial functor on `Cat`
(`codePFunctor`, `Code`), not an inductive family. `Cat.{v, u}` is closed under
the continuation step, `CodeNext` being the witness: the category of elements
of a presheaf valued in `Type u` over a base in `Type u` is again in `Type u`
(`ElObj`), with homs a subtype of the base's (`elCategory`). The fibre is
therefore recovered by a projection out of an ordinary W-type, and nothing is
defined simultaneously with anything else. This answers negatively the question
of whether codes must be encoded to work around Lean's lack of
inductive-inductive types, and it avoids the route Remark 3.4 of
[GhaniNordvallForsbergMalatesta2015] describes and declines.

## Definitions: transcription or novel

Per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature when
transcribing.

No discrete analogue named in a `Status` cell below is an elaborated
identification: each names either the declaration occupying the corresponding
role over a discrete base or the published result stating it, and nothing
relates the two. The `iotaPresheaf` row is
the case where the gap is widest: nothing identifies it with the discrete-base
`ι`, the two being at different universe instantiations.

| Definition | Status |
| --- | --- |
| `PshHom`, to be named `PresheafPFunctor.Hom` upstream | Novel in this repository. The shapes-forward arities-backward form is Definition 7 of [HancockMcBrideGhaniMalatestaAltenkirch2013] (morphisms of indexed containers) in the discrete case; its Definition 6 is the dependent-polynomial presentation of morphisms; the `r`/`q` naming this repository follows comes from the `(r, t, q)` triples of its Definition 1, this repository absorbing `t` into the dependent family `B` |
| The action of a `Hom`, and its naturality | Novel |
| The representation theorem (`pshHomEquivNatFamily`) | Novel at this level. Its discrete analogue is Theorem 1 of [HancockMcBrideGhaniMalatestaAltenkirch2013] (which that paper states with a bracketed reference to Theorem 2.12 of the 2010 arXiv version of [GambinoKock2013]; the bracket number differs between the proceedings and the preprint, and whether the numbering 2.12 survives into the 2013 journal article is unchecked), together with Definition 7 for the indexed-container form. Theorem 3 of the same paper is the code-level statement, present as `IR.interpHomEquiv`, and is the analogue of proof obligation 7, not of this |
| Identity, composition, and the category structure on `Hom` | Novel |
| The `δ` code rule | Transcription of Section 6 of [HancockMcBrideGhaniMalatestaAltenkirch2013], generalized from families to presheaves: its sections `(p : P) → D (i p)` become `PshMor`, and the family of subcodes over them becomes one subcode over their category of elements. The further generalization of the arity from an object of `Set/I` to one varying over the output object is novel; § Why `δ`'s arity varies over the output object records that no declaration establishes the separation from the constant-arity rule, and marks the claim *Unelaborated* |
| The leaf code rule `praCode` | Novel. It has no small-`IR` counterpart, `IR I O` having no primitive notion of the functors it denotes to inject; the closest statement in [HancockMcBrideGhaniMalatestaAltenkirch2013] is its Lemma 1, which constructs by hand what `praCode` takes as data |
| `iotaPresheaf` — the constant functor at a representable | Transcription of `ι : O → IR I O` as a semantic operation, generalized by replacing equality with a morphism: `ι`'s interpretation sends `o'` to `o' = o`, and `iotaPresheaf j₀`'s shape type over `j'` is `Hom(j', j₀)`; § The rules and their relation to small induction recursion marks the presheaf-level reading as inference. It is not a code rule; it is retained as the continuation of the `deltaVaries` worked example. No declaration identifies it with the discrete-base `ι` (`IR.toSlicePFunctorIota`, in a module the prototype does not import), the two being at different universe instantiations |
| Indexing the code type by a base category, with `δ` replacing it by a category of elements | Novel |
| `adjoinArity`, adjoining an arity | Novel at this level; the discrete analogue is `SliceDomPFunctor.prodSlice` against a representable |
| `sigmaPsh`, the base change along `ElObj S → J` | Transcription of Section 6's `σ` as a semantic operation, generalized from a family over a set to a base change along a category of elements; it is not a code rule. Its discrete analogue in this repository is not identified: over a discrete base the category of elements is discrete, so the base change is expected to collapse into `SlicePFunctor.coprod`, but open question 4 leaves that degeneration open and nothing establishes it |
| `DomArity` — a presheaf on `I`, unbundled | Novel presentation of a standard object, chosen so its directions plug into a `PresheafPFunctorData`'s without transport |
| `ShapeArity` — the arity a `δ` adjoins, varying over the shape presheaf | Novel; it carries a family over `F.A` with a reindexing along `shapeRestr`. § Why `δ`'s arity varies over the output object marks its reading as a functor `el(T₁) ⥤ (Iᵒᵖ ⥤ Type)` an inference, there being no `ShapeArity.functor` to `BaseArity.functor`'s pattern |
| `BaseArity`, `BaseArity.pullback` — the arity indexed by output objects, and its pullback along `q` | Novel |
| `DomArity.presheaf`, `BaseArity.famPresheaf`, `BaseArity.reindexHom`, `BaseArity.functor` — the fibrewise form of an arity, the presheaf it gives at each output object, the morphism each output morphism induces, and those three with `isFunctorial_fam` bundled as a functor `J ⥤ (Iᵒᵖ ⥤ Type uB)` | Novel presentations of a standard identification. The content is that a `DomArity` is a discrete fibration over `I`, hence a presheaf on it, and that `BaseArity` is that functorially in the output — the arity side of [nLabParametricRightAdjoint]'s two-sided discrete fibration, which § The setting is indexed induction-recursion, not induction-recursion marks *Unelaborated*. `functor` writes `⥤` into a functor category and so is in `Functor.lean` |
| `ElObj`, `elCategory` — the category of elements as a base category | Transcription of the category of elements, [MacLaneMoerdijk1992] Chapter I. § The setting is indexed induction-recursion, not induction-recursion marks its agreement with mathlib's `S.Elementsᵒᵖ` an inference. It is written out rather than reused to avoid `Opposite` transport, and obligation 4 revisits the choice |
| `CodeShape`, `CodeDir`, `CodeNext`, `codePFunctor`, `Code` | Novel. Indexing by a base category, with `δ` replacing it by a category of elements, has no counterpart in the cited literature; nor does a leaf that injects the denoted functors, which is what `CodeShape`'s first summand is |
| `codeAlgOn`, `codeAlg`, `interp` — the interpretation | Novel at this level; the discrete analogue is `IR.interpObj` |
| The code-level morphism type (obligation 7) | Novel at this level; the discrete analogue is `IR.Hom` |
| The p.r.a. formula `T Z ≃ Σ a, Hom(E(a), Z)` (`objEquivSigmaArityHom`, bundled as `objEquivSigmaHom`) | Transcription: the familial presentation of a parametric right adjoint, [Weber2007]; novel only in being stated with the hom unbundled |
| `shapePresheaf`, `arityPresheaf` — `T₁` and each `E(a)` as functors | Transcription: the familial presentation of [Weber2007] |
| `SliceHom`, `sliceHomApp` — the slice-level morphism formula | Transcription of Definition 7 of [HancockMcBrideGhaniMalatestaAltenkirch2013] at a discrete base; retained in the prototype as the derivation and ported by nothing |
| `Functoriality` — the witness family attached over pre-codes | Novel; retained in the prototype as the derivation and ported by nothing |
| `ArityHom` — the unbundled presheaf hom `E(a) ⟶ Z` | Novel presentation of a standard object, chosen to avoid the functor category's `Classical.choice` |
| `ShapeHom` — the unbundled presheaf hom `T₁ ⟶ T₁'` | Novel presentation, as `ArityHom` |
| `ObjFib`, `objFibRestr`, `objFibMap` — the output presheaf's fibres and their two actions, unbundled | Novel presentation. They are `objPresheaf`'s and `mapPresheaf`'s components; obligation 1 states the interpretation against those directly |
| `PshNatFamily` — the natural families a `PshHom` represents | Novel; obligation 3 relates it to natural transformations of the interpreted functors |
| `DomHom`, `DomNatFamily` — the domain-level morphism data and its natural families | Novel. The domain-level warm-up for `PshHom`, superseded by it; retained in the prototype as the derivation and ported by nothing |
| `sigmaLiftHom` — the morphism of elements a `σ` restricts along | Novel |
| `elEqToHom` — the transport in the category of elements with a definitionally reducing underlying morphism | Novel; a presentational device, `elEqToHom_eq` identifying it with `eqToHom` |
| `Interp` — the interpretation's target, a functor paired with its base | Novel |
| `arityHomEquivNatTrans` — the bundling isomorphism `ArityHom ≃ (arityPresheaf ⟶ Z)` | Novel; it is the elaborated form of the `ArityHom` row's identification |
| `arityPresheafHomAtUB`, `arityPresheafHomULifted` — the universes at which the bundled hom is formable | Novel; retained in the prototype as the derivation and ported by nothing |
| `genericFib`, `idElt`, `ofSigmaFib`, `reindexArityHom`, `pshHomSigma`, `domHomSigma` — the fibre-level intermediates of the representation theorem | Novel presentations; those the theorem needs travel with obligation 1, the rest are retained derivation |
| The unbundled-data layers and their law predicates — each `…Data` beside the structure it underlies (`iotaPresheafData`, `adjoinArityData`, `sigmaPshData`), the three `IsFunctorial` predicates (`DomArity.IsFunctorial`, `ShapeArity.IsFunctorial`, `BaseArity.IsFunctorial`), `DomArity.Dir`, and the component maps the representation theorem is assembled from (`ofArityHomElt`, `idArityHom`, `natTransOfArityHom`, `postcompArityHom`, `natFamilyPshHom`, `pshHomFamily`, `natFamilyShape`, `natFamilyArity`) | Novel presentations, each carrying no mathematics beyond the structure it splits: the data/law separation is the repository's standing pattern for keeping a construction choice-free, not a claim about the objects |
| The transport and law lemmas the ports carry — the five `σ` laws with their nine transport lemmas, `BaseArity.isFunctorial_pullback` with `reindex_eqToHom`, `reindex_comp_apply` and `reindex_cast_shape`, `elCategory_id_val`, `elCategory_comp_val`, `elCategory_eqToHom_val`, `elEqToHom` with `elEqToHom_eq`, `adjoinArity_cast_inl` and `_cast_inr`, `fibreArity_restr_val`, `isFunctorial_fibreArity`, `decArity_reindex_val` and `isFunctorial_decArity` | Novel, and proof-engineering rather than mathematics: each discharges a transport that the chosen presentation introduces, and none states anything about the objects that the structure it serves does not already carry |
| `ArityB`, `termPsh`, `arityVariesBase`, `decUnit`, `decVariesElt`, `deltaVaries`, `deltaCodeVaries` — the worked example of § The decoding-dependent continuation | Novel. Fixtures, carrying no mathematics beyond the computation they exhibit |
| `PshMor` — a morphism from a `DomArity` to a presheaf, unbundled | Novel presentation; it is the presheaf reading of Section 6's sections `(p : P) → D (i p)` |
| `fibreArity` — the arity a decoding adjoins | Novel |
| `decPresheaf` — the decodings of an output-varying arity, as a presheaf on the output base | Novel |
| `decArity` — that arity, indexed by the elements of `decPresheaf` | Novel |
| `delta` — the `δ` carrying both features. Both are by construction: the arity it takes is a `BaseArity`, and the continuation is summed over `decPresheaf`. `deltaVaries` exhibits an output-varying instance, and no declaration states that the constant-arity case fails to reach it | Novel; it is Section 6's `δ` rule with the arity generalized over the output object, § Why `δ`'s arity varies over the output object marking the separation from the constant-arity rule *Unelaborated* |
| `praCodeOf`, `leftInverse_interp_praCodeOf`, `surjective_interp` — the leaf as a section of the interpretation | Novel. The split-epimorphism form of obligation 5's content: `praCodeOf` is `praCode` uncurried over `Interp`, and the two theorems state that `interp` retracts onto it. The first holds by `rfl`, `Interp` being a `Sigma` and so carrying structure eta; the second is `LeftInverse.surjective` of it |

## Branches

[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape binds one concern
per branch. A fifth branch precedes them and carries no *unproved* obligation,
only the writing of obligation 5's content: the prototype's own, which adds
this document, retires the fifty-two declarations
§ Scope of this document lists, repairs the documentation that retirement
breaks, and adds `praCodeOf` with `leftInverse_interp_praCodeOf` and
`surjective_interp`. Its acceptance is that `Geb/Internal/PresheafIRProto/`
builds, lints and passes `scripts/pre-push.sh` with none of the retired
declarations and no dangling docstring cross-reference. It is downstream-only,
so it has no `Geb/Mathlib/` deliverable and no `docs/index.md` entry.

Of the seven obligations below, obligation 5 is discharged and the
remaining six divide into the four upstream branches. W-e is separate because
no other
branch's deliverable consumes the collapse: it justifies the input-side design,
the no-mutuality argument and open question 2, none of which is code another
branch ports.

| Branch | Obligations | Acceptance |
| --- | --- | --- |
| W-a — Stage 1 upstream | 1, 2, 3 | `PshHom`, its action and the hom-set bijection in `Geb/Mathlib/`, choice-free, with the bundled restatements and the natural-transformation identification in a module on `GebMeta.classicalAllowedModules`; composition and the category structure; and `docs/index.md` entries |
| W-b — Stage 2 upstream | 4 | the semantic operations, the decoding layer, the code type, the interpretation and the leaf's section, in `Geb/Mathlib/`, each new module carrying its `docs/index.md` entry |
| W-d — code morphisms | 7 | the code-level morphism type and representation theorem, in `Geb/Mathlib/`, with `docs/index.md` entries |
| W-e — the collapse | 6 | `PSh(𝕀)/D ≃ PSh(el(D))` in `Geb/Mathlib/`, in a module on `GebMeta.classicalAllowedModules`, with its `docs/index.md` entry |

W-a and W-b depend on nothing; W-d depends on W-a and W-b. W-e depends on
nothing. The branch letters are not renamed: W-c is withdrawn with the bound
it carried, and reusing its letter would make the `TODO.md` history of this
workstream read as though a different branch had been renumbered.

Each acceptance cell's "in `Geb/Mathlib/`" carries the repository's standing
practice for that subtree: a `GebTests/Mathlib/` mirror per new module, which
81 of the 82 existing `Geb/Mathlib/` modules have, the exception being
`Geb/Mathlib/Data/Vector/Scatter.lean`, and which
`GebMeta.classicalAllowedModules`' own docstring describes as the practice for
a module a branch adds to that allowlist ("Feature branches append their own
wrapper module names together with their test parallels"). It is practice
rather than a requirement: the prototype's own allowlisted module has no test
parallel. W-a, W-b and W-e each add
one such module — W-a's carrying obligation 1's `functor`-form corollary, the
two bundled restatements and obligation 3's identification together, and W-b's
carrying `BaseArity.functor`, which writes `⥤` into a functor category — so
each adds one allowlist pair.

`docs/index.md` describes some directories module by module, others by a single
directory bullet, and several — `Data/PFunctor/Presheaf/` and
`Data/PFunctor/IndRec/` among them — by a directory bullet plus per-module
bullets for later additions. A branch adding to a directory that already has a
bullet adds per-module bullets beneath it; a branch creating a directory writes
the directory bullet.

This document is the design record for all four and is removed with the last
of them, which deviates from § Concern shape's per-branch spec lifetime. The
rationale: between branches it presents decisions that are pending, not
superseded, which is what that section guards against. If W-a lands and the
rest are deferred, the deviation is to be resolved by moving the design record
into `docs/` as persistent documentation rather than leaving a spec on `main`.

## Proof obligations

Obligation 5 is discharged, as its entry records; each of the other six is
unproved.

1. **Stage 1 at upstream quality** (W-a). Port `PshHom`, its action, and
   `pshHomEquivNatFamily` from the prototype into `Geb/Mathlib/`, together with
   what they rest on: `shapePresheaf` and `arityPresheaf`, `ArityHom`,
   `ShapeHom`, `objEquivSigmaArityHom` with `ofArityHomElt` and
   `value_ofArityHom`, `reindexArityHom`, `sigmaArityHom_ext`, `idArityHom`,
   `natTransOfArityHom`, `postcompArityHom`, `map_symm_arityHom`, `idPshHom`,
   `PshNatFamily`, the inverse `natFamilyPshHom`, and the round-trip lemmas
   `natFamily_generic`, `objFibMap_eq_objFibRestr_apply`,
   and `natFamilyArity_pshHomFamily`. `PshHom` carries `@[ext]`, so its
   extensionality lemma travels with the structure rather than as a listed
   item. This port is
   dependency-closed on the same grounds as obligation 4's: anything a listed
   item needs travels with it. Port it against the choice-free `objPresheaf`
   and `mapPresheaf` rather than `PresheafPFunctor.functor`, and drop the
   prototype's parallel `ObjFib` / `objFibRestr` / `objFibMap` layer entirely:
   `ObjFib` is `objPresheaf`'s object part at `j.unop` and the two actions are
   `objPresheaf.map` and `mapPresheaf.app` verbatim, so nothing of it survives
   the replacement. W-a deletes that layer from the prototype in the same step,
   rather than leaving it under § Scope of this document's removal rule, which
   retains a declaration only while something consumes it, and the layer's one
   consumer
   is the representation theorem's own chain, which W-a restates. One listed
   item, `objFibMap_eq_objFibRestr_apply`, is stated in the layer's own terms,
   so W-a restates it against `objPresheaf` and `mapPresheaf` and renames it
   accordingly; open question 9 covers the naming. The `functor` form is a
   corollary and belongs in a module
   on `GebMeta.classicalAllowedModules`, together with `arityHomEquivNatTrans`
   and `objEquivSigmaHom`, the prototype's two bundled restatements. The ported
   chain needs `PresheafPFunctor.value_objRestrElt`, which is `private` in
   `Geb/Mathlib/Data/PFunctor/Presheaf/Basic.lean` and which the prototype
   restates locally; this obligation decides between dropping the `private` and
   restating it locally. Docstrings port under the same closure clause as
   terms: a ported declaration whose docstring names a retired or unported
   declaration has that docstring rewritten, `docs/rules/lean-coding.md`
   § Documentation making the docstring and its cross-references part of the
   deliverable.
2. **Category structure** (W-a). Composition on `PshHom` (`idPshHom` already
   supplies the identity), that composition is associative with that identity
   as unit, and that the bijection of obligation 1 carries them to the
   identities and composition of natural transformations. Full and faithfulness
   of the interpretation is delivered by this obligation and obligation 3
   jointly, not by obligation 1: the predicate is not even well-formed until
   obligation 3 identifies `PshNatFamily` with natural transformations. Depends
   on obligation 3.
3. **The natural-transformation identification** (W-a). That `PshNatFamily`,
   the unbundled proxy `pshHomEquivNatFamily` lands in, is equivalent to the
   natural transformations `F.functor ⟶ F'.functor`. The prototype relates
   `PshNatFamily` to nothing outside `Basic.lean`. Its statement writes `⟶` in
   a functor category, so the deliverable belongs in a module on
   `GebMeta.classicalAllowedModules`, as obligation 1's choice-dependent half
   and obligation 6 entire do.
4. **Stage 2 at upstream quality** (W-b). Port `iotaPresheaf`, `sigmaPsh`,
   `adjoinArity`, `PshMor`, `fibreArity`, `decPresheaf`, `decArity`,
   `delta`, the code type and the interpretation, together with the structures
   and lemmas they rest on: `DomArity` with the discrete-fibration
   identification `presheaf`;
   `ShapeArity`;
   `BaseArity` with `pullback`, `isFunctorial_pullback`, the three lemmas that
   reduction needs (`reindex_eqToHom`, `reindex_comp_apply`,
   `reindex_cast_shape`) and the fibration layer `isFunctorial_fam`,
   `famPresheaf` and `reindexHom`, with the bundled `BaseArity.functor : J ⥤
   (Iᵒᵖ
   ⥤ Type uB)` as a corollary in a module on `GebMeta.classicalAllowedModules`,
   since it writes `⥤` into a functor category; `ElObj` / `elCategory` with
   `elCategory_id_val`, `elCategory_comp_val` and `elCategory_eqToHom_val`;
   `sigmaLiftHom`, `elEqToHom` and `elEqToHom_eq`; `isFunctorial_fibreArity`
   and `fibreArity_restr_val`; `isFunctorial_decArity` and
   `decArity_reindex_val`; `adjoinArity_cast_inl` and `adjoinArity_cast_inr`;
   the two code constructors `praCode` and
   `deltaCode` with their computation rules `interp_praCode`,
   `interp_deltaCode`, `interp_praCode_interp` and `interp_fst`. Of these only
   `interp_fst` is reached by the closure clause, `interp_deltaCode`'s
   statement applying it; the other three and the two constructors are listed
   because nothing else in the library half of this obligation's list depends
   on them, `deltaCodeVaries` being in the test half below;
   `praCodeOf` with `leftInverse_interp_praCodeOf` and `surjective_interp`,
   obligation 5's content in named form; the
   five `σ` laws
   (`sigmaPsh_shapeRestr_id`, `_shapeRestr_comp`, `_reindex_naturality`,
   `_reindex_id`, `_reindex_comp`) with the transport lemmas they use
   (`elObj_eq_of_hom`, `elHom_eq_eqToHom_comp`, `shapeRestr_eqToHom`,
   `cast_shape_val`, `shapeRestr_val_eqToHom_comp`, `reindex_heq_congr_shape`,
   `reindex_heq_eqToHom`, `reindex_eq_of_eq_comp`,
   `reindex_eq_of_eq_eqToHom_comp`); and `Interp`. The port is to be
   dependency-closed: anything a listed item needs travels with it, since
   [docs/rules/upstream-eligible.md](../../rules/upstream-eligible.md) §
   Subtree import rules forbids `Geb/Mathlib/` importing `Geb.Internal.*`.
   The
   prototype's `ElObj` / `elCategory` is written out rather than reused; the
   upstream version should be `S.Elementsᵒᵖ`. Acceptance for that choice: reuse
   is adopted unless it requires more transport and projection lemmas than the
   seven the written-out version needs: `elObj_eq_of_hom`,
   `elHom_eq_eqToHom_comp` and `elEqToHom_eq` at explicit call sites, the `def`
   `elEqToHom` they are stated about, and the three `@[simp]` projection lemmas
   `elCategory_eqToHom_val`, `elCategory_id_val` and `elCategory_comp_val`. Only
   the first has an explicit call site; the other two fire inside the `σ` laws'
   `simp` calls, deleting them leaving three goals unsolved, so all seven
   count. Weigh also whether `CategoryOfElements`' API removes the transport
   obstructions the five `σ` laws work around, since those are artefacts of
   presenting the shape presheaf as a subtype of a `ULift`ed sigma rather than
   of the mathematics — *Unelaborated*, nothing here having measured that API
   against them.

   The worked example does not go to `Geb/Mathlib/`. `ArityB`,
   `subsingleton_arityB`, `termPsh`, `arityVariesBase`,
   `arityVariesBase_dir_ext`, `isFunctorial_arityVariesBase`, `decUnit`,
   `decVariesElt`, `deltaVaries`, `deltaCodeVaries` and
   `interp_deltaCodeVaries` are fixtures and one check, consumed by nothing
   outside themselves, so they belong in the `GebTests/Mathlib/` mirror this
   obligation's modules carry — `interp_deltaCodeVaries` being the only check
   that `interp_deltaCode`'s transports reduce at a closed instance once
   `not_hasBijectiveReindex_interp_deltaCodeVaries` goes with the bound, and
   `interp_deltaCode` itself stating the computation with those transports
   written out. Shipping them in an upstream-eligible subtree with no library
   consumer would be cost without return under
   [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost. Open question 3
   asks whether that example should be replaced by one exercising
   `shapeRestr`, `reindex` and `reindexCompat` together, and open question 8
   whether this obligation should port the code type and the interpretation at
   all.

   Docstrings port under obligation 1's clause. The trim
   has already repaired the
   prototype's copies, per § Scope of this document, so for these the clause
   bites only where the ported form differs — a docstring naming a prototype
   declaration this obligation does not port, or one whose subject is renamed
   upstream. The declaration docstrings the trim repairs, and against which the
   ported form is checked, are `iotaPresheaf`, `PshMor`,
   `sigmaPsh`, `decArity`, `delta`, `arityVariesBase`, `decVariesElt` — whose
   "which is where reindexing fails" names the retired predicate — and
   `deltaCodeVaries`.
   `decArity`'s is the second, after `sigmaPsh`'s, that asserts in the strong
   form the claim
   § Why `δ`'s arity varies over the output object marks *Unelaborated*, its
   "the arity therefore varies over the output, which is the capability
   `not_hasBijectiveReindex_arityVaries` and
   `hasBijectiveReindex_adjoinArityConst` separate" naming two retired
   theorems. `deltaVaries`
   is not among them, the docstring naming the bound there being
   `not_hasBijectiveReindex_deltaVaries`'s, which is itself removed. Two
   `/-! … -/` section docstrings are written in their place: `Basic.lean`'s
   `Reindex`, whose argument is the removed material entire, and the merged
   `WorkedExample`, replacing `VaryingWitness`'s and `FusedWitness`'s, the
   latter of which asserts in the strong form the claim § The
   decoding-dependent continuation marks *Unelaborated*. All three module
   docstrings are affected, not two:
   `Basic.lean`'s summary and its numbered claims list, whose claims 2, 3 and 5
   are wholly about retired declarations, together with its
   `## Main definitions` — but not its `## Main statements`, whose one bullet
   survives; `Codes.lean`'s summary, which names `iotaConst`, with its
   `## Main definitions`, `## Main statements` and `## Implementation notes`,
   `Basic.lean` having no section of the last kind; and
   `Functor.lean`'s summary count and its `## Main statements`,
   whose only bullet is the retired shape-type equality, so that section is
   deleted rather than emptied, `docs/rules/lean-coding.md` § Documentation
   requiring a vacuous section be omitted and never left as a placeholder.
5. **Completeness.** Discharged: nothing remains to prove. The prototype's own
   branch writes the three declarations that state it and obligation 4 ports
   them, so what no branch carries is the proof, not the content. Every
   `PresheafPFunctor` over the interpretation's own input base — `interp` lands
   in `Σ 𝔹, PresheafPFunctor (el(D)) 𝔹`, so the question is about functors
   out of `el(D)` at the universes `CodeShape` pins, not about
   `PresheafPFunctor` at large — has a code, on the nose rather than up to
   isomorphism: `praCode 𝔹 F` is the code and `interp_praCode` is the proof,
   both definitional. The analogue is Lemma 1 of
   [HancockMcBrideGhaniMalatestaAltenkirch2013] ("Every dependent polynomial
   functor is an IR functor"), which that paper has to construct because its
   codes have no leaf to inject into; the leaf is what makes the statement
   trivial here rather than any new argument, and the content it would have
   carried is instead `delta`'s type. `praCodeOf` names the section — `praCode`
   uncurried over `Interp` — and `leftInverse_interp_praCodeOf` and
   `surjective_interp` state that `interp` retracts onto it, so the
   discharge is a named statement rather than a reading of two computation
   rules. `leftInverse_interp_praCodeOf` holds by `rfl`, `Interp` being a
   `Sigma` and so carrying structure eta; `surjective_interp` is
   `LeftInverse.surjective` of it, an existential and so not itself an
   equality. Obligation 4 ports all three.
6. **The collapse** (W-e). The equivalence `PSh(𝕀)/D ≃ PSh(el(D))`, which
   § The setting is indexed induction-recursion, not induction-recursion marks
   *Unelaborated*, and on which the input-side design, the
   no-mutuality argument of § Why no inductive-inductive definition is needed,
   and open question 2 all rest. In mathlib it is the composite of
   `overEquivPresheafCostructuredArrow` and
   `CategoryOfElements.costructuredArrowYonedaEquivalence`, the second
   transported through the presheaf construction before the two compose. Both
   name functor-category instances and so depend on `Classical.choice`, and the
   deliverable therefore belongs in a module on
   `GebMeta.classicalAllowedModules`.
7. **Code morphisms** (W-d). A code-level morphism type `Code.Hom` defined by
   recursion over the two rules, independently of `interp`, and a bijection
   with `PshHom` of the interpretations. `PshHom F F'` requires `F` and `F'`
   over one output base, where `Code` is fibred over `Cat` by
   `codePFunctor.wIndex`, and `interp_fst` identifies a code's index with the
   base its interpretation lands in, so
   the statement is over a fixed base: for `c c' : Code` with
   `h : wIndex c = 𝔹` and `h' : wIndex c' = 𝔹`, a bijection between
   `Code.Hom c c'` and `PshHom` of `(interp c).2` and `(interp c').2`
   transported along `(interp_fst c).trans h` and `(interp_fst c').trans h'`,
   the transports being the ones `interp_deltaCode` already performs along
   `(interp_fst K).trans hK`. Whether
   to state it that way or to re-present `Code` as a family indexed by `Cat`
   is part of the obligation. It is the analogue of
   Theorem 3 of [HancockMcBrideGhaniMalatestaAltenkirch2013], present in the
   discrete case as `IR.interpHomEquiv`, and the code-level full and
   faithfulness § Motivation opens with. The independence of the definition
   from `interp` is what gives the bijection content: defining `Code.Hom` as
   `PshHom` of the interpretations would make it hold by construction and
   assert nothing, which is the degenerate reading § The rules and their
   relation to small induction recursion records. Stage 1 supplies the
   codomain and obligation 2 the category structure the bijection must
   respect. Whether a `Code.Hom` so defined exists for these two rules is
   open, on two counts: the leaf's morphisms are `PshHom`s outright, so the
   recursion has content only at `δ` — and the leaf/leaf clause needs the same
   `wIndex` alignment the top-level statement does, `Code` being unindexed;
   and the `δ`/`δ` clause must relate
   subcodes over `ElObj (decPresheaf A hA D)` and
   `ElObj (decPresheaf A' hA' D)`, two different categories of elements, where
   the same one-base restriction applies and no `interp_fst` transport is
   available.

## Open questions

To be answered by the work rather than before it.

1. Whether the universes the code type pins need to vary. `CodeShape` puts the
   input base and the decoding presheaf, the `δ`-arity's carrier, and `Cat.{v,
   u}`'s object universe all at `u`, and the input base's homs at `u` as well.
   `Interp`'s shape universe is `max u v` rather than `u`, which costs one
   universe and no more, and admitting the representables into the leaf is what
   costs it: a representable's shape type is the total space of a hom-family,
   and a family of fibres indexed by the base is larger than either. The
   pinning is what makes `Cat.{v, u}` closed under the continuation step. What
   is open is whether a leaf restricted below the representables would let
   `max u v` come down to `u`, and whether anything wants it to.
2. Whether the output side should also carry a decoding presheaf `E`, as
   Section 6 of [HancockMcBrideGhaniMalatestaAltenkirch2013] does. The
   prototype's output index is a bare category, which by the collapse of § The
   setting is indexed induction-recursion, not induction-recursion already
   subsumes a pair `(𝕁, E)` at `el(E)`; whether the syntax gains from naming
   `E` separately is not settled.
3. Whether the walking arrow should carry a worked example exercising
   `shapeRestr`, `reindex` and `reindexCompat` together, while staying small
   enough to compute with by hand. `arityVariesBase` has the walking arrow as
   its output base and exercises `reindex` alone: its fibres are `ArityB`, its
   input base `Fin 1` makes `directionRestr` trivial, and `reindexCompat` is a
   `PshHom` field, of which `deltaVaries` carries none. The worked example
   would be new.
4. Whether `PresheafPFunctor` at discrete `I` and `J` carries information
   beyond `SlicePFunctor`, and whether the code system degenerates to `IR`
   there.
5. A source, with a searchable identifier, for the embedding of `Fam(C)` in
   presheaves as the coproducts of representables, and for its fullness. The §
   Non-goals section invokes it in passing; nothing in the workstream depends
   on it.
6. What the interpretation's fibres over a functor look like.
   `interp_praCode_interp` exhibits, for every code, a one-node code with the
   same interpretation, and `leftInverse_interp_praCodeOf` states the same fact
   as a retraction. That is an equality of interpretations and no more: it
   does not establish that the two codes differ, and for a `pra` code they do
   not, so it bounds the fibres from below only once the two are known
   distinct. Whether `deltaCode … ≠ praCode …` is unproved here, as is the
   structure of the fibre — whether the codes over a functor are related by
   anything better than sharing an interpretation, which is what obligation
   7's morphism type has to answer for the code system to carry information
   the functors do not.
7. Whether the leaf should be a parameter of the code type. `CodeShape`'s first
   summand is `PresheafPFunctor (el(D)) 𝔹` outright, so the restricted-leaf
   question of § The rules and their relation to small induction recursion
   cannot be posed inside the present code type: it needs a different
   `CodeShape`, hence a different `Code` and `interp`. Taking a predicate on
   `PresheafPFunctor (el(D)) 𝔹` as a parameter, with the subtype it cuts out
   as the first summand and the present system its instance at `True`, would
   let one code type carry both. It is not built: nothing consumes the general
   form yet, and a parameter with one instantiation is cost without return
   under [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost. Posing the
   restricted-leaf question at all would need this first, together with a
   property separating the classes of functor the two leaves admit; the design
   carries neither.
8. Whether obligation 4 should port the code type and the interpretation at
   all. `delta` and the semantic operations carry the content and are wanted
   upstream on their own merits. The interpretation is surjective on objects
   by construction, and § The rules and their relation to small induction
   recursion marks *Unelaborated* — not established —
   that `Code` and `interp` therefore record derivations and nothing else;
   open question 6 leaves open whether they record anything a morphism theory
   can use. Obligation 4 lists them; whether that
   half meets § Code is cost is not settled by this document. Deferring the
   code type to W-d has costs of its own: `deltaCodeVaries` is a `Code`
   term, `interp_deltaCodeVaries` is the closed-instance check obligation 4
   describes, `praCodeOf` and its two theorems are statements about `interp`,
   and
   W-b's acceptance cell names the code type outright, so the deferral would
   also cut obligation 4 back to its semantic-operation results and restate
   W-b's acceptance.
9. Which `Geb/Mathlib/` modules the ports occupy, and what the upstream names
   are. The acceptance cells say "in `Geb/Mathlib/`" and no more; obligation 1
   lists about twenty-five declarations and obligation 4 seventy named
   explicitly, with eight more named only as "the code type and the
   interpretation", with no file split, and § Branches' `docs/index.md` clause
   is written to branch on
   whether a directory bullet already exists without saying which case obtains.
   One upstream name is fixed — `PshHom` becomes `PresheafPFunctor.Hom` — and
   no other. This bears on more than tidiness: § Scope of this document
   requires each of W-a and
   W-b to rewrite the retained remainder against the names it has established,
   and both edit `Basic.lean` and `Functor.lean`, so with no scheme fixed the
   rebase of whichever lands second is undetermined. It is left to the branches
   rather than settled here because the decomposition follows from what each
   port turns out to need, and because settling it would be a second concern in
   this document under [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern
   shape. Each branch fixes its own layout and names as its first task, and
   whichever lands second reconciles.

## Non-goals

- Positive inductive-recursive definitions over `Fam(C)`
  ([GhaniNordvallForsbergMalatesta2015]). On the reading § Motivation records
  and marks *Unelaborated*: over `Fam(C)` the code-level
  full-and-faithfulness is available only by Remark 3.4's route, defining the
  interpretation simultaneously with the codes. The
  presheaf setting is not claimed to have it: obligation 7 is where it would
  be discharged, and that obligation records that whether its `Code.Hom` exists
  for these two rules is open. What the presheaf setting has structurally,
  without a simultaneous definition, is Stage 1's functor-level
  classification, which is the input such a discharge would use. If wanted they
  are better recovered
  inside the presheaf construction, since `Fam(C)` embeds in presheaves as the
  coproducts of representables — an embedding this document neither establishes
  nor cites to a source, and whose fullness the recovery would need. Locating a
  source for it is recorded as open question 5, not as an obligation: nothing
  in the workstream depends on it.
- Initial algebras of the interpreted functors. `IR`'s are not constructed
  either; the set-theoretic model of [DybjerSetzer1999] justifies their
  existence using a Mahlo cardinal. [GhaniNordvallForsbergMalatesta2015] § 7
  attributes it there: "We briefly revisit the initial algebra argument used by
  Dybjer and Setzer [DS99]".
- Uniqueness of the interpretation fold.
  `Geb/Mathlib/Data/PFunctor/Slice/W.lean` establishes only the existence half
  of the initial-algebra universal property, and this workstream inherits that.

## Notes

`docs/references.bib`'s note on `HancockMcBrideGhaniMalatestaAltenkirch2013` is
wrong, not merely narrow. It claims the extended preprint "renumbers two of"
the results this repository cites. Checked against the preprint, the preprint
numbers Definitions, Examples, Lemmas, Theorems and Corollaries in one shared
sequence, where the proceedings number each kind separately. Definitions 1 to 4
are unaffected, being the first four numbered items in both; everything from
the proceedings' Example 1 onward shifts, because the preprint's counter
absorbs the examples. Across every numbered result this repository cites or a
branch of this workstream will cite — Corollary 4 being cited only by the
transient handoff, Theorem 4 only by `TODO.md` § Theorems 2 and 4 for `IR`
codes, and Definition 6 and Theorem 1 only prospectively, and Definition 7
only by the
transient prototype —
the proceedings' Definition 2, Definition 3, Definition 5, Definition 6,
Definition 7, Definition 8, Example 1, Lemma 1, Lemma 2, Lemma 3, Lemma 4,
Theorem 1, Theorem 2, Theorem 3, Theorem 4, Corollary 2 and Corollary 4 are
the
preprint's Definition 2, Definition 3, Definition 8, Definition 10, Definition
11, Definition 17, Example 5, Lemma 7, Lemma 9, Lemma 14, Lemma 16, Theorem 12,
Theorem 15, Theorem 18, Theorem 21, Corollary 19 and Corollary 22. Example 1 is
cited by `Geb/Mathlib/Data/PFunctor/IndRec/Container.lean`, its test module and
`docs/index.md`. No branch of this workstream touches the first two, and
each branch adds to `docs/index.md` without touching that line, so that
citation's correction is independent of the ordering constraint below. The
existing note covers Definition 8, Theorems 2, 3 and 4 and Corollary 2. Of the
results it does not, the repository's most-cited are Lemma 4 (62 occurrences
over 7 files, the most-cited outright), Lemma 3 (14 over 5) and Definition 5
(13 over 2). Definition 5 is cited in
`Geb/Mathlib/Data/PFunctor/IndRec/Slice.lean` and its test mirror; Lemma 3 in
`Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`,
`Geb/Mathlib/Data/PFunctor/IndRec/{Basic,Naturality}.lean`, one test mirror and
`docs/index.md`; Lemma 4 in
`Geb/Mathlib/Data/PFunctor/IndRec/{Basic,Category,Naturality}.lean`, their
three test mirrors and `docs/index.md`, `Category.lean` being its largest
single consumer. A key-only search under-scopes all three, as it does the
author order below. One collision is recorded separately: the preprint's
Definition 8 is the proceedings' Definition 5, while the proceedings'
Definition 8 is the preprint's Definition 17, so a reader who does not know
which numbering a citation uses lands on the wrong statement. Section numbering
is unchanged, though the preprint adds numbered subsections the proceedings
runs in. The preprint is not merely a renumbering: it carries a different title
and a different author order, so the key
`HancockMcBrideGhaniMalatestaAltenkirch2013` names the proceedings version
alone.
Correcting and extending the note is recorded in [TODO.md](../../../TODO.md) §
Citation corrections deferred to their own branch, which is where it is done
rather than in any branch of this workstream, though it is due now rather than
at a future one. Of the results
the existing note does not cover, Lemma 4, Lemma 3, Lemma 2, Lemma 1 and
Definition 5 are each cited in persistent content — Lemma 1 at three sites in
`Geb/Mathlib/Data/PFunctor/IndRec/Slice.lean` and once in its test mirror —
so those citations are ambiguous between the two numberings today, and no
branch of this workstream introduced any of them.
Definition 7 is in the same position as Lemma 1: the prototype cites it at
`Basic.lean`'s `SliceHom`, and while the prototype is transient, obligation 1
ports the role `SliceHom` records — Definition 7 travelling to `PshHom`'s row
— into persistent content, though not the declaration, which no obligation
ports. Definition 6 and Theorem 1 no
repository file cites yet, so of this workstream's own citations those two and
Definition 7 would newly bind W-a; the correction is due before any branch
regardless, on
Lemma 1's account. Theorem 3, which
W-d cites, the existing note already covers, so W-d is unconstrained. W-b
cites the paper twice: § Definitions' `praCode` row cites Lemma 1, which
the note above places, and obligation 4's `δ` material cites Section 6. The
second is to a section, and section numbering is unchanged.
That ordering constraint is recorded in `TODO.md` too, this document being
removed with the last branch.

The author order of `GhaniNordvallForsbergMalatesta2015` in
`docs/references.bib` is wrong. The published LMCS byline is Ghani, Malatesta,
Nordvall Forsberg, and so is the arXiv preprint's. What the entry and the
citation key encode is the metadata order — what arXiv's listing, the LMCS
landing page and the DOI record `10.2168/LMCS-11(1:13)2015` all return — which
disagrees with the byline of either PDF. A reviewer of the correction branch
who checks the DOI record alone will find the present entry matches it, so the
correction cites the article itself. It is pre-existing. Four persistent
modules carry the key — `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`
and `Geb/Mathlib/Data/PFunctor/IndRec/{Basic,Functor,Universes}.lean` — besides
`docs/references.bib`, `TODO.md`, this spec, the transient prototype and the
transient handoff. The repair surface is larger than the key count:
`docs/index.md` spells the wrong order out in prose at three places without
using the key, so a key-only search under-scopes the branch. It is deferred to
its own branch per one concern per branch, recorded in `TODO.md`.

## References

Each key is cited in the body above; the bibliographic detail lives in
[docs/references.bib](../../references.bib).

- [GhaniNordvallForsbergMalatesta2015] — positive inductive-recursive
  definitions; Remark 3.4 on the choice of morphism collection, and Section 2
  on the loss of full and faithfulness over `Fam(C)`.
- [HancockMcBrideGhaniMalatestaAltenkirch2013] — small induction recursion;
  Section 6 for `IIR`, Definition 1 for the `(r, t, q)` presentation of
  dependent polynomials, Definition 6 for morphisms of dependent polynomials,
  Definition 7 for morphisms of indexed containers, Theorem 1 for the discrete
  representation theorem, Theorem 3 for the code-level full-and-faithfulness
  statement, Lemma 1 for the constructed-by-hand completeness result the leaf
  makes definitional.
- [Weber2007] — parametric right adjoints and familial functors.
- [nLabParametricRightAdjoint] — the presentation of presheaf p.r.a. functors
  as the polynomials `I ← E → K → J` in `Cat` whose last leg is a discrete
  fibration and whose first two form a two-sided discrete fibration, which is
  what fixes the shape and arity data.
- [MacLaneMoerdijk1992] — the category of elements.
- [GambinoKock2013] — polynomial functors. The result
  [HancockMcBrideGhaniMalatestaAltenkirch2013] restates as its Theorem 1 is
  numbered 2.12 in the 2010 arXiv version it cites; whether that numbering
  survives into the 2013 journal article this key names is unchecked.
- [DybjerSetzer1999] — inductive-recursive definitions.
