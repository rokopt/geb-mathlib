/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import VersoManual
public import GebManual.Bibliography
import Geb.Prototypes.QuotientPRA
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Dense
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.Data.QPF.Univariate.Basic

/-! # Quotient polynomial functors chapter

The relation between the quotient presheaf polynomial functors of
`Geb/Prototypes/QuotientPRA/` and the density formula for presheaves:
what is constructed in Lean, what is argued, what is conjectured, and
the constructions that remain.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open GebProto.QuotientPRA

#doc (Manual) "Quotient polynomial functors and the density formula" =>

A quotient presheaf polynomial functor over a category `I` is a
presheaf polynomial endofunctor over `I × W`, where `W` is the walking
parallel pair `zero ⇉ one`. Its W-type is a graph of terms and
witnesses of equality, internal to the presheaves on `I`, and its
quotient identifies the two endpoints of every witness. This chapter
relates that construction to the density formula, which presents
every presheaf as a quotient of a coproduct of representable
presheaves, and records which of the relations are constructed in
Lean.

Every section ends with a status line of one of three kinds.
Constructed: a Lean declaration states the claim, and the section
names it. Argued: the section gives an argument that has not been
written in Lean. Conjectured: the section states an expectation
without a complete argument. The last section lists the constructions
that would make the argued and conjectured claims constructed; it is
revised as each is made, together with the status line of the section
it serves.

Throughout, `π : I × W → I` is the projection, `π*` is restriction
along it, and `π₍!₎` is its left adjoint.

# What is constructed

A presheaf on `I × W` is a pair of presheaves on `I`, the terms over
`(i, zero)` and the witnesses over `(i, one)`, with two maps from
witnesses to terms, the restrictions along the two morphisms
`zero ⟶ one` ({name}`src` and {name}`tgt`). {name}`coeq` sends such a
graph to the presheaf on `I` whose value at `i` is the coequalizer of
the two endpoint maps at `i`. {name}`discrete` sends a presheaf `P` on
`I` to the graph whose terms and witnesses are both `P`, and
{name}`coeqHomEquiv` is the adjunction between the two.

A quotient presheaf polynomial functor `F` has a W-type
{name}`PresheafPFunctor.W`, a graph, and {name}`quotient` is its image
under {name}`coeq`. A model is a presheaf `P` on `I` with an algebra
`F (discrete P) → discrete P`; {name}`elim` is the eliminator into a
model and {name}`elim_intro` its computation rule. Reflexivity,
symmetry, transitivity and transport are not constructors of fixed
shape ({name}`no_uniform_refl`, {name}`no_uniform_symm`,
{name}`no_uniform_trans`, {name}`no_uniform_transport`), for the W-type
and the M-type alike.

For a functor with free arities ({name}`FreeArity`), finitely many
arguments per constructor, term constructors whose arguments are terms
({name}`TermArguments`), and a congruence for every term constructor
({name}`HasCongruences`), the quotient carries a model structure
({name}`quotientModel`), and the eliminator is the only morphism of
models out of it ({name}`existsUnique_isModelHom`): the quotient is the
initial model. {name}`Signature.eq_lift` is the one-sorted instance,
and a test in `GebTests/Prototypes/QuotientPRA/` applies the theorem to
the leaf paths of commutative binary trees over the walking arrow. No
declaration named in this section depends on `Classical.choice`.

Status: constructed.

# The quotient is a left Kan extension

{name}`discrete` is restriction along `π`: its value at an object of
`I × W` is the value of `P` at the object's first component, and its
restriction along a morphism is that of `P` along the morphism's first
component. Restriction along a functor has a left adjoint, the left
Kan extension, whose pointwise value is a coend (Proposition 2.3.6
of {citet Loregian2021}[], numbered as in its arXiv version). For a
graph `Y`,

```
(π₍!₎ Y)(i) = ∫^{(i', x)} I(i, i') × Y(i', x) ≅ ∫^{x} Y(i, x)
```

the isomorphism being the co-Yoneda lemma in the variable `i'`
(Proposition 2.2.1 of {citet Loregian2021}[]). The remaining coend is
that of a functor of one variable, so a colimit: the colimit of
`Y(i, one) ⇉ Y(i, zero)`, which is the coequalizer of the two endpoint
maps, the value of {name}`coeq` at `i`. Hence {name}`coeq` is `π₍!₎`,
{name}`discrete` is `π*`, {name}`coeqHomEquiv` is the adjunction
`π₍!₎ ⊣ π*`, and its unit {name}`coeqUnit` sends a term to its class.

mathlib states the left Kan extension along a functor as
{name}`CategoryTheory.Functor.lan`, with the adjunction
{name}`CategoryTheory.Functor.lanAdjunction`. Those definitions depend
on `Classical.choice`, so a comparison between them and {name}`coeq`
belongs in a module of `GebMeta.classicalAllowedModules`, the
construction here remaining choice-free.

Status: the adjunction {name}`coeqHomEquiv` is constructed. Its
identification with the left Kan extension along `π` is argued. The
comparison with {name}`CategoryTheory.Functor.lan` is not constructed.

# The density formula as a quotient functor

For a presheaf `X` on a category `C`, let `D(X)` be the graph on
`C × W` with

```
D(X)(d, zero) = Σ (h : d → c), X(c)                  terms
D(X)(d, one)  = Σ (g : d → c') (f : c' → c), X(c)    witnesses
src (g, f; x) = (f ∘ g; x)                           composition
tgt (g, f; x) = (g; X(f) x)                          action of X
```

Then `π₍!₎ D(X) ≅ X`. The map sends the class of `(h; x)` to
`X(h) x`, and `x ↦ (id; x)` is its inverse, since the witness
`(id, h; x)` has source `(h; x)` and target `(id; X(h) x)`. This is the
co-Yoneda lemma with the coend written as the coequalizer of two maps
between coproducts (Proposition 2.2.1, Remark 1.2.4 and Exercise 1.9
of {citet Loregian2021}[]). The inverse is explicit, so the
isomorphism is constructive. mathlib states the density formula as
{name}`CategoryTheory.Presheaf.colimitOfRepresentable`, a presheaf as
the colimit of representable presheaves over its category of elements,
and as the density of the Yoneda embedding, an instance of
{name}`CategoryTheory.Functor.IsDense`.

`D(X)` is `F_D (π* X)` for a quotient presheaf polynomial functor
`F_D` over `C` with free arities, each shape having one argument, over a
term object:

* the term shapes over `(d, zero)` are the morphisms `h : d → c`, with
  argument over `(c, zero)`;
* the witness shapes over `(d, one)` are the composable pairs
  `d → c' → c`, written `(g, f)`, with argument over `(c, zero)`;
* restriction along the source morphism sends `(g, f)` to `f ∘ g`,
  the reindexing ({name}`FreeArity.reindex`) sending the argument of
  `f ∘ g` to that of `(g, f)` along an identity; restriction along the
  target morphism sends `(g, f)` to `g`, the reindexing sending the
  argument of `g`, over `(c', zero)`, to that of `(g, f)` along the
  morphism `(f, 𝟙)`;
* restriction along a morphism `k` of `C` precomposes `k`.

Three properties of `F_D` connect it to the rest of this chapter. The
witness shape `(g, f)` has endpoints of two different term shapes,
`f ∘ g` and `g`, so the quotient identifies elements across shapes.
Each endpoint is one term constructor applied to the argument, so the
equations are one-step, in the sense of {name}`Signature.Equations`.
The witness shape `(g, id)` has both endpoints equal to `g`, a
reflexivity indexed by the shape, which {name}`no_uniform_refl` does not
exclude, since it concerns one constructor applied to every term; the
coequalizer is reflexive.

Status: argued, not constructed.

# Models are algebras, and initiality is a transfer

By the adjunction, a model `α : F (π* P) → π* P` corresponds to a
morphism `π₍!₎ F π* P → P`. The models of `F` are therefore the
algebras of the endofunctor `F̄ = π₍!₎ F π*` of presheaves on `I`,
{name}`IsModelHom` is the condition on a morphism of such algebras, and
{name}`existsUnique_isModelHom` states that `π₍!₎` of the W-type is the
initial `F̄`-algebra.

Initial algebras transfer along a left adjoint: for `L ⊣ R` and a
natural isomorphism `F ∘ L ≅ L ∘ G`, the adjunction lifts to one
between the categories of algebras, and `L` sends an initial
`G`-algebra to an initial `F`-algebra (Theorem 2.1 of
{citet AtkeyJohannGhani2012}[], which credits it to
{citet HermidaJacobs1998}[]). Here `L` is `π₍!₎`, the `G` of that
statement is the functor `F` of this chapter and its `F` is `F̄`, and
the comparison `π₍!₎ F ⇒ F̄ π₍!₎` is `π₍!₎` applied to `F` of the unit
{name}`coeqUnit`. The hypotheses of {name}`existsUnique_isModelHom`
make the comparison invertible at the W-type: every node over the
quotient's discrete graph is the image of a node over the W-type
({name}`mapPresheaf_unit_surjective`), and nodes whose arguments have
equal classes have equal classes ({name}`unit_mk_congr`, which states
it for the trees the nodes build; the same argument applies to the
nodes). The unit is a morphism of algebras ({name}`quotientModel_unit`),
and {name}`elim` is defined as the transpose ({name}`coeqDesc`) of the
W-type's eliminator, as the lifted adjunction prescribes.

The transfer theorem assumes the comparison invertible at every graph,
while the Lean proof uses it at the W-type alone. Whether the
hypotheses make it invertible at every graph is not settled: the
argument uses reflexivity witnesses, which the W-type has
({name}`exists_refl`) and an arbitrary graph need not.

Status: the elementwise statement {name}`existsUnique_isModelHom` is
constructed. Its restatement as the initiality of an `F̄`-algebra, the
invertibility of the comparison at the W-type, and its derivation from
the transfer theorem are argued, not constructed.

# Arities, transport and truncation

For a presheaf `E` on `C`, the adjunction and the density formula give

```
Hom(E, X) ≅ Hom(π₍!₎ D(E), X) ≅ Hom(D(E), π* X)
```

naturally in `X`. A parametric right adjoint on the presheaves on `C`
with arities `E` is therefore the restriction to discrete graphs of a
functor on graphs with arities `D(E)`. On a graph `Y` that is not
discrete, a morphism `D(E) → Y` assigns a term of `Y` to each element
`e` of `E`, and to each morphism `f : c' → c` and element `e` over `c`
a witness between the restriction along `f` of the term of `e` and the
term of `E(f) e`: a family natural up to witnesses. Those witnesses are
transport. For a free arity, a coproduct of representable presheaves, a
morphism into `Y` is a family of terms subject to no condition, which
is why the free arities of {name}`FreeArity` require no transport.

The arity `D(E)` has arguments over witness objects, so resolving an
arity that is not free produces a term constructor that takes
witnesses, which {name}`TermArguments` excludes. A congruence for such
a constructor relates two applications with different witness
arguments, and so needs witnesses between witnesses. `D(X)` is the
first stage of a resolution of `X` by coproducts of representable
presheaves: its terms and witnesses at `d` are indexed by paths of
lengths one and two out of `d`. The next stage is indexed by paths of
length three, and `W` would be replaced by a longer truncation of the
opposite of the simplex category. The conjecture is
that {name}`TermArguments` marks the one-truncation of that resolution,
and that the initiality theorem extends, one stage at a time, to term
constructors that take witnesses.

Status: the isomorphism of hom-sets and the description of transport
are argued. The truncation statement is conjectured.

# Identification across shapes

A morphism of polynomial functors sends each shape of its source to a
shape of its target and each direction of the target shape back to a
direction of the source shape; it identifies two elements only by
sending them to one element. The identification of `(f ∘ g; x)` with
`(g; X(f) x)` in the density formula changes the shape and moves the
argument along `f`. In the construction here that identification is
the value of {name}`coeq` on a separate sort, the witnesses: the
functors `F_D` and `D` are polynomial, and the construction leaves
polynomial functors only at `π₍!₎`.

Analytic functors identify elements within a shape, by symmetries of
its arguments: an analytic functor is a left Kan extension along the
groupoid of finite sets and bijections (Example 2.3.11 of
{citet Loregian2021}[]). mathlib's {name}`QPF`
{citep AvigadCarneiroHudon2019}[] identifies elements across shapes. A
QPF is a functor with a map {name}`QPF.abs` from a polynomial functor,
a section {name}`QPF.repr` of that map, and the equation
{name}`QPF.abs_repr`. Its fixed point {name}`QPF.Fix` is the quotient
of the W-type by the relation {name}`QPF.Wequiv`, and its constructor
{name}`QPF.Fix.mk` obtains canonical representatives through
{name}`QPF.fixToW`, built from the section, without `Classical.choice`.
A quotient presheaf polynomial functor is presented instead: its
quotient is generated by the witness constructors, as the density
formula's is generated by the composable pairs, and the representatives
its initiality requires come from the finiteness of the arguments
rather than from a section.

Status: the description of mathlib's QPF is read from its source at the
pinned mathlib revision. The comparison is argued, not constructed.

# Constructions to build

Each item replaces an argued or conjectured claim of a section above by
Lean declarations; when an item is done, the status line of that
section changes accordingly.

1. The density functor. Define `F_D` as a {name}`FreeArity` instance
   over `C × W` and construct, without `Classical.choice`, the natural
   isomorphism between {name}`coeq` of `F_D (discrete X)` and `X`. In a
   module of `GebMeta.classicalAllowedModules`, relate it to mathlib's
   density formula: {name}`CategoryTheory.Presheaf.colimitOfRepresentable`,
   {name}`CategoryTheory.Presheaf.isColimitTautologicalCocone`, the
   density of the Yoneda embedding ({name}`CategoryTheory.Functor.IsDense`),
   and mathlib's coends ({name}`CategoryTheory.Limits.coend`). The
   instance also exercises the framework on witness shapes whose
   endpoints differ in shape.

2. Initiality as a transfer. Construct the correspondence between the
   models of `F` and the algebras of `π₍!₎ F π*`, state
   {name}`existsUnique_isModelHom` as the initiality of an algebra, and
   prove that the comparison is invertible at the W-type under the
   hypotheses of {name}`HasCongruences`. In an allowlisted module,
   identify {name}`coeq` with {name}`CategoryTheory.Functor.lan` along
   the projection. The transfer theorem (Theorem 2.1 of
   {citet AtkeyJohannGhani2012}[]) can be stated once for categories of
   algebras and instantiated.

3. Quotient functors between presheaf categories. For a parametric
   right adjoint `T` from the presheaves on `C × W` to the presheaves on
   `D × W`, which {name}`PresheafPFunctor` admits with two base
   categories, take the functor `π₍!₎ T π*` from the presheaves on `C`
   to the presheaves on `D`. The expectation is that two such functors
   compose to a third when the second descends along the unit, its
   comparison being invertible at the graphs the first produces: the
   condition of item 2, required at those graphs rather than at a
   W-type. The conjecture is that the finitary functors of this form
   include the analytic functors of
   {citet FioreGambinoHylandWinskel2008}[]: their coend over finite
   sequences of objects (their Section 3.2) is a coequalizer of the same
   form, whose term shapes are a sequence with an element of the species
   at it, whose witness shapes are the morphisms of sequences, and whose
   reindexing follows a morphism's bijection and components.

4. mathlib's quotients of polynomial functors. For a one-sorted
   quotient functor with finitary arities and congruences, construct a
   {name}`QPF` instance on `π₍!₎ F π*` and an isomorphism between
   {name}`QPF.Fix` and {name}`quotient`. The section {name}`QPF.repr`
   chooses representatives, so the instance belongs in an allowlisted
   module unless the functor has normal forms. Conversely, present a
   QPF whose relation {name}`QPF.Wequiv` is generated by relations
   between single applications of shapes as a signature with one-step
   equations ({name}`Signature.Equations`), and compare the two fixed
   points.

5. Term constructors that take witnesses. Replace `W` by a longer
   truncation of the opposite of the simplex category, resolve arities
   that are not free by the corresponding stage of the resolution of
   the section on arities, and extend {name}`HasCongruences` and
   {name}`existsUnique_isModelHom` to term constructors whose arguments
   include witnesses. This tests the conjecture of that section.
