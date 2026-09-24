# Handoff: equational presentations uniting quotients and definitions

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [End goal](#end-goal)
- [State of the repository](#state-of-the-repository)
  - [The definitions development](#the-definitions-development)
  - [The quotient development](#the-quotient-development)
  - [Supporting infrastructure](#supporting-infrastructure)
- [The analysis carried over](#the-analysis-carried-over)
  - [Presentations as coequalizers](#presentations-as-coequalizers)
  - [Definitions are presentations that change nothing](#definitions-are-presentations-that-change-nothing)
  - [Why neither development re-expresses the other today](#why-neither-development-re-expresses-the-other-today)
  - [Guarded blocks sit on the coalgebraic side](#guarded-blocks-sit-on-the-coalgebraic-side)
- [The design question to open with](#the-design-question-to-open-with)
- [Work breakdown](#work-breakdown)
- [Conventions and pitfalls](#conventions-and-pitfalls)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

This document hands a follow-on session the unification of two
developments on `main`: the quotient presheaf polynomial functors of
`Geb/Prototypes/QuotientPRA/` and the definitions of
`Geb/Prototypes/Definition/`. It records the state of both, the
mathematical analysis that relates them, the design question the
session opens with, a breakdown of the work, and the conventions that
cost time in the sessions that built them.

## End goal

One construction of equational presentations over a polynomial
signature in which the sides of an equation are terms of the free
monad, of any depth, rather than single operations applied to
variables. Both developments become instances of it:

- the quotient development's one-step equations are the presentations
  whose sides have depth one, and its quotient agrees with the general
  quotient on them;
- a definition is a presentation whose quotient is the theory it
  extends: the definitional-extension theorems of
  `Geb/Prototypes/Definition/Solution.lean` become the statement that
  the quotient of a definitional presentation is isomorphic to the
  free monad of the base signature.

Two equations that no one-step presentation can express serve as the
flagship examples: associativity, whose sides have depth two, and a
unit law, one of whose sides is a bare variable. Binary trees modulo
associativity, with the unit law added, should present the free monoid.

## State of the repository

### The definitions development

`Geb/Prototypes/Definition/` (namespace `Geb.Definition`, index
`Geb/Prototypes/Definition.lean`), designed in
[definitions.md](definitions.md):

- `Basic.lean`: `Direction s`, the directions of the free polynomial at
  a shape `s : P.FreeM Unit`; `freePolynomial`;
  `Derived P Q := (a : Q.A) → P.FreeM (Q.B a)`, a Kleisli morphism
  `Q ⇒ T_P`; `expandOps d := FreeM.liftM d`, the induced monad morphism,
  with `expandOps_bind`; `link`, Kleisli composition, with `link_pure`
  and `link_assoc`; `eval alg env t`, evaluation in an algebra through
  `FreeM.liftM` into `Cont`, with `eval_pure`, `eval_liftBind`,
  `eval_bind` and `eval_map`; `Block P Γ E := E → P.FreeM (Γ ⊕ E)`,
  `IsSolution`, `unfold`, `eval_unfold`; `ofCoalgebra` and
  `coalgebra_solution_unique` for flat guarded blocks in mathlib's
  M-type; `encode` into `RoseTree ℕ`.
- `Vertex.lean`: `Vertex t`, the vertices of a term (the directions of
  the cofree comonoid); `subterm`, `Vertex.root`, `Vertex.append` with
  the five directed-container laws; `Vertex.ofDirection`;
  `link_map_append`, transport of a body along a vertex of its
  environment.
- `Solution.lean`: `derivedAlg`, the interpretation of derived
  operations, and `eval_expandOps`, that expansion preserves meaning;
  `WFBlock`, blocks whose body at `i` ranges over the exports below
  `i`, and `WFBlock.existsUnique_isSolution` in every algebra.
- `Guarded.lean`: `GuardedBlock P Γ E := E → P.Obj (P.FreeM (Γ ⊕ E)) ⊕ Γ`
  and `GuardedBlock.existsUnique_isSolution` in `Geb.MType.M`, both
  halves by bisimulation.

### The quotient development

`Geb/Prototypes/QuotientPRA/` (namespace `GebProto.QuotientPRA`),
described in [index.md](index.md) and in the manual chapter
[QuotientPRA.lean](../manual/GebManual/QuotientPRA.lean):

- `Basic.lean`: graphs internal to presheaves on `I`, as presheaves on
  `I × WalkingParallelPair` (terms over `zero`, witnesses over `one`);
  `coeq`, the pointwise quotient; `discrete`; `coeqHomEquiv`;
  `coeqMk_eq_iff`.
- `W.lean`: a quotient presheaf polynomial functor, its W-type of terms
  and witnesses built together, `quotient`, `intro`, models,
  `model_sound`, `elim`, `IsModelHom`.
- `Obstruction.lean`: restriction in a presheaf W-type rebuilds only the
  root of a tree (`head_map`), so a witness constructor's endpoints are
  single term constructors applied to its arguments; reflexivity,
  symmetry, transitivity and transport are not witness constructors
  (`no_uniform_refl` and its siblings).
- `FreeArity.lean`, `Congruence.lean`, `InitialModel.lean`: free arities;
  `HasCongruences`; the initial model for finitary free arities with
  congruences (`existsUnique_isModelHom`), using finitely many choices
  (`exists_forall_of_finEnum`, `Quotient.listChoice`).
- `Signature.lean`, `Initial.lean`: `Signature.Equations`, with fields
  `E`, `V`, `lhs rhs : (e : E) → P.Obj (V e)`; `qpra`, which adds reversed
  orientations and a congruence per operation; `Satisfies`, `model`,
  `lift`; the quotient as the initial algebra satisfying the equations
  (`satisfies_opQ`, `lift_opQ`, `eq_lift`).
- Tests: `GebTests/Prototypes/QuotientPRA/CommTree.lean` (binary trees
  modulo commutativity) and `Directions.lean` (leaf directions over the
  walking arrow, with depths).

The manual chapter's § Constructions to build lists the chapter's own
open items (the density functor, initiality as a transfer, quotient
functors between presheaf categories, mathlib's `QPF`). The unification
here is not among them and may add an item.

### Supporting infrastructure

- `Geb/Cslib/Foundations/Data/PFunctor/Free.lean` issues
  `compile_inductive% PFunctor.FreeM`, making `FreeM.rec` executable.
  Import it; issuing the command again fails.
- `Geb/Prototypes/MType/` builds an M-type from W-types, `Geb.MType.M`,
  whose destructor, `bisim` and `corec_unique` pass the axiom linter;
  `Geb.MType.mEquiv` identifies it with mathlib's `PFunctor.M`.
- No univariate `PFunctor` sum exists in mathlib, Cslib or the
  repository (the slice layer has `coprod`); presenting a definition
  over `P ⊕ Q` needs one, as the shapes `P.A ⊕ Q.A` with
  `Sum.elim P.B Q.B`.

## The analysis carried over

### Presentations as coequalizers

Both developments work with equational presentations over a signature
`Σ`: equations `E`, each with variables `V e` and two sides in the free
monad `T_Σ(V e)`. As polynomial maps, the sides are a parallel pair of
Kleisli morphisms `E ⇉ T_Σ`, that is, two elements of `Derived Σ E`;
they induce a parallel pair of monad morphisms `T_E ⇉ T_Σ`, whose
coequalizer is the monad the presentation presents. Every finitary monad
arises this way (Kelly and Power 1993). The walking parallel pair of the
quotient development is this parallel pair, internalized: witnesses over
`one`, their two endpoints by restriction, and `coeq` the quotient.

### Definitions are presentations that change nothing

A family of derived operations `δ : Derived P Q` is the presentation
over `P ⊕ Q` of the equations `q(x⃗) ≈ δ_q(x⃗)`. Its coequalizer is `T_P`:

- unfolding, `expandOps` of the handler `[lift, δ]`, coequalizes the
  two sides, since it sends each `q` to `δ_q` and fixes `P`-terms;
- a monad morphism out of `T_{P+Q}` coequalizes them exactly when it
  sends each `q` to the image of `δ_q`, so it is determined by its
  action on `P`; the unfolding is therefore universal, and the
  inclusion of `T_P` is a section of it.

In quotient terms a presentation over `Σ ⊆ Σ'` is definitional when the
composite `T_Σ → T_Σ' → quotient` is a bijection. Surjectivity is
eliminability, every new term equal to an old one; injectivity is
non-creativity, no new identification of old terms. These are the two
criteria for a definition of Leśniewski, stated by Suppes (1957,
pp. 151–173). Commutativity fails them: it presents a new theory.

### Why neither development re-expresses the other today

| Axis | Quotient development | Definitions development |
| --- | --- | --- |
| Depth of a side | one step | any depth |
| Form of an equation | any axiom | a new symbol on the left |
| Question | the presented object | that it is the old one |
| Cyclic equations | not treated | guarded blocks |

The depth limit is structural (`Obstruction.lean`), not a choice of the
existing code. A defining equation fits a one-step presentation only
when its body has depth one (`double(x) ≈ add(x, x)` does; a body such
as `g(h(x), x)` does not).

### Guarded blocks sit on the coalgebraic side

The block `c = s(c)` over zero and successor presents, as a quotient of
the initial algebra, a theory with a new element `c` satisfying
`s(c) = c`: non-creative, not eliminable, and without a solution in the
natural numbers. Its unique solution exists in completely iterative
algebras, the M-type among them. Guarded blocks are therefore
definitional relative to those algebras and not relative to all; a
quotient of a W-type does not capture them. The reading of Milius and
Moss's unique-solution theorem as "guarded presentations are
definitional among completely iterative monads" is unverified.

## The design question to open with

How to build the quotient of a presentation whose sides are free-monad
terms. The session starts by brainstorming this with the user
(`superpowers:brainstorming`, then design in the session; AGENTS.md has
no written specification). Three candidates:

1. Kleisli restriction. Keep the presheaf W-type of terms and
   witnesses, and let restriction of a witness to an endpoint produce a
   free-monad term over the witness's arguments, computed by
   substitution (`link`) rather than by rebuilding a root. This keeps
   the quotient development's framing and its proof-relevant witnesses,
   and needs a carrier whose restriction maps are Kleisli morphisms,
   which `Obstruction.lean` shows a presheaf W-type is not; it touches
   `TODO.md` § Polynomial functors item 4 (relative free monads).
2. Derivations. Witnesses are derivation trees of equational logic,
   an instance of an equation under a substitution in a context, with
   the equivalence closure left to `Quot` as the quotient development
   does. Endpoints are computed by a fold over the derivation, so the
   obstruction does not arise, and witnesses stay proof-relevant.
3. Rewriting at a vertex. One step relates `t` and `u` when, at a vertex
   `v` of `t`, the subterm is an instance of one side of an equation
   and `u` replaces it by the same instance of the other side;
   `Quot` takes the equivalence closure. Congruence is automatic, since
   `v` ranges over every node. It reuses `Vertex` and `subterm`, and
   needs one new operation: replacement of the subterm at a vertex, the
   other half of the vertex's decomposition of a term into a one-hole
   context and a subterm. Witnesses are not proof-relevant.

The earlier session inclined to option 3 as the smallest, since it
turns the cofree-comonoid side of the definitions design into the means
of locating redexes; whether proof-relevant witnesses matter, as they
do for the manual chapter's constructions, decides between it and the
other two. The user chooses.

## Work breakdown

1. Orientation. Run the session-start checks (AGENTS.md § Session-start
   checks). Read [definitions.md](definitions.md) (§ Which equations
   are definitions; § Equations in slice, presheaf and depth-indexed
   settings), the modules above, and the manual chapter. Verify the
   Kelly–Power and Suppes citations before recording them (neither is
   in [references.bib](references.bib) yet). Brainstorm the design
   question.
2. Presentations with free-monad sides. A structure whose sides are
   `P.FreeM (V e)`, equivalently a signature of equations with two
   `Derived` maps; the embedding of `Signature.Equations` through
   `FreeM.liftObj`; satisfaction, `∀ e σ, eval alg σ (lhs e) =
   eval alg σ (rhs e)`, agreeing with `Signature.Satisfies` on
   one-step presentations.
3. The quotient, by the chosen option, and its initiality among models,
   constructive for finitary signatures through finitely many choices
   as in `Congruence.lean`.
4. Agreement with the quotient development on one-step presentations:
   the two quotients are isomorphic as initial models.
5. Definitional presentations. A univariate sum of polynomial functors;
   the presentation of `δ : Derived P Q` over `P ⊕ Q`; that unfolding
   coequalizes and the inclusion of `T_P` is a section; that the
   composite `T_P → quotient` is a bijection; that the models of the
   presentation correspond to the algebras of `P`, through
   `derivedAlg` and `eval_expandOps`. Well-founded blocks as
   presentations with constants, through `WFBlock.existsUnique_isSolution`.
6. Examples. Associativity and a unit law presenting the free monoid on
   binary trees; commutativity agreeing with
   `GebTests/Prototypes/QuotientPRA/CommTree.lean`; a definition of depth
   two (`quad(x) ≈ double(double(x))`) whose quotient is the base; the
   block `c = s(c)`, whose quotient is not.
7. Documentation. A section of [definitions.md](definitions.md) on
   definitions as presentations, recording the analysis above as the
   work establishes it; the manual chapter's status lines and items if
   the work bears on them; [index.md](index.md) entries in the same
   branch; `TODO.md` follow-ups; this handoff removed or revised.

Done means: the modules build with their tests, the axiom linter passes
on them, and `scripts/pre-push.sh` is clean.

## Conventions and pitfalls

- VCS is `jj` in a colocated checkout; route every mutation through
  it. Bookmarks do not follow a new commit: set them after committing.
  One concern per branch; no push without the user's line-by-line
  review; subjects in mathlib's convention, at most 72 characters.
- Every recursion goes through a recursor (`FreeM.rec`, `WType.rec`,
  `Nat.rec`): no `induction` tactic, no self-calling `def`, no
  self-referential `inductive` (a `Prop` relation included). No
  `noncomputable`.
- The axiom linter, `lake exe batteries/runLinter <Module>`, decides
  choice-freedom, not `#print axioms`: it stops at
  `GebMeta.upstreamChoiceRoots` (core's `Fin` order instances).
  mathlib's `PFunctor.M.dest`, `mk_dest`, `dest_corec`, `corec_unique`
  and `bisim` fail it; `M.mk`, `M.corec`, `M.corec_def`, `M.approx_mk`,
  `M.ext'` and `M.truncate_approx` pass. Use `Geb.MType.M` for anything
  that destructs an M-type value.
- Unfolding `Geb.MType.M.corec` by definitional equality exhausts the
  heartbeat limit; state one layer through `dest_corec` and `dest_mk`
  and `rfl` facts about the step function.
- `rw` closes goals only up to reducible `rfl`; a goal needing
  structure eta needs an explicit `rfl` after it.
- Numerals at a direction type such as `P.B a` where `P.B` is computed
  by `Option.elim` fail instance search; annotate them, `(0 : Fin 2)`.
- Literate modules: `set_option doc.verso true in` before the module
  docstring and `set_option doc.verso true` after it; every code span
  in any docstring carries a role (`{name}` for a constant declared
  earlier or imported, `{lit}` otherwise, `{cite}` for a key of
  `docs/references.bib`, with `meta import GebMeta -- shake: keep`).
- Tests: a `#guard` needs `public meta import` of the module under test,
  with `-- shake: keep`; a named declaration anchors an import for
  `lake shake`.
- Never write "position" for either half of a polynomial: shapes and
  directions; vertices are the directions of the cofree comonoid.
- The arXiv MCP's `get_abstract` failed on valid identifiers; fetching
  `https://arxiv.org/abs/<id>` works.
- `scripts/pre-push.sh` takes several minutes; run it in the background.

## References

- Kelly, G. M. and Power, A. J., "Adjunctions whose counits are
  coequalizers, and presentations of finitary enriched monads",
  Journal of Pure and Applied Algebra 89 (1993) 163–179,
  doi:10.1016/0022-4049(93)90092-8: finitary monads presented by
  operations and equations, as coequalizers of free monads.
- Suppes, P., Introduction to Logic, Van Nostrand, 1957, pp. 151–173:
  the criteria of eliminability and non-creativity.
- Keys already in [references.bib](references.bib): `MiliusMoss2009`,
  `FiorePittsSteenkamp2020`, `Dijkstra2017`,
  `AltenkirchCapriottiDijkstraKrausNordvallForsberg2018`,
  `AhmanChapmanUustalu2014`, `NiuSpivak2023`, `LibkindSpivak2025`,
  `BirkedalMogelbergSchwinghammerStovring2012`, `AtkeyJohannGhani2012`,
  `FioreGambinoHylandWinskel2008`.
