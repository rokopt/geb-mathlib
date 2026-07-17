# geb-mathlib documentation

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Directory structure](#directory-structure)
- [Implemented content](#implemented-content)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Directory structure

The repository is laid out narrow-and-deep, with one indexing
`.lean` file per directory.

- `Geb/` — root namespace, split between upstream-eligible and
  downstream-only content.
  - `Geb/Mathlib/` — content authored in mathlib's style and
    intended for eventual upstream extraction to mathlib4;
    imports from `Mathlib.*` and `Geb.Mathlib.*` only.
  - `Geb/Cslib/` — content authored in CSLib's style and
    intended for eventual upstream extraction to CSLib;
    imports from `Mathlib.*`, `Cslib.*`, and `Geb.Cslib.*`
    only.
  - `Geb/Internal/` — content not intended for upstream
    extraction; may import from `Mathlib.*`, `Cslib.*`,
    `Geb.Mathlib.*`, `Geb.Cslib.*`, or `Geb.Internal.*`.
- `GebTests/` — test library mirroring `Geb/`'s structure, with
  `GebTests/Mathlib/`, `GebTests/Cslib/`, and
  `GebTests/Internal/` subdirectories.

The directory split denotes upstream eligibility; the
import-direction rules above are enforced by
`scripts/lint-imports.sh` and corresponding CI.

## Implemented content

- `Geb/Mathlib/Logic/Equiv/Basic.lean` — extensions of mathlib's
  `Mathlib/Logic/Equiv/Basic.lean`. `sigmaFstSectionElim` eliminates a
  function into a sigma type along a proof that it is a section of the
  first projection, producing a dependent function (the inverse
  direction of mathlib's `Equiv.piEquivSubtypeSigma`).
  `Classical.choice`-free.
- `Geb/Mathlib/CategoryTheory/Grothendieck.lean` — covariant and
  contravariant Grothendieck constructions for 1-functors.
  `Grothendieck.functorToCat` packages mathlib's covariant
  construction as a functor to `Cat`. `GrothendieckOp F` is the
  covariant construction applied to the oppositization
  `F ⋙ Cat.opFunctor`; `CoGrothendieck G`, for `G : Cᵒᵖ ⥤ Cat`,
  is its opposite category — the contravariant Grothendieck
  construction, which mathlib states in a comment but implements
  only for pseudofunctors. Both carry constructor/destructor
  interfaces (`mk`/`base`/`fiber`, `homMk`/`homBase`/`homFiber`)
  using morphisms of `C`, with `rfl` round-trips, projections
  (`forget`), functoriality (`map`), and packaged forms
  (`functor` into `Over`, `functorToCat` into `Cat`). The source
  and test modules are listed in `GebMeta.classicalAllowedModules`
  because mathlib's `Grothendieck` and `Cat.opFunctor` are
  `Classical.choice`-dependent.
- `Geb/Mathlib/Data/PFunctor/Slice/` — slice polynomial functors on
  `Type`. Given a `PFunctor` with a direction-input map `r : Idx → dom`
  and a shape-output map `q : A → cod`, a restriction of the `PFunctor`
  interpretation defines a functor `Type/dom → Type/cod`.
  `Slice/Basic.lean` is the constructive core (`SliceDomPFunctor`,
  `SlicePFunctor`, `Compatible`, `obj`/`map` with functoriality),
  `Classical.choice`-free. `Slice/Functor.lean` packages it
  categorically as `domFunctor : Over dom ⥤ Type` (reusing the core
  `obj`/`map`) and, via `Functor.toOver`, `functor : Over dom ⥤ Over cod`;
  that module is listed in `GebMeta.classicalAllowedModules` because
  mathlib's `Over` is `Classical.choice`-dependent at the type level.
  `Slice/W.lean` builds the W-type (initial algebra) of a slice
  endofunctor (`dom = cod = I`) on top of mathlib's `PFunctor` W-type.
  The root index `wIndexRoot` (a tree's root output index) is non-recursive; the
  domain-restriction predicate `WValid` comes from the non-dependent
  W-type eliminator `WType.elim`, which folds an index and a validity
  component together as `wIndexValid : P.W → WIndex I` (its index
  component agreeing with `wIndexRoot`). The carrier `W` is the
  admissible trees, with structure map `wIndex`, mutually-inverse
  constructor and destructor `W.mk`/`W.dest`, and eliminator `W.elim`
  into any slice algebra over `I`. Only the existence half of
  initiality is established (the carrier, its fixed-point structure,
  and the catamorphism `W.elim` with its laws), not uniqueness.
  `Classical.choice`-free.
- `Geb/Mathlib/Data/PFunctor/Presheaf/` — presheaf polynomial functors
  (parametric-right-adjoint functors `(Iᵒᵖ ⥤ Type) ⥤ (Jᵒᵖ ⥤ Type)`),
  built as a restriction of `SlicePFunctor`. The per-layer structure
  mirrors the slice pattern: a `…Data` record bundles the operations, a
  `Prop`-valued `…Data.IsFunctorial` record carries the named law
  conditions, and the bundle wraps both. `Presheaf/Basic.lean` is the
  constructive core (`PresheafDomPFunctor`, `PresheafPFunctor`,
  `obj`/`map`, `objPresheaf` assembling the output as a
  presheaf), `Classical.choice`-free. `Presheaf/Functor.lean` packages
  the result as a categorical functor (`domFunctor`, `functor`); that
  module is listed in `GebMeta.classicalAllowedModules`.
  `Presheaf/W.lean` builds the W-type (initial algebra) of a presheaf
  endofunctor (`I = J`) on top of the slice W-type. Its carrier is the
  presheaf `W : Iᵒᵖ ⥤ Type (max uI uA uB)` whose fiber over `j` is the
  `ULift` of the hereditarily-natural slice W-trees indexed at `j`
  (`IsHereditarilyNatural`, the tree-level analogue of `IsNatural`, defined
  through the slice W-type's `Prop`-valued paramorphism); restriction is the
  root-only `wRestr`. The `ULift` places the fibers at the functor's value
  universe `max uI uA uB`, since the presheaf functor raises the value
  universe by `uI` through the total-space `Σ` of `elemProj`. Mutually
  inverse `W.mk`/`W.dest` exhibit `W` as a fixed point of the
  `objPresheaf`-action, and `W.elim` is the eliminator into any presheaf
  algebra, computed by a bespoke `WType.elim` fold whose value is guarded by
  hereditary naturality (the presheaf algebra acts only on natural nodes).
  Only the existence half of initiality is established (carrier, fixed
  point, and `W.elim` with `elim_mk`/`comp_elim`), not uniqueness.
  `Classical.choice`-free.
- `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` — the free
  coproduct completion of a type `D` treated as a discrete category:
  the category of families of elements of `D` (the discrete case of
  the family construction `Fam C`, a Grothendieck construction).
  Objects pair an index type with a `D`-valued assignment; morphisms
  (`Hom`, with the codomain transport `homOfEq`) are index functions
  commuting with the assignments. `Endo`/`EndoMor` are the object-map
  and morphism-map components of endofunctors, and
  `coprod`/`coprodMor` are the indexed coproducts with their
  functorial action. No mathlib
  `Category` instance is taken: the categorical packaging is deferred
  to a `Classical.choice`-enabled wrapper (see `TODO.md` § Complete
  Theorem 2.4 for `IndRec`). `Classical.choice`-free.
- `Geb/Mathlib/Data/PFunctor/IndRec/` — codes for positive
  inductive-recursive definitions (Dybjer–Setzer IR codes, following
  Ghani–Nordvall Forsberg–Malatesta Section 2; the module docstring
  carries the citations). `IR D` is the type of codes with output type
  `D`: the W-type of the polynomial functor `IR.pFunctor` whose shapes
  are the three code constructors (`IR.iota`, `IR.sigma`, `IR.delta`)
  and whose directions are their subcode arities. One functor layer
  carries a destructor interface (`IR.Dest` and the dependent
  `IR.DepDest`, each with `elim`/`elimInv` and the equivalences
  `IR.destEquiv`/`IR.depDestEquiv`); the code type carries
  extensionality (`IR.ext`/`IR.snd_eq_of_eq`), the eliminator
  `IR.elim`, the induction principle `IR.induction`, and the dependent
  recursor `IR.rec`, derived through the fold into a sigma type
  (`IR.sigmaRec`) with step arguments
  `IR.RecStep`/`IR.InductionStep` specializing the `Sort`-valued
  `IR.Step`. A code is interpreted on
  the free coproduct completion of `D` treated as a discrete category
  (`CategoryTheory.FreeCoprodCompDisc`, its own module above):
  `IR.interpObj` and `IR.interpMor` are the object and morphism maps
  of the interpretation. The functor
  laws completing Theorem 2.4, the propositional computation rule of
  `IR.rec`, and the initial algebras of the interpreted endofunctors
  are deferred (see `TODO.md` § Complete Theorem 2.4 for `IndRec`).
  `univCode` instantiates the theory: the code of the universe
  generated by an arbitrary family of starting types and closed under
  dependent sums and dependent products (Examples 2.5 and 2.6,
  combined and generalized), with interpretation maps
  `univEndo`/`univEndoMor`. `Classical.choice`-free.
