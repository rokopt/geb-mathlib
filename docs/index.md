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
  `sigmaSubtypeEquiv` commutes a sigma with a fiberwise subtype;
  `arrowPEmptyEquiv` equates empty-valued function types across
  universes. `Classical.choice`-free.
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
- `Geb/Mathlib/Data/W/Basic.lean` — the two laws of the W-type fold
  mathlib does not state: the computation rule `WType.elim_mk` and
  uniqueness `WType.elim_unique`. Together with mathlib's `WType.elim`
  they are the initiality of `WType β` among algebras of the polynomial
  endofunctor `X ↦ Σ a, β a → X`, stated concretely. `WType.para`
  generalises the fold to a paramorphism, whose step additionally sees
  each node's children as subtrees, with computation rule `WType.para_mk`
  [Meertens1992]. `WType.beq` is Boolean equality of W-trees, decidable
  when the shape type has decidable equality and every direction type is
  finitely enumerable; `WType.beq_eq_true_iff` is its correctness lemma
  and `WType.instDecidableEq` the resulting `DecidableEq (WType β)`
  instance, which mathlib reaches only through `Encodable`, at the cost
  of an unwanted countability hypothesis. Depends on mathlib's
  `Data/W/Basic.lean` and `Geb/Mathlib/Data/FinEnum.lean`; no category
  theory.
- `Geb/Mathlib/Data/PFunctor/Univariate/` — the categorical reading of
  mathlib's univariate `PFunctor`. `Functor.lean` packages the
  interpretation as `PFunctor.functor : Type v ⥤ Type (max v uA uB)`,
  transported from the upstream `Functor` / `LawfulFunctor` instances
  along `ofTypeFunctor`. `W.lean` gives the W-type its algebra
  structure (`wAlgebra`), the algebra morphism into any algebra
  (`wElim`), initiality as `Unique` on the hom-sets (`wUniqueHom`), and
  the structure map as an isomorphism (`wStrIso`); all of it is
  `Classical.choice`-free. `Initial.lean` packages that initiality as
  mathlib's `Limits.IsInitial` (`wIsInitial`) and is listed in
  `GebMeta.classicalAllowedModules`, since
  `Limits.IsInitial.ofUnique` is `Classical.choice`-dependent.
  Consumers wanting a choice-free development use `wUniqueHom`
  directly. Depends on mathlib's `Data/PFunctor/Univariate/Basic.lean`,
  `CategoryTheory/Endofunctor/Algebra.lean`, and
  `Geb/Mathlib/Data/W/Basic.lean`, and mathlib's
  `CategoryTheory/Types/Basic.lean` and
  `CategoryTheory/Limits/Shapes/IsTerminal.lean`.
- `Geb/Mathlib/Data/PFunctor/Slice/` — slice polynomial functors on
  `Type`. Given a `PFunctor` with a direction-input map `r : Idx → dom`
  and a shape-output map `q : A → cod`, a restriction of the `PFunctor`
  interpretation defines a functor `Type/dom → Type/cod`.
  `Slice/Basic.lean` is the constructive core (`SliceDomPFunctor`,
  `SlicePFunctor`, `Compatible`, `obj`/`map` with functoriality),
  `Classical.choice`-free. `Slice/Functor.lean` packages it
  categorically: `domSubfunctor` cuts the `r`-compatible assignments out
  of the underlying polynomial functor `Over.forget dom ⋙ PFunctor.functor`,
  `domFunctor : Over dom ⥤ Type` reads that subfunctor as a functor, and
  `functor : Over dom ⥤ Over cod` is its `Functor.toOver` lift;
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
- `Geb/Mathlib/Data/FinEnum.lean` — three choice-free `Decidable`
  instances for mathlib's `FinEnum`: `FinEnum.decidableForallFinEnum`
  (a bounded `∀`), `FinEnum.decidableForallSubtype` (a bounded `∀` over
  a decidable subtype, without forming a `FinEnum` on the subtype), and
  `FinEnum.decidablePiFinEnum` (`DecidableEq` of functions out of a
  finitely enumerable domain, given `DecidableEq` of the codomain).
  Each routes through `List.decidableBAll` over `FinEnum.toList`, unlike
  mathlib's own route through `Fintype`, which is `Classical.choice`-
  dependent. `Classical.choice`-free.
- `Geb/Mathlib/Data/PFunctor/Univariate/Finitary.lean` —
  `PFunctor.Finitary`, the condition that every shape has finitely many
  directions (`∀ a, FinEnum (P.B a)`). A reducible `abbrev` on
  `PFunctor` rather than a `class`, so `[F.Finitary]` is transparent to
  instance resolution and serves as the finitary binder for the slice
  and presheaf layers as well, through their `toPFunctor` projections.
  `Classical.choice`-free.
- `Geb/Mathlib/Data/PFunctor/Slice/Decidable.lean` — decidability of
  the slice functor's term-level predicates, given `F.Finitary` and
  decidable equality of the base or output index type:
  `SliceDomPFunctor.decidableDirectionOver` and
  `SlicePFunctor.decidableShapeOver` decide the two fiber predicates;
  `SliceDomPFunctor.decidableForallDirection` decides a quantifier over
  the directions of a shape lying over an index;
  `SliceDomPFunctor.decidableCompatible` decides `Compatible`; and
  `SlicePFunctor.decidableWValid` decides `WValid`, computed by the
  `WType.elim` fold `wValidData`/`wValidStep` alongside the tree's root
  index in a single pass, with correctness lemma
  `wValidBool_eq_true_iff`. `Classical.choice`-free.
- `Geb/Mathlib/Data/PFunctor/Presheaf/Decidable.lean` — decidability of
  the presheaf functor's naturality predicates.
  `PresheafDomPFunctorData.decidableIsNatural` decides `IsNatural`
  given finitarity, a finite index category (`FinEnum I` and finite
  hom-sets), and decidable equality of the input presheaf's values.
  `PresheafPFunctor.decidableIsHereditarilyNatural` decides
  `IsHereditarilyNatural` through a classless `Bool`-valued core,
  `isHereditarilyNaturalBoolCore` (a `WType.para` fold over the raw
  tree, with correctness lemma
  `isHereditarilyNaturalBoolCore_eq_true_iff`), taking every finiteness
  and decidability datum as an explicit argument because instance
  resolution does not traverse the `PresheafPFunctor` diamond to
  synthesise `decidableForallDirection` there. `Classical.choice`-free.
- `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` — the free
  coproduct completion of a type `D` treated as a discrete category:
  the category of families of elements of `D` (the discrete case of
  the family construction `Fam C`, a Grothendieck construction).
  Objects pair an index type with a `D`-valued assignment; morphisms
  (`Hom`, with the codomain transport `homOfEq`) are index functions
  commuting with the assignments. `Map`/`MapMor` are the object-map
  and morphism-map components of functors between the free coproduct
  completions of two (generally different) types, with `Endo`/`EndoMor`
  the endofunctor specializations `Map D D`/`MapMor D D`, and
  `coprod`/`coprodMor` are the indexed coproducts with their
  functorial action, `Hom.comp` their composition (in diagrammatic
  order) and `Hom.id` their identity, with the category laws
  (`Hom.id_comp`/`Hom.comp_id`/`Hom.comp_assoc`) and the
  functoriality of `coprodMor`
  (`coprodMor_id`/`coprodMor_comp`). `coprodPair`/`plus` are the
  binary coproduct and its
  fixed-left-object specialization, with injections
  `coprodPairInl`/`coprodPairInr` (whose two summands may sit at
  different index universes) and the universal cotuple
  `coprodPairDesc`; `copower`/`copowerEquiv` are the copower and its
  universal property; `lift`/`homLiftEquiv` are the `ULift` renaming
  of an object and its universal property. `Iso` is the isomorphism
  type (a name-type equivalence commuting with the decodings), with
  `refl`/`symm`/`trans`, the transport `isoOfEq`, and the congruence
  `coprodIso` of `coprod` along an index equivalence and a family of
  isomorphisms of the summands. `emptyObj`/`emptyDesc` are the
  initial object and its universal morphism, with uniqueness.
  `coprodInj`/`coprodDesc`/`coprodHomEquiv` are the injections, the
  cotuple, and the universal property of the indexed coproduct, with
  the composition compatibilities; `coprodPairMor` is the functorial
  action of `coprodPair` on morphisms, with its laws.
  `homSingletonEquiv` describes morphisms out of a singleton object
  as the fiber of the decoding over its value. `Iso.hom`/`Iso.invHom`
  are the underlying morphisms of an isomorphism, with the inverse
  laws. No mathlib
  `Category` instance is taken: the categorical packaging is deferred
  to a `Classical.choice`-enabled wrapper (see `TODO.md` § Complete
  Theorem 2.4 for `IndRec`). `Classical.choice`-free.
- `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc/NatTrans.lean` —
  natural transformations between morphism-mapped object maps of
  free coproduct completions: the naturality condition
  (`IsNatTrans`), the transformation space (`NatTrans`, a subtype
  over the `Prop`-valued condition), the vertical structure
  (`NatTrans.id`/`NatTrans.vcomp` with the category laws),
  whiskering and horizontal composition with the coherence and
  interchange laws (taking the outer morphism map's
  `PreservesId`/`PreservesComp` laws as hypotheses), inverse pairs
  (`NatTrans.IsInverse`) with the conversion of a natural family
  of isomorphisms (`NatTrans.ofIsoFamily`/`invOfIsoFamily`),
  transport equivalences
  (`NatTrans.equivOfInverseTarget`/`equivOfInverseSource`,
  `NatTrans.congrSource`), the coproduct decomposition
  (`natCoprodEquiv`), and the copower–Yoneda adjunction
  (`natCopowerPlusEquiv`). `Classical.choice`-free.
- `Geb/Mathlib/Data/PFunctor/IndRec/` — codes for positive
  inductive-recursive definitions (Dybjer–Setzer IR codes, following
  Ghani–Nordvall Forsberg–Malatesta Section 2; the module docstring
  carries the citations). `IR I O` is the type of codes with input
  index type `I` and output index type `O` (the input/output split
  follows Hancock–McBride–Ghani–Malatesta–Altenkirch Definition 3):
  the W-type of the polynomial functor `IR.pFunctor` whose shapes are
  the three code constructors (`IR.iota`, `IR.sigma`, `IR.delta`)
  and whose directions are their subcode arities. One functor layer
  carries a destructor interface (`IR.Dest` and the dependent
  `IR.DepDest`, each with `elim`/`elimInv` and the equivalences
  `IR.destEquiv`/`IR.depDestEquiv`); the code type carries
  extensionality (`IR.ext`/`IR.snd_eq_of_eq`), the eliminator
  `IR.elim`, the induction principle `IR.induction`, and the dependent
  recursor `IR.rec`, derived through the fold into a sigma type
  (`IR.sigmaRec`) with step arguments
  `IR.RecStep`/`IR.InductionStep` specializing the `Sort`-valued
  `IR.Step`. A code is interpreted as a functor from the free
  coproduct completion of `I` to that of `O`
  (both treated as discrete categories,
  `CategoryTheory.FreeCoprodCompDisc`, its own module above):
  `IR.interpObj` and `IR.interpMor` are the object and morphism maps
  of the interpretation, with the propositional computation rule
  `IR.rec_mk` and the functor laws (see the
  `Geb/Mathlib/Data/PFunctor/IndRec/Functor.lean` entry below). The
  initial algebras of the interpreted endofunctors (the `IR I I`
  case) are deferred (see `TODO.md` § Complete Theorem 2.4 for
  `IndRec`). `IR.precomp` precomposes a code along a coproduct (the `γ^i` of
  Hancock–McBride–Ghani–Malatesta–Altenkirch, Definition 3's
  discussion and Lemma 4, which asserts existence only; this
  construction is the project's), with computation rules at each
  code constructor (Hancock–McBride–Ghani–Malatesta–Altenkirch,
  Lemma 4). `IR.interpPrecompIso` establishes Lemma 4:
  interpreting a precomposed code is isomorphic to interpreting the
  original code at the coproduct object, generated by `IR.rec` from
  per-shape steps; the paper states an equality, recorded here as the
  deviation to a pointwise isomorphism (the naturality upgrade is
  `IR.interpPrecompIso_natural` in `Naturality.lean`, below).
  `IR.interpDeltaIso`
  establishes Lemma 3: the dependent product (`delta`) interpretation
  is isomorphic to the indexed coproduct, over its direction
  assignments, of copowers of the subcode interpretations by the
  morphisms into the object; the paper states a natural isomorphism,
  recorded here as the deviation to the pointwise statement (the
  per-summand natural form is `IR.natDeltaEquiv` in
  `Naturality.lean`, below).
  `Classical.choice`-free.
- `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean` — the homset of `IR`
  codes (Hancock–McBride–Ghani–Malatesta–Altenkirch Definition 8),
  `IR.Hom`, by `IR.elimAlg` on the domain code with `IR.InnerHom`
  (`IR.elimAlg` on the codomain) in the `ι`-case. The identity morphism
  `IR.id` — a construction, since the paper gives no explicit one — is
  built
  through a list-generalized pre-unit `IR.preUnitStack`, using
  injection helpers (`IR.sigmaPush`, `IR.deltaEmptyPush`,
  `IR.msigmaPush`) and a navigation construction (`IR.deltaNavBase`,
  `IR.deltaNav`) up an iterated-precomposition tower recorded by
  `IR.mprecomp` (folding `IR.precomp` over a list of superscript
  objects `IR.SupObj`). The recursions of `IR.sigmaPush`,
  `IR.deltaEmptyPush`, and `IR.preUnitStack` run over named motives
  and steps, so each carries its computation equations at the three
  code constructors (`IR.sigmaPush_mk_iota` and its siblings).
  `Classical.choice`-free.
- `Geb/Mathlib/Data/PFunctor/IndRec/Functor.lean` — the
  functoriality content of Theorem 2.4 of
  Ghani–Nordvall Forsberg–Malatesta (attributed there to
  Dybjer–Setzer): the characterizing equations of `IR.interpMor`
  at each code constructor (from the propositional computation
  rule `IR.rec_mk` of `Basic.lean`), and preservation of identity
  (`IR.interpMor_id`) and composition (`IR.interpMor_comp`), so
  the interpretation of a code is a functor between free coproduct
  completions. The composition proof eliminates the
  morphism-commutation equalities before the shape split, reducing
  both laws to the functoriality of `FreeCoprodCompDisc.coprodMor`
  (`coprodMor_id`/`coprodMor_comp`, with the identity `Hom.id` and
  category laws, in `FreeCoprodCompDisc.lean`).
  `Classical.choice`-free.
- `Geb/Mathlib/Data/PFunctor/IndRec/Naturality.lean` — Theorem 3
  of Hancock–McBride–Ghani–Malatesta–Altenkirch: the homset
  between two codes is equivalent to the space of natural
  transformations between their interpretations
  (`IR.interpHomEquiv`, with the directions
  `IR.interpHom`/`IR.natToHom` and their round-trip laws), by
  `IR.rec` on the domain code. The `δ`-case goes through the
  per-summand naturality upgrade of Lemma 3 (`IR.deltaInto`,
  `IR.deltaDesc`, `IR.natDeltaEquiv`), the copower–Yoneda
  adjunction, the plus-lift bridge (`IR.plusLiftBridgeNat`), and
  the naturality upgrade of Lemma 4
  (`IR.interpPrecompIso_natural`); the `σ`-case through the
  coproduct decomposition; the `ι`-case through the ∅-evaluation
  equivalence (`IR.natIotaEquiv`) and the `InnerHom` fiber
  equivalence (`IR.innerHomEquiv`). `Classical.choice`-free.
- `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean` — Corollary 2
  of Hancock–McBride–Ghani–Malatesta–Altenkirch: `IR` codes over a
  fixed input/output index pair, with the homsets of Definition 8,
  form a category. Composition (`IR.comp`) is the code morphism
  carried by the vertical composite of the interpreted
  transformations, and the category laws (`IR.id_comp`,
  `IR.comp_id`, `IR.comp_assoc`) follow from the vertical laws
  together with the round-trip laws of the Theorem 3 equivalence;
  `IR.interpHom_comp` records that the interpretation is
  functorial on composition; `IR.interpHom_id` records that it is
  functorial on the identity and, consumed by the identity laws as
  the identity-image equation, is proved by induction on the domain
  code with the stack of `IR.preUnitStack` generalized
  (`IR.interpHom_preUnitStack`), against the semantic counterpart of
  that stack: the iterated coproduct tower (`IR.mplus`,
  `IR.mplusInj`, `IR.mplusMorMap`) with its iterated Lemma 4
  isomorphism (`IR.mprecompIso`, natural in the interpreted object
  by `IR.mprecompIso_natural`) and the semantic pre-unit component
  (`IR.preUnitComponent`). The induction consumes the
  characterizing equations of `IR.interpHom` at each code
  constructor (`IR.interpHom_iota`, `IR.interpHom_sigma`,
  `IR.interpHom_delta`) and a characterization of each injection
  helper of `Hom.lean` as composition with an explicit semantic
  inclusion (`IR.interpHom_sigmaPush`,
  `IR.interpHom_deltaEmptyPush`, `IR.interpHom_msigmaPush`,
  `IR.interpHom_deltaNavBase`, `IR.interpHom_deltaNav`).
  `Classical.choice`-free.
- `Geb/Mathlib/Data/PFunctor/IndRec/Universes.lean` — `univCode`
  instantiates the theory: the code of the universe generated by an
  arbitrary family of starting types and closed under dependent sums
  and dependent products (Ghani–Nordvall Forsberg–Malatesta
  Examples 2.5 and 2.6, combined and generalized), assembled from
  constructor subcodes (`univBinder`, `univSigma`, `univPi`,
  `univIota`, `univConstructorCode` over the constructor index
  `UnivConstructor`), with interpretation maps
  `univEndo`/`univEndoMor`. `Classical.choice`-free.
- `Geb/Mathlib/Data/PFunctor/IndRec/Container.lean` — `contCode`
  translates a simple container (a `PFunctor`) to an `IR` code over
  the unit type (Hancock–McBride–Ghani–Malatesta–Altenkirch
  Example 1). `Classical.choice`-free.
