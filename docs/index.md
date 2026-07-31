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
    imports from `Mathlib.*`, `Batteries.*`, and `Geb.Mathlib.*`
    only. Where those import rules leave no alternative, a module
    here may instead target Lean core or Batteries; that
    destination is open, per `TODO.md` § Upstream destination of
    core- and Batteries-targeted content.
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
  universes. `Equiv.arrowCongrLeftC` transports a function type along
  an equivalence of its domain. `Classical.choice`-free.
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
- `Geb/Mathlib/Data/Tree/Binary.lean` — unlabelled binary trees as the
  W-type of a two-element shape family: `BinTree.Shape`,
  `BinTree.Direction` (`Fin 0` at a leaf, `Fin 2` at a node),
  `BinTree := WType Direction`, the constructors `leaf` and `node`,
  `size` counting nodes and leaves alike, and `BinTree.induction`, which
  gives induction in the two-constructor presentation so that no
  downstream proof mentions `WType.rec`. `Direction` is `@[expose]`
  because the module system does not unfold a non-exposed definition and
  `WType.mk .leaf Fin.elim0` would not elaborate without it. Depends on
  mathlib's `Mathlib/Data/W/Basic.lean`.
- `Geb/Mathlib/Data/Tree/Preorder.lean` — the preorder encoding of
  binary trees as bitstrings and its inverse. `BinTree.print` spells a
  leaf `[false]` and a node a `true` bit followed by its children;
  `parseStep`, `parseAux` and `parse` are the fuel-bounded
  recursive descent, bounded by an explicit `ℕ` because a child is
  parsed from a remainder the previous call computes;
  `depth` and `ok` are the stack depth read right to left and the
  condition that every node bit is read at depth at least two, and
  `Valid w` is their conjunction with `depth w = 1`. `parse_print` and
  `print_injective` give the retraction and injectivity;
  `parseAux_eq_some` and `parse_eq_some_iff` give the other direction,
  so the parser is the printer's inverse and not merely its retraction;
  `valid_iff_exists_print` characterizes the encoding's image, and is
  what the Bellantoni-Cook recognizer's correctness is stated against,
  and `valid_iff_isSome_parse` reads that characterization as a decision
  procedure. Cites mathlib's `DyckWord` as the adjacent bijection it
  does not reuse. Depends on `Geb.Mathlib.Data.Tree.Binary`.
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
  `MemW` states fiber membership on a raw W-tree, so that it can be
  decided by a fold, and `memW_iff_exists_obj` identifies it with the
  carrier's fiber. `Classical.choice`-free.
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
- `Geb/Mathlib/Computability/BellantoniCook/Basic.lean` — the function
  class `B` of [HeraudNowak2011] § 3.2: its arity relation as a
  `SlicePFunctor` over `ℕ × ℕ`, its syntax as that functor's slice
  W-type, and its semantics by the W-type's eliminator. `compChildren`
  orders a `comp` node's children as `Direction` gives them. Depends on
  `Geb.Mathlib.Data.PFunctor.Slice.W` and
  `Geb.Mathlib.Data.PFunctor.Univariate.Finitary`. `evalRec` depends on
  `propext`; `finEnumCompDirection`, `sigFinitary`, `evalValue`,
  `evalStep` and `BC.eval` on `propext` and `Quot.sound`.
- `Geb/Mathlib/Computability/BellantoniCook/Tree.lean` — a recognizer
  for the preorder spellings of binary trees, as three expressions of
  `B`. `comb` is a `safeRec` carrying the stack depth and the underflow
  verdict in one value: the depth in unary offset by one while no node
  bit has been read below depth two, and the absorbing `[false]` once
  one has; `eqOne` tests a bitstring for length one; `isTree` applies
  `eqOne` to the scan's predecessor. `combSem_eq` identifies the scan
  with `BinTree.depth` and `BinTree.ok`; `eqOneSem_eq` identifies the
  one-test with a length test;
  `isTreeSem_eq_singleton_iff_valid` identifies the recognizer with
  `BinTree.Valid`, and `isTreeSem_eq_singleton_iff_exists_print`
  composes that with `BinTree.valid_iff_exists_print` to give acceptance
  of exactly the spellings of trees. The recognizer is a single scan
  rather than a recursive descent, a descent needing recursion on a safe
  argument, which the class forbids; each bit is read once. Depends on
  `Geb.Mathlib.Computability.BellantoniCook.Basic`,
  `Geb.Mathlib.Data.PFunctor.Slice.Decidable` and
  `Geb.Mathlib.Data.Tree.Preorder`.
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
- `Geb/Mathlib/Data/PFunctor/Presheaf/Finite/Basic.lean` — finite
  presheaf polynomial functors: a bundled structure
  `FinitePresheafPFunctor` wrapping `PresheafPFunctor I J` with
  `FinEnum` evidence for shapes, directions, the domain index category
  and its hom-sets, and the codomain index category. Derived
  projections supply `DecidableEq` on the shape and index types.
  Forwarding instances supply the bundled evidence to the existing
  general-tier decision procedures (`decidableIsNatural`,
  `decidableCompatible`, `decidableShapeOver`,
  `decidableDirectionOver`). `Classical.choice`-free.
- `Geb/Mathlib/Data/PFunctor/Presheaf/Finite/W.lean` — decidable
  membership in the carrier presheaf's fiber for finite presheaf
  polynomial endofunctors. The `Bool`-valued validator `wValidBool`
  conjoins slice admissibility (`SlicePFunctor.wValidBool`) and
  hereditary naturality (`isHereditarilyNaturalBoolCore`), and
  `memWBool` adds the index test; `wValidBool_eq_true_iff` and
  `memWBool_eq_true_iff` are their correctness lemmas, the latter
  stated against `PresheafPFunctor.MemW`, so `decidableMemW` decides
  the whole fiber condition by a single fold. Forwarding instances for
  `decidableWValid` and `decidableIsHereditarilyNatural`;
  `decidableEqW` provides `DecidableEq` on raw W-trees.
  `Classical.choice`-free.
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
  `IR.interpDeltaIso` establishes Lemma 3: the dependent product
  (`delta`) interpretation is isomorphic to the indexed coproduct,
  over its direction assignments, of copowers of the subcode
  interpretations by the morphisms into the object; the paper states
  a natural isomorphism, recorded here as the deviation to the
  pointwise statement (the per-summand natural form is
  `IR.natDeltaEquiv` in `Naturality.lean`, below).
  `Classical.choice`-free.
- `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean` — the homset of `IR`
  codes (Hancock–McBride–Ghani–Malatesta–Altenkirch Definition 8),
  `IR.Hom`, by `IR.elimAlg` on the domain code with `IR.InnerHom`
  (`IR.elimAlg` on the codomain) in the `ι`-case. The identity morphism
  `IR.id` — a construction, since the paper gives no explicit one — is
  built through a list-generalized pre-unit `IR.preUnitStack`, using
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
- `Geb/Mathlib/Data/Vector/OfFn.lean` — a choice-free `ofFn` for
  root `Vector`. Core's `Vector.ofFn` indexing lemmas depend on
  `Classical.choice` through the private `Array.getElem_ofFn_go`;
  `Vector.ofFnC` routes construction through `List.ofFn` instead,
  leaving the result array-backed and indexing constant-time.
  `Vector.get_eq_getElem` bridges to the `getElem` API.
  `Classical.choice`-free.
- `Geb/Mathlib/Data/Vector/Scatter.lean` — `Vector.scatter` writes a
  list of index-value pairs into a vector in one left-to-right pass,
  with `get_scatter_of_not_mem` for an index no pair carries and
  `get_scatter_of_mem` for an index carried with a single value. The
  second hypothesis is uniqueness of the value rather than
  distinctness of the indices, so a list of constant value needs no
  `Nodup`. Both lemmas quantify over the starting vector, and so
  apply part-way through a pass. `Classical.choice`-free.
- `Geb/Mathlib/Data/List/NodupEquivFin.lean` — extensions of
  mathlib's `Mathlib/Data/List/NodupEquivFin.lean`.
  `List.Nodup.getEquivC` rebuilds `List.Nodup.getEquiv` choice-free,
  substituting `List.idxOf_lt_length_of_mem` for the
  `Classical.choice`-dependent `List.idxOf_lt_length_iff`.
  `Fin.compressEquiv` renumbers the indices of `Fin n` satisfying a
  `Bool`-valued predicate onto an initial segment; it is in the `Fin`
  namespace, the module's `List` content being the rebuild.
  `Classical.choice`-free.
- `Geb/Mathlib/Data/Vector/NodupEquivFin.lean` —
  `Vector.invOfInjective` inverts an injective vector, stated over
  the `get` view rather than over `toList.Nodup`, with
  `invOfInjective_apply` reading its forward direction back as the
  vector's lookup. `Classical.choice`-free.
- `Geb/Mathlib/Data/UnionFind/OfEdges.lean` —
  `Batteries.UnionFind.Sized`, a union-find of a fixed size, so that
  its indices are `Fin n` and no operation changes their type;
  `Sized.ofEdges` folds `union` over a list of pairs. The two
  theorems about it are the two directions of correctness: every
  listed pair is merged, and nothing beyond them is, the latter in
  eliminator form rather than as a characterisation of the merged
  relation as an equivalence closure. Its upstream target is
  Batteries rather than mathlib4, per `TODO.md` § Upstream
  destination of core- and Batteries-targeted content.
  `Classical.choice`-free.
- `Geb/Mathlib/CategoryTheory/FinSetSkel/Basic.lean` — `FinSetSkel`,
  a skeletal category of finite sets whose morphisms are
  length-indexed vectors of codomain indices. Objects are a one-field
  structure, so the length projection reduces at reducible
  transparency; morphisms carry `DecidableEq` and `Repr`, both pinned
  to choice-free terms, and the representation is sealed once the
  `ofVec`/`toVec` API is in place. `Classical.choice`-free.
- `Geb/Mathlib/CategoryTheory/FinSetSkel/Skeleton.lean` — the
  comparison with `FintypeCat.Skeleton`. The comparison functors are
  mutually inverse on the nose, giving an isomorphism in `Cat` and
  not merely an equivalence, together with the transported `Skeletal`
  and `IsSkeletonOf`. Allowlisted for `Classical.choice`:
  `CategoryTheory.Cat.category` depends on it, so an `Iso` in `Cat`
  carries the dependence however it is built.
- `Geb/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean` — the
  coequalizer of a parallel pair in `FinSetSkel`, computed: the pairs
  a parallel pair generates are folded through
  `Batteries.UnionFind.Sized.ofEdges`, the roots are renumbered onto
  an initial segment by `Fin.compressEquiv`, and the carrier's length
  is the number of roots. The carrier, projection and factorisation
  are stated over the application-normal form `f.toVec.get i`, and
  each of the three definitions calling `Vector.ofFnC` carries an
  unfolding lemma stated by hand, `rw [Vector.get_ofFnC]` reporting no
  occurrence of the pattern where the index types differ.
  `Classical.choice`-free.
- `Geb/Mathlib/CategoryTheory/FinSetSkel/Coequalizer.lean` — the
  packaging of that construction as `ColimitCocone (parallelPair f g)`,
  the per-diagram `HasColimit`, and `HasCoequalizers FinSetSkel`.
  Allowlisted for `Classical.choice`: `Cofork.ofπ`,
  `Cofork.IsColimit.mk` and
  `hasCoequalizers_of_hasColimit_parallelPair` each depend on it,
  while the construction being packaged does not.
- `Geb/Mathlib/CategoryTheory/ElementaryTopos.lean` — the
  `ElementaryTopos` class: a cartesian closed category with a
  subobject classifier, carrying chosen data for the generators of
  its finite limits and finite colimits — the cartesian and closed
  structures, the initial object, binary coproducts, equalizers,
  coequalizers, and the classifier — and deriving `HasInitial`,
  `HasBinaryCoproducts`, `HasEqualizers`, `HasCoequalizers`,
  `HasFiniteCoproducts`, `HasFiniteLimits` and `HasFiniteColimits`
  from them. Accessors are definitions for the data-carrying classes
  and instances for the `Prop` classes. `tensorUnitIsoΩ₀` compares
  the cartesian terminal with the classifier's `Ω₀`, both being
  terminal. The source and test modules are listed in
  `GebMeta.classicalAllowedModules`, the module being a wrapper over
  mathlib's `Classical`-dependent category theory.
- `Geb/Mathlib/Data/Fin/Basic.lean` — choice-free division,
  remainder and pairing on `Fin`. Batteries' `Fin.divNat` proves its
  bound through `Nat.div_lt_of_lt_mul`, which depends on
  `Classical.choice`; `Fin.divNatC`, `Fin.modNatC` and `Fin.pairC`
  are choice-free counterparts of `Fin.divNat`, `Fin.modNat` and
  `Fin.mkDivMod`, with the round trips `Fin.divNatC_pairC`,
  `Fin.modNatC_pairC` and `Fin.pairC_divNatC_modNatC` exhibiting them
  as a bijection `Fin m × Fin n ≃ Fin (m * n)`. `Fin.modNat` and
  `Fin.mkDivMod` depend on no axiom outside `propext`, so
  `Fin.modNatC` and `Fin.pairC` are present for uniformity rather
  than necessity: both round trips stated over `Fin.divNat` inherit
  its dependence on `Classical.choice`. `Nat`'s division and order
  API interleaves choice-dependent lemmas with choice-free ones under
  no separating convention, so the bound proofs route through `omega`
  over individually named hypotheses or through case analysis on
  `Nat.lt_or_ge`. The upstream target is Batteries rather than
  mathlib4, per `TODO.md` § Upstream destination of core- and
  Batteries-targeted content. `Classical.choice`-free.
- `Geb/Mathlib/Logic/Equiv/Fin/Basic.lean` — choice-free product and
  exponential encodings of `Fin`. `finProdFinEquivC` and
  `finFunctionFinEquivC` are the counterparts of mathlib's
  `finProdFinEquiv` and `finFunctionFinEquiv`, which depend on
  `Classical.choice` through `Fin.divNat` and through the
  `Finset.sum` lemmas of the base-`m` digit round trips. The
  exponential is an explicit `Nat.rec` on the arity over the product
  encoding rather than digit arithmetic; `Fin.funEncodeC` and
  `Fin.funDecodeC` name its two directions, with round trips
  `Fin.funDecodeC_funEncodeC` and `Fin.funEncodeC_funDecodeC`.
  `Fin.funDecodeC` returns a function, so the recursion building it
  is re-run on each application. `Classical.choice`-free.
- `Geb/Mathlib/CategoryTheory/FinSetSkel/Shapes/Core.lean` — the
  initial and terminal objects, the binary coproducts and the binary
  products of `FinSetSkel` over `Fin` and vectors, with the content
  of their universal properties (`fromZero_uniq`, `toOne_uniq`,
  `coprodDesc_uniq`, `prodLift_uniq` and the compatibilities) stated
  in the application-normal form `f.toVec.get i`. `homEquivIdxFun`
  packages the correspondence between morphisms and index functions
  as an `Equiv` with both `ULift`s removed, so a universal property
  stated over index functions transports to one over morphisms; its
  domain transport is `Equiv.arrowCongrLeftC`, mathlib's
  `Equiv.arrowCongr` and `Equiv.piCongrLeft` family all depending on
  `Classical.choice`. `point` picks an index as a morphism out of the
  one-element object. `Classical.choice`-free.
- `Geb/Mathlib/CategoryTheory/FinSetSkel/Shapes/Instances.lean` — the
  mathlib packaging of `Shapes/Core.lean`: the chosen `terminalCone`,
  `binaryProductCone`, `initialCocone` and `binaryCoproductCocone`,
  the `cartesianMonoidalCategory` instance built from the cones by
  `CartesianMonoidalCategory.ofChosenFiniteProducts` (which supplies
  the associator, the unitors and the coherence conditions, so no
  monoidal law is proved here), `isTerminalOne`, and the colimit
  `Prop` instances `hasInitial`, `hasColimit_pair`,
  `hasBinaryCoproducts` and `hasFiniteCoproducts`.
  `HasFiniteProducts` arrives with the cartesian instance at priority
  100, and with it `HasTerminal` and `HasBinaryProducts`, so none of
  the three is registered separately. The source and test modules are
  listed in `GebMeta.classicalAllowedModules`, since
  `CartesianMonoidalCategory` depends on `Classical.choice`.
- `Geb/Mathlib/CategoryTheory/FinSetSkel/Mono.lean` —
  `FinSetSkel.mono_iff_injective`: a morphism is a monomorphism
  exactly when its vector is injective. `CategoryTheory.Mono` and
  `CategoryTheory.Category` are both axiom-free, so the statement
  belongs in the choice-free layer; the forward direction tests a
  morphism against two points and the reverse is `hom_ext`. It
  supplies the hypothesis `Vector.invOfInjective` takes, and so is a
  prerequisite of the subobject classifier rather than a
  free-standing characterisation. `Classical.choice`-free.
- `Geb/Mathlib/CategoryTheory/FinSetSkel/Exponential/Core.lean` — the
  exponential of `FinSetSkel` over carriers. The exponential object
  of `Fin m` into `Fin y` is `Fin (y ^ m)`, and `expEquivIdx` and
  `expEquivHom` give the adjunction's hom-level equivalence over
  index functions and over morphisms, with `expEquivIdx_naturality`
  its naturality in the parameter. The chain is stated over the raw
  carrier and the explicit product projections, never over `⊗` or `◁`,
  both of which elaborate through the `Classical.choice`-dependent
  `CartesianMonoidalCategory` instance. Its swap step is forced by
  the adjunction `tensorLeft X ⊣ ihom X` varying in the second
  factor while `Equiv.curry` produces the first outermost.
  `Classical.choice`-free.
- `Geb/Mathlib/CategoryTheory/FinSetSkel/Exponential/Closed.lean` —
  the monoidal packaging of `Exponential/Core.lean`: `expHomEquiv`,
  the hom-level equivalence in the form the adjunction consumes, and
  the `monoidalClosed` structure, obtained from
  `Adjunction.rightAdjointOfEquiv` and
  `Adjunction.adjunctionOfEquivRight`, which supply the functor, the
  unit, the counit and the triangle identities. `X ⊗ Z` is the object
  of length `X.len * Z.len` on the nose, so restating the equivalence
  at `X ⊗ Z ⟶ Y` transports along a definitional equality rather than
  a comparison isomorphism. `whiskerLeft_get` and
  `expHomEquiv_naturality` are content rather than packaging: left
  whiskering acts on indices by pairing the first component with the
  whiskered morphism's action on the second, and that bridge connects
  the carrier-level naturality to `F.map f`, but `◁` elaborates
  through the cartesian instance and so cannot be stated choice-free.
  The source and test modules are listed in
  `GebMeta.classicalAllowedModules`.
- `Geb/Mathlib/CategoryTheory/FinSetSkel/Equalizer/Core.lean` — the
  binary equalizers of `FinSetSkel`, as the sub-object on the indices
  at which a parallel pair agrees: `Equalizer.agree` filters
  `List.finRange X.len` by `decide (f.toVec.get i = g.toVec.get i)`,
  `Equalizer.obj` and `Equalizer.ι` are the equalizer object and its
  injection, `Equalizer.invVec` inverts the injection in one pass
  over `Vector.scatter`, and `Equalizer.lift` is the factorisation,
  with `ι_comp`, `lift_ι` and `lift_uniq` the universal property. The
  inverse is a vector of `ℕ` rather than of `Fin k`, which is
  uninhabited whenever `k = 0` and `X.len > 0` — a case any pair
  differing at every index reaches — and the `Fin k` is built at the
  lift site, where the bound lemma applies. The agreement list and
  the inverse vector are bound outside anything function-valued, a
  `let` above a lambda being re-run on each application of the
  partially applied function.
  `Classical.choice`-free.
- `Geb/Mathlib/CategoryTheory/FinSetSkel/Equalizer/Limits.lean` —
  `equalizerCone`, the mathlib packaging of the agreement sub-object, its
  injection and its factorisation as a `LimitCone (parallelPair f g)`.
  `HasEqualizers` is not registered here: it is one of the `Prop` classes
  derived once from `ElementaryTopos`, and a consumer resolves it through that
  route. The source and test modules are listed in
  `GebMeta.classicalAllowedModules`, since `LimitCone` and `parallelPair` depend
  on `Classical.choice`.
- `Geb/Mathlib/CategoryTheory/FinSetSkel/Classifier/Core.lean` — the
  subobject classifier of `FinSetSkel` over vectors. The classifying
  object is the object of length 2, and `Classifier.chi` sends the
  members of a monomorphism's image to `1` and everything else to
  `0`, with `chiVec_get_eq_one_iff` identifying the characteristic
  vector as the indicator of the image, `chi_uniq` its uniqueness
  among morphisms with that indicator, and `Classifier.pullbackLift`
  the factorisation through a monomorphism of a morphism whose image
  it contains. The orientation follows mathlib's own: `finTwoEquiv`
  is `fun i ↦ i == 1`, and `Presheaf.truth` and `Sheaf.truth` both
  pick the maximal sieve, so with truth at `1` every bridge to
  `Bool`, `decide` or `Prop` is `finTwoEquiv` composed with nothing,
  where truth at `0` would put a negation in each. The characteristic
  vector is scattered in one pass over a `Vector.replicate` rather
  than written index-by-index over a membership test, which would
  rebuild and rescan the image per index. `Classical.choice`-free.
- `Geb/Mathlib/CategoryTheory/FinSetSkel/Classifier/Instance.lean` —
  `truth`, the morphism out of the one-element object picking the
  index `1`, and `classifier`, the `Subobject.Classifier FinSetSkel`
  built by `Subobject.Classifier.mkOfTerminalΩ₀` over that object, so
  the classifier's `Ω₀` and the cartesian unit are the same object
  and their comparison is an isomorphism between an object and
  itself. `chi_iff_of_isPullback` is content rather than packaging:
  it derives the vector-level hypothesis of `Classifier.chi_uniq`
  from `IsPullback` through the pullback's universal property, which
  cannot be stated choice-free. The source and test modules are
  listed in `GebMeta.classicalAllowedModules`.
- `Geb/Mathlib/CategoryTheory/FinSetSkel/ElementaryTopos.lean` —
  `FinSetSkel.elementaryTopos`, the `ElementaryTopos FinSetSkel` instance,
  assembling unchanged the cartesian and monoidal-closed structures, the
  initial cocone, the binary-coproduct cocones, the equalizer cones, the
  coequalizer cocones and the classifier. It depends on the five
  field-supplying entries above and on the `ElementaryTopos` class entry.
  `HasInitial`, `HasBinaryCoproducts`, `HasCoequalizers` and
  `HasFiniteCoproducts` are registered by the field-supplying modules and
  resolve without it; `HasEqualizers`, `HasFiniteLimits`,
  `HasFiniteColimits` and `HasPushouts` are derived through the class and
  resolve only through the instance. The source and test modules are
  listed in `GebMeta.classicalAllowedModules`, the module inheriting its
  `Classical.choice` dependence entirely from the field terms.
- `Geb/Mathlib/CategoryTheory/FinCat/Basic.lean` —
  `CategoryTheory.FinCat`, the specification of a finite category: a
  count of objects, a count of non-identity morphisms at each pair
  (`nonIdCount`), a composition function on those morphisms (`comp`),
  and a `Bool` equation asserting associativity
  (`CategoryTheory.FinCat.assocCheckOf` and
  `CategoryTheory.FinCat.assocCheck`) that a client with a concrete
  category discharges by `rfl`. The client designates no identities:
  one is reserved at the index one past the client's range in each
  endo-hom (`CategoryTheory.FinCat.homCountOf`,
  `CategoryTheory.FinCat.embOf`, `CategoryTheory.FinCat.emb`,
  `CategoryTheory.FinCat.id`), so the identity laws
  (`CategoryTheory.FinCat.id_comp`, `CategoryTheory.FinCat.comp_id`)
  hold of the reserved index by construction and only associativity is
  checked; composition on the full hom types
  (`CategoryTheory.FinCat.compTotalOf` and
  `CategoryTheory.FinCat.compTotal`) is total and associative on all
  triples (`CategoryTheory.FinCat.compTotal_assoc`). The six unbundled
  declarations — `CategoryTheory.FinCat.homCountOf_of_ne`,
  `CategoryTheory.FinCat.homCountOf_diag`,
  `CategoryTheory.FinCat.objEq_of_le`,
  `CategoryTheory.FinCat.val_eq_of_le`,
  `CategoryTheory.FinCat.compTotalOf` and
  `CategoryTheory.FinCat.assocCheckOf` — are axiom-free.
  `CategoryTheory.FinCat.id_comp`, `CategoryTheory.FinCat.comp_id` and
  `CategoryTheory.FinCat.compTotal_assoc` depend on `propext`.
- `Geb/Mathlib/CategoryTheory/FinCat/Category.lean` —
  `CategoryTheory.FinCat.Obj`, the object type a specification
  generates: a one-field structure over `ULift (Fin S.objCount)`, a
  structure projection reducing by iota at reducible transparency,
  where a `Category` instance placed directly on `ULift` would not.
  `CategoryTheory.FinCat.Obj.category` is the generated mathlib
  `Category` instance, with objects and morphisms at independent
  universe levels `u` and `v`;
  `CategoryTheory.FinCat.Obj.decidableEqHom` supplies `DecidableEq` on
  the generated hom-sets, since instance search does not unfold
  `Quiver.Hom`. `CategoryTheory.FinCat.Obj.category` depends on
  `propext`; `CategoryTheory.FinCat.Obj.decidableEqHom` on `propext`
  and `Quot.sound`; the derived
  `DecidableEq (CategoryTheory.FinCat.Obj S)` on `Quot.sound`.
- `Geb/Mathlib/CategoryTheory/FinCat/FinCategory.lean` —
  `CategoryTheory.FinCat.Obj.finCategory`: where the object and
  morphism levels of `CategoryTheory.FinCat.Obj.category` coincide,
  the generated category is small and its objects and hom-sets are
  finite, mathlib's `CategoryTheory.FinCategory` applying at that
  coinciding level. Allowlisted for `Classical.choice`, together with
  its test parallel, in `GebMeta.classicalAllowedModules`: `Fintype`'s
  `complete` field routes membership through `Finset.instSetLike`,
  itself `Classical.choice`-dependent, so no choice of witness and no
  hand-rolled instance avoids it, and `Finite` is not an escape,
  `FinCategory`'s fields being `Fintype`s. `Obj.finCategory` depends
  on `propext`, `Quot.sound` and `Classical.choice`.
- `Geb/Mathlib/CategoryTheory/FinCat/Hom.lean` —
  `CategoryTheory.FinCat.Hom`, the specification of a functor between
  two finite-category specifications: a map on object indices
  (`objMap`), a map on client morphisms landing in the target's full
  hom type (`map`), and a `Bool` equation asserting preservation of
  composition (`CategoryTheory.FinCat.Hom.compCheckOf` and
  `CategoryTheory.FinCat.Hom.compCheck`). Preservation of identities
  is not checked: the extension of the morphism map to the full hom
  types (`CategoryTheory.FinCat.Hom.mapTotalOf` and
  `CategoryTheory.FinCat.Hom.mapTotal`) sends the reserved identity to
  the reserved identity by construction (`mapTotal_id`) and preserves
  the total composition on all pairs (`mapTotal_compTotal`).
  `CategoryTheory.FinCat.Hom.id` and `CategoryTheory.FinCat.Hom.comp`
  are the identity specification and composition of specifications,
  satisfying the unit and associativity laws as equalities of
  specifications (`id_comp`, `comp_id`, `assoc`), not merely up to
  isomorphism; `CategoryTheory.FinCat.Hom.toFunctor` is the mathlib
  functor a specification generates. `mapTotalOf`, `compCheckOf`,
  the three `mapTotal` lemmas (`mapTotal_emb`, `mapTotal_id`,
  `mapTotal_compTotal`), `Hom.id`, `Hom.comp` and `toFunctor` depend
  on `propext`; the three strict equalities `id_comp`, `comp_id` and
  `assoc` on `propext` and `Quot.sound`.
- `Geb/Mathlib/CategoryTheory/FinCat/Hom2.lean` —
  `CategoryTheory.FinCat.Hom₂`, the specification of a natural
  transformation between two functor specifications with the same
  source and target: a component at each object index, ranging over
  the target's full hom type from the outset so the identity 2-cell
  has every component an identity, and a `Bool` equation asserting
  naturality (`CategoryTheory.FinCat.Hom₂.natCheckOf` and
  `CategoryTheory.FinCat.Hom₂.natCheck`).
  `CategoryTheory.FinCat.Hom.instCategory` is the hom-category of
  2-cells under componentwise vertical composition and the identity
  2-cell; `CategoryTheory.FinCat.Hom₂.toNatTrans` is the mathlib
  natural transformation a 2-cell specification generates.
  `Hom.instCategory` depends on `propext` and `Quot.sound`;
  `natCheck_total` and `toNatTrans` on `propext`.
- `Geb/Mathlib/CategoryTheory/FinCat/Bicategory.lean` —
  `CategoryTheory.FinCat.Hom₂.whiskerLeft` and
  `CategoryTheory.FinCat.Hom₂.whiskerRight`, whiskering a 2-cell
  specification by a 1-cell specification on either side, with the ten
  coherence theorems of a bicategory (`id_whiskerLeft`,
  `comp_whiskerLeft`, `id_whiskerRight`, `comp_whiskerRight`,
  `whiskerRight_id`, `whiskerRight_comp`, `whisker_assoc`,
  `whisker_exchange`, `pentagon`, `triangle`), the associator and the
  unitors taken to be `CategoryTheory.eqToHom` at the strict
  equalities `CategoryTheory.FinCat.Hom.assoc`,
  `CategoryTheory.FinCat.Hom.id_comp` and
  `CategoryTheory.FinCat.Hom.comp_id`
  (`CategoryTheory.FinCat.Hom₂.eqToHom_app` gives their components).
  `CategoryTheory.FinCat.bicategory` packages this as a
  `Bicategory CategoryTheory.FinCat`,
  `CategoryTheory.FinCat.bicategory_strict` as its strictness (1-cell
  composition unital and associative on the nose), and
  `CategoryTheory.FinCat.category` as the resulting
  `Category CategoryTheory.FinCat`, from the strict bicategory. The
  whiskerings, `eqToHom_app`, the ten coherence theorems, and the
  three instances all depend on `propext` and `Quot.sound`.
- `Geb/Mathlib/CategoryTheory/FinCat/Decidable.lean` — decidable
  equality at each of the three levels, decided field by field and
  transported along the equality of an earlier field wherever a
  later field's type mentions it; the `Bool`-valued equation fields
  contribute no decision, being proof-irrelevant.
  `CategoryTheory.FinCat.decidableEqPiFin` decides equality of
  functions out of `Fin n` pointwise and is `scoped`, with every
  `DecidableEq` argument at a Π-type use site supplied explicitly so
  that only the innermost `DecidableEq (Fin _)` is left to instance
  resolution — `Fintype.decidablePiFintype` being a competitor at the
  same head symbol that default resolution would otherwise select;
  `CategoryTheory.FinCat.decidableEqComp` specialises it to
  composition tables at fixed counts.
  `CategoryTheory.FinCat.Hom₂.decidableEq`,
  `CategoryTheory.FinCat.Hom.decidableEq` and
  `CategoryTheory.FinCat.decidableEq` are the three levels.
  `decidableEqPiFin` and `decidableEqComp` depend on `Quot.sound`;
  `Hom.decidableEq` and `Hom₂.decidableEq` on `propext` and
  `Quot.sound`; the outer `decidableEq` on `Quot.sound`.
- `Geb/Mathlib/CategoryTheory/FinCat/Repr.lean` — `Repr` at each of
  the three levels, rendering the counts and the tables as nested
  naturals through `List.ofFn` and `Fin.val`:
  `CategoryTheory.FinCat.instRepr` renders a specification as its
  object count, its count matrix and its composition table;
  `CategoryTheory.FinCat.Hom.instRepr` renders a functor
  specification as its object map and its morphism table;
  `CategoryTheory.FinCat.Hom₂.instRepr` renders a 2-cell
  specification as its component vector. The `Bool`-validity fields
  are not rendered, carrying no information a reader of the table
  needs. All three instances depend on `propext`.
- `Geb/Internal/ConcreteSyntax.lean` — prototype of the concrete-syntax
  layer for the Geb abstract syntax tree. `Geb.Ast k` is the initial
  algebra of `F X = Fin k + X × X`: binary trees whose leaves carry a
  label in `Fin k`. `Geb.Tree k A` annotates every node with an `A`,
  and carries `extract`/`duplicate` with the three comonad laws
  (`Tree.extract_duplicate`, `Tree.map_extract_duplicate`,
  `Tree.duplicate_duplicate`); `Geb.Doc k` is the annotated document
  type `Tree k Ann`, and `Tree.erase` forgets the annotations, with
  `Ast.erase_trivialDoc` the round trip against the trivial
  decoration. `Geb.Rose k` is the rose-tree presentation, and
  `ofRose_toRose`/`toRose_ofRose` are the two halves of its bijection
  with `Ast k` under the head-child-left convention;
  `rosePathToBin_last` records that the binary occurrences nameable in
  the rose presentation are exactly the root and the paths ending in
  `L`. `Ast.subtreeMH` and `Ast.coreMH` are the domain-separated
  Merkle fold in the style of [RFC6962] § 2.1, over an arbitrary
  `HashFn`; `tags_equal_length` discharges the equal-length side
  condition the domain-separation argument needs. `Retraction`,
  `format_idem` and `printDoc_injective` state the law a concrete
  syntax must satisfy and derive formatter idempotence and printer
  injectivity from it once for every syntax. `Geb.print`/`Geb.parse`
  are the first such syntax, the canonical S-expression encoding of
  [RFC9804] restricted to the bare tree, with `parse_print` the
  retraction and `csexp_format_idem`/`csexp_print_injective` its two
  instantiated corollaries. `Tree.extract_duplicate`,
  `tags_equal_length`, `printDoc_injective` and `charDigit_digitChar`
  depend on no axioms; the remaining theorems of the
  format-independent core depend on `propext` alone, and the remaining
  theorems of the S-expression syntax on `propext` and `Quot.sound`.
  No declaration depends on `Classical.choice`.
