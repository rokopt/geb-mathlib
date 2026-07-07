# Contravariant Grothendieck construction — design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Goal](#goal)
- [Transcription status](#transcription-status)
- [Naming](#naming)
- [Module layout](#module-layout)
- [Universe scheme](#universe-scheme)
- [Core declarations](#core-declarations)
  - [Wrapper API — `GrothendieckOp` (hides the fiber-side `op`)](#wrapper-api--grothendieckop-hides-the-fiber-side-op)
  - [Wrapper API — `CoGrothendieck` (hides the outer `ᵒᵖ` and base-side `op`s)](#wrapper-api--cogrothendieck-hides-the-outer-%E1%B5%92%E1%B5%96-and-base-side-ops)
  - [Interface discipline](#interface-discipline)
- [Functor layer](#functor-layer)
- [Theorem set](#theorem-set)
- [Out of scope (follow-on branches when a consumer demands them)](#out-of-scope-follow-on-branches-when-a-consumer-demands-them)
- [Tests](#tests)
- [Axiom hygiene](#axiom-hygiene)
- [Documentation](#documentation)
- [Verification gates](#verification-gates)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Goal

Define the contravariant Grothendieck construction for 1-functors
`G : Cᵒᵖ ⥤ Cat` as a wrapper over mathlib's covariant
`CategoryTheory.Grothendieck`, together with convenience
constructors and destructors that present an interface free of
structural `op`/`unop`, and packaged functorial forms. Mathlib
mentions this construction in a comment in
`Mathlib/CategoryTheory/Grothendieck.lean` but implements it only
at the pseudofunctor level
(`CategoryTheory.Pseudofunctor.CoGrothendieck`); the 1-functor
version and its expression via the covariant construction are
absent from mathlib and CSLib.

The first downstream consumer is the family functor and the free
coproduct completion (a later branch); this branch delivers only
the construction itself.

## Transcription status

- The contravariant Grothendieck construction is a transcription
  of standard mathematics. Sources (verified against arXiv
  metadata 2026-07-07):
  - `[Vistoli2008]` — Angelo Vistoli, *Notes on Grothendieck
    topologies, fibered categories and descent theory*,
    arXiv:math/0412512. The source mathlib's
    `Pseudofunctor.CoGrothendieck` cites for the contravariant
    construction.
  - `[JohnsonYau2021]` — Niles Johnson and Donald Yau,
    *2-Dimensional Categories*, arXiv:2002.06055 (Oxford
    University Press, 2021), ch. 10 (Grothendieck construction).
  - The identity "contravariant Grothendieck construction =
    opposite of the covariant construction applied to the
    oppositized functor" is stated on the nLab page
    [Grothendieck construction](https://ncatlab.org/nlab/show/Grothendieck+construction).
- The packaging (`GrothendieckOp` as a named intermediate,
  `functorToCat` post-compositions) is a presentation choice; the
  mathematics is the standard composition of known functors.
- Both new bib keys are added to
  [docs/references.bib](../../references.bib); the module
  docstring cites them in `[Key]` form.

## Naming

- `CoGrothendieck` — the name mathlib explicitly reserves for the
  contravariant construction
  (`Mathlib/CategoryTheory/Bicategory/Grothendieck.lean`
  § Naming conventions), used there at the pseudofunctor level;
  we use it for the 1-functor level.
- `GrothendieckOp` — the covariant construction applied to the
  oppositization of a functor; the `Op` suffix follows mathlib
  precedent (`createsLimitsOp`, `Functor.op`/`leftOp`/`rightOp`).
- `homMk` follows `Over.homMk` / `StructuredArrow.homMk`;
  `homBase` / `homFiber` destructors have no mathlib precedent
  (upstream they are structure fields) and are flat names because
  no name is reachable by dot notation on morphisms (see
  § Interface discipline).

## Module layout

- `Geb/Mathlib/CategoryTheory/Grothendieck.lean` — parallel to
  mathlib's path. Namespace `CategoryTheory`.
- New index file `Geb/Mathlib/CategoryTheory.lean`;
  `Geb/Mathlib.lean` gains
  `public import Geb.Mathlib.CategoryTheory`.
- Imports: `Mathlib.CategoryTheory.Grothendieck`,
  `Mathlib.CategoryTheory.Category.Cat.Op`, plus whiskering and
  `Over` modules as required. All `Mathlib.*` (floodgate-clean).
- File sections:
  1. `Covariant` — extension to mathlib's covariant file:
     `Grothendieck.functorToCat` (in mathlib's
     `CategoryTheory.Grothendieck` namespace, so upstreaming
     inserts it into mathlib's own file).
  2. `Contravariant` — `GrothendieckOp`, then `CoGrothendieck`.
- Tests: `GebTests/Mathlib/CategoryTheory/Grothendieck.lean`,
  mirrored path, with a new index file
  `GebTests/Mathlib/CategoryTheory.lean` imported from
  `GebTests/Mathlib.lean` (the lean_lib glob discovers the files
  by path; the import chain is what makes the `GebTests`
  test-driver root elaborate them). Both the source
  module and the test module are appended to
  `GebMeta.classicalAllowedModules` (see § Axiom hygiene).
- The new module opens with the `module` keyword and
  `@[expose] public section`, as mathlib's
  `CategoryTheory/Grothendieck.lean` does. Exposure is a
  correctness requirement: the `rfl` round-trip proofs in
  `GebTests` (a different module) and any downstream consumer
  depend on the `def` bodies being definitionally transparent
  across module boundaries. (The `inferInstanceAs` instances need
  only in-module transparency.)
- The module opens the `Functor` namespace (as mathlib's file
  does); code snippets below assume it.

## Universe scheme

Match mathlib's `Grothendieck` conventions for the declarations
in scope: `universe u v u₂ v₂`, `{C : Type u} [Category.{v} C]`,
functors into `Cat.{v₂, u₂}`. (Mathlib's file also declares
`w u₁ v₁`, used only by material out of scope here; unused
universe declarations are removed per
[docs/rules/lean-coding.md](../../rules/lean-coding.md).) Both
new categories are ascribed
`Type (max u u₂)` with explicit `Category.{max v v₂}` instances —
identical levels to the covariant construction, since `ᵒᵖ` and
`Cat.opFunctor` preserve universes. Every `def` carries an
explicit return type.

Exception: the packaged functors restrict to `E : Cat.{v, u}`
with fibers in the same `Cat.{v, u}`, inherited verbatim from
mathlib's `Grothendieck.functor` (an `Over` in `Cat` forces base
and total category into one `Cat`). `forget` and `map` keep full
polymorphism.

## Core declarations

Approach: transparent `def` type synonyms (not `abbrev`, not new
structures), so mathlib's category instance and functoriality are
reused directly and all round-trip lemmas are `rfl`.
Semireducibility is the interface boundary: instance synthesis
and object-level dot notation stop at the new names.

```lean
def GrothendieckOp (F : C ⥤ Cat.{v₂, u₂}) : Type (max u u₂) :=
  Grothendieck (F ⋙ Cat.opFunctor)

instance (F : C ⥤ Cat.{v₂, u₂}) :
    Category.{max v v₂} (GrothendieckOp F) :=
  inferInstanceAs (Category (Grothendieck (F ⋙ Cat.opFunctor)))

def CoGrothendieck (G : Cᵒᵖ ⥤ Cat.{v₂, u₂}) : Type (max u u₂) :=
  (GrothendieckOp G)ᵒᵖ

instance (G : Cᵒᵖ ⥤ Cat.{v₂, u₂}) :
    Category.{max v v₂} (CoGrothendieck G) :=
  inferInstanceAs (Category (GrothendieckOp G)ᵒᵖ)
```

The `GrothendieckOp` instance must spell the unfolded type on its
right-hand side (synthesis does not unfold semireducible
definitions); the `CoGrothendieck` instance resolves through the
`GrothendieckOp` instance and mathlib's opposite-category
instance without unfolding.

### Wrapper API — `GrothendieckOp` (hides the fiber-side `op`)

| Declaration | Type |
| --- | --- |
| `mk` | `(base : C) → (fiber : F.obj base) → GrothendieckOp F` |
| `base` | `GrothendieckOp F → C` |
| `fiber` | `(X : GrothendieckOp F) → F.obj X.base` |
| `homMk` | `(base : X.base ⟶ Y.base) → (fiber : Y.fiber ⟶ (F.map base).toFunctor.obj X.fiber) → (X ⟶ Y)` |
| `homBase` | `(X ⟶ Y) → (X.base ⟶ Y.base)` |
| `homFiber` | `(f : X ⟶ Y) → (Y.fiber ⟶ (F.map (homBase f)).toFunctor.obj X.fiber)` |

### Wrapper API — `CoGrothendieck` (hides the outer `ᵒᵖ` and base-side `op`s)

| Declaration | Type |
| --- | --- |
| `mk` | `(base : C) → (fiber : G.obj (op base)) → CoGrothendieck G` |
| `base` | `CoGrothendieck G → C` |
| `fiber` | `(X : CoGrothendieck G) → G.obj (op X.base)` |
| `homMk` | `(base : X.base ⟶ Y.base) → (fiber : X.fiber ⟶ (G.map base.op).toFunctor.obj Y.fiber) → (X ⟶ Y)` |
| `homBase` | `(X ⟶ Y) → (X.base ⟶ Y.base)` |
| `homFiber` | `(f : X ⟶ Y) → (X.fiber ⟶ (G.map (homBase f).op).toFunctor.obj Y.fiber)` |

`CoGrothendieck.homMk`'s fiber direction matches both the mathlib
comment (`φ : f ⟶ (G.map (op β)).obj f'`) and
`Pseudofunctor.CoGrothendieck.Hom.fiber` (`h : b ⟶ F(f)(a)`).
The single `op` in the fiber type (`G.map base.op`) cannot be
hidden: `G` has domain `Cᵒᵖ`.

Morphisms of `Cat` are bundled (`Cat.Hom`, a one-field structure
over functors, with no coercion to functors), so `.toFunctor`
appears in the fiber types exactly where mathlib's own
`Grothendieck.Hom.fiber` has it
(`(F.map base).toFunctor.obj X.fiber`); the wrappers do not
attempt to hide this layer, matching both mathlib's covariant
`Hom` and `Pseudofunctor.CoGrothendieck.Hom`.

### Interface discipline

- Object-level dot notation (`X.base`, `X.fiber`) resolves to the
  wrappers (the type's head constant is the synonym).
- Morphism-level dot notation resolves through `Quiver.Hom` to
  `Grothendieck.Hom`'s own projections, whose op-side types make
  direction misuse a type error, not a silent one. No wrapper
  name is dot-reachable on morphisms; clients use
  `open CoGrothendieck` or qualified names.
- All round-trip lemmas are `@[simp]`, so simp rewrites toward
  the wrapper vocabulary.

## Functor layer

All definitions are compositions of existing functors; no
hand-written object maps, morphism maps, or law proofs.

```lean
def GrothendieckOp.forget (F : C ⥤ Cat.{v₂, u₂}) :
    GrothendieckOp F ⥤ C :=
  Grothendieck.forget (F ⋙ Cat.opFunctor)

def CoGrothendieck.forget (G : Cᵒᵖ ⥤ Cat.{v₂, u₂}) :
    CoGrothendieck G ⥤ C :=
  (GrothendieckOp.forget G).leftOp

def GrothendieckOp.map {F F' : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ F') :
    GrothendieckOp F ⥤ GrothendieckOp F' :=
  Grothendieck.map (whiskerRight α Cat.opFunctor)

def CoGrothendieck.map {G G' : Cᵒᵖ ⥤ Cat.{v₂, u₂}} (α : G ⟶ G') :
    CoGrothendieck G ⥤ CoGrothendieck G' :=
  (GrothendieckOp.map α).op
```

Both `map`s are covariant in `α` (the two `op`s in
`CoGrothendieck.map` cancel on variance), matching
`Pseudofunctor.CoGrothendieck.map`. Laws mirror mathlib:
`map_id_eq`, `map_comp_eq` (derived from
`Grothendieck.map_id_eq` / `map_comp_eq` via `whiskerRight` and
`Functor.op` preservation lemmas), plus `mapIdIso` / `mapCompIso`
as `eqToIso` packagings.

Packaged forms (universe-restricted as noted above). The
covariant `Grothendieck.functorToCat` is included although its
consumer (the free product completion, alongside the free
coproduct completion consuming the contravariant form) arrives
with the family-functor workstream: it is the covariant
counterpart the two `functorToCat` wrappers mirror, and it sits
in mathlib's `CategoryTheory.Grothendieck` namespace as a direct
upstream-insertion candidate for mathlib's own file.

```lean
def Grothendieck.functorToCat {E : Cat.{v, u}} :
    (↑E ⥤ Cat.{v, u}) ⥤ Cat.{v, u} :=
  Grothendieck.functor ⋙ Over.forget E

def GrothendieckOp.functor {E : Cat.{v, u}} :
    (↑E ⥤ Cat.{v, u}) ⥤ Over (T := Cat.{v, u}) E :=
  (whiskeringRight ↑E Cat.{v, u} Cat.{v, u}).obj
      Cat.opFunctor ⋙
    Grothendieck.functor

def GrothendieckOp.functorToCat {E : Cat.{v, u}} :
    (↑E ⥤ Cat.{v, u}) ⥤ Cat.{v, u} :=
  GrothendieckOp.functor ⋙ Over.forget E

def CoGrothendieck.functor {E : Cat.{v, u}} :
    ((↑E)ᵒᵖ ⥤ Cat.{v, u}) ⥤ Over (T := Cat.{v, u}) E :=
  GrothendieckOp.functor ⋙ Over.post Cat.opFunctor ⋙
    Over.map (unopUnop ↑E).toCatHom

def CoGrothendieck.functorToCat {E : Cat.{v, u}} :
    ((↑E)ᵒᵖ ⥤ Cat.{v, u}) ⥤ Cat.{v, u} :=
  CoGrothendieck.functor ⋙ Over.forget E
```

`CoGrothendieck.functor` pipeline: `GrothendieckOp.functor` lands
in `Over (Cat.of (↑E)ᵒᵖ)`; `Over.post Cat.opFunctor` oppositizes
the total category (producing `CoGrothendieck G` over
`Cat.of (↑E)ᵒᵖᵒᵖ`); `Over.map (unopUnop ↑E).toCatHom` retargets
to `E`.

Consistency lemmas (expected `rfl`; verified during
implementation, with `Functor.ext`-based fallback proofs if
elaboration disagrees):

- `(GrothendieckOp.functor.obj F).hom =
  (GrothendieckOp.forget F).toCatHom`
- `(CoGrothendieck.functor.obj G).hom =
  (CoGrothendieck.forget G).toCatHom`
- `functorToCat_obj` for all three: the object image is
  `Cat.of` the corresponding construction.

## Theorem set

For each of `GrothendieckOp` and `CoGrothendieck`:

- Round-trips, all `@[simp]`, all expected `rfl`: `base_mk`,
  `fiber_mk`, `mk_base_fiber` (object eta), `homBase_homMk`,
  `homFiber_homMk`, `homMk_base_fiber` (hom eta).
- `hom_ext` (`@[ext]`), derived from `Grothendieck.ext`:
  `homBase f = homBase g →
  homFiber f ≫ eqToHom (by rw [...]) = homFiber g → f = g`.
- Identity and composition characterizations mirroring mathlib's
  simp API through the wrappers:
  - `homBase_id : homBase (𝟙 X) = 𝟙 X.base` (`rfl`)
  - `homFiber_id : homFiber (𝟙 X) = eqToHom (by simp)`
  - `homBase_comp :
    homBase (f ≫ g) = homBase f ≫ homBase g` (`rfl`)
  - `homFiber_comp` (`CoGrothendieck` form):
    `homFiber (f ≫ g) = homFiber f ≫
    (G.map (homBase f).op).toFunctor.map (homFiber g) ≫
    eqToHom (by simp)`
    — the composition order reverses relative to the covariant
    `comp_fiber`; the `eqToHom` arises from `G.map_comp`, as
    upstream.
- `forget_obj` / `forget_map` and `map` object/morphism
  characterizations in wrapper vocabulary (expected `rfl`), e.g.
  `(CoGrothendieck.map α).obj (mk b f) =
  mk b ((α.app (op b)).toFunctor.obj f)`.

## Out of scope (follow-on branches when a consumer demands them)

- `isoMk`, `transport`, `pre`, `ι` / `functorFrom` analogues.
- Any equivalence with `Pseudofunctor.CoGrothendieck`.
- The family functor and free coproduct completion (next
  workstream).

## Tests

`GebTests/Mathlib/CategoryTheory/Grothendieck.lean`: named
`def`s / `theorem`s (not `example`s — `lake shake` cannot see
example-only imports), exercising a concrete instantiation (e.g.
the constant functor `(Functor.const Cᵒᵖ).obj (Cat.of D)` for
small concrete `C`, `D`):

- Build objects and morphisms via `mk` / `homMk`; round-trip via
  destructors with `rfl` proofs.
- Compose two morphisms; check `homBase` / `homFiber` against
  expected values.
- Apply `forget` and `map` and check object/morphism images.

## Axiom hygiene

Mathlib's covariant construction is not choice-free: verified
empirically under the repository toolchain (2026-07-07,
`#print axioms`), `Cat.opFunctor`,
`Grothendieck.instCategory`, `Grothendieck.forget`,
`Grothendieck.map`, and `Grothendieck.functor` all depend on
`Classical.choice`. Every declaration in the new module —
including the type synonyms themselves — therefore carries
`Classical.choice`, and no choice-free composition route exists.
Accordingly:

- `Geb.Mathlib.CategoryTheory.Grothendieck` and
  `GebTests.Mathlib.CategoryTheory.Grothendieck` are appended to
  `GebMeta.classicalAllowedModules` in the same branch, following
  that allowlist's documented convention for categorical wrappers
  over mathlib's `Classical`-dependent category theory and their
  test parallels (precedent: the `PFunctor` `Functor` wrapper
  modules).
- This is the case the constructive-only rule provides for: the
  `Classical` dependence is inherited from a reused mathlib
  concept, not introduced here. No `noncomputable` is expected or
  accepted.
- Each public declaration is verified (`lean_verify`) as it
  lands, confirming no axiom beyond
  `{propext, Classical.choice, Quot.sound}` enters.

## Documentation

- Module docstring with mathlib's required sections;
  `## Implementation notes` records the `def`-synonym
  transparency discipline (why `def` not `abbrev`; the
  morphism-level dot-notation caveat) and the universe story;
  `## References` cites `[Vistoli2008]` and `[JohnsonYau2021]`.
- `docs/references.bib` gains the two entries.
- `docs/index.md` gains the entry in topological position.

## Verification gates

`lake build`, `lake test`, `lake lint`,
`scripts/lint-imports.sh`, `lake exe shake` (as wired in
pre-push), `markdownlint-cli2` on touched Markdown,
`lean4:review` before commit, `scripts/pre-push.sh` before push.
The spec and plan receive adversarial review before execution and
are removed in the branch's final commits (transient artifacts).
