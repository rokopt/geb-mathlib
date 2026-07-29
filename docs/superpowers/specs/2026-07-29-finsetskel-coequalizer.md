# W4: binary coequalizers in FinSetSkel by union-find

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [Findings re-verified](#findings-re-verified)
- [Transcription or novel](#transcription-or-novel)
- [The union-find layer](#the-union-find-layer)
- [The quotient core](#the-quotient-core)
  - [Sharing](#sharing)
  - [Definitions](#definitions)
  - [Index types](#index-types)
  - [Statements](#statements)
  - [Constraint 9](#constraint-9)
- [The wrapper](#the-wrapper)
- [Tests](#tests)
- [Non-Lean deliverables](#non-lean-deliverables)
- [Out of scope](#out-of-scope)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope

Row i of the operation table in `TODO.md` § FinSetSkel
as an elementary topos: binary coequalizers in `FinSetSkel`, and
`HasCoequalizers FinSetSkel`, constructed by folding
`Batteries.UnionFind.union` over the domain of a parallel pair.

W4 depends on W0 (the `Batteries.` allow-list) and W1 (`FinSetSkel`
and its morphism API), both merged. It is independent of W2 and of W3,
which proceeds concurrently in a separate worktree.

The coequalizer's data term is what W5 consumes for the
`coequalizerCocone` field of `ElementaryTopos`; `HasCoequalizers` is
one of the two hypotheses of row k, which is also W5's.

## Findings re-verified

The umbrella spec's findings were pinned to the mathlib revision
current when they were taken. The following were re-verified at the
revision this branch builds against, by `#print axioms` through the
`lean-lsp` MCP. All depend on `propext` and `Quot.sound` only:

`Batteries.UnionFind.equiv_union`, `equiv_push`, `equiv_empty`,
`equiv_rootD`, `find_size`, `arr_link`, `linkAux_size`, `rootD_rootD`;
and W1's `Fin.compressEquiv` and `List.Nodup.getEquivC`.

Four of the umbrella spec's records of W4 are corrected.

1. Size preservation is not a derivation from `arr_link`,
   `linkAux_size` and `find_size`. `(self.union x y).size = self.size`
   is `by unfold union; simp [UnionFind.size]`. The `push` counterpart
   is needed too, for `Sized.discrete`; the `link` counterpart is not,
   `size_union` never routing through it.
2. `Batteries.UnionFind.unionN`, which takes `x y : Fin n` together
   with `h : n = self.size`, already exists, so the fold threads its
   size invariant without casting indices.
3. The renumbering is `Fin.compressEquiv`, not `Vector.invOfInjective`.
   `compressEquiv` renumbers the indices of `Fin n` satisfying a
   `Bool`-valued predicate onto an initial segment, which is the
   operation a coequalizer carrier needs.
   `Vector.invOfInjective` inverts an injective vector, which is what
   W3's rows h and m need. Constraint 7's placement of the inversion in
   W1 is unaffected: both are W1 deliverables, in
   `Geb/Mathlib/Data/List/NodupEquivFin.lean` and
   `Geb/Mathlib/Data/Vector/NodupEquivFin.lean` respectively.
4. Constraint 9's closing paragraph says that deciding a proposition
   quantified over `Fin n` is a case where the choice-free term is
   named rather than searched for, and that W3 and W4 both need it. W4
   does not: nothing in the interface below decides a quantified
   proposition. `isRoot` decides an equation, and `List.filter` applies
   a `Bool`-valued function pointwise.

Measured against the mathlib limit interface: `parallelPair` depends on
`propext` alone, but `Cofork.ofπ`, `Cofork.IsColimit.mk` and
`hasCoequalizers_of_hasColimit_parallelPair` each depend on
`Classical.choice`. The allowlist amendment the standing obligation
predicts for W4 is therefore required, and is required for the wrapper
module alone.

## Transcription or novel

`CONTRIBUTING.md` § Cite the literature requires the
brainstorming-phase spec to mark each definition.

The mathematics W4 transcribes is one construction: the coequalizer of
a parallel pair of functions between finite sets is the quotient of the
codomain by the equivalence relation the pair generates, and its
universal property. The transcribed declarations are `obj`, `π`,
`desc`, `comp_π`, `π_desc`, `desc_uniq` and the wrapper's
`coequalizerCocone`, cited to `[MacLaneMoerdijk1992]`.

Everything else is novel, in the sense of being a representation
choice rather than a statement taken from a source: `Sized`,
`Sized.discrete`, `Sized.union`, `Sized.root`, `ofEdges` and the
theorems about them; and `edges`, `unionFind`, `isRoot`, `len`, `rep`
and the application-normal-form lemmas. The disjoint-set algorithm is
not novel, but it is not restated here either — it is Batteries'.

## The union-find layer

`Geb/Mathlib/Data/UnionFind/OfEdges.lean`, in namespace
`Batteries.UnionFind`. Choice-free, and free of any reference to
category theory or to `FinSetSkel`: it is stated over a size `n`, a
list of edges, and an arbitrary target type. Named for the fold, not
for a closure: the closure characterisation is out of scope below.

Its upstream target is Batteries rather than mathlib4, which is the
subject of `TODO.md` § Upstream destination of core- and
Batteries-targeted content. That item's scoping criterion does not
reach this module as written — it covers modules whose declarations
"restate or replace" core or Batteries declarations, and these
declarations do neither, being new statements about a Batteries type.
The criterion is widened to cover them, which is the third of W4's
`TODO.md` edits. The hazard the item names applies here in full:
`scripts/extract-pr.sh` maps `Geb/Mathlib/*` to `Mathlib/`
unconditionally, so this module would extract to
`Mathlib/Data/UnionFind/OfEdges.lean`, which is the wrong upstream.

The six declarations the quotient core consumes are `Sized`,
`Sized.root`, `ofEdges`, `root_root`, `root_ofEdges_of_mem` and
`apply_root_ofEdges`; the rest support them. `lakefile.toml` sets
`autoImplicit = false`, so the binders below are declared, not elided.

```lean
universe u
variable {n : Nat}

theorem size_union (self : UnionFind) (x y : Fin self.size) :
    (self.union x y).size = self.size
theorem size_push (self : UnionFind) : self.push.size = self.size + 1

def Sized (n : Nat) : Type := {u : UnionFind // u.size = n}

def Sized.discrete (n : Nat) : Sized n
def Sized.union (v : Sized n) (x y : Fin n) : Sized n
def Sized.root (v : Sized n) (x : Fin n) : Fin n

theorem Sized.root_eq_iff {v : Sized n} {a b : Fin n} :
    v.root a = v.root b ↔ v.1.Equiv a b
theorem Sized.rootD_discrete (m x : Nat) : (discrete m).1.rootD x = x
theorem Sized.root_discrete (x : Fin n) : (discrete n).root x = x

def ofEdges (n : Nat) (l : List (Fin n × Fin n)) : Sized n

theorem root_root (v : Sized n) (x : Fin n) :
    v.root (v.root x) = v.root x
theorem root_ofEdges_of_mem {l : List (Fin n × Fin n)} {a b : Fin n}
    (hab : (a, b) ∈ l) :
    (ofEdges n l).root a = (ofEdges n l).root b
theorem apply_root_ofEdges {α : Type u} {l : List (Fin n × Fin n)}
    {h : Fin n → α} (hl : ∀ p ∈ l, h p.1 = h p.2) (x : Fin n) :
    h ((ofEdges n l).root x) = h x
```

`apply_root_ofEdges` is named for its left-hand side; `_sound` is not
among mathlib's discharging-operator suffixes.

`Sized` carries the size as a subtype rather than re-deriving it at
each step, so the `Fin n` indices passed to `union` need no cast.
`Sized.root` returns `Fin n` rather than Batteries' `Nat`-valued
`rootD`, discharging the bound once so that every downstream statement
is an equation between `Fin n` terms, which is W1's normal form.
Batteries has two `Fin`-valued forms already:
`UnionFind.root (self) (x : Fin self.size) : Fin self.size`, whose
index type is tied to `self.size` rather than to a fixed `n` and so
reintroduces the cast `Sized` exists to remove, and `UnionFind.rootN`,
about which Batteries states no lemma at all. Building on `rootD` keeps
`rootD_rootD`, `rootD_lt` and the `Equiv` API.

The two theorems the construction consumes are the two directions of
correctness. `root_ofEdges_of_mem` says every listed edge is merged.
`apply_root_ofEdges` says nothing beyond the listed edges is merged; it
is stated as the eliminator — any `h` agreeing on the edges agrees on
roots — rather than as a characterisation of the merged relation as the
equivalence closure of the edges. The eliminator form is what the
coequalizer's factorisation law instantiates directly, and the
characterisation has no other consumer in W4 or W5.

Three auxiliary recursions over the edge list carry them, each
generalised over the accumulated `Sized n`:

```lean
theorem equiv_foldl_of_equiv (l : List (Fin n × Fin n)) (a b : Fin n)
    (v : Sized n) (hv : v.1.Equiv a b) :
    (l.foldl (fun v p ↦ v.union p.1 p.2) v).1.Equiv a b
theorem equiv_foldl_of_mem (l : List (Fin n × Fin n)) (a b : Fin n)
    (hab : (a, b) ∈ l) (v : Sized n) :
    (l.foldl (fun v p ↦ v.union p.1 p.2) v).1.Equiv a b
theorem apply_root_foldl {α : Type u} {h : Fin n → α}
    (l : List (Fin n × Fin n)) (hl : ∀ p ∈ l, h p.1 = h p.2)
    (v : Sized n) (hv : ∀ x, h (v.root x) = h x) (x : Fin n) :
    h ((l.foldl (fun v p ↦ v.union p.1 p.2) v).root x) = h x
```

The first two are `Equiv`-level and give `root_ofEdges_of_mem`: the
left disjunct of `equiv_union` supplies monotonicity, its middle
disjunct the step. The third is generalised over `h` as well as over
the accumulator, and is the one `apply_root_ofEdges` is read off, at
`v := Sized.discrete n` with `Sized.root_discrete` discharging its
invariant. It is not derivable from the first two: those are statements
about `Equiv`, and passing from them to a statement about an arbitrary
`h` is exactly the closure characterisation this module declines to
prove. Its own step discharges the three disjuncts of `equiv_union`
against `hv` and `hl`.

Per `docs/rules/lean-coding.md` § Recursion and induction through
recursors, every recursion here is an explicit recursor application
rather than an `induction` tactic: the three above, and also
`Sized.discrete`, which is an `n`-fold `push`, and its lemma
`Sized.rootD_discrete`.

## The quotient core

`Geb/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean`, in namespace
`FinSetSkel.Quotient`. Choice-free. The namespace tracks the module
path, and the extra level is not optional: `FinSetSkel.len` is the
object structure's field, so a `len` declared directly in `FinSetSkel`
collides with it. `Quotient` shadows nothing — a namespace with no
declaration of that name does not — and W4 uses neither `Quot` nor
`Quotient`.

Stated over `FinSetSkel` morphisms in W1's application-normal form
`f.toVec.get i`, not over bare index functions: W1's `Basic.lean` is
choice-free, so the core may import it, and stating over morphisms
makes the wrapper a transcription rather than a translation.

### Sharing

The fold must run once per coequalizer, not once per index. `TODO.md`
§ Class fields carries the coequalizer as data precisely so that a
chosen algorithm runs, and a term that reruns the fold `Y.len` times is
not that algorithm.

Two facts govern the shape below, both measured. `Vector.ofFnC` applies
its argument once per index. And a `let` shares only in a definition
whose result is a value: a definition whose result is a function is
compiled at the arity of all its binders, including those under the
`let`, so its `let` body is re-entered on every application. A
`fun`-valued `def` therefore cannot hold an expensive `let` for its
callers.

Hence: nothing expensive sits above a lambda anywhere in this module.
The union-find is a parameter, so no definition below rebuilds it; the
per-index renumbering data is a `Vector`, not a function; and the two
definitions that do call `Vector.ofFnC` bind what their lambda needs in
a `let`, which shares because their result is a morphism.

### Definitions

```lean
universe u
variable {X Y Z : FinSetSkel.{u}}

def edges (f g : X ⟶ Y) : List (Fin Y.len × Fin Y.len) :=
  (List.finRange X.len).map fun i ↦ (f.toVec.get i, g.toVec.get i)

def unionFind (f g : X ⟶ Y) : UnionFind.Sized Y.len :=
  UnionFind.ofEdges _ (edges f g)

def isRoot (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len) :
    Fin Y.len → Bool :=
  fun j ↦ decide (v.root j = j)

def len (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len) : ℕ :=
  ((List.finRange Y.len).filter (isRoot Y v)).length

def obj (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len) :
    FinSetSkel.{u} := ⟨len Y v⟩

theorem isRoot_root (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len)
    (j : Fin Y.len) : isRoot Y v (v.root j)

def rep (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len) :
    Vector (Fin Y.len) (obj Y v).len
def π (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len) :
    Y ⟶ obj Y v
def desc (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len)
    (h : Y ⟶ Z) : obj Y v ⟶ Z
```

`Y` is an explicit argument of every definition taking `v`:
`UnionFind.Sized Y.len` mentions `Y.len`, not `Y`, so the elaborator
cannot recover `Y` from it.

`rep Y v` is `Vector.ofFnC fun c ↦ (Fin.compressEquiv (isRoot Y v) c).1`
with the equivalence bound in a `let` above the lambda — a vector
rather than the function `Fin (obj Y v).len → Fin Y.len`, so that its
consumers index it in constant time instead of rebuilding
`Fin.compressEquiv` per class. `π Y v` is
`ofVec (Vector.ofFnC …)` sending `j` to the compressed index of
`v.root j`, the side condition that this root satisfies `isRoot Y v`
being `isRoot_root`, itself `root_root`; it binds the equivalence in a
`let` likewise. `desc Y v h` is
`ofVec (Vector.ofFnC fun c ↦ h.toVec.get (r.get c))` under
`let r := rep Y v`; it carries no compatibility hypothesis, so it
computes for any `h`, and only `π_desc` below constrains `h`.

`isRoot Y v` stays a function rather than a vector: `v` is a parameter,
so applying it costs a `root` lookup and rebuilds nothing.

The universal-property statements below are stated at
`v := unionFind f g`, which is where the edges enter; the definitions
above never call `unionFind`, and the wrapper binds it once.

### Index types

Three forms of the carrier's index type are in play:
`Fin (obj Y v).len`, `Fin (len Y v)`, and
`Fin ((List.finRange Y.len).filter (isRoot Y v)).length`, which is the
domain of `Fin.compressEquiv (isRoot Y v)`. The first two differ by
iota, the second and third by delta. Every statement uses
`Fin (obj Y v).len`, which the morphism types force.

The difference is not cosmetic: `π_get` below does not follow from
`Vector.get_ofFnC` by `rw`, which reports no occurrence of the pattern,
nor by a term-mode application, which reports an invalid projection out
of `Y.Hom (obj Y v)`. It goes through
`change (Hom.ofVec _).toVec.get j = _` followed by
`rw [Hom.toVec_ofVec]` and `Vector.get_ofFnC`. `change`, not `show`:
`linter.style.show` is in `mathlibStandardSet` and rejects a
goal-changing `show`, which `weak.warningAsError = true` makes an
error.

### Statements

```lean
theorem π_get (f g : X ⟶ Y) (j : Fin Y.len) :
    (π Y (unionFind f g) ).toVec.get j
      = (Fin.compressEquiv (isRoot Y (unionFind f g))).symm
          ⟨(unionFind f g).root j, isRoot_root Y (unionFind f g) j⟩
@[simp] theorem rep_π (f g : X ⟶ Y) (j : Fin Y.len) :
    (rep Y (unionFind f g)).get ((π Y (unionFind f g)).toVec.get j)
      = (unionFind f g).root j
@[simp] theorem π_rep (f g : X ⟶ Y) (c : Fin (obj Y (unionFind f g)).len) :
    (π Y (unionFind f g)).toVec.get ((rep Y (unionFind f g)).get c) = c

theorem comp_π (f g : X ⟶ Y) :
    f ≫ π Y (unionFind f g) = g ≫ π Y (unionFind f g)
theorem π_desc (f g : X ⟶ Y) (h : Y ⟶ Z) (w : f ≫ h = g ≫ h) :
    π Y (unionFind f g) ≫ desc Y (unionFind f g) h = h
theorem desc_uniq (f g : X ⟶ Y) (h : Y ⟶ Z)
    (m : obj Y (unionFind f g) ⟶ Z)
    (hm : π Y (unionFind f g) ≫ m = h) : m = desc Y (unionFind f g) h
```

`π_get` is the unfolding of `π`, not a normal form, and carries no
attribute; `rep_π` and `π_rep` are the rewrites a proof wants and are
`@[simp]`. Per the note following the cross-workstream constraints,
neither is marked in a direction that rewrites a carrier-level normal
form W3 introduces; W3's rows and W4's row first meet at W5.

`rep_π` is `Equiv.apply_symm_apply` read at the normal form. `π_rep` is
not its mirror image: it is `Equiv.symm_apply_apply` composed with the
step from `(Fin.compressEquiv (isRoot Y v) c).2`, a `Bool` equation, to
the `Prop` that `(rep Y v).get c` is its own root. Rewriting with that
step under `(Fin.compressEquiv …).symm ⟨_, _⟩` fails on a dependent
motive, the proof argument mentioning the term being rewritten, and
`conv` fails the same way; `simp only` at the subterm succeeds, and the
remainder is `congrArg … (Subtype.ext rfl)` composed with
`symm_apply_apply`.

`comp_π` instantiates `root_ofEdges_of_mem` at the membership witness
supplied by `List.mem_map` and `List.mem_finRange`. `π_desc`
instantiates `apply_root_ofEdges` at `h.toVec.get`, whose hypothesis is
`w` read indexwise through W1's `comp_get`. `desc_uniq` needs no
recursion: by `π_rep`, `m.toVec.get c` is
`m.toVec.get ((π Y v).toVec.get ((rep Y v).get c))`, which `hm` and
W1's `comp_get` identify with `h.toVec.get ((rep Y v).get c)`.

### Constraint 9

The constructions use `Vector.ofFnC` and never `Vector.ofFn`,
`Vector.range` or `Vector.finRange`. `List.finRange` is not covered by
that ban and its lemmas are choice-free; W1's `Fin.compressEquiv`
already uses it.

Decidability in `isRoot` is left to instance search rather than named.
Constraint 9's rule to name the term is conditional on two routes
inhabiting the class, and for `DecidableEq (Fin n)` only
`instDecidableEqFin` is in scope; implementation confirms this by
elaborating `isRoot` with `pp.all` and reading the instance off the
term, as constraint 9's measurement discipline requires.

Constraint 9's paragraph on the `Nat` division and order API, added on
branch `doc/constraint-9-nat-arithmetic`, names W4's `Fin self.size`
obligations among the two consumers it binds. In the interface above
the binding is weak: no `Nat` division arises anywhere in W4, the index
arithmetic W3 needs for products and exponentials having no counterpart
here, and the only `Fin` bound discharged is `Sized.root`'s, which is
`Batteries.UnionFind.rootD_lt` applied to `x.isLt` with no arithmetic
between them. Where a bound does need arithmetic — `Sized.discrete`'s
`size + 1` — the constraint's rule applies as stated, and each lemma's
axioms are re-measured at the revision this branch builds against
rather than taken from the paragraph's v4.33.0-rc1 measurement.

## The wrapper

`Geb/Mathlib/CategoryTheory/FinSetSkel/Coequalizer.lean`, in namespace
`FinSetSkel`. The only module of W4 that reaches
`GebMeta.classicalAllowedModules`, per constraint 8.

```lean
def coequalizerCocone (f g : X ⟶ Y) : ColimitCocone (parallelPair f g)
instance hasColimit_parallelPair (f g : X ⟶ Y) :
    HasColimit (parallelPair f g)
instance : HasCoequalizers FinSetSkel.{u}
```

No declaration here carries a namespace prefix in its own name. Writing
`def FinSetSkel.hasColimit_parallelPair` inside a `FinSetSkel`
namespace would name it `FinSetSkel.FinSetSkel.hasColimit_parallelPair`,
which the `dupNamespace` linter rejects; `weak.warningAsError = true`
makes that a build failure.

`coequalizerCocone` opens with `let v := unionFind f g`, which is where
the fold runs, and is `Cofork.ofπ (π Y v) (comp_π f g)` together with
`Cofork.IsColimit.mk` applied to `desc`, `π_desc` and `desc_uniq`,
whose signature —
`(∀ s, t.π ≫ desc s = s.π) → (∀ s m, t.π ≫ m = s.π → m = desc s)` —
takes the three as written, `s.condition` supplying `π_desc`'s `w`. It
is exported under that stable public name because constraint 5 requires
each row's data term to be, and because it is what W5's
`coequalizerCocone` field consumes. The per-diagram `HasColimit`
carries it into instance search, and `HasCoequalizers` follows through
`hasCoequalizers_of_hasColimit_parallelPair`; the two-step route is
`ElementaryTopos.lean`'s own, so W5's field and W4's export meet
without an intervening construction. Constraint 5 requires W4 to
register `HasCoequalizers`, it being one of row k's two hypotheses.

## Tests

Three parallels under `GebTests/Mathlib/`, compositional per
`docs/rules/lean-coding.md`
§ Structure and typeclass patterns.

- `Data/UnionFind/OfEdges.lean` — a fold over a small edge list, with
  the root map computed and asserted, and the two correctness theorems
  instantiated at that list.
- `CategoryTheory/FinSetSkel/Quotient.lean` — a worked coequalizer.
  The objects are `abbrev`s, not `def`s: a numeral at type
  `Fin Y.len` needs `Y.len` to reduce at instance-search transparency,
  which a `def` blocks and an `abbrev` does not. With `X` of length 3
  and `Y` of length 4, `f = ofVec ⟨#[0, 1, 3], rfl⟩` and
  `g = ofVec ⟨#[1, 2, 3], rfl⟩`, the edges are `(0,1)`, `(1,2)` and the
  reflexive `(3,3)`, and the classes are `{0,1,2}` and `{3}`. The
  assertions are `len Y (unionFind f g) = 2` and that `π` sends
  `0`, `1`, `2` to one index and `3` to the other. Which representative
  each class gets is a union-by-rank internal and is not asserted;
  `desc` is exercised at a morphism to an object of length 2 and its
  factorisation checked by computation.
- `CategoryTheory/FinSetSkel/Coequalizer.lean` — resolution of
  `HasCoequalizers FinSetSkel` and of the per-diagram `HasColimit`.

The axiom discipline is checked by `lake lint` through
`GebMeta.detectNonstandardAxiom`, not by a bespoke test.

## Non-Lean deliverables

- `Geb/Mathlib/Data/UnionFind.lean` and its `GebTests` parallel, the
  index files for the new directory; and the corresponding lines in
  `Geb/Mathlib/Data.lean` and `GebTests/Mathlib/Data.lean`.
- The `FinSetSkel` index files, source and test, gain the two new
  modules.
- `GebMeta.classicalAllowedModules` gains
  `Geb.Mathlib.CategoryTheory.FinSetSkel.Coequalizer` and
  `GebTests.Mathlib.CategoryTheory.FinSetSkel.Coequalizer`, and those
  two only.
- `docs/index.md` gains an entry for each of
  the three new source modules.
- `TODO.md` § Triggers gains the entry the umbrella
  spec specifies: whether mathlib accepts a mathlib-to-Batteries
  dependency edge is a maintainer judgement, no `Mathlib.*` module
  referencing `UnionFind`; the condition is the preparation of W4's
  upstream submission, which outlives this group.
- `TODO.md` § Upstream destination of core- and Batteries-targeted
  content: its scoping criterion widens to reach modules that extend
  core or Batteries API as well as those that restate or replace it,
  and the union-find module is named alongside
  `Geb/Mathlib/Data/Vector/OfFn.lean`.
- `TODO.md` § Status: W4's row becomes complete, with
  its module list.
- The spec and plan are removed in the branch's final commits, per
  `CONTRIBUTING.md` § Concern shape.

W4 edits `TODO.md` in three places, and appends to
`GebMeta.classicalAllowedModules`, to `docs/index.md`, and to the
`FinSetSkel` index files. W3 appends to all four, and branch
`doc/constraint-9-nat-arithmetic` amends `TODO.md` as well. These are
the ordinary textual conflicts the group's standing obligation
anticipates for concurrent siblings; W4 rebases onto whichever of them
merges first.

`docs/references.bib` is unchanged. The module docstring of
`Quotient.lean` cites `[MacLaneMoerdijk1992]` for colimits in `Set`,
the coequalizer of a parallel pair being the quotient by the
equivalence relation the pair generates. The section locator is
verified against the primary source before the docstring ships, per the
group's standing obligation on textbook locators.

## Out of scope

- Any complexity claim in a docstring. Establishing the near-linear
  bound would require a citation for the union-find analysis and a
  proof; unproved complexity conjectures already have a home in
  `TODO.md` § Complexity of the decidable validity
  checkers, and W4 adds none.
- The characterisation of the merged relation as the equivalence
  closure of the edges.
- Row k and `HasFiniteColimits`, which are W5's, as is the
  `ElementaryTopos FinSetSkel` instance.
- The stale duplicate W1 row in `TODO.md` § Status,
  which is a defect of the W1/W2 rebase and belongs on its own branch
  per `CONTRIBUTING.md` § Concern shape.
