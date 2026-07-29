# W4: binary coequalizers in FinSetSkel by union-find

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [Findings re-verified](#findings-re-verified)
- [The union-find layer](#the-union-find-layer)
- [The quotient core](#the-quotient-core)
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

Three of the umbrella spec's records of W4 are corrected.

1. Size preservation is not a derivation from `arr_link`,
   `linkAux_size` and `find_size`. `(self.union x y).size = self.size`
   is `by unfold union; simp [UnionFind.size]`, and the `link` and
   `push` counterparts are the same shape.
2. `Batteries.UnionFind.unionN`, which takes `x y : Fin n` together
   with `h : n = self.size`, already exists, so the fold threads its
   size invariant without casting indices.
3. The renumbering is `Fin.compressEquiv`, not `Vector.invOfInjective`.
   W1 exported both; `compressEquiv` renumbers the indices of `Fin n`
   satisfying a `Bool`-valued predicate onto an initial segment, which
   is the operation a coequalizer carrier needs.
   `Vector.invOfInjective` inverts an injective vector, which is what
   W3's rows h and m need. Constraint 7's placement of the inversion in
   W1 is unaffected: `compressEquiv` is in the same W1 module.

Measured against the mathlib limit interface: `parallelPair` depends on
`propext` alone, but `Cofork.ofπ`, `Cofork.IsColimit.mk`,
`Cofork.IsColimit.hom_ext` and
`hasCoequalizers_of_hasColimit_parallelPair` each depend on
`Classical.choice`. The allowlist amendment the standing obligation
predicts for W4 is therefore required, and is required for the wrapper
module alone.

## The union-find layer

`Geb/Mathlib/Data/UnionFind/Closure.lean`, in namespace
`Batteries.UnionFind`. Choice-free, and free of any reference to
category theory or to `FinSetSkel`: it is stated over a size `n`, a
list of edges, and an arbitrary target type. Its upstream target is
Batteries rather than mathlib4, which places it under
`TODO.md` § Upstream destination of core- and
Batteries-targeted content, alongside
`Geb/Mathlib/Data/Vector/OfFn.lean`.

The interface below elaborates as written, with proofs, at the current
revision. The five declarations the quotient core consumes are
`Sized.root`, `ofEdges`, `root_root`, `root_ofEdges_of_mem` and
`root_ofEdges_sound`; the rest support them.

```lean
theorem size_union (self : UnionFind) (x y : Fin self.size) :
    (self.union x y).size = self.size

def Sized (n : Nat) : Type := {u : UnionFind // u.size = n}

def Sized.discrete (n : Nat) : Sized n
def Sized.union (u : Sized n) (x y : Fin n) : Sized n
def Sized.root (u : Sized n) (x : Fin n) : Fin n

theorem Sized.root_eq_iff {u : Sized n} {a b : Fin n} :
    u.root a = u.root b ↔ u.1.Equiv a b
theorem Sized.rootD_discrete : ∀ m x : Nat, (discrete m).1.rootD x = x
theorem Sized.root_discrete {a b : Fin n} :
    (discrete n).root a = (discrete n).root b ↔ a = b

def ofEdges (n : Nat) (l : List (Fin n × Fin n)) : Sized n

theorem root_root (u : Sized n) (x : Fin n) :
    u.root (u.root x) = u.root x
theorem root_ofEdges_of_mem {l : List (Fin n × Fin n)} {a b : Fin n}
    (hab : (a, b) ∈ l) :
    (ofEdges n l).root a = (ofEdges n l).root b
theorem root_ofEdges_sound {α : Type} {l : List (Fin n × Fin n)}
    {h : Fin n → α} (hl : ∀ p ∈ l, h p.1 = h p.2) (x : Fin n) :
    h ((ofEdges n l).root x) = h x
```

`Sized` carries the size as a subtype rather than re-deriving it at
each step, so the `Fin n` indices passed to `union` need no cast.
`Sized.root` returns `Fin n` rather than Batteries' `Nat`-valued
`rootD`, discharging the bound once so that every downstream statement
is an equation between `Fin n` terms, which is W1's normal form.

The two theorems the construction consumes are the two directions of
correctness. `root_ofEdges_of_mem` says every listed edge is merged;
its proof is a recursion over the edge list using the left disjunct of
`equiv_union` for monotonicity and its middle disjunct for the step.
`root_ofEdges_sound` says nothing beyond the listed edges is merged; it
is stated as the eliminator — any `h` agreeing on the edges agrees on
roots — rather than as a characterisation of the merged relation as the
equivalence closure of the edges. The eliminator form is what the
coequalizer's factorisation law instantiates directly, and the
characterisation has no other consumer in W4 or W5. Its proof is a
recursion over the edge list, generalised over the accumulated
structure, with the three disjuncts of `equiv_union` discharged by the
inductive hypothesis and by `hl`.

Two auxiliary recursions, `equiv_foldl_of_equiv` and
`equiv_foldl_of_mem`, carry the fold-level statements those two
theorems are read off. Per
`docs/rules/lean-coding.md`
§ Recursion and induction through recursors, each recursion is written
as an explicit recursor application rather than through the `induction`
tactic.

## The quotient core

`Geb/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean`. Choice-free.
Named for what it constructs rather than for its categorical role,
parallel to W1's `Basic.lean` and `Skeleton.lean`.

Stated over `FinSetSkel` morphisms in W1's application-normal form
`f.toVec.get i`, not over bare index functions: W1's `Basic.lean` is
choice-free, so the core may import it, and stating over morphisms
makes the wrapper a transcription rather than a translation.

Both W4 modules declare `namespace FinSetSkel.Coequalizer`, the
wrapper's `coequalizerCocone` excepted. The namespace is not optional:
`FinSetSkel.len` is the object structure's field, so a `len` declared
directly in `FinSetSkel` would collide with it. Nor is it
`FinSetSkel.Quotient`, on the precedent `TODO.md` records for
`PFunctor.id`: a namespace member shadowing a root-namespace name —
here `Quot` or `Quotient` — breaks unqualified uses of the root name
throughout the namespace.

For `f g : X ⟶ Y`:

```lean
def edges (f g : X ⟶ Y) : List (Fin Y.len × Fin Y.len) :=
  (List.finRange X.len).map fun i ↦ (f.toVec.get i, g.toVec.get i)

def unionFind (f g : X ⟶ Y) : UnionFind.Sized Y.len :=
  UnionFind.ofEdges _ (edges f g)

def isRoot (f g : X ⟶ Y) : Fin Y.len → Bool :=
  fun j ↦ decide ((unionFind f g).root j = j)

def len (f g : X ⟶ Y) : ℕ :=
  ((List.finRange Y.len).filter (isRoot f g)).length

def obj (f g : X ⟶ Y) : FinSetSkel.{u} := ⟨len f g⟩

theorem isRoot_root (f g : X ⟶ Y) (j : Fin Y.len) :
    isRoot f g ((unionFind f g).root j)

def rep (f g : X ⟶ Y) : Fin (len f g) → Fin Y.len
def π (f g : X ⟶ Y) : Y ⟶ obj f g
def desc (f g : X ⟶ Y) {Z : FinSetSkel.{u}} (h : Y ⟶ Z) : obj f g ⟶ Z
```

`rep` is the first projection of `Fin.compressEquiv (isRoot f g)`, and
`π` is `ofVec (Vector.ofFnC …)` sending `j` to the compressed index of
`(unionFind f g).root j`; the side condition that this root satisfies
`isRoot f g` is `root_root`. `desc h` is
`ofVec (Vector.ofFnC fun c ↦ h.toVec.get (rep f g c))`; it carries no
compatibility hypothesis, so it computes for any `h`, and only
`π_desc` below constrains `h`.

The constructions use `Vector.ofFnC` and never `Vector.ofFn`,
`Vector.range` or `Vector.finRange`, per constraint 9. `List.finRange`
is not covered by that ban and its lemmas are choice-free; W1's
`Fin.compressEquiv` already uses it. Each decidability instance is
named rather than left to search, per constraint 9's general shape:
`isRoot` decides an equation in `Fin Y.len` through
`instDecidableEqFin`.

Constraint 9's paragraph on the `Nat` division and order API, added on
branch `doc/constraint-9-nat-arithmetic`, names W4's `Fin self.size`
obligations among the two consumers it binds. In the interface
elaborated above the binding is weak: no `Nat` division arises anywhere
in W4, the index arithmetic W3 needs for products and exponentials
having no counterpart here, and the only `Fin` bound discharged is
`Sized.root`'s, which is `Batteries.UnionFind.rootD_lt` applied to
`x.isLt` with no arithmetic between them. Where a bound does need
arithmetic — `Sized.discrete`'s `size + 1` — the constraint's rule
applies as stated, and each lemma's axioms are re-measured at the
revision this branch builds against rather than taken from the
paragraph's v4.33.0-rc1 measurement.

Three application-normal-form lemmas carry what a proof needs about the
pair:

```lean
theorem π_get (f g : X ⟶ Y) (j : Fin Y.len) :
    (π f g).toVec.get j
      = (Fin.compressEquiv (isRoot f g)).symm
          ⟨(unionFind f g).root j, isRoot_root f g j⟩
theorem rep_π (f g : X ⟶ Y) (j : Fin Y.len) :
    rep f g ((π f g).toVec.get j) = (unionFind f g).root j
theorem π_rep (f g : X ⟶ Y) (c : Fin (len f g)) :
    (π f g).toVec.get (rep f g c) = c
```

`rep_π` and `π_rep` are the two round trips of `Fin.compressEquiv`,
read at the normal form; `π_rep` is what makes `desc_uniq` a
calculation rather than a recursion. Per the note
following the cross-workstream constraints, none is marked `simp` in a
direction that rewrites a carrier-level normal form W3 introduces;
W3's rows and W4's row first meet at W5.

The universal property, in three statements:

```lean
theorem comp_π (f g : X ⟶ Y) : f ≫ π f g = g ≫ π f g
theorem π_desc (f g : X ⟶ Y) {Z} (h : Y ⟶ Z) (w : f ≫ h = g ≫ h) :
    π f g ≫ desc f g h = h
theorem desc_uniq (f g : X ⟶ Y) {Z} (h : Y ⟶ Z) (m : obj f g ⟶ Z)
    (hm : π f g ≫ m = h) : m = desc f g h
```

`comp_π` instantiates `root_ofEdges_of_mem` at the membership witness
supplied by `List.mem_map` and `List.mem_finRange`. `π_desc`
instantiates `root_ofEdges_sound` at `h.toVec.get`, whose hypothesis is
`w` read indexwise through W1's `comp_get`. `desc_uniq` needs no
recursion: by `π_rep`, `m.toVec.get c` is
`m.toVec.get ((π f g).toVec.get (rep f g c))`, which `hm` and W1's
`comp_get` identify with `h.toVec.get (rep f g c)`.

## The wrapper

`Geb/Mathlib/CategoryTheory/FinSetSkel/Coequalizer.lean`. The only
module of W4 that reaches `GebMeta.classicalAllowedModules`, per
constraint 8.

```lean
def FinSetSkel.coequalizerCocone (f g : X ⟶ Y) :
    ColimitCocone (parallelPair f g)
instance FinSetSkel.hasColimit_parallelPair (f g : X ⟶ Y) :
    HasColimit (parallelPair f g)
instance : HasCoequalizers FinSetSkel.{u}
```

`coequalizerCocone` is `Cofork.ofπ (π f g) (comp_π f g)` together with
`Cofork.IsColimit.mk` applied to `desc`, `π_desc` and `desc_uniq`. It
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

- `Data/UnionFind/Closure.lean` — a fold over a small edge list, with
  the root map computed and asserted, and the two correctness theorems
  instantiated at that list.
- `CategoryTheory/FinSetSkel/Quotient.lean` — a worked coequalizer:
  a parallel pair `Fin 3 ⟶ Fin 4` gluing `0 ~ 1` and `1 ~ 2`, with
  `len`, `π` and a `desc` computed and asserted.
- `CategoryTheory/FinSetSkel/Coequalizer.lean` — resolution of
  `HasCoequalizers FinSetSkel` and of the per-diagram `HasColimit`.

The axiom discipline is checked by `lake lint` through
`GebMeta.detectNonstandardAxiom`, not by a bespoke test.

## Non-Lean deliverables

- `Geb/Mathlib/Data/UnionFind.lean` and its test parallel, the index
  files for the new directory, and the corresponding lines in
  `Geb/Mathlib/Data.lean` and `GebTests/Mathlib/Data.lean`.
- The `FinSetSkel` index files gain the two new modules.
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
- `TODO.md` § Status: W4's row becomes complete, with
  its module list.
- The spec and plan are removed in the branch's final commits, per
  `CONTRIBUTING.md` § Concern shape.

W4 edits `TODO.md` in two places. So does branch
`doc/constraint-9-nat-arithmetic`, which amends constraint 9, and so
does W3. These are the ordinary textual conflicts the group's standing
obligation anticipates for concurrent siblings; W4 rebases onto
whichever of them merges first.

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
