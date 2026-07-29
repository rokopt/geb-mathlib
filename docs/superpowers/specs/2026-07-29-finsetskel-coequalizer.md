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
current when they were taken. The interface below consumes these, each
re-verified at the revision this branch builds against by
`#print axioms` through the `lean-lsp` MCP, and each depending on
`propext` and `Quot.sound` only:

`Batteries.UnionFind.equiv_union`, `rootD_rootD`, `rootD_lt`,
`rootD_empty` and `root_push`; and W1's `Fin.compressEquiv` and
`List.Nodup.getEquivC`.

The umbrella spec's list also named `arr_link`, `linkAux_size` and
`find_size`, which correction 1 below makes unnecessary; they are
choice-free too, but W4 does not reach them.

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
`coequalizerCocone`, cited in the module docstrings of both
`Quotient.lean` and `Coequalizer.lean`, the statement being the same
one in each.

The citation key is not settled here. `AGENTS.md` § Verify agent claims
requires the attribution verified against the primary source before the
identifier is recorded, and this spec is an artifact in that sense, so
naming a key on the strength of a plausible title would be the thing
that rule forbids. `MacLaneMoerdijk1992` is the candidate, being
already in `docs/references.bib`; Mac Lane, _Categories for the Working
Mathematician_, is the more usual locator for colimits in `Set` and is
not yet in the file. Settling which, and its section locator, is an
obligation on the plan, discharged against the book rather than against
a secondary attestation — the same standard the group's standing
obligation sets for the skeleton locator. No `.bib` change is entailed
if the candidate holds.

Everything else is novel, in the sense of being a representation
choice rather than a statement taken from a source: `Sized`,
`Sized.discrete`, `Sized.union`, `Sized.root`, `Sized.ofEdges` and the
theorems about them; and `edges`, `unionFind`, `isRoot`, `len`, `rep`
and the application-normal-form lemmas. The disjoint-set algorithm is
not novel, but it is not restated here either — it is Batteries'.

## The union-find layer

`Geb/Mathlib/Data/UnionFind/OfEdges.lean`, in namespace
`Batteries.UnionFind`. Every declaration but `size_union` and
`size_push` is about `Sized` and carries a `Sized.` prefix in its own
name, `ofEdges` included: `Batteries.UnionFind.root_root` would
otherwise read as a statement about Batteries' own `UnionFind.root`.
The prefix is written into the name rather than opened as a deeper
namespace, since `namespace Batteries.UnionFind.Sized` together with a
declaration named `Sized.root_root` yields
`Batteries.UnionFind.Sized.Sized.root_root`, which `linter.dupNamespace`
rejects — the same rule § The wrapper invokes.

Choice-free, and free of any reference to category theory or to
`FinSetSkel`: it is stated over a size `n`, a list of edges, and an
arbitrary target type. Named for the fold, not for a closure: the
closure characterisation is out of scope below.

Its upstream target is Batteries rather than mathlib4, which is the
subject of `TODO.md` § Upstream destination of core- and
Batteries-targeted content. W4 adds this module to that item's
"currently" list, a one-line edit and the third of W4's `TODO.md`
edits. It does not touch the item's scoping criterion, which reads
"restate or replace" and so does not literally reach declarations that
extend a Batteries type with new statements. The addition is therefore
made under the item's own subject — where content whose upstream target
is not mathlib4 belongs — and the mismatch between that subject and the
criterion's present wording is stated in the same edit, as the thing
the separate branch settles. Rewording the criterion
would oblige a re-sweep of `Geb/Mathlib/`, the item being deliberately
scoped by criterion rather than by module list; that is a second
concern, and `CONTRIBUTING.md` § Concern shape puts it on its own
branch, as it does the stale status-table row in § Out of scope.
Nothing in W4 depends on the outcome: `scripts/extract-pr.sh` maps
`Geb/Mathlib/*` to `Mathlib/` unconditionally, but it is a manual tool
whose `Geb/Mathlib/*` arm already defers to this item.

The six declarations the quotient core consumes are `Sized`,
`Sized.root`, `Sized.ofEdges`, `Sized.root_root`,
`Sized.root_ofEdges_eq_of_mem` and `Sized.apply_root_ofEdges`; the rest
support them. `lakefile.toml` sets `autoImplicit = false`, so the
binders below are declared, not elided. The module writes `Nat` rather
than `ℕ`, following Batteries, its upstream target; the quotient core
writes `ℕ`, following mathlib.

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
def Sized.ofEdges (n : Nat) (l : List (Fin n × Fin n)) : Sized n

theorem Sized.root_eq_iff {v : Sized n} {a b : Fin n} :
    v.root a = v.root b ↔ v.1.Equiv a b
theorem Sized.equiv_union {v : Sized n} {x y : Fin n} {a b : Nat} :
    (v.union x y).1.Equiv a b ↔
      v.1.Equiv a b ∨ v.1.Equiv a x ∧ v.1.Equiv y b
                    ∨ v.1.Equiv a y ∧ v.1.Equiv x b
theorem Sized.rootD_discrete (m x : Nat) : (discrete m).1.rootD x = x
theorem Sized.root_discrete (x : Fin n) : (discrete n).root x = x
theorem Sized.root_root (v : Sized n) (x : Fin n) :
    v.root (v.root x) = v.root x
theorem Sized.root_ofEdges_eq_of_mem {l : List (Fin n × Fin n)}
    {a b : Fin n} (hab : (a, b) ∈ l) :
    (ofEdges n l).root a = (ofEdges n l).root b
theorem Sized.apply_root_ofEdges {α : Type u} {l : List (Fin n × Fin n)}
    {h : Fin n → α} (hl : ∀ p ∈ l, h p.1 = h p.2) (x : Fin n) :
    h ((ofEdges n l).root x) = h x
```

`apply_root_ofEdges` is named for its left-hand side; `_sound` is not
among mathlib's discharging-operator suffixes.

`Sized.equiv_union` restates Batteries' `UnionFind.equiv_union` at
`Sized.union`, and is not optional. `Sized.union` is built on
`unionN`, whose `match n, h with` does not reduce until the size proof
is destructed, so Batteries' lemma does not apply to `(v.union x y).1`
as it stands; the restatement destructs `v` and is otherwise the same
lemma. All three recursions below consume this form rather than
Batteries'.

`Sized` carries the size as a subtype rather than re-deriving it at
each step, so the `Fin n` indices passed to `union` need no cast. It is
a `def`, and so opaque at reducible transparency — the property W1's
`Basic.lean` docstring records as its reason for making the objects a
structure instead. The cases differ in where the representation is
read. W1's objects are projected as `X.len` in every downstream
statement, so opacity would block every `simp` lemma; `Sized`'s
representation is projected as `v.1` in two proofs only, `Sized.union`
and `Sized.root`, both of which destruct it with `obtain ⟨u, rfl⟩`.
Every public statement is over `Sized.root`, not over `v.1`.
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
correctness. `root_ofEdges_eq_of_mem` says every listed edge is merged.
`apply_root_ofEdges` says nothing beyond the listed edges is merged; it
is stated as the eliminator — any `h` agreeing on the edges agrees on
roots — rather than as a characterisation of the merged relation as the
equivalence closure of the edges. The eliminator form is what the
coequalizer's factorisation law instantiates directly, and the
characterisation has no other consumer in W4 or W5.

Three auxiliary recursions over the edge list carry them, each
generalised over the accumulated `Sized n`:

```lean
theorem Sized.equiv_foldl_of_equiv (l : List (Fin n × Fin n))
    (a b : Fin n) (v : Sized n) (hv : v.1.Equiv a b) :
    (l.foldl (fun v p ↦ v.union p.1 p.2) v).1.Equiv a b
theorem Sized.equiv_foldl_of_mem (l : List (Fin n × Fin n))
    (a b : Fin n) (hab : (a, b) ∈ l) (v : Sized n) :
    (l.foldl (fun v p ↦ v.union p.1 p.2) v).1.Equiv a b
theorem Sized.apply_root_foldl {α : Type u} {h : Fin n → α}
    (l : List (Fin n × Fin n)) (hl : ∀ p ∈ l, h p.1 = h p.2)
    (v : Sized n) (hv : ∀ x, h (v.root x) = h x) (x : Fin n) :
    h ((l.foldl (fun v p ↦ v.union p.1 p.2) v).root x) = h x
```

The first two are `Equiv`-level and give `root_ofEdges_eq_of_mem`: the
left disjunct of `Sized.equiv_union` supplies monotonicity, its middle
disjunct the step. The third is generalised over `h` as well as over
the accumulator, and is the one `apply_root_ofEdges` is read off, at
`v := Sized.discrete n` with `Sized.root_discrete` discharging its
invariant. It is not derivable from the first two: those are statements
about `Equiv`, and passing from them to a statement about an arbitrary
`h` is exactly the closure characterisation this module declines to
prove. Its own step discharges the three disjuncts of
`Sized.equiv_union` against `hv` and `hl`.

Per `docs/rules/lean-coding.md` § Recursion and induction through
recursors, every recursion here is an explicit recursor application
rather than an `induction` tactic: the three above, and also
`Sized.discrete`, which is an `n`-fold `push`, and its lemma
`Sized.rootD_discrete`. Inside `List.rec (motive := …)` the fold
function's binders are annotated —
`fun (v : Sized n) (p : Fin n × Fin n) ↦ v.union p.1 p.2` — since with
them bare the lambda's elaboration is postponed and the inductive
hypothesis fails to apply.

`Sized.equiv_union` shares its base name with Batteries'
`UnionFind.equiv_union`, one namespace up. Both resolve, but a bare
`equiv_union` inside the module means Batteries'; this module writes
each qualified.

## The quotient core

`Geb/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean`, in namespace
`FinSetSkel.Quotient`. Choice-free. The namespace tracks the module
path, and the extra level is not optional: `FinSetSkel.len` is the
object structure's field, so a `len` declared directly in `FinSetSkel`
collides with it. The namespace does shadow `_root_.Quotient`, but only
for `open`: an `open Quotient` inside `namespace FinSetSkel` resolves
to this one and draws `linter.ambiguousOpen`. Qualified reference is
unaffected, and the wrapper qualifies — `Quotient.π`, `Quotient.comp_π`
— rather than opening. W4 uses neither `Quot` nor `Quotient` itself.

Stated over `FinSetSkel` morphisms in W1's application-normal form
`f.toVec.get i`, not over bare index functions: W1's `Basic.lean` is
choice-free, so the core may import it, and stating over morphisms
makes the wrapper a transcription rather than a translation.

The module `open`s `Batteries`. The union-find layer's declarations are
`Batteries.UnionFind.Sized` and below; this spec writes them as
`UnionFind.Sized`, `Sized.root_ofEdges_eq_of_mem` and so on throughout,
which is the form that `open` licenses.

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
per-index renumbering data is a `Vector`, not a function; and the three
definitions that call `Vector.ofFnC` — `rep`, `π` and `desc` — bind
what their lambda needs in a `let`, which shares in each because each
returns a value, a vector in the first case and a morphism in the other
two.

### Definitions

Two binder groups, and two `variable` scopes, since `Y` is a variable
in the first and an explicit binder in the second. `edges` and
`unionFind` take the parallel pair; everything after takes the
union-find and never calls `unionFind`.

```lean
universe u

section
variable {X Y : FinSetSkel.{u}}

def edges (f g : X ⟶ Y) : List (Fin Y.len × Fin Y.len) :=
  (List.finRange X.len).map fun i ↦ (f.toVec.get i, g.toVec.get i)

def unionFind (f g : X ⟶ Y) : UnionFind.Sized Y.len :=
  UnionFind.Sized.ofEdges _ (edges f g)

end

section
variable {n : ℕ} {Z : FinSetSkel.{u}}

def isRoot (v : UnionFind.Sized n) : Fin n → Bool :=
  fun j ↦ decide (v.root j = j)

def len (v : UnionFind.Sized n) : ℕ :=
  ((List.finRange n).filter (isRoot v)).length

theorem isRoot_root (v : UnionFind.Sized n) (j : Fin n) :
    isRoot v (v.root j)

def obj (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len) :
    FinSetSkel.{u} := ⟨len v⟩

def rep (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len) :
    Vector (Fin Y.len) (obj Y v).len
def π (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len) : Y ⟶ obj Y v
def desc (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len)
    (h : Y ⟶ Z) : obj Y v ⟶ Z

end
```

`isRoot_root` sits here rather than with the statements below because
`π` discharges its side condition with it, so it precedes `π` in the
file.

`Y` is a binder exactly where a `FinSetSkel` object or morphism occurs
in the type — `obj`, `rep`, `π`, `desc` — and is absent where only
indices do: `isRoot`, `len` and `isRoot_root` take `{n : ℕ}`, inferred
from `v`. Where `Y` is a binder it is explicit, because
`UnionFind.Sized Y.len` mentions `Y.len`, not `Y`, so the elaborator
cannot recover `Y` from it; `?Y.len =?= n` does not solve.

`isRoot` and `len` mention no `FinSetSkel` and could live in the
union-find module. They stay here because they exist to define the
carrier — `len`'s only consumer is `obj`, and `isRoot`'s consumers are
all in this module — and `TODO.md` § FinSetSkel as an elementary topos
assigns the carrier to this row; a module boundary drawn through one
construction would be paid for nothing.

`rep Y v` is `Vector.ofFnC fun c ↦ (Fin.compressEquiv (isRoot v) c).1`
with the equivalence bound in a `let` above the lambda — a vector
rather than the function `Fin (obj Y v).len → Fin Y.len`, so that its
consumers index it in constant time instead of rebuilding
`Fin.compressEquiv` per class. `π Y v` is `ofVec (Vector.ofFnC …)`
sending `j` to the compressed index of `v.root j`, the side condition
that this root satisfies `isRoot v` being `isRoot_root`, itself
`Sized.root_root`; it binds the equivalence in a `let` likewise.
`desc Y v h` is `ofVec (Vector.ofFnC fun c ↦ h.toVec.get (r.get c))`
under `let r := rep Y v`; it carries no compatibility hypothesis, so it
computes for any `h`, and only `π_desc` below constrains `h`.

`isRoot v` stays a function rather than a vector: `v` is a parameter,
so applying it costs a `root` lookup and rebuilds nothing.

### Index types

Three forms of the carrier's index type are in play:
`Fin (obj Y v).len`, `Fin (len v)`, and
`Fin ((List.finRange Y.len).filter (isRoot v)).length`, which is the
domain of `Fin.compressEquiv (isRoot v)`. The first two differ by iota,
the second and third by delta. Every statement uses
`Fin (obj Y v).len`, which the morphism types force.

The difference is not cosmetic, and it is why each of `π`, `rep` and
`desc` needs an unfolding lemma stated by hand rather than reached by
`rw [Vector.get_ofFnC]`, which reports no occurrence of the pattern
because the index types differ.

The two morphism-valued ones, `π_get` and `desc_get`, need more than
that: a term-mode `Vector.get_ofFnC _ _` reports an invalid projection
out of `Y.Hom _`, and `rfl` fails. Each goes through
`change (Hom.ofVec _).toVec.get _ = _`, then `rw [Hom.toVec_ofVec]`,
closing with `exact Vector.get_ofFnC _ _`. The closing step is `exact`,
not a further `rw`: `rw [Hom.toVec_ofVec, Vector.get_ofFnC]` fails with
the same no-occurrence error. `rep_get` needs none of this — it is
`Vector.get_ofFnC _ _` in term mode, its subject being a vector rather
than a morphism.

`change`, not `show`: `linter.style.show` is in `mathlibStandardSet`
and rejects a goal-changing `show`, which `weak.warningAsError = true`
makes an error.

### Statements

Two further `variable` scopes, on the pattern of § Definitions: the
five general lemmas take `Y` as an explicit binder with `Z` a variable;
the three universal-property statements take `X`, `Y` and `Z` all as
variables, `Y` included, since there `v` is `unionFind f g` and `Y`
comes from the pair.

The three unfolding lemmas and the two round-trip lemmas hold at an
arbitrary `v`, and are stated there, as `isRoot_root` above already is.
No edge enters them, and stating them at `unionFind f g` would carry
`X`, `f` and `g` through proofs that do not use them and would keep
them from firing in the worked example of § Tests, or at any other `v`
W5 might supply.

```lean
theorem π_get (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len)
    (j : Fin Y.len) :
    (π Y v).toVec.get j
      = (Fin.compressEquiv (isRoot v)).symm ⟨v.root j, isRoot_root v j⟩
theorem rep_get (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len)
    (c : Fin (obj Y v).len) :
    (rep Y v).get c = (Fin.compressEquiv (isRoot v) c).1
theorem desc_get (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len)
    (h : Y ⟶ Z) (c : Fin (obj Y v).len) :
    (desc Y v h).toVec.get c = h.toVec.get ((rep Y v).get c)

theorem rep_π (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len)
    (j : Fin Y.len) :
    (rep Y v).get ((π Y v).toVec.get j) = v.root j
theorem π_rep (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len)
    (c : Fin (obj Y v).len) :
    (π Y v).toVec.get ((rep Y v).get c) = c
```

`rep_π` is `π_get` then `rep_get` then `Equiv.apply_symm_apply`, taken
as one `exact … .trans …`: rewriting with `rep_get` after `π_get` hits
the index-type mismatch at the nested position. `π_rep` is not its
mirror image: it is `π_get` then `rep_get`, then
`Equiv.symm_apply_apply` composed with the step from
`(Fin.compressEquiv (isRoot v) c).2`, a `Bool` equation, to the `Prop`
that `(rep Y v).get c` is its own root. Rewriting with that step under
`(Fin.compressEquiv …).symm ⟨_, _⟩` fails on a dependent motive, the
proof argument mentioning the term being rewritten, and `conv` fails
the same way; `simp only` at the subterm succeeds.

None of the five carries `@[simp]` as specified. `rep_π` and `π_rep`
are the candidates, but the index types above obstruct `rw` at nested
positions, so whether `simp` can fire them is settled by exhibiting a
goal each closes, not in advance; implementation marks a lemma
`@[simp]` only then, and records which. Per the note following the
cross-workstream constraints, no such attribute is added in a direction
that rewrites a carrier-level normal form W3 introduces; W3's rows and
W4's row first meet at W5.

The universal property is where the edges enter, and is stated at
`v := unionFind f g`:

```lean
theorem comp_π (f g : X ⟶ Y) :
    f ≫ π Y (unionFind f g) = g ≫ π Y (unionFind f g)
theorem π_desc (f g : X ⟶ Y) (h : Y ⟶ Z) (w : f ≫ h = g ≫ h) :
    π Y (unionFind f g) ≫ desc Y (unionFind f g) h = h
theorem desc_uniq (f g : X ⟶ Y) (h : Y ⟶ Z)
    (m : obj Y (unionFind f g) ⟶ Z)
    (hm : π Y (unionFind f g) ≫ m = h) : m = desc Y (unionFind f g) h
```

`comp_π` instantiates `Sized.root_ofEdges_eq_of_mem` at the membership
witness supplied by `List.mem_map` and `List.mem_finRange`. `π_desc`
instantiates `Sized.apply_root_ofEdges` at `h.toVec.get`, whose
hypothesis is `w` read indexwise through W1's `comp_get`, and consumes
`desc_get` and `rep_π`. `desc_uniq` needs no recursion: it is
`hom_ext fun c ↦ by rw [desc_get, ← hm, comp_get, π_rep]`.

### Constraint 9

The constructions use `Vector.ofFnC` and never `Vector.ofFn`,
`Vector.range` or `Vector.finRange`. `List.finRange` is not covered by
that ban and its lemmas are choice-free; W1's `Fin.compressEquiv`
already uses it. Importing `Batteries.Data.UnionFind.Lemmas` makes no
`Batteries.Data.Vector.*` module reachable, so it admits none of
constraint 9's tainted `get`-form counterparts.

Decidability in `isRoot` is left to instance search rather than named.
Constraint 9's rule to name the term is conditional on two routes
inhabiting the class, and for `DecidableEq (Fin n)` only
`instDecidableEqFin` is in scope; implementation confirms this by
elaborating `isRoot` with `pp.all` and reading the instance off the
term, as constraint 9's measurement discipline requires.

Constraint 9 gains three paragraphs and a measurement rule on `jj`
change `ypqrxnwk`, "record three choice-taint families in constraint
9". Each binds W3 through W5, and two name W4. W4 answers all three.

That change is on branch `feat/choice-free-primitives` and is not an
ancestor of this branch, so the text this section answers is not
readable from W4 alone. W4 rebases onto it once it merges, which is the
precondition for this section reading as an answer rather than as an
assertion; if it does not merge, the three answers stand as
measurements in their own right — each is a statement about W4's own
construction — and this section loses only its addressee.

The `Nat` division and order paragraph names W4's `Fin self.size`
obligations. It reaches little of W4: no `Nat` division arises
anywhere, the index arithmetic W3 needs for products and exponentials
having no counterpart here, and the only `Fin` bound discharged is
`Sized.root`'s, which is `Batteries.UnionFind.rootD_lt` applied to
`x.isLt` with no arithmetic between them. Where a bound does need
arithmetic — `Sized.discrete`'s `size + 1` — the rule applies as
stated.

The `Equiv`-transport paragraph names W4's renumbering of union-find
roots onto an initial segment, as a domain transport, the family in
which `Equiv.arrowCongr` and `Equiv.piCongrLeft` are choice-dependent
and for which that branch supplies `Equiv.arrowCongrLeftC`. W4 does not
transport a function type in either direction: `rep` and `π` apply
`Fin.compressEquiv (isRoot v)` and its `symm` pointwise, to an index
and to a subtype element, and no `Equiv` of W4's is an equivalence
between arrow types. The paragraph's repair is therefore not needed
here, and W4 does not import `Geb/Mathlib/Logic/Equiv/Basic.lean`.

The equality-API paragraph binds W4 vacuously. Nothing in the interface
decides membership: `List.filter` applies a `Bool`-valued function,
`comp_π`'s membership witness is a proposition rather than a decision,
and the only `DecidableEq` W4 uses at `Fin n` is `instDecidableEqFin`,
which is axiom-free. The `LawfulBEq (Fin n)` the paragraph pins is not
reached. In the tests, deciding equality of morphisms goes through
W1's pinned `decidableEqHom`, which is the same paragraph's concern one
level down and is already settled.

Each of these is re-measured at the revision this branch builds
against rather than taken from the paragraph's v4.33.0-rc1 measurement,
and per the amendment's measurement rule the measurement is taken at a
monomorphic instantiation: `#print axioms` on `apply_root_ofEdges`,
whose `α` is a bare type variable carrying no instance, reports that
constant and not its use, so the reading that counts is the one at
`α := Fin Z.len` inside `π_desc`.

## The wrapper

`Geb/Mathlib/CategoryTheory/FinSetSkel/Coequalizer.lean`, in namespace
`FinSetSkel`. The only module of W4 that reaches
`GebMeta.classicalAllowedModules`, per constraint 8. Its module
docstring carries `[MacLaneMoerdijk1992]` in `## References`, the
declaration below being on the transcription list.

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
takes the three as written, `Cofork.condition` supplying `π_desc`'s
`w`. It is exported under that stable public name because constraint 5
requires each row's data term to be, and because it is what W5's
`coequalizerCocone` field consumes. The per-diagram `HasColimit`
carries it into instance search, and `HasCoequalizers` follows through
`hasCoequalizers_of_hasColimit_parallelPair`; the two-step route is
`ElementaryTopos.lean`'s own, so W5's field and W4's export meet
without an intervening construction. Constraint 5 requires W4 to
register `HasCoequalizers`, it being one of row k's two hypotheses.

## Tests

Three parallels under `GebTests/Mathlib/`, compositional per
`docs/rules/lean-coding.md`
§ Structure and typeclass patterns. Each carries a module docstring and
the per-declaration docstrings the same rules require of any `.lean`
file; the `Quotient` parallel qualifies rather than opens, for the
reason § The quotient core gives.

Computed assertions use `#guard`, not `by decide` or `by rfl`. Nothing
built from `UnionFind.union` or `rootD` reduces in the kernel:
`root`, `findAux` and `find` are well-founded recursions whose measure
is the `noncomputable` `rankMax`, so `by rfl` fails on so small a goal
as `(UnionFind.empty.push.push.union 0 1).size = 2`, and `decide` gets
stuck at the `Decidable` instance. `native_decide` is not the escape:
`GebMeta.detectNonstandardAxiom` forbids `Lean.ofReduceBool`
everywhere. `#guard` evaluates through the compiler and introduces no
declaration, hence no axiom obligation, and
`GebTests/Internal/AxiomLinter.lean` already uses it. W1's test
parallels use `rfl` and `decide` because their subjects are vectors,
which do reduce; the union-find is the difference.

- `Data/UnionFind/OfEdges.lean` — a fold over a small edge list, with
  the root map `#guard`ed, and `Sized.root_ofEdges_eq_of_mem` and
  `Sized.apply_root_ofEdges` instantiated at that list. Those two are
  proofs and need no reduction.
- `CategoryTheory/FinSetSkel/Quotient.lean` — a worked coequalizer.
  The objects are `abbrev`s, not `def`s: a numeral at type
  `Fin Y.len` needs `Y.len` to reduce at instance-search transparency,
  which a `def` blocks and an `abbrev` does not. With `X` of length 3
  and `Y` of length 4, `f = ofVec ⟨#[0, 1, 3], rfl⟩` and
  `g = ofVec ⟨#[1, 2, 3], rfl⟩`, the edges are `(0,1)`, `(1,2)` and the
  reflexive `(3,3)`, and the classes are `{0,1,2}` and `{3}`. The
  `#guard`s are `len (unionFind f g) == 2` and that `π` sends `0`, `1`,
  `2` to one index and `3` to the other. Which representative each
  class gets is fixed by union by rank, an internal of Batteries'
  algorithm, and is not asserted. For `desc`, take
  `h : Y ⟶ ⟨2⟩` to be `ofVec ⟨#[0, 0, 0, 1], rfl⟩`; that it satisfies
  `f ≫ h = g ≫ h`, and the factorisation
  `π Y (unionFind f g) ≫ desc Y (unionFind f g) h = h`, are both
  `#guard`ed through W1's morphism `DecidableEq` in its `Bool` form.
  The same two facts also follow from `comp_π` and `π_desc` as proofs;
  the test asserts them by computation, which is what exercises the
  algorithm.
- `CategoryTheory/FinSetSkel/Coequalizer.lean` — resolution of
  `HasCoequalizers FinSetSkel` and of the per-diagram `HasColimit`.
  Instance resolution needs no reduction, so this module is unaffected
  by the above.

The axiom discipline is checked by `lake lint` through
`GebMeta.detectNonstandardAxiom`, not by a bespoke test.

## Non-Lean deliverables

- `Geb/Mathlib/Data/UnionFind.lean` and its `GebTests` parallel, the
  index files for the new directory; and the corresponding lines in
  `Geb/Mathlib/Data.lean` and `GebTests/Mathlib/Data.lean`.
- The `FinSetSkel` index files, source and test, gain the two new
  modules.
- A module docstring for each of the three new source modules, with the
  sections `docs/rules/lean-coding.md` § Documentation makes mandatory.
  `OfEdges.lean`'s records why its upstream target is Batteries;
  `Quotient.lean`'s and `Coequalizer.lean`'s carry the citation key
  § Transcription or novel leaves to the plan, under `## References`.
- A `/-- … -/` docstring on every `def`, `instance` and theorem of the
  three modules, per `docs/rules/lean-coding.md` § Comment and
  docstring rules, which makes them mandatory rather than reserving
  them for major declarations. That is every declaration listed in this
  spec, the wrapper's unnamed `HasCoequalizers` instance included.
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
  content: `Geb/Mathlib/Data/UnionFind/OfEdges.lean` and its
  `GebTests` parallel are added to the item's "currently" list, which
  names source modules and their test parallels both. The criterion
  itself is not touched, per § The union-find layer.
- `TODO.md` § Status: W4's row becomes complete, with
  its module list.
- The spec and plan are removed in the branch's final commits, per
  `CONTRIBUTING.md` § Concern shape.

W4 edits `TODO.md` in three places, and appends to
`GebMeta.classicalAllowedModules`, to `docs/index.md`, and to the
`FinSetSkel` index files. W3 appends to all four, and branch
`feat/choice-free-primitives` (`jj` change `ypqrxnwk`) amends `TODO.md`
as well. These are the ordinary textual conflicts the group's standing
obligation anticipates for concurrent siblings; W4 rebases onto
whichever of them merges first. The standing obligation lists three
shared files and not the `FinSetSkel` index; W3's spec amends it to
add the fourth, so W4 does not.

W4's dependency on `feat/choice-free-primitives` is its `TODO.md` text
alone. That branch is specified to carry `Equiv.arrowCongrLeftC` and
`Fin.instLawfulBEqC`; § Constraint 9 above records that W4 reaches
neither, so W4 imports nothing from it.

Whether `docs/references.bib` changes depends on which citation key the
plan settles on, per § Transcription or novel: none if
`MacLaneMoerdijk1992` holds, one entry if the locator search lands on
Mac Lane's _Categories for the Working Mathematician_ instead.

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
- `FinSetSkel.homEquivIdxFun`, the equivalence between morphisms and
  bare index functions. Row i does not use it: every construction and
  statement above is over `f.toVec.get i`, W1's application-normal
  form, and `desc` is built by `Vector.ofFnC` with `hom_ext` supplying
  extensionality. It is W3-local, and constraint 7's rule placing
  shared declarations outside both branches does not engage.
- The stale duplicate W1 row in `TODO.md` § Status,
  which is a defect of the W1/W2 rebase and belongs on its own branch
  per `CONTRIBUTING.md` § Concern shape.
