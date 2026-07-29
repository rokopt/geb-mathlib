# W4: binary coequalizers in FinSetSkel by union-find — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
- [File structure](#file-structure)
- [Verification commands](#verification-commands)
- [Task 1: the `Sized` union-find wrapper](#task-1-the-sized-union-find-wrapper)
- [Task 2: the two correctness theorems and the union-find test](#task-2-the-two-correctness-theorems-and-the-union-find-test)
- [Task 3: the quotient core's definitions and unfolding lemmas](#task-3-the-quotient-cores-definitions-and-unfolding-lemmas)
- [Task 4: the universal property and the worked coequalizer](#task-4-the-universal-property-and-the-worked-coequalizer)
- [Task 5: the wrapper](#task-5-the-wrapper)
- [Task 6: documentation, citation and `TODO.md`](#task-6-documentation-citation-and-todomd)
- [Task 7: the conditional constraint-9 correction](#task-7-the-conditional-constraint-9-correction)
- [Task 8: remove the spec and the plan](#task-8-remove-the-spec-and-the-plan)
- [Self-review record](#self-review-record)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

**Goal:** binary coequalizers in `FinSetSkel`, and
`HasCoequalizers FinSetSkel`, constructed by folding
`Batteries.UnionFind.union` over the domain of a parallel pair.

**Architecture:** three source modules in dependency order. A
choice-free union-find layer over `Batteries.UnionFind`, stated at a
fixed size `n` and knowing nothing of category theory; a choice-free
quotient core stating the carrier, the projection, the factorisation
and their laws over `FinSetSkel` morphisms in W1's application-normal
form `f.toVec.get i`; and a wrapper packaging those as mathlib's
`ColimitCocone (parallelPair f g)`, `HasColimit` and
`HasCoequalizers`. Only the wrapper reaches
`GebMeta.classicalAllowedModules`.

**Tech stack:** Lean 4 (`v4.33.0-rc1`), mathlib pinned at the same
`rev`, Batteries via mathlib, `lake`, `jj`.

**The spec is the specification.** `docs/superpowers/specs/2026-07-29-finsetskel-coequalizer.md`
records which proof routes work, which fail and how, and why several
non-obvious choices are forced. Read the section named in each task
before starting that task. Where this plan and the spec disagree, the
spec is authoritative and the disagreement is a defect in this plan.

---

## Global constraints

Every task's requirements implicitly include this section.

- **No `noncomputable` anywhere.** No `native_decide`:
  `GebMeta.detectNonstandardAxiom` forbids `Lean.ofReduceBool`
  everywhere.
- **Choice-free except the wrapper.** Every declaration of Tasks 1
  through 4 depends on `propext` and `Quot.sound` only. Only
  `Geb.Mathlib.CategoryTheory.FinSetSkel.Coequalizer` and
  `GebTests.Mathlib.CategoryTheory.FinSetSkel.Coequalizer` are added
  to `GebMeta.classicalAllowedModules`, and those two only.
- **No `induction` tactic, no self-recursive `def`, no
  `termination_by`.** Every recursion is an explicit recursor
  application (`List.rec`, `Nat.rec`), per
  `docs/rules/lean-coding.md` § Recursion and induction through
  recursors. `cases` is permitted for non-recursive case analysis.
- **Module preamble.** Copyright block
  (`Copyright (c) 2026 Terence Rokop. All rights reserved.`, the
  Apache-2.0 line, `Authors: Terence Rokop`), then `module`, then the
  imports, then the `/-! … -/` module docstring, then
  `@[expose] public section`.
- **Import visibility.** Imports whose contents appear in a module's
  own statements are `public import`; source index files use
  `public import`, `GebTests` *index* files use plain `import`.
  `GebTests` *leaf* modules use `public import`, as W1's
  `GebTests/Mathlib/CategoryTheory/FinSetSkel/Basic.lean` does: a
  leaf opens `@[expose] public section` and declares public `def`s
  and theorems mentioning the imported names, and under a plain
  `import` those names are not in scope for a public declaration.
  Measured: `module`, `import …FinSetSkel.Basic`,
  `@[expose] public section`, `abbrev sDom : FinSetSkel.{0} := ⟨3⟩`
  reports "Unknown identifier `FinSetSkel`. Note: A public
  declaration `FinSetSkel` exists but is imported privately".
- **`autoImplicit = false`.** Every binder is declared.
- **Line length 100 characters** in `.lean` files; 80 in `.md` prose
  (`MD013`, tables and code blocks exempt).
- **`weak.warningAsError = true`.** A linter warning fails the build.
  In particular `linter.style.show` rejects a goal-changing `show`
  (use `change`), and `dupNamespace` rejects a declaration whose own
  name repeats its enclosing namespace.
- **Docstrings are mandatory** for every `def`, `instance` and
  theorem of the three source modules and the three test modules, and
  a `/-! … -/` module docstring with the sections
  `docs/rules/lean-coding.md` § Documentation makes mandatory heads
  each file. No development-history references in any docstring.
- **No self-prefix leakage.** `Geb.Mathlib.` and `GebTests.Mathlib.`
  appear only in `^import` lines, never in a namespace, a declaration
  body, a docstring or a comment.
- **`Nat` in the union-find layer, `ℕ` in the quotient core.** The
  first targets Batteries, the second mathlib.
- **Computed assertions use `#guard`.** Not `by decide`, not
  `by rfl`: nothing built from `UnionFind.union` or `rootD` reduces
  in the kernel, `root`/`findAux`/`find` being well-founded
  recursions measured by the `noncomputable` `rankMax`.
- **Every `#guard` term mentions only locally declared constants.**
  `#guard` elaborates its argument as a temporary `meta` definition,
  and under the Lean 4 module system a `meta` definition may only
  reference constants from modules imported with `meta import`. A
  `#guard` naming an imported constant directly therefore fails.
  Measured: with `public import …FinSetSkel.Basic` and a local
  `def rF`, `#guard rF.toVec.get 0 == rF.toVec.get 0` reports
  "Invalid `meta` definition `_tmp✝`, `FinSetSkel.Hom.toVec` is not
  accessible here", while `def rFAt (i : Fin 3) : Nat := (rF.toVec.get i).val`
  followed by `#guard rFAt 0 == 0` elaborates clean. So each assertion
  goes through a locally declared wrapper, one per quantity asserted.
  The compiler's suggested repair — adding
  `public meta import Geb.Mathlib.…` alongside the ordinary
  `public import` — does make the `#guard`s elaborate but is rejected
  by `scripts/lint-imports.sh`, whose Rule 2 exempts only lines
  matching the regex `^[0-9]+:(public[[:space:]]+)?import` followed by
  a space, so the `Geb.Mathlib.` self-prefix on a
  `public meta import` line is flagged. `public import all …` is
  rejected by Lean outright.
- **`#guard` is `info`, not `warning`.** `linter.hashCommand` fires
  on every `#guard`, but because `weak.warningAsError = true`
  mathlib's `HashCommandLinter` takes its `logInfoAt` branch, so the
  message does not fail the build. A `#guard` whose assertion is
  false is a genuine error and does.
- **VCS is `jj`.** No mutating `git` subcommand; the PreToolUse hook
  at `scripts/hooks/block-mutating-git.sh` blocks them.
- **Commit messages**: `<type>(<scope>): <subject>`, type in
  `feat | fix | doc | style | refactor | test | chore | perf | ci`,
  imperative present tense, no capital, no trailing period, subject
  under 72 characters.
- **Module list per file is a starting point**, not `lake shake`'s
  output. The pre-push `lake shake` settles the minimal set; adjust
  imports to whatever it reports and re-run.

## File structure

Created:

| File | Responsibility |
| --- | --- |
| `Geb/Mathlib/Data/UnionFind/OfEdges.lean` | `Batteries.UnionFind.Sized` and the fold over an edge list, with its two correctness theorems. No category theory, no `FinSetSkel`. |
| `Geb/Mathlib/Data/UnionFind.lean` | directory index. |
| `Geb/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean` | the carrier, projection and factorisation over `FinSetSkel` morphisms, and the universal property. Choice-free. |
| `Geb/Mathlib/CategoryTheory/FinSetSkel/Coequalizer.lean` | the mathlib packaging. The only allowlisted source module. |
| `GebTests/Mathlib/Data/UnionFind/OfEdges.lean` | the partition a small fold induces. |
| `GebTests/Mathlib/Data/UnionFind.lean` | directory index. |
| `GebTests/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean` | a worked coequalizer, computed. |
| `GebTests/Mathlib/CategoryTheory/FinSetSkel/Coequalizer.lean` | instance resolution. |

Modified:

| File | Change |
| --- | --- |
| `Geb/Mathlib/Data.lean` | `public import Geb.Mathlib.Data.UnionFind` |
| `GebTests/Mathlib/Data.lean` | `import GebTests.Mathlib.Data.UnionFind` |
| `Geb/Mathlib/CategoryTheory/FinSetSkel.lean` | two `public import` lines, one per task that creates a module (Task 3 Step 11, Task 5 Step 5) |
| `GebTests/Mathlib/CategoryTheory/FinSetSkel.lean` | two `import` lines (Task 4 Step 7, Task 5 Step 5) |
| `GebMeta.lean` | two names appended to `classicalAllowedModules` |
| `docs/index.md` | one entry per new source module |
| `docs/references.bib` | the `nLabCoequalizer` `@misc` entry |
| `TODO.md` | § Triggers, § Upstream destination, § Status, and the constraint-9 corrections |

## Verification commands

Referenced by name from the steps below.

- `lake build` — compiles `Geb` (the default target).
- `lake build GebTests` — compiles the test library.
- `lake test` — runs the test driver.
- `lake lint` — runs `GebMeta.detectNonstandardAxiom` and the
  environment linters over `Geb`; `lake lint -- GebTests` over
  `GebTests`.
- **Axiom check**: the `lean-lsp` MCP's `lean_verify` at the fully
  qualified name. `#print axioms` through the same MCP is
  equivalent. `lake env lean` is forbidden by
  `docs/rules/lean-coding.md` § Lake / build workflow.
- `markdownlint-cli2 '**/*.md'` — before each commit touching
  Markdown.
- `doctoc --update-only .` — regenerates in-place TOCs; run before
  each commit touching a Markdown file that carries doctoc markers
  and whose headings changed.

In a fresh worktree run `lake exe cache get` before the first
`lake build`.

---

## Task 1: the `Sized` union-find wrapper

Spec sections: § The union-find layer, § Findings re-verified
(corrections 1 and 2), § Constraint 9 (the `Nat` division and order
paragraph).

**Files:**

- Create: `Geb/Mathlib/Data/UnionFind/OfEdges.lean`
- Create: `Geb/Mathlib/Data/UnionFind.lean`
- Modify: `Geb/Mathlib/Data.lean`

**Interfaces:**

- Consumes: `Batteries.UnionFind` and its `union`, `push`, `empty`,
  `unionN`, `rootD`, `Equiv`, `rootD_rootD`, `rootD_lt`,
  `rootD_empty`, `root_push`, `equiv_union`.
- Produces, all in namespace `Batteries.UnionFind`:
  `size_union`, `size_push`, `Sized`, `Sized.discrete`,
  `Sized.union`, `Sized.root`, `Sized.ofEdges`, `Sized.root_eq_iff`,
  `Sized.equiv_union`, `Sized.rootD_discrete`,
  `Sized.root_discrete`, `Sized.root_root`. Task 2 adds the rest.

The declaration list is exactly the spec's. Every declaration but
`size_union` and `size_push` carries the
`Sized.` prefix in its own name, `ofEdges` included: a bare
`Batteries.UnionFind.root_root` would read as a statement about
Batteries' own `UnionFind.root`. The prefix is written into the name
rather than opened as a deeper namespace, so one
`namespace Batteries.UnionFind` block covers the module.

- [ ] **Step 1: create the module with its preamble and docstring**

Create `Geb/Mathlib/Data/UnionFind/OfEdges.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Batteries.Data.UnionFind
public import Mathlib.Data.List.Basic

/-!
# A size-indexed union-find and the fold over a list of edges

`Batteries.UnionFind` carries its size as a field, so an index into it
has type `Fin self.size` and every operation that changes the
structure changes the index type. `Sized n` fixes the size as a
subtype, so the indices are `Fin n` throughout and no cast is needed
to pass one operation's index to the next. `Sized.ofEdges` folds
`Sized.union` over a list of pairs, and the two theorems about it are
the two directions of correctness: every listed pair is merged, and
nothing beyond the listed pairs is.

The second is stated as an eliminator — any `h : Fin n → α` agreeing
on the listed pairs agrees on roots — rather than as a
characterisation of the merged relation as the equivalence closure of
the edges. The eliminator is what a coequalizer's factorisation law
instantiates directly.

The upstream target of this module is Batteries rather than mathlib4,
`Sized` being a wrapper over a Batteries type; where such content
belongs is `TODO.md` § Upstream destination of core- and
Batteries-targeted content.

## Main definitions

* `Batteries.UnionFind.Sized` — a union-find of a fixed size.
* `Batteries.UnionFind.Sized.discrete`,
  `Batteries.UnionFind.Sized.union`,
  `Batteries.UnionFind.Sized.root` — the operations, at `Fin n`.
* `Batteries.UnionFind.Sized.ofEdges` — the fold over a list of
  pairs.

## Main statements

* `Batteries.UnionFind.Sized.root_ofEdges_eq_of_mem` — every listed
  pair is merged.
* `Batteries.UnionFind.Sized.apply_root_ofEdges` — nothing beyond the
  listed pairs is merged, in eliminator form.

## Tags

union-find, disjoint set, quotient, choice-free
-/

@[expose] public section

universe u

namespace Batteries.UnionFind

variable {n : Nat}

end Batteries.UnionFind
```

Two forward references, both deliberate and both left as written.
`universe u` is first used by Task 2's `apply_root_ofEdges` and
`apply_root_foldl`, and the `## Main statements` section names those
two theorems, which Task 2 adds. Tasks 1 and 2 build one module across
two reviewable commits, and a module docstring describes the module,
not the commit that happens to be current.
`docs/rules/lean-coding.md` § Structure and typeclass patterns asks
that *unused* `universe` declarations be removed; this one is used by
the end of Task 2, and Lean emits no diagnostic for it in between
(measured: Task 1 verbatim gives zero diagnostics).

- [ ] **Step 2: add the two size lemmas, unproved, and confirm they
  fail**

Insert inside the namespace block:

```lean
/-- `union` preserves the size. -/
theorem size_union (self : UnionFind) (x y : Fin self.size) :
    (self.union x y).size = self.size := _

/-- `push` adds one to the size. -/
theorem size_push (self : UnionFind) : self.push.size = self.size + 1 := _
```

Run: `lake build`
Expected: FAIL, two "don't know how to synthesize placeholder" /
"unsolved goals" errors, one per underscore.

- [ ] **Step 3: prove them**

```lean
/-- `union` preserves the size. -/
theorem size_union (self : UnionFind) (x y : Fin self.size) :
    (self.union x y).size = self.size := by
  unfold union; simp [UnionFind.size]

/-- `push` adds one to the size. -/
theorem size_push (self : UnionFind) : self.push.size = self.size + 1 := by
  unfold push; simp [UnionFind.size]
```

Run: `lake build`
Expected: PASS.

Correction 1 of the spec's § Findings re-verified: size preservation
is these two lines, not a derivation from `arr_link`, `linkAux_size`
and `find_size`. The `link` counterpart is not needed; `size_union`
never routes through it.

- [ ] **Step 4: add `Sized` and its three operations**

```lean
/-- A union-find whose size is fixed, so that its indices are
`Fin n` and no operation changes their type. -/
def Sized (n : Nat) : Type := {u : UnionFind // u.size = n}

/-- The discrete partition on `n` elements: `n` `push`es onto the
empty structure. -/
def Sized.discrete (n : Nat) : Sized n :=
  Nat.rec (motive := fun m ↦ Sized m) ⟨.empty, rfl⟩
    (fun _ v ↦ ⟨v.1.push, by rw [size_push, v.2]⟩) n

/-- Merge the classes of two indices. -/
def Sized.union (v : Sized n) (x y : Fin n) : Sized n :=
  ⟨v.1.unionN x y v.2.symm, by obtain ⟨u, rfl⟩ := v; exact size_union u x y⟩

/-- The representative of an index's class, as an index. -/
def Sized.root (v : Sized n) (x : Fin n) : Fin n :=
  ⟨v.1.rootD x, by obtain ⟨u, rfl⟩ := v; exact UnionFind.rootD_lt.mpr x.isLt⟩

/-- The union-find obtained by merging every listed pair. -/
def Sized.ofEdges (n : Nat) (l : List (Fin n × Fin n)) : Sized n :=
  l.foldl (fun v p ↦ v.union p.1 p.2) (discrete n)
```

Five points, each measured:

- `Sized.discrete` is an `n`-fold `push` through `Nat.rec`, not an
  `induction` tactic and not a self-recursive `def`.
- **The value is in term mode; only the bound is a tactic block.**
  This shape is load-bearing and is why the module needs no auxiliary
  lemma reading the `Nat` off a root. Writing the whole of `Sized.root`
  in tactic mode — `by obtain ⟨u, rfl⟩ := v; exact ⟨u.rootD x, …⟩` —
  makes `(discrete n).root x` a stuck `Subtype.rec` over a `Nat.rec` at
  a variable `n`, and then `root_discrete` below is unreachable
  (measured: `Fin.ext (rootD_discrete n x)` reports "the argument
  `rootD_discrete n ↑x` has type `(↑(discrete n)).rootD ↑x = ↑x` but is
  expected to have type `↑((discrete n).root x) = ↑x`"). With the value
  written as `v.1.rootD x`, that projection is already in the term and
  `Fin.ext (rootD_discrete n x)` closes it directly.
  Discharging the bound with `▸` instead of a tactic block does not
  elaborate either — "invalid `▸` notation, failed to compute motive
  for the substitution" — so the tactic block is the third and only
  working option for that component. The spec's requirement is met:
  § The union-find layer asks that `Sized.union` and `Sized.root`
  destruct with `obtain ⟨u, rfl⟩`, and both still do, inside the module
  that owns the representation.
- `Sized.union` is built on `unionN`, which takes `x y : Fin n`
  together with `h : n = self.size` and so threads the size invariant
  without casting indices (correction 2). Its bound destructs `v` with
  `obtain ⟨u, rfl⟩`; without that, `rw [size_union]` reports no
  occurrence of the pattern, `unionN`'s `match n, h with` not
  reducing until the size proof is destructed.
- `Sized.root` returns `Fin n`, not Batteries' `Nat`-valued `rootD`,
  discharging the bound once so that every downstream statement is an
  equation between `Fin n` terms — W1's normal form. Its bound is
  `rootD_lt.mpr x.isLt`: `rootD_lt` is an `Iff`, not a function, and
  no arithmetic sits between it and `x.isLt`, which is what
  constraint 9's `Nat` division and order paragraph asks of a `Fin`
  bound.
- Batteries' two `Fin`-valued forms are declined:
  `UnionFind.root (self) (x : Fin self.size) : Fin self.size` ties
  the index type to `self.size` rather than to a fixed `n` and so
  reintroduces the cast `Sized` exists to remove; `UnionFind.rootN`
  carries no lemma at all. Building on `rootD` keeps `rootD_rootD`,
  `rootD_lt` and the `Equiv` API.

Run: `lake build`
Expected: PASS.

- [ ] **Step 5: state the five structural lemmas unproved, confirm
  they fail**

```lean
/-- Two indices have the same root exactly when they are equivalent. -/
theorem Sized.root_eq_iff {v : Sized n} {a b : Fin n} :
    v.root a = v.root b ↔ v.1.Equiv a b := _

/-- `Batteries.UnionFind.equiv_union` restated at `Sized.union`. The
`Nat` arguments match Batteries' `Equiv`; the `Fin n` arguments the
other lemmas pass are coerced. -/
theorem Sized.equiv_union {v : Sized n} {x y : Fin n} {a b : Nat} :
    (v.union x y).1.Equiv a b ↔
      v.1.Equiv a b ∨ v.1.Equiv a x ∧ v.1.Equiv y b
                    ∨ v.1.Equiv a y ∧ v.1.Equiv x b := _

/-- Every index is its own root in the discrete partition. -/
theorem Sized.rootD_discrete (m x : Nat) : (discrete m).1.rootD x = x := _

/-- `Sized.rootD_discrete` at `Fin n`. -/
theorem Sized.root_discrete (x : Fin n) : (discrete n).root x = x := _

/-- A root is its own root. -/
theorem Sized.root_root (v : Sized n) (x : Fin n) :
    v.root (v.root x) = v.root x := _
```

Run: `lake build`
Expected: FAIL, five errors.

- [ ] **Step 6: prove them, one at a time**

`docs/rules/lean-coding.md` § Proof guidelines: one declaration at a
time, first errors first. All five were elaborated verbatim at this
module's own import set, so replace each `_` with the term below —
keeping the docstring written in Step 5:

```lean
theorem Sized.root_eq_iff {v : Sized n} {a b : Fin n} :
    v.root a = v.root b ↔ v.1.Equiv a b := Fin.ext_iff

theorem Sized.equiv_union {v : Sized n} {x y : Fin n} {a b : Nat} :
    (v.union x y).1.Equiv a b ↔
      v.1.Equiv a b ∨ v.1.Equiv a x ∧ v.1.Equiv y b
                    ∨ v.1.Equiv a y ∧ v.1.Equiv x b := by
  obtain ⟨u, rfl⟩ := v
  exact UnionFind.equiv_union

theorem Sized.rootD_discrete (m x : Nat) : (discrete m).1.rootD x = x :=
  Nat.rec (motive := fun k ↦ (discrete k).1.rootD x = x)
    UnionFind.rootD_empty (fun _ ih ↦ (UnionFind.root_push).trans ih) m

theorem Sized.root_discrete (x : Fin n) : (discrete n).root x = x :=
  Fin.ext (rootD_discrete n x)

theorem Sized.root_root (v : Sized n) (x : Fin n) :
    v.root (v.root x) = v.root x := Fin.ext UnionFind.rootD_rootD
```

Four points:

- `root_eq_iff` is `Fin.ext_iff` alone, with no destructuring:
  `Batteries.UnionFind.Equiv` is definitionally the `rootD` equation,
  and `Sized.root`'s value component is already `v.1.rootD x`, so
  `Fin.ext_iff` lands on it directly.
- `equiv_union` is the one that still needs `obtain ⟨u, rfl⟩`, and the
  restatement is not optional: `unionN`'s `match n, h with` does not
  reduce until the size proof is destructed, so Batteries' lemma does
  not apply to `(v.union x y).1` as it stands. All three recursions of
  Task 2 consume this form, never Batteries'.
- `rootD_discrete`'s motive is the proposition
  `fun k ↦ (discrete k).1.rootD x = x`, not `Sized.discrete`'s own
  `fun m ↦ Sized m`, which is `Type`-valued and cannot carry a proof.
  `rootD_empty` is the base and `root_push` the step, as an explicit
  `Nat.rec` application rather than an `induction` tactic.
- `root_discrete` and `root_root` are each one `Fin.ext` application.
  They are this short only because `Sized.root`'s value is in term
  mode; see Step 4's second point.

Inside a `Sized.*` declaration Lean opens the declaration's own
prefix, so a bare `equiv_union` resolves to the restatement, while
outside one it resolves to Batteries'. Write each qualified rather
than relying on that.

Run: `lake build`
Expected: PASS.

- [ ] **Step 7: create the directory index and wire it in**

Create `Geb/Mathlib/Data/UnionFind.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.UnionFind.OfEdges

/-!
# UnionFind — index
-/
```

In `Geb/Mathlib/Data.lean`, add in alphabetical position (after
`Geb.Mathlib.Data.PFunctor`, before `Geb.Mathlib.Data.Vector`):

```lean
public import Geb.Mathlib.Data.UnionFind
```

Run: `lake build`
Expected: PASS.

- [ ] **Step 8: check the axioms**

Through the `lean-lsp` MCP, `lean_verify` each of `size_union`,
`size_push`, `Sized`, `Sized.discrete`, `Sized.union`, `Sized.root`,
`Sized.ofEdges`, `Sized.root_eq_iff`, `Sized.equiv_union`,
`Sized.rootD_discrete`, `Sized.root_discrete`, `Sized.root_root`,
fully qualified as `Batteries.UnionFind.size_union` and so on — twelve
names, matching the Interfaces block.

Expected: each depends on `propext` and `Quot.sound` only.

Also check that this module's direct `Batteries.` import has not
admitted constraint 9's Batteries `get`-form family. Spec
§ Constraint 9 states that importing `Batteries.Data.UnionFind`, whose
index module `public import`s `Basic` and `Lemmas`, makes no
`Batteries.Data.Vector.*` module reachable. W4 is the first workstream
to take a direct `Batteries.` import, and `TODO.md` constraint 9 names
that as a standing choice rather than an impossibility — "a workstream
that adds one admits the same family into the `get` normal form" — so
this is the one place the choice is exercised and must be checked.

In a scratch file at this module's import set, `#check` each of
`@Vector.get_ofFn`, `@Vector.get_range`, `@Vector.get_mk` and
`@Vector.toArray_injective`, all declared only in
`Batteries/Data/Vector/Lemmas.lean`.

Expected: all four report `Unknown constant`. That was the measurement
when this plan was written; `Batteries/Data/UnionFind.lean`
`public import`s only `.Basic` and `.Lemmas`, whose own imports are
`Batteries.Tactic.Lint.Misc`, `Batteries.Tactic.SeqFocus` and
`Batteries.Util.Panic`. Delete the scratch file afterwards. Should a
later import change make the family reachable, `lake lint`'s axiom
check is the net that catches the consequence, but it catches it only
after a tainted lemma has fired, which is why the reachability itself
is checked here.

Run: `lake lint`
Expected: PASS (no `detectNonstandardAxiom` report).

- [ ] **Step 9: commit**

```bash
jj commit -m "feat(unionfind): add a size-indexed union-find wrapper"
```

---

## Task 2: the two correctness theorems and the union-find test

Spec sections: § The union-find layer (the three auxiliary
recursions), § Tests (first bullet).

**Files:**

- Modify: `Geb/Mathlib/Data/UnionFind/OfEdges.lean`
- Create: `GebTests/Mathlib/Data/UnionFind/OfEdges.lean`
- Create: `GebTests/Mathlib/Data/UnionFind.lean`
- Modify: `GebTests/Mathlib/Data.lean`

**Interfaces:**

- Consumes: everything Task 1 produced.
- Produces: `Batteries.UnionFind.Sized.equiv_foldl_of_equiv`,
  `Sized.equiv_foldl_of_mem`, `Sized.apply_root_foldl`,
  `Sized.root_ofEdges_eq_of_mem`, `Sized.apply_root_ofEdges`. The
  last two are what Task 4 consumes; the first three support them.

- [ ] **Step 1: state the two correctness theorems unproved, confirm
  they fail**

Append inside the namespace block of
`Geb/Mathlib/Data/UnionFind/OfEdges.lean`:

```lean
/-- Every listed pair is merged. -/
theorem Sized.root_ofEdges_eq_of_mem {l : List (Fin n × Fin n)}
    {a b : Fin n} (hab : (a, b) ∈ l) :
    (ofEdges n l).root a = (ofEdges n l).root b := _

/-- Nothing beyond the listed pairs is merged: a function agreeing on
every listed pair agrees on roots. -/
theorem Sized.apply_root_ofEdges {α : Type u} {l : List (Fin n × Fin n)}
    {h : Fin n → α} (hl : ∀ p ∈ l, h p.1 = h p.2) (x : Fin n) :
    h ((ofEdges n l).root x) = h x := _
```

`apply_root_ofEdges` is named for its left-hand side; `_sound` is not
among mathlib's discharging-operator suffixes.

Run: `lake build`
Expected: FAIL, two errors.

- [ ] **Step 2: state the three auxiliary recursions unproved**

Insert them above the two theorems of Step 1, each generalised over
the accumulated `Sized n`:

```lean
/-- Equivalence in an accumulator survives the fold. -/
theorem Sized.equiv_foldl_of_equiv (l : List (Fin n × Fin n))
    (a b : Fin n) (v : Sized n) (hv : v.1.Equiv a b) :
    (l.foldl (fun (v : Sized n) (p : Fin n × Fin n) ↦ v.union p.1 p.2) v).1.Equiv
      a b := _

/-- A listed pair is equivalent after the fold, from any accumulator. -/
theorem Sized.equiv_foldl_of_mem (l : List (Fin n × Fin n))
    (a b : Fin n) (hab : (a, b) ∈ l) (v : Sized n) :
    (l.foldl (fun (v : Sized n) (p : Fin n × Fin n) ↦ v.union p.1 p.2) v).1.Equiv
      a b := _

/-- A function agreeing on every listed pair, and on the accumulator's
roots, agrees on the roots after the fold. -/
theorem Sized.apply_root_foldl {α : Type u} {h : Fin n → α}
    (l : List (Fin n × Fin n)) (hl : ∀ p ∈ l, h p.1 = h p.2)
    (v : Sized n) (hv : ∀ x, h (v.root x) = h x) (x : Fin n) :
    h ((l.foldl (fun (v : Sized n) (p : Fin n × Fin n) ↦ v.union p.1 p.2) v).root
      x) = h x := _
```

Run: `lake build`
Expected: FAIL, five errors.

- [ ] **Step 3: prove the three recursions, one at a time**

Each is an explicit `List.rec` application, not an `induction`
tactic:

```lean
  List.rec (motive := fun l ↦ ∀ (v : Sized n), _) _ _ l
```

with the motive generalised over the accumulator `v`, since the fold
changes it at every step.

The annotation on the fold function's binders —
`fun (v : Sized n) (p : Fin n × Fin n) ↦ v.union p.1 p.2` — is not
optional inside a `List.rec` motive or a proof driven by one. With the
binders bare the lambda's elaboration is postponed and the inductive
hypothesis fails to apply. Write it annotated in every statement and
proof of this task.

Task 1's `Sized.ofEdges` leaves them bare, and correctly: there the
binder types are forced by `List.foldl`'s own type at elaboration
time, no motive is in play, and the elaborated terms coincide.

Ingredients:

- `equiv_foldl_of_equiv` — base: `hv`. Step: the left disjunct of
  `Sized.equiv_union` carries `hv` past one `union`, then the
  inductive hypothesis at the new accumulator.
- `equiv_foldl_of_mem` — base: `hab` is a membership in `[]`, closed
  by `List.not_mem_nil`. Step: `List.mem_cons` splits `hab`; in the
  head case the middle disjunct of `Sized.equiv_union` supplies the
  merge, then `equiv_foldl_of_equiv` carries it through the rest; in
  the tail case the inductive hypothesis at the new accumulator.
- `apply_root_foldl` — base: `hv x`. Step: the new accumulator's
  invariant is discharged by casing on `Sized.equiv_union`'s three
  disjuncts against `hv` and `hl`, then the inductive hypothesis.

`apply_root_foldl` is generalised over `h` as well as over the
accumulator, and is not derivable from the first two: those are
statements about `Equiv`, and passing from them to a statement about
an arbitrary `h` is exactly the closure characterisation this module
declines to prove (spec § Out of scope).

Run: `lake build`
Expected: PASS.

- [ ] **Step 4: prove the two correctness theorems**

- `root_ofEdges_eq_of_mem` — `Sized.root_eq_iff` reduces the goal to
  `Equiv`, then `Sized.equiv_foldl_of_mem` at `v := Sized.discrete n`.
- `apply_root_ofEdges` — `Sized.apply_root_foldl` at
  `v := Sized.discrete n`, its invariant `∀ x, h (v.root x) = h x`
  discharged by `Sized.root_discrete`.

Run: `lake build`
Expected: PASS.

- [ ] **Step 5: check the axioms of the five new declarations**

Through `lean_verify`, fully qualified.
Expected: `propext` and `Quot.sound` only.

Run: `lake lint`
Expected: PASS.

- [ ] **Step 6: write the test module**

Create `GebTests/Mathlib/Data/UnionFind/OfEdges.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.UnionFind.OfEdges

/-!
# Tests for the size-indexed union-find

A fold over a small edge list, asserted by `#guard`. What is checked
is the partition the fold induces — roots equal within each class,
unequal across — not the root map itself: which representative a
class gets is union by rank's business, an internal of Batteries'
algorithm.

Nothing built from `UnionFind.union` or `rootD` reduces in the kernel,
`root`, `findAux` and `find` being well-founded recursions whose
measure is the `noncomputable` `rankMax`, so the assertions are
`#guard`, which evaluates through the compiler, rather than
`by decide` or `by rfl`. `#guard` introduces no declaration and hence
no axiom obligation.

Each assertion goes through a locally declared wrapper. `#guard`
elaborates its argument as a temporary `meta` definition, which may
only reference constants from modules imported with `meta import`, so
a `#guard` naming an imported constant directly does not elaborate.

## Tags

union-find, disjoint set, test
-/

@[expose] public section

open Batteries

/-- A three-element edge list over `Fin 5`, merging `0`, `1`, `2` and,
separately, `3` and `4`. -/
def sampleEdges : List (Fin 5 × Fin 5) :=
  [(⟨0, by decide⟩, ⟨1, by decide⟩), (⟨1, by decide⟩, ⟨2, by decide⟩),
   (⟨3, by decide⟩, ⟨4, by decide⟩)]

/-- The union-find the sample edges induce. -/
def sampleUnionFind : UnionFind.Sized 5 :=
  UnionFind.Sized.ofEdges 5 sampleEdges

/-- The root of a sample index, as a `Nat`. The wrapper is what the
`#guard`s below name; see the module docstring. -/
def sampleRoot (i : Fin 5) : Nat := (sampleUnionFind.root i).val

#guard sampleRoot ⟨0, by decide⟩ == sampleRoot ⟨1, by decide⟩
#guard sampleRoot ⟨1, by decide⟩ == sampleRoot ⟨2, by decide⟩
#guard sampleRoot ⟨3, by decide⟩ == sampleRoot ⟨4, by decide⟩
#guard sampleRoot ⟨0, by decide⟩ != sampleRoot ⟨3, by decide⟩

/-- A listed pair is merged: `root_ofEdges_eq_of_mem` at the sample.
A proof, so no reduction is needed. -/
theorem sampleUnionFind_root_zero_eq_one :
    sampleUnionFind.root ⟨0, by decide⟩ = sampleUnionFind.root ⟨1, by decide⟩ :=
  UnionFind.Sized.root_ofEdges_eq_of_mem (by simp [sampleEdges])

/-- The eliminator at the sample: a function constant on each class
agrees on roots. -/
theorem sampleUnionFind_apply_root (h : Fin 5 → Bool)
    (hl : ∀ p ∈ sampleEdges, h p.1 = h p.2) (x : Fin 5) :
    h (sampleUnionFind.root x) = h x :=
  UnionFind.Sized.apply_root_ofEdges hl x
```

The index arguments are written with explicit bounds
(`⟨0, by decide⟩`), not as numerals: a numeral at `Fin u.size` runs
into the same non-reduction.

Run: `lake build GebTests`
Expected: PASS, and no `#guard` failure. A failing `#guard` is a
build error naming the assertion.

- [ ] **Step 7: create the test directory index and wire it in**

Create `GebTests/Mathlib/Data/UnionFind.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import GebTests.Mathlib.Data.UnionFind.OfEdges

/-!
# UnionFind tests — index
-/
```

In `GebTests/Mathlib/Data.lean`, add after
`GebTests.Mathlib.Data.PFunctor`:

```lean
import GebTests.Mathlib.Data.UnionFind
```

Run: `lake build GebTests` then `lake test` then
`lake lint -- GebTests`
Expected: all PASS.

- [ ] **Step 8: commit**

```bash
jj commit -m "feat(unionfind): prove the fold merges exactly the listed edges"
```

---

## Task 3: the quotient core's definitions and unfolding lemmas

Spec sections: § The quotient core, § Sharing, § Definitions,
§ Index types, § Statements (the first five lemmas), § Constraint 9.

**Files:**

- Create: `Geb/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean`
- Modify: `Geb/Mathlib/CategoryTheory/FinSetSkel.lean`

**Interfaces:**

- Consumes: Task 1's `Batteries.UnionFind.Sized`, `Sized.root`,
  `Sized.ofEdges` and `Sized.root_root` — not Task 2's two theorems,
  which are Task 4's; W1's `FinSetSkel`, `FinSetSkel.Hom.ofVec`,
  `FinSetSkel.Hom.toVec` and `FinSetSkel.Hom.toVec_ofVec`;
  `Vector.ofFnC` and `Vector.get_ofFnC`; `Fin.compressEquiv`,
  `Equiv.apply_symm_apply` and `Equiv.symm_apply_apply`;
  `instDecidableEqFin`, named explicitly by `isRoot`, and
  `decide_eq_true_eq`, used by `isRoot_root`.
  `FinSetSkel.hom_ext` and `FinSetSkel.comp_get` are Task 4's, not
  this task's.
- Produces, all in namespace `FinSetSkel.Quotient`: `edges`,
  `unionFind`, `isRoot`, `len`, `isRoot_root`, `obj`, `rep`, `π`,
  `desc`, `π_get`, `rep_get`, `desc_get`, `rep_π`, `π_rep`. Task 4
  adds `comp_π`, `π_desc`, `desc_uniq`.

The namespace's extra level is not optional: `FinSetSkel.len` is the
object structure's field, so a `len` declared directly in
`FinSetSkel` collides with it. The namespace shadows `_root_.Quotient`
for `open` only — an `open Quotient` inside `namespace FinSetSkel`
resolves to this one and draws `linter.ambiguousOpen` — so the wrapper
qualifies rather than opening. W4 uses neither `Quot` nor `Quotient`
itself.

- [ ] **Step 1: create the module with its preamble and docstring**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.UnionFind.OfEdges
public import Geb.Mathlib.CategoryTheory.FinSetSkel.Basic
public import Geb.Mathlib.Data.List.NodupEquivFin
public import Geb.Mathlib.Data.Vector.OfFn

/-!
# The coequalizer of a parallel pair in `FinSetSkel`

The coequalizer of `f g : X ⟶ Y` in the category of finite sets is
the quotient of `Y` by the equivalence relation generated by
`f i ∼ g i`. Here that quotient is computed: the pairs
`(f.toVec.get i, g.toVec.get i)` are folded through
`Batteries.UnionFind.Sized.ofEdges`, the resulting roots are
renumbered onto an initial segment by `Fin.compressEquiv`, and the
carrier's length is the number of roots.

Everything is stated over W1's application-normal form
`f.toVec.get i` rather than over bare index functions, so the wrapper
that packages this as a `ColimitCocone` is a transcription rather than
a translation. The module is `Classical.choice`-free; the wrapper is
not, and is separate for that reason.

Nothing expensive sits above a lambda anywhere in this module. A `let`
shares only in a definition whose result is a value: a definition
whose result is a function is compiled at the arity of all its
binders, including those under the `let`, so its `let` body is
re-entered on every application. The union-find is therefore a
parameter that no definition below rebuilds, the per-class
renumbering data is a `Vector` rather than a function, and the three
definitions calling `Vector.ofFnC` each return a value, so their
`let` shares.

## Main definitions

* `FinSetSkel.Quotient.edges`, `FinSetSkel.Quotient.unionFind` — the
  pairs a parallel pair generates, and the fold over them.
* `FinSetSkel.Quotient.obj`, `FinSetSkel.Quotient.rep`,
  `FinSetSkel.Quotient.π`, `FinSetSkel.Quotient.desc` — the carrier,
  its chosen representatives, the projection, and the factorisation.

## Main statements

* `FinSetSkel.Quotient.comp_π` — the projection coequalizes the pair.
* `FinSetSkel.Quotient.π_desc`,
  `FinSetSkel.Quotient.desc_uniq` — the universal property.

## Implementation notes

`Fin (obj Y v).len`, `Fin (len v)` and
`Fin ((List.finRange Y.len).filter (isRoot v)).length` are three
forms of the carrier's index type, differing by iota and by delta.
Every statement uses the first, which the morphism types force, and
each of `π`, `rep` and `desc` therefore carries an unfolding lemma
stated by hand: `rw [Vector.get_ofFnC]` reports no occurrence of the
pattern, the index types differing.

## References

* [nLabCoequalizer] — the coequalizer, and the quotient-set
  construction of it in `Set`.

## Tags

category, finite set, coequalizer, quotient, union-find, choice-free
-/

@[expose] public section

universe u

open CategoryTheory Batteries

namespace FinSetSkel.Quotient

end FinSetSkel.Quotient
```

As in Task 1 Step 1, the `## Main statements` section names three
declarations a later task adds — `comp_π`, `π_desc` and `desc_uniq`
are Task 4's. Tasks 3 and 4 build one module across two reviewable
commits, and the docstring describes the module.

The `CategoryTheory` open is what puts `⟶` and `≫` in scope, as W1's
`Basic.lean` does for the same reason. The `Batteries` open licenses
`UnionFind.Sized` and no shorter form: with the union-find layer
declaring `Sized` inside `namespace Batteries.UnionFind`,
`UnionFind.Sized` resolves under that `open` and a bare `Sized` does
not. Write `UnionFind.Sized`, `UnionFind.Sized.root_root`,
`UnionFind.Sized.root_ofEdges_eq_of_mem` and
`UnionFind.Sized.apply_root_ofEdges` throughout. Likewise W1's
constructors are `Hom.ofVec` and `Hom.toVec_ofVec`, not bare `ofVec`.

Run: `lake build`
Expected: PASS (an empty namespace).

- [ ] **Step 2: add `edges` and `unionFind`**

Inside the namespace:

```lean
section
variable {X Y : FinSetSkel.{u}}

/-- The pairs a parallel pair generates: one per domain index. -/
def edges (f g : X ⟶ Y) : List (Fin Y.len × Fin Y.len) :=
  (List.finRange X.len).map fun i ↦ (f.toVec.get i, g.toVec.get i)

/-- The union-find merging exactly the pairs a parallel pair
generates. This is where the fold runs, once per coequalizer. -/
def unionFind (f g : X ⟶ Y) : UnionFind.Sized Y.len :=
  UnionFind.Sized.ofEdges _ (edges f g)

end
```

`List.finRange` is not covered by constraint 9's ban — the ban is on
`Vector.ofFn`, `Vector.range`, `Vector.finRange` and the
`Array.toList_ofFn` / `List.toArray_ofFn` bridges — and its lemmas
are choice-free; W1's `Fin.compressEquiv` already uses it.

Run: `lake build`
Expected: PASS.

- [ ] **Step 3: add `isRoot`, `len` and `isRoot_root`**

```lean
section
variable {n : ℕ} {Z : FinSetSkel.{u}}

/-- Whether an index is its own root. The decidability instance is
named rather than left to search: two routes inhabit
`DecidableEq (Fin n)`, and which of them is choice-free depends on
the import set, so a bump could otherwise change this term's axioms
silently. -/
def isRoot (v : UnionFind.Sized n) : Fin n → Bool :=
  fun j ↦ @decide (v.root j = j) (instDecidableEqFin _ _ _)

/-- The number of classes: the number of indices that are their own
root. -/
def len (v : UnionFind.Sized n) : ℕ :=
  ((List.finRange n).filter (isRoot v)).length

/-- A root is its own root. -/
theorem isRoot_root (v : UnionFind.Sized n) (j : Fin n) :
    isRoot v (v.root j) := by
  simp only [isRoot, decide_eq_true_eq, UnionFind.Sized.root_root]

end
```

`isRoot` writes its proposition out rather than eliding it: with
`@decide _ …` nothing constrains `decide`'s `p`, and
`instDecidableEqFin`'s three arguments stay unsolved. At W4's imports
both `instDecidableEqFin` and `instDecidableEqOfLawfulBEq` are
axiom-free and search picks the former, but under `import Mathlib`
the latter measures `[propext, Classical.choice, Quot.sound]`, its
`LawfulBEq (Fin n)` resolving to the choice-dependent
`Std.LawfulBEqOrd.lawfulBEq`. Pinning costs one elaboration and
removes the dependence on the import set; W1 pins `decidableEqHom`
for the same reason.

`isRoot` stays a function rather than a vector: `v` is a parameter,
so applying it costs a `root` lookup and rebuilds nothing.

`isRoot_root` sits here rather than with the statements below because
`π` discharges its side condition with it, so it precedes `π` in the
file.

Run: `lake build`
Expected: PASS.

- [ ] **Step 4: add `obj`, `rep`, `π` and `desc`**

Continue inside the same `section` as Step 3, before its `end`:

```lean
/-- The coequalizer's carrier: one index per class. -/
def obj (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len) :
    FinSetSkel.{u} := ⟨len v⟩

/-- A chosen representative of each class, as a vector so that its
consumers index it rather than rebuilding `Fin.compressEquiv` per
class. -/
def rep (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len) :
    Vector (Fin Y.len) (obj Y v).len :=
  let e := Fin.compressEquiv (isRoot v)
  Vector.ofFnC fun c ↦ (e c).1

/-- The projection onto the carrier: an index goes to the compressed
index of its root. -/
def π (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len) : Y ⟶ obj Y v :=
  let e := Fin.compressEquiv (isRoot v)
  Hom.ofVec (Vector.ofFnC fun j ↦ e.symm ⟨v.root j, isRoot_root v j⟩)

/-- The factorisation of a morphism through the carrier. It carries no
compatibility hypothesis, so it computes for any `h`; only `π_desc`
constrains `h`. -/
def desc (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len)
    (h : Y ⟶ Z) : obj Y v ⟶ Z :=
  let r := rep Y v
  Hom.ofVec (Vector.ofFnC fun c ↦ h.toVec.get (r.get c))
```

`Y` is an explicit binder exactly where a `FinSetSkel` object or
morphism occurs in the type — `obj`, `rep`, `π`, `desc` — and absent
where only indices do: `isRoot`, `len` and `isRoot_root` take
`{n : ℕ}`, inferred from `v`. Where `Y` is a binder it is explicit,
because `UnionFind.Sized Y.len` mentions `Y.len`, not `Y`, so the
elaborator cannot recover `Y` from it: `?Y.len =?= n` does not solve.

`isRoot` and `len` mention no `FinSetSkel` and could live in the
union-find module. They stay here because they exist to define the
carrier — `len`'s only consumer is `obj`, and `isRoot`'s consumers
are all in this module.

The constructions use `Vector.ofFnC` and never `Vector.ofFn`,
`Vector.range` or `Vector.finRange`, per constraint 9.

Run: `lake build`
Expected: PASS.

- [ ] **Step 5: state the three unfolding lemmas and the two round
  trips unproved, confirm they fail**

After Step 3's `end` and before `end FinSetSkel.Quotient`, insert a
complete section — opener and closer together, so the file compiles at
every step:

```lean
section
variable {Z : FinSetSkel.{u}}

-- Steps 5 through 9's declarations go here.

end
```

Write the `end` now, not later. An unnamed section left open ahead of
`end FinSetSkel.Quotient` does not elaborate: measured, it reports
"Unexpected name `FinSetSkel.Quotient` after `end`: The current
section is unnamed" together with "unclosed sections or namespaces",
so every `lake build` from here to Step 10 would fail for a reason
unrelated to the declaration under test.

Steps 5 through 9 all insert above that `end`. Inside it:

```lean
/-- The projection at an index. -/
theorem π_get (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len)
    (j : Fin Y.len) :
    (π Y v).toVec.get j
      = (Fin.compressEquiv (isRoot v)).symm ⟨v.root j, isRoot_root v j⟩ := _

/-- The representative of a class. -/
theorem rep_get (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len)
    (c : Fin (obj Y v).len) :
    (rep Y v).get c = (Fin.compressEquiv (isRoot v) c).1 := _

/-- The factorisation at a class. -/
theorem desc_get (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len)
    (h : Y ⟶ Z) (c : Fin (obj Y v).len) :
    (desc Y v h).toVec.get c = h.toVec.get ((rep Y v).get c) := _

/-- The representative of an index's class is its root. -/
theorem rep_π (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len)
    (j : Fin Y.len) :
    (rep Y v).get ((π Y v).toVec.get j) = v.root j := _

/-- The class of a representative is that class. -/
theorem π_rep (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len)
    (c : Fin (obj Y v).len) :
    (π Y v).toVec.get ((rep Y v).get c) = c := _
```

All five hold at an arbitrary `v` and are stated there. No edge enters
them, and stating them at `unionFind f g` would carry `X`, `f` and `g`
through proofs that do not use them and would keep them from firing in
Task 4's worked example, or at any other `v` W5 might supply.

Run: `lake build`
Expected: FAIL, five errors.

- [ ] **Step 6: prove `π_get`, `rep_get` and `desc_get`**

Replace each `_` with the proof below, keeping the docstring Step 5
wrote above it — the blocks here omit the `/-- … -/` lines only to keep
the proof in view, and Global constraints makes a docstring mandatory
on every theorem of these modules.

```lean
theorem π_get (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len)
    (j : Fin Y.len) :
    (π Y v).toVec.get j
      = (Fin.compressEquiv (isRoot v)).symm ⟨v.root j, isRoot_root v j⟩ := by
  change (Hom.ofVec _).toVec.get _ = _
  rw [Hom.toVec_ofVec]
  exact Vector.get_ofFnC _ _

theorem rep_get (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len)
    (c : Fin (obj Y v).len) :
    (rep Y v).get c = (Fin.compressEquiv (isRoot v) c).1 :=
  Vector.get_ofFnC _ _

theorem desc_get (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len)
    (h : Y ⟶ Z) (c : Fin (obj Y v).len) :
    (desc Y v h).toVec.get c = h.toVec.get ((rep Y v).get c) := by
  change (Hom.ofVec _).toVec.get _ = _
  rw [Hom.toVec_ofVec]
  exact Vector.get_ofFnC _ _
```

Each step of the two morphism-valued proofs is forced. A term-mode
`Vector.get_ofFnC _ _` reports an invalid projection out of
`Y.Hom _`, and `rfl` fails. The closing step is `exact`, not a
further `rw`: `rw [Hom.toVec_ofVec, Vector.get_ofFnC]` fails with the
same no-occurrence error. And it is `change`, not `show`:
`linter.style.show` is in `mathlibStandardSet` and rejects a
goal-changing `show`, which `weak.warningAsError = true` makes an
error.

`rep_get` needs none of it — its subject is a vector rather than a
morphism.

Run: `lake build`
Expected: PASS for these three; `rep_π` and `π_rep` still fail.

- [ ] **Step 7: prove `rep_π`**

Again, keep Step 5's docstring above it.

```lean
theorem rep_π (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len)
    (j : Fin Y.len) :
    (rep Y v).get ((π Y v).toVec.get j) = v.root j :=
  (congrArg _ (π_get Y v j)).trans
    ((rep_get Y v _).trans
      (congrArg Subtype.val (Equiv.apply_symm_apply _ _)))
```

Taken as one term. Rewriting with `rep_get` after `π_get` hits the
index-type mismatch at the nested position.

Run: `lake build`
Expected: PASS for `rep_π`.

- [ ] **Step 8: prove `π_rep`**

Not the mirror image of `rep_π`. It is `π_get` then `rep_get`, then
`Equiv.symm_apply_apply` composed with the step from
`(Fin.compressEquiv (isRoot v) c).2` — a `Bool` equation — to the
`Prop` that `(rep Y v).get c` is its own root.

Rewriting with that step under `(Fin.compressEquiv …).symm ⟨_, _⟩`
fails on a dependent motive, the proof argument mentioning the term
being rewritten, and `conv` fails the same way. `simp only` at the
subterm succeeds; use it there and nowhere else in the proof.

Run: `lake build`
Expected: PASS.

- [ ] **Step 9: run the `@[simp]` test, and mark neither**

None of the five carries `@[simp]` as specified. `rep_π` and `π_rep`
are the candidates, and the spec settles the question by measurement:
"whether `simp` can fire them is settled by exhibiting a goal each
closes, not in advance; implementation marks a lemma `@[simp]` only
then, and records which."

**The outcome is that neither is marked.** Both pass the exhibited-goal
test, but passing it is the spec's necessary condition, not a
sufficient one, and no W4 proof needs either mark: `rw` reaches both
lemmas at the nested positions their consumers put them in. Measured —
with `rep_π` unmarked, `by rw [rep_π]` closes probe 1 below with zero
diagnostics, while `by simp` on the same goal reports "`simp` made no
progress"; and `desc_uniq` reaches `π_rep` by plain
`rw [desc_get, ← hm, comp_get, π_rep]`, which Task 4 Step 4 already
gives as a working term. An attribute no consumer needs is a cost
without a return, which `CONTRIBUTING.md` § Code is cost rejects.

Not marking is also the safer side of the note following `TODO.md`'s
cross-workstream constraints: W3 and W4 each add carrier-level `simp`
lemmas that first meet at W5, and neither workstream marks a lemma in
a direction that rewrites the other's normal form. W5 may mark either
lemma if it turns out to need it, with W3's carrier-level lemmas then
visible for comparison — which they are not from here.

**One discrepancy to record for the user's review.** Spec § Statements
motivates the deferral with the clause "the index types above obstruct
`rw` at nested positions". That is true where § Index types establishes
it — of `rw [Vector.get_ofFnC]` against the three unfolding lemmas, and
of rewriting with `rep_get` after `π_get` inside `rep_π`'s own proof —
but it does not hold of rewriting *with* `rep_π` or `π_rep` at their
call sites, which is the position this step is about. The spec's
operative instruction is unaffected: it says to settle the question by
exhibiting a goal, and that is what this step does.

Run the test anyway rather than taking the outcome on trust.
Immediately above Step 5's section-closing `end`, temporarily:

```lean
example (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len) (h : Y ⟶ Z)
    (j : Fin Y.len) :
    h.toVec.get ((rep Y v).get ((π Y v).toVec.get j))
      = h.toVec.get (v.root j) := by simp

example (Y : FinSetSkel.{u}) (v : UnionFind.Sized Y.len)
    (m : obj Y v ⟶ Z) (c : Fin (obj Y v).len) :
    m.toVec.get ((π Y v).toVec.get ((rep Y v).get c))
      = m.toVec.get c := by simp
```

They go inside that section, not after `end FinSetSkel.Quotient`:
each uses `Z` as an implicit variable and unqualified `rep`, `π` and
`obj`, all of which are out of scope outside it, and
`autoImplicit = false` means `Z` would not be auto-bound.

The measured table, which the implementation reproduces:

| `rep_π` | `π_rep` | probe 1 | probe 2 |
| --- | --- | --- | --- |
| unmarked | unmarked | no progress | no progress |
| `@[simp]` | unmarked | closes | no progress |
| `@[simp]` | `@[simp]` | closes | closes |

Each probe is closed by its own lemma and by nothing else — with both
unmarked neither closes, so no third `simp` lemma reaches either goal.
That answers constraint 9 for these two probes: no choice-tainted
`Vector` lemma is doing the work. It is also what makes the marks
dispensable: nothing else was relying on them.

Delete both `example`s once the table is reproduced, and leave both
lemmas unmarked — the `example`s are scaffolding, not tests, and
`CONTRIBUTING.md` § Document only the persistent keeps them out of the
tree. Record the outcome under the module docstring's
`## Implementation notes`, in one sentence:

```text
Neither round trip carries `@[simp]`: `rw` reaches each at the position
its consumer uses, so the attribute would have no consumer here.
```

Run: `lake build`
Expected: PASS.

- [ ] **Step 10: check the axioms**

Through `lean_verify`, each of `FinSetSkel.Quotient.edges`,
`unionFind`, `isRoot`, `len`, `isRoot_root`, `obj`, `rep`, `π`,
`desc`, `π_get`, `rep_get`, `desc_get`, `rep_π`, `π_rep`.
Expected: `propext` and `Quot.sound` only.

Additionally, elaborate `isRoot` with `set_option pp.all true` and
read the decidability instance off the term.
Expected: `instDecidableEqFin`, as written — not
`instDecidableEqOfLawfulBEq`.

Run: `lake lint`
Expected: PASS.

- [ ] **Step 11: wire the module into the source index**

In `Geb/Mathlib/CategoryTheory/FinSetSkel.lean`, add after `.Basic` and
before `.Skeleton`:

```lean
public import Geb.Mathlib.CategoryTheory.FinSetSkel.Quotient
```

This happens here rather than in Task 4, so the commit does not ship a
`Geb/Mathlib/` module unreachable from `Geb.lean` —
`CONTRIBUTING.md` § Repo structure asks for one indexing file per
directory. The `GebTests` index line waits for Task 4 Step 7, where the
test module arrives.

Run: `lake build`
Expected: PASS.

- [ ] **Step 12: commit**

```bash
jj commit -m "feat(finsetskel): construct the coequalizer carrier and projection"
```

---

## Task 4: the universal property and the worked coequalizer

Spec sections: § Statements (the universal property), § Tests (second
bullet).

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean`
- Create: `GebTests/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/FinSetSkel.lean`

**Interfaces:**

- Consumes: everything Task 3 produced, plus
  `UnionFind.Sized.root_ofEdges_eq_of_mem` and
  `UnionFind.Sized.apply_root_ofEdges` from Task 2, and W1's
  `comp_get` and `hom_ext`.
- Produces: `FinSetSkel.Quotient.comp_π`,
  `FinSetSkel.Quotient.π_desc`, `FinSetSkel.Quotient.desc_uniq` —
  the three Task 5 feeds to `Cofork.ofπ` and
  `Cofork.IsColimit.mk`.

- [ ] **Step 1: state the three unproved, confirm they fail**

After Task 3 Step 5's `end` and before `end FinSetSkel.Quotient`,
insert the file's last section, opener and closer together:

```lean
section
variable {X Y Z : FinSetSkel.{u}}

-- Steps 1 through 4's declarations go here.

end
```

Steps 1 through 4 all insert above that `end`. Inside it:

```lean
/-- The projection coequalizes the pair. -/
theorem comp_π (f g : X ⟶ Y) :
    f ≫ π Y (unionFind f g) = g ≫ π Y (unionFind f g) := _

/-- A morphism coequalizing the pair factors through the projection. -/
theorem π_desc (f g : X ⟶ Y) (h : Y ⟶ Z) (w : f ≫ h = g ≫ h) :
    π Y (unionFind f g) ≫ desc Y (unionFind f g) h = h := _

/-- The factorisation is unique. -/
theorem desc_uniq (f g : X ⟶ Y) (h : Y ⟶ Z)
    (m : obj Y (unionFind f g) ⟶ Z)
    (hm : π Y (unionFind f g) ≫ m = h) : m = desc Y (unionFind f g) h := _
```

These take `X`, `Y` and `Z` all as variables, `Y` included, since here
`v` is `unionFind f g` and `Y` comes from the pair.

Run: `lake build`
Expected: FAIL, three errors.

- [ ] **Step 2: prove `comp_π`**

`hom_ext` reduces to an indexwise equation; `comp_get` puts both sides
in application-normal form; `π_get` unfolds the projection; the two
sides then differ only in the root argument, and
`UnionFind.Sized.root_ofEdges_eq_of_mem` closes it at the membership
witness supplied by `List.mem_map` and `List.mem_finRange`.

`edges` needs no unfolding lemma of its own, unlike `π`, `rep` and
`desc`: it returns a list rather than a morphism or a vector at a
mismatched index type, so `List.mem_map` applies to it directly.

Run: `lake build`
Expected: PASS for `comp_π`.

- [ ] **Step 3: prove `π_desc`**

`hom_ext`, then `comp_get`, `desc_get` and `rep_π` reduce the goal to
`h.toVec.get ((unionFind f g).root j) = h.toVec.get j`, which is
`UnionFind.Sized.apply_root_ofEdges` instantiated at
`h := h.toVec.get`. Its hypothesis `∀ p ∈ edges f g, h p.1 = h p.2`
is `w` read indexwise through W1's `comp_get`, the membership again
unfolded by `List.mem_map` and `List.mem_finRange`.

Run: `lake build`
Expected: PASS for `π_desc`.

- [ ] **Step 4: prove `desc_uniq`**

Keeping Step 1's docstring above it.

```lean
theorem desc_uniq (f g : X ⟶ Y) (h : Y ⟶ Z)
    (m : obj Y (unionFind f g) ⟶ Z)
    (hm : π Y (unionFind f g) ≫ m = h) : m = desc Y (unionFind f g) h :=
  hom_ext fun c ↦ by rw [desc_get, ← hm, comp_get, π_rep]
```

No recursion.

Run: `lake build`
Expected: PASS.

- [ ] **Step 5: check the axioms of the three**

Through `lean_verify`.
Expected: `propext` and `Quot.sound` only.

Run: `lake lint`
Expected: PASS.

- [ ] **Step 6: write the worked-coequalizer test**

Create `GebTests/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Quotient

/-!
# Tests for the coequalizer of a parallel pair in `FinSetSkel`

A worked coequalizer, computed. With `X` of length 3 and `Y` of
length 4, the pair generates the edges `(0,1)`, `(1,2)` and the
reflexive `(3,3)`, so the classes are `{0,1,2}` and `{3}`. What is
asserted is the number of classes and the partition the projection
induces; which representative each class gets is fixed by union by
rank, an internal of Batteries' algorithm, and is not asserted.

The two facts about `desc` also follow from `comp_π` and `π_desc` as
proofs; asserting them by computation is what exercises the
algorithm. Assertions are `#guard` for the reason recorded in the
union-find test module: nothing built from `UnionFind.union` or
`rootD` reduces in the kernel.

The objects are `abbrev`s, not `def`s: a numeral at type `Fin Y.len`
needs `Y.len` to reduce at instance-search transparency, which a `def`
blocks and an `abbrev` does not.

Each assertion goes through a locally declared wrapper, for the reason
recorded in the union-find test module: `#guard` elaborates its
argument as a temporary `meta` definition, which may not reference an
imported constant.

## Tags

category, finite set, coequalizer, test
-/

@[expose] public section

open CategoryTheory

/-- The domain of the sample parallel pair. -/
abbrev coeqDom : FinSetSkel.{0} := ⟨3⟩

/-- The codomain of the sample parallel pair. -/
abbrev coeqCod : FinSetSkel.{0} := ⟨4⟩

/-- The first leg of the sample parallel pair. -/
def coeqF : coeqDom ⟶ coeqCod :=
  FinSetSkel.Hom.ofVec ⟨#[0, 1, 3], rfl⟩

/-- The second leg of the sample parallel pair. -/
def coeqG : coeqDom ⟶ coeqCod :=
  FinSetSkel.Hom.ofVec ⟨#[1, 2, 3], rfl⟩

/-- The union-find the sample pair induces. -/
def coeqV : Batteries.UnionFind.Sized coeqCod.len :=
  FinSetSkel.Quotient.unionFind coeqF coeqG

/-- The number of classes. -/
def coeqClasses : Nat := FinSetSkel.Quotient.len coeqV

#guard coeqClasses == 2

/-- The projection of the sample pair. -/
def coeqPi : coeqCod ⟶ FinSetSkel.Quotient.obj coeqCod coeqV :=
  FinSetSkel.Quotient.π coeqCod coeqV

/-- The class of a sample index, as a `Nat`. -/
def coeqPiAt (j : Fin coeqCod.len) : Nat := (coeqPi.toVec.get j).val

#guard coeqPiAt 0 == coeqPiAt 1
#guard coeqPiAt 1 == coeqPiAt 2
#guard coeqPiAt 0 != coeqPiAt 3

/-- A morphism coequalizing the sample pair. -/
def coeqH : coeqCod ⟶ (⟨2⟩ : FinSetSkel.{0}) :=
  FinSetSkel.Hom.ofVec ⟨#[0, 0, 0, 1], rfl⟩

/-- Whether the sample morphism coequalizes the pair. -/
def coeqCoequalizes : Bool := (coeqF ≫ coeqH) == (coeqG ≫ coeqH)

/-- Whether the factorisation through the projection recovers it. -/
def coeqFactors : Bool :=
  (coeqPi ≫ FinSetSkel.Quotient.desc coeqCod coeqV coeqH) == coeqH

#guard coeqCoequalizes
#guard coeqFactors
```

`coeqCoequalizes` and `coeqFactors` go through W1's morphism
`DecidableEq` in its `Bool` form: `==` resolves on morphisms through
`instBEqOfDecidableEq` at the pinned `FinSetSkel.decidableEqHom`.
They are wrappers for the same reason as `coeqPiAt` — keeping
`decidableEqHom`, an imported constant, out of the guarded term.

The test module declares no namespace and reaches the declarations
under test fully qualified, as W1's parallel does with
`FinSetSkel.Hom.ofVec`. Qualifying is a house convention here, not a
constraint: `open FinSetSkel.Quotient` would be unambiguous in a
module with no enclosing namespace.

Run: `lake build GebTests`
Expected: PASS, and no `#guard` failure.

If a `#guard` fails on the projection assertions, check first that
the classes are as stated by `#eval coeqClasses` and
`#eval (List.finRange 4).map coeqPiAt`; a wrong class count means the
edge list is wrong, a right count with wrong grouping means `π` is.

- [ ] **Step 7: wire the test module into the test index**

In `GebTests/Mathlib/CategoryTheory/FinSetSkel.lean`, add in
alphabetical position — after `.Basic`, before `.Skeleton`:

```lean
import GebTests.Mathlib.CategoryTheory.FinSetSkel.Quotient
```

The source index already has its `.Quotient` line from Task 3 Step 11.

Run: `lake build` then `lake build GebTests` then `lake test` then
`lake lint` then `lake lint -- GebTests`
Expected: all PASS.

- [ ] **Step 8: commit**

```bash
jj commit -m "feat(finsetskel): prove the coequalizer's universal property"
```

---

## Task 5: the wrapper

Spec sections: § The wrapper, § Tests (third bullet), § Findings
re-verified (the last paragraph).

**Files:**

- Create: `Geb/Mathlib/CategoryTheory/FinSetSkel/Coequalizer.lean`
- Create: `GebTests/Mathlib/CategoryTheory/FinSetSkel/Coequalizer.lean`
- Modify: `GebMeta.lean`
- Modify: `Geb/Mathlib/CategoryTheory/FinSetSkel.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/FinSetSkel.lean`

**Interfaces:**

- Consumes: `FinSetSkel.Quotient.unionFind`, `.π`, `.desc`,
  `.comp_π`, `.π_desc`, `.desc_uniq`; mathlib's `ColimitCocone`,
  `parallelPair`, `Cofork.ofπ`, `Cofork.IsColimit.mk`,
  `HasColimit`, `HasCoequalizers`,
  `hasCoequalizers_of_hasColimit_parallelPair`.
- Produces: `FinSetSkel.coequalizerCocone`,
  `FinSetSkel.hasColimit_parallelPair`, and an anonymous
  `HasCoequalizers FinSetSkel.{u}` instance. `coequalizerCocone` is
  the stable public name W5's `coequalizerCocone` field consumes,
  which constraint 5 requires of each row's data term.

`Cofork.ofπ`, `Cofork.IsColimit.mk` and
`hasCoequalizers_of_hasColimit_parallelPair` each depend on
`Classical.choice`; `parallelPair` depends on `propext` alone. The
allowlist amendment is therefore required, and among W4's source
modules is required for this one alone.

- [ ] **Step 1: allowlist the two module names first**

In `GebMeta.lean`, append to `classicalAllowedModules`, after the two
`ElementaryTopos` entries:

```lean
   `Geb.Mathlib.CategoryTheory.FinSetSkel.Coequalizer,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.Coequalizer
```

Those two only. Doing this before the module exists keeps the next
`lake lint` from failing on a module the linter is right to reject.

Run: `lake build`
Expected: PASS.

- [ ] **Step 2: create the wrapper module**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Quotient
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# `FinSetSkel` has binary coequalizers

The coequalizer of a parallel pair of functions between finite sets is
the quotient of the codomain by the equivalence relation the pair
generates; `Geb/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean`
computes that quotient and proves its universal property. This module
packages it as mathlib's `ColimitCocone (parallelPair f g)`, registers
the per-diagram `HasColimit`, and derives `HasCoequalizers`.

The packaging is where `Classical.choice` enters: `Cofork.ofπ`,
`Cofork.IsColimit.mk` and
`hasCoequalizers_of_hasColimit_parallelPair` each depend on it, while
the construction being packaged does not. This module is allowlisted
for that reason and the construction is separate for the same reason.

## Main definitions

* `FinSetSkel.coequalizerCocone` — the coequalizer as a chosen
  colimit cocone.

## References

* [nLabCoequalizer] — the coequalizer, and the quotient-set
  construction of it in `Set`.

## Tags

category, finite set, coequalizer, colimit
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace FinSetSkel

variable {X Y : FinSetSkel.{u}}

/-- The coequalizer of a parallel pair, as a chosen colimit cocone.
The fold runs once, in the `let`. -/
def coequalizerCocone (f g : X ⟶ Y) : ColimitCocone (parallelPair f g) :=
  let v := Quotient.unionFind f g
  { cocone := Cofork.ofπ (Quotient.π Y v) (Quotient.comp_π f g)
    isColimit :=
      Cofork.IsColimit.mk _ (fun s ↦ Quotient.desc Y v s.π)
        (fun s ↦ Quotient.π_desc f g s.π s.condition)
        (fun s m hm ↦ Quotient.desc_uniq f g s.π m hm) }

/-- Every parallel pair has a colimit. -/
instance hasColimit_parallelPair {f g : X ⟶ Y} :
    HasColimit (parallelPair f g) :=
  ⟨⟨coequalizerCocone f g⟩⟩

/-- The category has binary coequalizers. -/
instance : HasCoequalizers FinSetSkel.{u} :=
  hasCoequalizers_of_hasColimit_parallelPair _

end FinSetSkel
```

Three points:

- `hasColimit_parallelPair`'s binders are implicit, matching
  `ElementaryTopos.lean`'s declaration of the same name and the shape
  `hasCoequalizers_of_hasColimit_parallelPair` requires of its
  instance argument, which quantifies `{X Y} {f g}` implicitly.
- No declaration carries a namespace prefix in its own name. Writing
  `def FinSetSkel.hasColimit_parallelPair` inside a `FinSetSkel`
  namespace would name it
  `FinSetSkel.FinSetSkel.hasColimit_parallelPair`, which the
  `dupNamespace` linter rejects and `weak.warningAsError = true`
  makes a build failure.
- `Cofork.IsColimit.mk`'s signature takes the three as written,
  `Cofork.condition` supplying `π_desc`'s `w`:

  ```lean
  (desc : (s : Cofork f g) → t.pt ⟶ s.pt) →
    (∀ s, t.π ≫ desc s = s.π) →
    (∀ s m, t.π ≫ m = s.π → m = desc s)
  ```

Run: `lake build`
Expected: PASS.

- [ ] **Step 3: check the axioms**

Through `lean_verify` on `FinSetSkel.coequalizerCocone` and
`FinSetSkel.hasColimit_parallelPair`.
Expected: `propext`, `Quot.sound` and `Classical.choice` — and
nothing else. Any fourth axiom is a defect.

Run: `lake lint`
Expected: PASS (the module is allowlisted as of Step 1).

- [ ] **Step 4: write the instance-resolution test**

Create `GebTests/Mathlib/CategoryTheory/FinSetSkel/Coequalizer.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Coequalizer

/-!
# Tests for `HasCoequalizers FinSetSkel`

Instance resolution needs no reduction, so this module is unaffected
by the kernel non-reduction of `UnionFind.union` that makes the
sibling test modules use `#guard`.

## Tags

category, finite set, coequalizer, test
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/-- The category has binary coequalizers. -/
example : HasCoequalizers FinSetSkel.{0} := inferInstance

/-- A concrete parallel pair has a colimit. -/
example (f g : (⟨3⟩ : FinSetSkel.{0}) ⟶ (⟨4⟩ : FinSetSkel.{0})) :
    HasColimit (parallelPair f g) := inferInstance
```

This module's only declarations are `example`s, which are private, so
a plain `import` would also elaborate here. It uses `public import`
anyway, matching W1's test parallel and the Global-constraints rule
for test leaves; the pre-push `lake shake` settles it if it disagrees.

Run: `lake build GebTests` then `lake lint -- GebTests`
Expected: PASS. `lake lint -- GebTests` passes because this test
module is allowlisted as of Step 1; a test of a `Classical`-allowed
wrapper is itself `Classical`-dependent.

- [ ] **Step 5: wire both modules into their directory indices**

In `Geb/Mathlib/CategoryTheory/FinSetSkel.lean`, add after `.Basic`
and before `.Quotient`:

```lean
public import Geb.Mathlib.CategoryTheory.FinSetSkel.Coequalizer
```

In `GebTests/Mathlib/CategoryTheory/FinSetSkel.lean`, add
correspondingly:

```lean
import GebTests.Mathlib.CategoryTheory.FinSetSkel.Coequalizer
```

Run: `lake build` then `lake build GebTests` then `lake test` then
`lake lint` then `lake lint -- GebTests`
Expected: all PASS.

- [ ] **Step 6: run the import linters**

Run: `bash scripts/lint-imports.sh`
Expected: PASS. The new modules import `Batteries.*`, `Mathlib.*` and
`Geb.Mathlib.*` only, and no self-prefix appears outside an `^import`
line.

Run: `lake shake --add-public --keep-implied --keep-prefix Geb GebTests`
Expected: no report against the new modules. If it reports a
removable import, remove it and re-run `lake build`; the module lists
in this plan are starting points, not `lake shake`'s output.

- [ ] **Step 7: commit**

```bash
jj commit -m "feat(finsetskel): register HasCoequalizers for FinSetSkel"
```

---

## Task 6: documentation, citation and `TODO.md`

Spec section: § Non-Lean deliverables.

**Files:**

- Modify: `docs/references.bib`
- Modify: `docs/index.md`
- Modify: `TODO.md`

No Lean changes. `CONTRIBUTING.md` § Concern shape puts the
persistent documentation with the implementation commits, which this
is the last of.

- [ ] **Step 1: add the citation**

In `docs/references.bib`, on the pattern of the `nLabSkeletalCategory`
entry already there:

```bibtex
@misc{nLabCoequalizer,
  author        = {{nLab authors}},
  title         = {Coequalizer},
  howpublished  = {\url{https://ncatlab.org/nlab/show/coequalizer}},
  note          = {nLab wiki entry},
}
```

The existing `MacLaneMoerdijk1992` entry is left alone; W4 does not
cite it. An nLab entry cited as itself is verifiable and a textbook
locator is not, absent the book.

Confirm the key matches the `[nLabCoequalizer]` references already
written into the two module docstrings in Tasks 3 and 5.

- [ ] **Step 2: add the `docs/index.md` entries**

Three entries in the § Implemented content list. The list is
topological, not alphabetical, so the anchors are given rather than a
rule: `Geb/Mathlib/Data/UnionFind/OfEdges.lean` goes after
`Geb/Mathlib/Data/Vector/NodupEquivFin.lean` and before
`Geb/Mathlib/CategoryTheory/FinSetSkel/Basic.lean`, its dependencies
being Batteries' alone; the two `FinSetSkel` entries go after
`Geb/Mathlib/CategoryTheory/FinSetSkel/Skeleton.lean` and before
`Geb/Mathlib/CategoryTheory/ElementaryTopos.lean`, in the order
`Quotient.lean` then `Coequalizer.lean`. Follow the shape of the
neighbouring entries: what the module contains, the non-obvious
decision, and the axiom status.

```markdown
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
- `Geb/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean` — the
  coequalizer of a parallel pair in `FinSetSkel`, computed: the pairs
  a parallel pair generates are folded through
  `Batteries.UnionFind.Sized.ofEdges`, the roots are renumbered onto
  an initial segment by `Fin.compressEquiv`, and the carrier's length
  is the number of roots. The carrier, projection and factorisation
  are stated over W1's application-normal form, and each of the three
  definitions calling `Vector.ofFnC` carries an unfolding lemma
  stated by hand, `rw [Vector.get_ofFnC]` reporting no occurrence of
  the pattern where the index types differ. `Classical.choice`-free.
- `Geb/Mathlib/CategoryTheory/FinSetSkel/Coequalizer.lean` — the
  packaging of that construction as `ColimitCocone (parallelPair f g)`,
  the per-diagram `HasColimit`, and `HasCoequalizers FinSetSkel`.
  Allowlisted for `Classical.choice`: `Cofork.ofπ`,
  `Cofork.IsColimit.mk` and
  `hasCoequalizers_of_hasColimit_parallelPair` each depend on it,
  while the construction being packaged does not.
```

§ Directory structure needs no change. It enumerates `Geb/`,
`Geb/Mathlib/`, `Geb/Cslib/`, `Geb/Internal/` and `GebTests/` and no
per-module directories, so the new `Geb/Mathlib/Data/UnionFind/`
directory is already covered by its `Geb/Mathlib/` line.

- [ ] **Step 3: add the `TODO.md` § Triggers entry**

The entry `TODO.md` § Workstreams' W4 bullet specifies. Place it in
the § Triggers list:

```markdown
- **mathlib-to-Batteries dependency edge**: whether mathlib accepts a
  `Mathlib/`-to-`Batteries/` dependency edge is a maintainer
  judgement — no `Mathlib.*` module references `UnionFind` — and
  `Geb/Mathlib/Data/UnionFind/OfEdges.lean` needs one to extract.
  Trigger: the preparation of that module's upstream submission,
  which outlives this workstream group.
```

The umbrella spec that first stated this is not in the tree, having
been removed on its own branch.

- [ ] **Step 4: extend `TODO.md` § Upstream destination**

The item currently reads, at `TODO.md`:

```text
currently `Geb/Mathlib/Data/Vector/OfFn.lean` and its test parallel.
```

Replace that sentence with:

```text
currently `Geb/Mathlib/Data/Vector/OfFn.lean` and
`Geb/Mathlib/Data/UnionFind/OfEdges.lean`, and their test parallels.
The criterion does not literally reach `OfEdges.lean`, whose
declarations extend a Batteries type with new statements rather than
restating or replacing existing ones; it is listed here because this
item's subject — content under `Geb/Mathlib/` whose upstream target is
not mathlib4 — is where such a module belongs. Reconciling the
criterion's wording with that subject is a separate concern, on its
own branch.
```

Do not reword the criterion itself. Rewording it would oblige a
re-sweep of `Geb/Mathlib/`, the item being deliberately scoped by
criterion rather than by module list; `CONTRIBUTING.md` § Concern
shape puts that on its own branch.

- [ ] **Step 5: correct constraint 9's closing paragraph**

Constraint 9's closing paragraph currently reads "Deciding a
proposition quantified over `Fin n` is another, and W3 and W4 both
need it". W4 does not — nothing in W4 decides a quantified
proposition; `isRoot` decides an equation and `List.filter` applies a
`Bool`-valued function pointwise — so narrow the clause to W3.

This edit is unconditional: the paragraph is already in this branch's
`TODO.md`, not on a sibling. W4 speaks only for itself; whether W3
needs it is W3's to record.

- [ ] **Step 6: mark W4 complete in § Status**

Set W4's row to Complete and fill its Code column with the three
source modules:

```markdown
| W4 Row i, union-find | W0, W1 | Complete | `Geb/Mathlib/Data/UnionFind/OfEdges.lean`, `Geb/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean`, `Geb/Mathlib/CategoryTheory/FinSetSkel/Coequalizer.lean` |
```

Leave the stale duplicate W1 row alone. It is a defect of the W1/W2
rebase and belongs on its own branch per `CONTRIBUTING.md` § Concern
shape (spec § Out of scope).

- [ ] **Step 7: lint the Markdown**

Run: `doctoc --update-only .`
Expected: `TODO.md`'s TOC regenerates if § Triggers' headings
changed; nothing else moves.

Run: `markdownlint-cli2 '**/*.md'`
Expected: PASS.

- [ ] **Step 8: full pre-push check**

Run: `bash scripts/pre-push.sh`
Expected: PASS at every step. This is the gate
`superpowers:verification-before-completion` requires before any
completion claim.

- [ ] **Step 9: commit**

```bash
jj commit -m "doc(finsetskel): document the coequalizer and cite its source"
```

---

## Task 7: the conditional constraint-9 correction

Spec section: § Non-Lean deliverables (the conditional bullet),
§ Constraint 9 (the last three paragraphs).

**Files:**

- Modify: `TODO.md`

This task is conditional and is performed on the rebase onto
`feat/choice-free-primitives` (`jj` change `ypqrxnwk`), not before.
That branch amends constraint 9 with three choice-taint families and
a measurement rule. W4 imports nothing from it; the dependency is its
`TODO.md` text alone.

- [ ] **Step 0: if the sibling has not merged, skip this task**

Check whether `feat/choice-free-primitives` has merged to `main`. If it
has not, and W4 is otherwise complete, skip Task 7 in full and go to
Task 8. Do not wait for it: the clause this task would correct is not
in this branch's `TODO.md`, so there is nothing to correct, and W4's
three constraint-9 answers stand as measurements about W4's own
construction either way — spec § Constraint 9: "if it does not merge,
the three answers stand as measurements in their own right … and this
section loses only its addressee". The correction then falls to
whichever branch rebases after the clause lands.

If it has merged, continue.

- [ ] **Step 1: rebase once `feat/choice-free-primitives` merges**

```bash
jj rebase -b feat/finsetskel-coequalizer -d main
```

Resolve the ordinary textual conflicts the group's standing
obligation anticipates. W4 appends to `GebMeta.classicalAllowedModules`,
`docs/index.md`, the `FinSetSkel` index files, and
`Geb/Mathlib/Data.lean` and `GebTests/Mathlib/Data.lean`; W3 appends
to several of the same, and `feat/choice-free-primitives` amends
`TODO.md`. W4 rebases onto whichever merges first.

- [ ] **Step 2: read the merged constraint 9 and decide**

Read constraint 9's `Equiv`-transport paragraph as merged.

- If it still closes with "W4's renumbering of union-find roots onto
  an initial segment is a domain transport", delete that clause. W4's
  `rep` and `π` apply `Fin.compressEquiv (isRoot v)` and its `symm`
  pointwise, to an index and to a subtype element; no `Equiv` of W4's
  is an equivalence between arrow types, so the paragraph's repair
  (`Equiv.arrowCongrLeftC`) is not needed here and W4 does not import
  `Geb/Mathlib/Logic/Equiv/Basic.lean`.
- If it merged already corrected — the discrepancy has been reported
  to its author — make no edit and mark this task complete.

The clause names W4, so correcting it is W4's. Constraint 9 binds W5,
which would otherwise read the clause as current.

- [ ] **Step 3: re-measure, do not carry over**

`lean-toolchain` and the mathlib pin in `lakefile.toml` are both
`v4.33.0-rc1`, which is what constraint 9's paragraphs measured at, so
the two revisions presently coincide. If the rebase brings a bump,
re-run the axiom checks of Tasks 1 through 5 rather than carrying the
earlier measurements over.

The amendment's measurement rule does not engage: it concerns a
polymorphic constant whose instance argument may be instantiated at a
choice-dependent instance, and W4's two declarations over a type
variable — `apply_root_ofEdges` and `apply_root_foldl` — both take
`α` bare, with no instance argument.

- [ ] **Step 4: verify and commit**

Run: `markdownlint-cli2 '**/*.md'` then `bash scripts/pre-push.sh`
Expected: PASS.

```bash
jj commit -m "doc(finsetskel): narrow constraint 9's Equiv-transport clause"
```

If Step 2 found the clause already corrected, skip the commit.

---

## Task 8: remove the spec and the plan

Spec section: § Non-Lean deliverables (last bullet).

**Files:**

- Delete: `docs/superpowers/specs/2026-07-29-finsetskel-coequalizer.md`
- Delete: `docs/superpowers/plans/2026-07-29-finsetskel-coequalizer.md`

`CONTRIBUTING.md` § Concern shape: specs and plans are transient. They
remain reachable in history and are absent from the working tree, so
no active branch presents superseded decisions as current. This is the
branch's final commit.

- [ ] **Step 1: confirm nothing references either file**

Run:

```bash
grep -rn "2026-07-29-finsetskel-coequalizer" \
  --include='*.md' --include='*.lean' .
```

Expected: matches in the plan only — six lines of it, namely the
spec's path in the preamble, the two `Delete:` bullets in this task's
Files block, the `grep` command itself, and the two `rm` commands
below. The spec names neither path. A match in any third file is a
docstring or a `docs/` entry citing a transient artifact, which
`CONTRIBUTING.md` § Document only the persistent forbids; fix it
before deleting.

- [ ] **Step 2: delete both**

```bash
rm docs/superpowers/specs/2026-07-29-finsetskel-coequalizer.md
rm docs/superpowers/plans/2026-07-29-finsetskel-coequalizer.md
```

- [ ] **Step 3: verify**

Run: `bash scripts/pre-push.sh`
Expected: PASS.

- [ ] **Step 4: commit**

```bash
jj commit -m "chore(finsetskel): remove the W4 spec and plan"
```

The branch is then ready for the user's line-by-line review. No
`jj git push` happens without it (`AGENTS.md` § No `jj git push`
without user line-by-line review).

---

## Self-review record

**Spec coverage.** Each spec section maps to a task: § The union-find
layer → Tasks 1 and 2; § The quotient core, § Sharing, § Definitions,
§ Index types, § Statements → Tasks 3 and 4; § The wrapper → Task 5;
§ Tests → Tasks 2, 4 and 5, one bullet each; § Non-Lean deliverables →
Tasks 6, 7 and 8; § Constraint 9 → Task 3 Step 3 and Step 10 (the
instance pinning and its measurement), Task 1 Step 4 (the `Fin`
bound), Task 7 (the `Equiv`-transport clause); § Findings re-verified
corrections 1 and 2 → Task 1, correction 3 → Task 3 Step 4,
correction 4 → Task 6 Step 5; § Transcription or novel → the
`[nLabCoequalizer]` docstring references in Tasks 3 and 5 and the
`.bib` entry in Task 6; § Out of scope → nothing, deliberately: no
complexity claim appears in any docstring above, no closure
characterisation is stated, `homEquivIdxFun` is never mentioned, and
the stale W1 status row is explicitly left alone in Task 6 Step 6.
The one docstring above that touches cost — `rep`'s, on why the
representatives are a vector — states the sharing property without a
timing claim, so the § Out of scope ban on complexity claims is
unqualified here.

**Signatures.** Every signature and every definition body in Tasks 1,
3 and 5 was elaborated against this branch's toolchain; the proofs
given verbatim (`size_union`, `size_push`, all five of the union-find
layer's structural lemmas, `isRoot_root`, `π_get`, `rep_get`,
`desc_get`, `rep_π`, `desc_uniq`, `coequalizerCocone`, both instances)
compiled. The proofs left as routes rather than terms are the
union-find layer's three recursions, its two correctness theorems, and
`π_rep`, `comp_π` and `π_desc`.

**Measured after review round 1.** `#guard` elaborates its argument
as a temporary `meta` definition, so every assertion in the two
computational test modules goes through a locally declared wrapper;
test *leaf* modules take `public import`, only test *index* files
take plain `import`. Both were reproduced directly before the plan was
changed.

**Measured after review round 2.** An unnamed section left open ahead
of `end FinSetSkel.Quotient` does not elaborate, so Task 3 Step 5 and
Task 4 Step 1 now write each section's `end` in the same block as its
opener and the later steps insert above it. Both round trips carry
`@[simp]`: reproduced across all three configurations, each probe
closed by its own lemma and neither closed with both unmarked.

**Corrected after review round 3.** Round 2 recorded that a term-mode
`Sized.root` does not elaborate, and concluded that an auxiliary
`Sized.val_root` — a declaration outside the spec's enumerated
interface — was forced. That was wrong: only the `▸`-discharged
variant fails. Writing the *value* in term mode and the *bound* as a
tactic block elaborates, and with it `root_eq_iff` is `Fin.ext_iff`,
`root_discrete` is `Fin.ext (rootD_discrete n x)`, and `root_root` is
`Fin.ext UnionFind.rootD_rootD` — all measured, all
`[propext, Quot.sound]`. `Sized.val_root` is gone and the module's
declaration list is exactly the spec's. The whole of Task 1 as revised,
together with Task 3, elaborates with zero diagnostics.

Round 3 also found that the spec's § Constraint 9 claim about
`Batteries.Data.Vector.*` being unreachable was not carried into the
plan at all. It is now a step: Task 1 Step 8 checks that
`Vector.get_ofFn`, `Vector.get_range`, `Vector.get_mk` and
`Vector.toArray_injective` are all unknown constants at the new
module's import set, W4 being the first workstream to take a direct
`Batteries.` import and so the one place `TODO.md` constraint 9's
standing choice is exercised.

**Reversed after review round 4.** Rounds 2 and 3 recorded that both
round trips would be marked `@[simp]`, on the strength of the probe
table. The table is right, but the conclusion was not: measured,
`by rw [rep_π]` closes probe 1's goal with `rep_π` unmarked, and
`desc_uniq` already reaches `π_rep` by plain `rw`. So `rw` reaches both
lemmas at the positions their consumers use, no W4 proof needs either
mark, and `CONTRIBUTING.md` § Code is cost rejects an attribute with no
consumer. Task 3 Step 9 now marks neither and records the measurement.
The plan's earlier motivation for the marks — that "the index types
obstruct `rw` at nested positions", a clause quoted from spec
§ Statements — is true of the three unfolding lemmas and of `rep_π`'s
own internal proof, but not of rewriting *with* `rep_π` or `π_rep` at a
call site; Step 9 records that discrepancy rather than repeating the
clause. The spec's operative instruction, to settle the question by
exhibiting a goal, is unaffected and is what the step does.

**Type consistency.** `Sized`, `Sized.root`, `Sized.ofEdges`,
`Sized.root_ofEdges_eq_of_mem` and `Sized.apply_root_ofEdges` are
spelled `UnionFind.Sized…` in Tasks 3 and 4, under the `Batteries`
open, and `Sized…` in Tasks 1 and 2, inside
`namespace Batteries.UnionFind`. `obj`, `rep`, `π` and `desc` take
`Y` explicitly and `isRoot`, `len` and `isRoot_root` do not,
consistently across Tasks 3 and 4. `coequalizerCocone` is the name in
Task 5, in the § Non-Lean deliverables coordination note, and in W5's
field.
