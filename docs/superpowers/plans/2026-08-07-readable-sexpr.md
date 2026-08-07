# Readable S-expressions implementation plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global Constraints](#global-constraints)
- [Decisions this plan settles](#decisions-this-plan-settles)
- [File structure](#file-structure)
  - [Task 0: Commit the spec and the plan](#task-0-commit-the-spec-and-the-plan)
  - [Task 1: Relocate the shared child loop](#task-1-relocate-the-shared-child-loop)
  - [Task 2: The module skeleton, the whitespace class and the printer](#task-2-the-module-skeleton-the-whitespace-class-and-the-printer)
  - [Task 3: The decimal-layer extensions and the head lemma](#task-3-the-decimal-layer-extensions-and-the-head-lemma)
  - [Task 4: The parser](#task-4-the-parser)
  - [Task 5: The child-loop retraction lemma](#task-5-the-child-loop-retraction-lemma)
  - [Task 6: The retraction law and its corollaries](#task-6-the-retraction-law-and-its-corollaries)
  - [Task 7: The `Ast` composites](#task-7-the-ast-composites)
  - [Task 8: The test module](#task-8-the-test-module)
  - [Task 9: Persistent documentation](#task-9-persistent-documentation)
  - [Task 10: The pre-push gate](#task-10-the-pre-push-gate)
  - [Task 11: Remove the transient documents](#task-11-remove-the-transient-documents)
- [Self-review](#self-review)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps
> use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add `Geb/Internal/ReadableSExpr.lean`, a second spelling of
`Rose k` as whitespace-separated parenthesized text, with its retraction
law proved and its tests, per
[docs/superpowers/specs/2026-08-03-readable-sexpr-design.md](../specs/2026-08-03-readable-sexpr-design.md).

**Architecture:** A printer by `WType.elim` over `Rose k` spelling a
childless node as a bare numeral and a node with children as
`(label child…)`, and a recursive-descent parser in four layers —
`parse`, `parseAux`, `parseStep`, and the relocated shared
`Rose.parseChildren` — plus a whitespace skip, under a strip-on-return
discipline that lets the child loop be reused verbatim. The retraction
proof carries a delimiting side condition that the canonical spelling
does not need.

**Tech Stack:** Lean 4 (version pinned by `lean-toolchain`), mathlib,
`lake`, `jj` as the working VCS.

## Global Constraints

Every task's requirements implicitly include these.

- **No `noncomputable` anywhere; minimise `Classical`.**
  ([CONTRIBUTING.md](../../../CONTRIBUTING.md) § Constructive-only.)
  `lake lint` runs `GebMeta.detectNonstandardAxiom` over declarations.
- **No `sorry`, and not as a scratch placeholder either.**
  [docs/rules/lean-coding.md](../../rules/lean-coding.md) § sorry,
  admit, and underscores permits it "between commits as a stand-in
  while working with a development tool that requires placeholders
  during proof development (e.g. `lean4:sorry-filler-deep`,
  `lean4:autoprove`)", and directs that "[w]hen no tool specifically
  requires `sorry` and we just need a placeholder for an unfilled term
  or hypothesis, use an underscore (`_`)". Note also that
  `lakefile.toml` sets `weak.warningAsError = true`, so a `sorry`
  makes `lake build` *fail*, not warn — `lake build` cannot be used to
  check that a statement elaborates while its proof is outstanding.
  Use the `lean-lsp` MCP (`lean_diagnostic_messages`, `lean_goal`) for
  that, or one of the two named skills, which manage their own
  placeholders.
- **Recursion goes through recursors** — `Nat.rec`, `List.rec`,
  `WType.elim` — per
  [docs/rules/lean-coding.md](../../rules/lean-coding.md), which bans
  `induction`/`induction'`, self-calling `def`s and `termination_by`.
  Non-recursive pattern matching is unaffected: `parseStep` is a case
  analysis on its input and is written with match syntax, as
  `Geb.Rose.parseStep` already is.
- **`linter.style.show` is in `mathlibStandardSet` and
  `lakefile.toml` sets `weak.warningAsError = true`.** Use `change`,
  never `show`, to change a goal.
- **Module system:** library modules open with `module` then
  `public import`s. A `#guard` whose argument calls a non-`meta`
  declaration from another module **of this package** needs a
  `public meta import` of that module beside the ordinary one, and the
  meta import carries `-- shake: keep`.
- **Line references in this plan are against the branch tip**, before
  Task 1's move. The move shifts everything after the cut in
  `CanonicalSExpr.lean` and after the insertion in
  `ConcreteSyntax.lean`, so where a later task needs something in
  either file it cites the declaration by name; find those with
  `grep`. Apart from Task 1's own cut range, which Step 2 consumes before the
  move, the surviving line citations all sit before those points or in
  files Task 1 does not touch.
- **Test inputs are `List Char` literals or fixtures.** Core's
  `String.toList` depends on `Classical.choice`. `String.ofList` is
  choice-free and may be used to compare against a string literal.
- **Copyright header** on every new *committed* `.lean` file, in
  mathlib's named form, copied from
  `Geb/Internal/CanonicalSExpr.lean`. The temporary scratch modules
  several tasks build and delete need none.
- **Citations** for transcribed definitions live in the module
  docstring's `## References` or in the declaration docstring, by
  `[Key]` into `docs/references.bib`.
- **Module docstrings carry the mandatory sections in order**, ending
  with `## Tags`, and **every declaration of public interest carries a
  `/-- … -/` docstring**
  ([docs/rules/lean-coding.md](../../rules/lean-coding.md)
  § Comment and docstring rules). A docstring is unconditional for
  every `def`, `structure`, `class` and `instance`; "of public
  interest" qualifies theorems only. The statements this plan gives
  are bare so that the type is unambiguous; each acquires a docstring
  when written, as the canonical analogues have — `Rose.parseAux_print`,
  `Rose.parse_print`, `Rose.parseChildren_print`,
  `Rose.exists_print_eq_cons`, `Csexp.readVerbatim_append`. Bare
  statements do occur in the two existing modules — the `@[simp]`
  equation lemmas, `Rose.parseChildren_succ_cons` (which Task 1
  relocates unedited, hence bare), and parts of the decimal layer — so
  the bar is "of public interest", not "all".
- **Lean lines stay within 100 characters**, which
  `linter.style.longLine` enforces as an error under
  `weak.warningAsError = true`.
- **Markdown** passes `markdownlint-cli2 '**/*.md'` and
  `doctoc --update-only`.
- **Commit messages:** `<type>(<optional-scope>): <subject>`,
  imperative present, no capital, no trailing period. Use `jj`, never a
  mutating `git` subcommand.

## Decisions this plan settles

The spec leaves two choices to the plan.

1. **The childless branch builds the node directly.** `parseStep`
   constructs `Rose.node ⟨m, h⟩ Fin.elim0`, and the reconciliation in
   `parseAux_print` is
   `congrArg (Rose.node i) (funext fun j ↦ j.elim0)`. The `ofList i []`
   route is not taken: it would buy uniformity with the list branch at
   the cost of two rewrites (`List.ofFn_zero`, then
   `Geb.Rose.ofList_ofFn`) in place of one term, and the childless
   branch has no list to build from.
2. **The § Alternatives considered dimensions take these values:**
   whitespace is consumed at the entry point and at the four sites
   inside `parseStep`; `Geb.Rose.parseChildren` is relocated and reused;
   the parser's input type is `List Char`; the printer is § Printer's
   spelling. The spec asks the plan to settle and record them, which
   this section does. They do not go into
   `docs/concrete-syntaxes.md`'s profile-decisions block, which is
   about the *format*; the enduring, contract-level content of all
   four — the four strip sites and the strip-on-return discipline,
   that the loop is shared,
   the `List Char` input type in every signature, and the printer's
   spelling in `print`'s own docstring — is committed in the
   docstrings Task 1 Step 3, Task 2 Steps 1 and 4, and Task 4 Step 1
   write, where
   [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost's
   "Document only the persistent" puts a contract.

## File structure

| File | Responsibility |
| --- | --- |
| `Geb/Internal/ConcreteSyntax.lean` | receives `Rose.parseChildren` and its two equation lemmas (modify) |
| `Geb/Internal/CanonicalSExpr.lean` | gives them up (modify) |
| `Geb/Internal/ReadableSExpr.lean` | the whole readable spelling (create) |
| `Geb/Internal.lean` | gains one import (modify) |
| `GebTests/Internal/ReadableSExpr.lean` | the assertions (create) |
| `GebTests/Internal.lean` | gains one import (modify) |
| `docs/concrete-syntaxes.md`, `docs/index.md`, `docs/references.bib`, `docs/references.md`, `TODO.md` | persistent documentation (modify) |
| `GebTests/Internal/ConcreteSyntax.lean`, `GebTests/Internal/CanonicalSExpr.lean` | swept by Task 9 Step 1, edited only if the sweep finds a stale claim |

---

### Task 0: Commit the spec and the plan

[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape orders the
branch: commits adding the spec and plan, then the implementation, then
the commits removing them. The plan is new in the working copy and the
spec is modified there, so without this task Task 1's `jj commit`
would sweep both into a
refactor commit.

**Files:**

- `docs/superpowers/specs/2026-08-03-readable-sexpr-design.md`
- `docs/superpowers/plans/2026-08-07-readable-sexpr.md`

- [ ] **Step 1: Confirm both are present and lint-clean**

Run: `markdownlint-cli2 'docs/superpowers/**/*.md'` and
`doctoc --dryrun --update-only docs/superpowers/plans/2026-08-07-readable-sexpr.md`
Expected: 0 issues, "Everything is OK".

- [ ] **Step 2: Commit**

```bash
jj commit -m "doc(concrete-syntax): plan the readable rose spelling"
```

Anything the spec still needs is committed here too; Task 11 removes
both files at the end of the branch.

---

### Task 1: Relocate the shared child loop

The move is what lets the readable module reuse the loop without
importing the canonical development. The three declarations move with
their code unchanged; the definition's docstring gains one closing
sentence saying the loop is
shared, which is enduring contract text rather than history.

**Files:**

- Modify: `Geb/Internal/CanonicalSExpr.lean:249-278` (remove three
  declarations; 249 is where the definition's docstring starts)
- Modify: `Geb/Internal/ConcreteSyntax.lean` (add them in a re-opened
  `namespace Rose` block, after the existing `Rose` block that ends at
  `ofList_ofFn`)

**Interfaces:**

- Consumes: nothing.
- Produces: `Geb.Rose.parseChildren`,
  `Geb.Rose.parseChildren_succ_close` (`@[simp]`, `rfl`),
  `Geb.Rose.parseChildren_succ_cons` (`if_neg`), all at
  `Geb.Internal.ConcreteSyntax` and reachable without importing
  `Geb.Internal.CanonicalSExpr`.

- [ ] **Step 1: Confirm the pre-move build is clean**

Run: `lake build Geb.Internal.CanonicalSExpr`
Expected: no errors. This is the baseline the move must preserve.

- [ ] **Step 2: Cut the three declarations**

Delete from `Geb/Internal/CanonicalSExpr.lean` the `parseChildren`
definition together with its docstring, and the two equation lemmas
`parseChildren_succ_close` and `parseChildren_succ_cons`. Leave the
`/-! ## Parser -/` section comment and `exists_print_eq_cons` in place.

- [ ] **Step 3: Paste them into `ConcreteSyntax.lean`**

Append a new block after the `Rose` namespace block that ends with
`ofList_ofFn`. The code is exactly the text cut in Step 2; the docstring gains one
closing sentence, the last in it, saying the loop is shared:

```lean
namespace Rose

/-- Read children until the closing parenthesis, delegating each to
`childParse`. The `Nat` argument bounds the loop: it recurses on the
remainder `childParse` returns, which is not a form Lean's structural
recursion accepts. The loop consumes one unit per child and one on the
closing parenthesis, so a node of `n` children needs `n + 1`.
Shared by every spelling that closes a child list with `')'`. -/
def parseChildren {k : Nat}
    (childParse : List Char → Option (Rose k × List Char)) :
    Nat → List Char → Option (List (Rose k) × List Char) :=
  Nat.rec (motive := fun _ ↦ List Char → Option (List (Rose k) × List Char))
    (fun _ ↦ none)
    fun _ ih cs ↦
      match cs with
      | [] => none
      | c :: cs' =>
        if c = ')' then some ([], cs')
        else (childParse (c :: cs')).bind fun p ↦
          (ih p.2).map fun q ↦ (p.1 :: q.1, q.2)

@[simp] theorem parseChildren_succ_close {k : Nat}
    (childParse : List Char → Option (Rose k × List Char)) (f : Nat)
    (rest : List Char) :
    parseChildren childParse (f + 1) (')' :: rest) = some ([], rest) := rfl

theorem parseChildren_succ_cons {k : Nat}
    (childParse : List Char → Option (Rose k × List Char)) (f : Nat)
    (c : Char) (cs : List Char) (h : c ≠ ')') :
    parseChildren childParse (f + 1) (c :: cs)
      = (childParse (c :: cs)).bind fun p ↦
          (parseChildren childParse f p.2).map fun q ↦ (p.1 :: q.1, q.2) :=
  if_neg h

end Rose
```

The only edit against the cut text is the docstring's closing sentence,
which now says the loop is shared.

- [ ] **Step 4: Rebuild both modules**

Run: `lake build Geb.Internal.ConcreteSyntax Geb.Internal.CanonicalSExpr`
Expected: no errors. `CanonicalSExpr` still sees the three declarations
through its existing `public import Geb.Internal.ConcreteSyntax`, so no
consumer is restated.

- [ ] **Step 5: Confirm the loop is reachable without the canonical module**

Scratch checks go in a temporary module *inside* the package and are
built with `lake build`. Never use `lake env lean`: it does not pick up
`lakefile.toml`'s options — including `autoImplicit = false` and
`weak.warningAsError = true` — so it accepts code that `lake build`
rejects (`docs/rules/lean-coding.md` § Lake / build workflow). Files
under `/tmp` cannot be built by lake at all.

Create `GebTests/Internal/ScratchReach.lean`. It goes under
`GebTests` because `lakefile.toml` disables `linter.hashCommand` for
that library alone, and `Geb` keeps the ban on `#`-commands
(`docs/rules/lean-coding.md` § Lean 4 module system):

```lean
module
public import Geb.Internal.ConcreteSyntax
open Geb
#check @Geb.Rose.parseChildren
#check @Geb.Rose.parseChildren_succ_cons
```

Run: `lake build GebTests.Internal.ScratchReach`
Expected: builds. Delete the file afterwards; it is not added to
`GebTests/Internal.lean`.

- [ ] **Step 6: Commit**

```bash
jj commit -m "refactor(internal): relocate the shared rose child loop"
```

---

### Task 2: The module skeleton, the whitespace class and the printer

**Files:**

- Create: `Geb/Internal/ReadableSExpr.lean`
- Modify: `Geb/Internal.lean` (one import)
- Modify: `docs/references.bib` (three entries, Step 8)

**Interfaces:**

- Consumes: `Geb.Rose`, `Geb.Rose.node`, `Geb.Csexp.decOf` from
  `Geb.Internal.ConcreteSyntax`.
- Produces, all in namespace `Geb.Rsexp`:
  - `isWs : Char → Bool`
  - `skipWs : List Char → List Char`
  - `print {k : Nat} : Rose k → List Char`
  - `print_zero` (`@[simp]`) `{k : Nat} (i : Fin k) (f : Fin 0 → Rose k) :
    print (Rose.node i f) = Csexp.decOf i.val`
  - `print_succ {k n : Nat} (i : Fin k) (f : Fin (n + 1) → Rose k) :
    print (Rose.node i f)
      = '(' :: (Csexp.decOf i.val
          ++ (((List.ofFn f).map (fun t ↦ ' ' :: print t)).flatten
              ++ [')']))`
  - `skipWs_nil` (`@[simp]`) and `skipWs_cons`, the skip's two
    equations; `skipWs_cons` is consumed by Tasks 3 and 5, `skipWs_nil`
    by `parse_print`'s `rest = []` instantiation in Task 6

- [ ] **Step 1: Create the file with header, imports and module docstring**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.ConcreteSyntax

/-!
# A readable spelling of the rose syntax

`Geb.Csexp.print` and `Geb.Ast.printViaRose` are both [RFC9804]
canonical: length-prefixed and whitespace-free, so neither has a
readable form. This module spells the same `Rose k` as parenthesized
text, a node's label followed by its children, so that
`fork (leaf 0) (fork (leaf 1) (leaf 2))` reads as `(0 (1 2))`.

The fragment lies inside [R7RS] `<datum>`: a reader conforming to that
grammar accepts it without new code, and tools operating on
parenthesized text apply to it directly. Labels are decimal numerals,
which the [RFC9804] advanced form cannot spell as tokens — § 4.3
requires a token not begin with a digit — where [R7RS] and [EDN] read a
digit-initial token as a number.

## Main definitions

* `Rsexp.print` — the readable spelling of a `Rose k`.
* `Rsexp.parse` — the parser matching it, built from `Rsexp.parseStep`,
  `Rsexp.parseAux` and the shared `Rose.parseChildren`.
* `Rsexp.skipWs` — the whitespace skip the stripping discipline runs.
* `Rsexp.printViaRose`, `Rsexp.parseViaRose` — the composites with the
  rose bijection, spelling an `Ast k`.

## Main statements

* `Rsexp.parse_print`, `Rsexp.parseViaRose_printViaRose` — the
  retraction law, on `Rose` and on `Ast`, with `Rsexp.format_idem` and
  `Rsexp.print_injective` instantiating the generic corollaries.

## Implementation notes

The parser strips whitespace on return rather than on entry:
`parseStep` is called on stripped input and returns a stripped
remainder. That discipline is what lets `Rose.parseChildren` be reused
verbatim — the loop tests its input's head against `')'` immediately,
so it must be called on already-stripped input — and what lets `parse`
match `some (r, [])` syntactically rather than testing a remainder for
whitespace.

A childless node prints as a bare numeral, so a printed tree can end in
a digit and `parseAux_print` carries a delimiting side condition on the
caller's remainder. Always parenthesizing would remove the obligation
and the spelling; `Csexp.readDigits_append` carries the same condition
for the same reason.

## References

* [R7RS] §§ 4.1.3, 7.1.1, 7.1.2 — the datum grammar this fragment lies
  inside.
* [EDN] — the second readable format the spelling agrees with.
* [RFC9804] §§ 4.3, 6, 8 — the token rule that rules out the advanced
  form, and the conformance of declining it.
* [RFC8259] § 2 — the `ws` production this whitespace class matches.

## Tags

concrete syntax, s-expression, parser, retraction, rose tree
-/

@[expose] public section

namespace Geb
namespace Rsexp
```

Close the file with `end Rsexp` and `end Geb`. Match
`Geb/Internal/CanonicalSExpr.lean`'s use of `@[expose] public section`.
`## Tags` is mandatory for a module with substantive content
([docs/rules/lean-coding.md](../../rules/lean-coding.md)
§ Documentation); all four peer modules carry one
(`Geb/Internal/CanonicalSExpr.lean:106`,
`Geb/Internal/ConcreteSyntax.lean:108`).

- [ ] **Step 2: Add the whitespace class and the skip**

```lean
/-! ## Whitespace -/

/-- The whitespace class this syntax admits: space, horizontal tab,
carriage return and line feed. It is a subset of the class [R7RS]
§ 7.1.1 fixes, and admits the same four characters as [RFC8259]
§ 2's `ws`. -/
def isWs (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\r' || c = '\n'

/-- Drop a leading run of whitespace. Carried by `List.rec` rather than
by structural recursion, per the recursor rule. -/
def skipWs : List Char → List Char :=
  List.rec [] fun c cs ih ↦ if isWs c then ih else c :: cs
```

- [ ] **Step 3: Verify the skip's two equations hold by `rfl`**

Add, and check they compile without a tactic block:

```lean
@[simp] theorem skipWs_nil : skipWs [] = [] := rfl

theorem skipWs_cons (c : Char) (cs : List Char) :
    skipWs (c :: cs) = if isWs c then skipWs cs else c :: cs := rfl
```

Run: `lake build Geb.Internal.ReadableSExpr`
Expected: no errors.

- [ ] **Step 4: Add the printer**

```lean
/-! ## Printer -/

/-- The readable spelling: a childless node is its label, a node with
children is its label and their spellings, parenthesized and each
preceded by one space. The uniform space is what makes every element of
the child block a cons, which the arity bound and the whitespace skip
both use. -/
def print {k : Nat} : Rose k → List Char :=
  WType.elim (List Char) fun x ↦
    match x with
    | ⟨(i, 0), _⟩ => Csexp.decOf i.val
    | ⟨(i, _ + 1), ch⟩ =>
      '(' :: (Csexp.decOf i.val
        ++ (((List.ofFn ch).map (fun s ↦ ' ' :: s)).flatten ++ [')']))
```

`WType.elim` takes the motive as an explicit first argument and hands
its algebra a single `Σ a, β a → γ` rather than a shape and a child
function — both readable off `WType.elim_mk`'s statement at
`Geb/Mathlib/Data/W/Basic.lean:70-73`; `WType.elim` itself is
mathlib's — which is why the clause destructures the sigma. `Geb.Rose.toCSexp`
(`Geb/Internal/CanonicalSExpr.lean:215-217`) is the established
`WType.elim` over this same family and passes the motive the same way.
`Geb.Rose.print` at `:227` is not a model here: it is
`CSexp.render r.toCSexp` and contains no recursor.

- [ ] **Step 5: Add the two spelling equations**

The arity-zero one is `rfl`. The other unfolds the recursor, reduces
the arity split, rewrites twice with core's `List.map_ofFn` — one on
the `WType.elim` side, one on the `List (Rose k)` side — and closes by
`rfl`. The split is a `match` on the recursor's sigma argument, not an
`if`, so the bare `simp only []` is what reduces it — `print` contains
no `if` at all:

```lean
@[simp] theorem print_zero {k : Nat} (i : Fin k) (f : Fin 0 → Rose k) :
    print (Rose.node i f) = Csexp.decOf i.val := rfl

theorem print_succ {k n : Nat} (i : Fin k) (f : Fin (n + 1) → Rose k) :
    print (Rose.node i f)
      = '(' :: (Csexp.decOf i.val
          ++ (((List.ofFn f).map (fun t ↦ ' ' :: print t)).flatten
              ++ [')'])) := by
  unfold print Rose.node
  rw [WType.elim_mk]
  simp only []
  rw [List.map_ofFn, List.map_ofFn]
  rfl
```

`change _ = _` alone does not work here: it does not reduce the
`WType.elim` matcher, and the matcher does not reduce definitionally at
a symbolic arity `n + 1` (it does at a literal), so the second
`List.map_ofFn` rewrite finds no target. `WType.elim_mk`
(`Geb/Mathlib/Data/W/Basic.lean:70-73`) is the computation rule that
exposes it. The statement is fixed; develop the script against the
compiler from this starting point, and use `change` rather than `show`
for any goal restatement.

- [ ] **Step 6: Build**

Run: `lake build Geb.Internal.ReadableSExpr`
Expected: no errors, no `sorry`.

- [ ] **Step 7: Check the spelling by evaluation**

Temporary module `GebTests/Internal/ScratchSpell.lean`, built rather
than run through `lake env lean`, per Task 1 Step 5:

```lean
module
public import Geb.Internal.ReadableSExpr
public meta import Geb.Internal.ReadableSExpr  -- shake: keep; #guard needs it
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

open Geb
def scratchTree : Rose 8 :=
  Rose.node 0 ![Rose.node 1 ![], Rose.node 2 ![],
    Rose.node 3 ![Rose.node 4 ![]], Rose.node 5 ![], Rose.node 6 ![],
    Rose.node 7 ![]]
#guard String.ofList (Rsexp.print scratchTree) == "(0 1 2 (3 4) 5 6 7)"
```

Run: `lake build GebTests.Internal.ScratchSpell`
Expected: builds, which is the `#guard` passing — a failing `#guard` is
a build error. That is § Shape's sample. Delete the file afterwards; it
is not added to `GebTests/Internal.lean`.

The `@[expose] public section` is required: without it `linter.privateModule`
reports "The current module only contains private declarations" and,
under `weak.warningAsError = true`, the build fails.

- [ ] **Step 8: Add the three bibliography entries**

The module docstring cites `[R7RS]`, `[EDN]` and `[RFC8259]`, none of
which is in `docs/references.bib` yet — it carries `[RFC9804]` but not
these. Add all three now rather than in Task 9, so the tree never
carries a dangling citation key. The works are the spec's § References
entries: R7RS is Shinn, Cowan and Gleckler (eds.), *Revised⁷ Report on
the Algorithmic Language Scheme*, 2013, errata-corrected edition dated
19 December 2022; EDN is *extensible data notation*; RFC 8259 is Bray
(ed.), *The JavaScript Object Notation (JSON) Data Interchange
Format*, RFC Editor, December 2017. Nothing in `scripts/` reads
`references.bib`, so no gate will catch a malformed entry — match the
form of the existing keys by hand. Task 9
still owns `docs/references.md`, whose entries are tooling pointers
rather than citable literature.

- [ ] **Step 9: Add the import to the directory index**

In `Geb/Internal.lean`, add `public import Geb.Internal.ReadableSExpr`
in alphabetical order among the existing imports.

Run: `lake build`
Expected: no errors.

- [ ] **Step 10: Commit**

```bash
jj commit -m "feat(internal): print the readable rose spelling"
```

---

### Task 3: The decimal-layer extensions and the head lemma

The spec's inventory is five lemmas extending the decimal layer, six
junction facts the count of five excludes, and the head lemma replacing
`Geb.Rose.exists_print_eq_cons`
([the spec](../specs/2026-08-03-readable-sexpr-design.md) § What the
decimal layer supplies). This task produces all of them, plus the two
forms of the skip-over-a-printed-tree fact that the head lemma's two
consumers need, and one that turns `Csexp.decOf_ne_nil`'s `≠ []` into
a cons — needed at three sites — two in this task and one in Task 6 — so
factored once: fifteen declarations. None of the three
digit-versus-character facts can be closed by `omega` after
substituting a literal, since it does not evaluate `Char.toNat`; they
need `decide` or `simp` on the character, in the shapes Step 3 gives.

**Files:**

- Modify: `Geb/Internal/ReadableSExpr.lean`

**Interfaces:**

- Consumes: `Csexp.readDigits_append`, `Csexp.digitsVal_decOf`,
  `Csexp.decOf_ne_nil`, `Csexp.decOf_all_digits`, `Csexp.readNat`,
  `Csexp.charDigit`; and `print`, `print_zero`, `print_succ`, `isWs`,
  `skipWs`, `skipWs_cons` from Task 2.
- Produces the five decimal-layer lemmas:

```lean
theorem readNat_append (n : Nat) (rest : List Char)
    (h : ∀ c cs, rest = c :: cs → Csexp.charDigit c = none) :
    Csexp.readNat (Csexp.decOf n ++ rest) = some (n, rest)

theorem skipWs_decOf_append (n : Nat) (rest : List Char) :
    skipWs (Csexp.decOf n ++ rest) = Csexp.decOf n ++ rest

theorem digit_not_ws {c : Char} (h : (Csexp.charDigit c).isSome) :
    isWs c = false

theorem digit_not_open {c : Char} (h : (Csexp.charDigit c).isSome) :
    c ≠ '('

theorem digit_not_close {c : Char} (h : (Csexp.charDigit c).isSome) :
    c ≠ ')'
```

  `digit_not_ws`'s conclusion is `isWs c = false`, not a disequality:
  whitespace is a four-character class, not one character.

- the six junction facts, together with `decOf_eq_cons`, which is not
  one of the spec's counts but is what `skipWs_decOf_append`,
  `print_head` and Task 6's arity-zero branch each need before
  `decOf_head_digit` applies:

```lean
theorem decOf_eq_cons (n : Nat) : ∃ c cs, Csexp.decOf n = c :: cs

theorem decOf_head_digit (n : Nat) :
    ∀ c cs, Csexp.decOf n = c :: cs → (Csexp.charDigit c).isSome

theorem open_ne_close : ('(' : Char) ≠ ')'

theorem open_not_ws : isWs '(' = false

theorem close_not_ws : isWs ')' = false

theorem space_is_ws : isWs ' ' = true

theorem block_append_head_not_digit {k : Nat} (ts : List (Rose k))
    (rest : List Char) :
    ∀ c cs, (ts.map (fun t ↦ ' ' :: print t)).flatten ++ ')' :: rest
        = c :: cs → Csexp.charDigit c = none
```

  `block_append_head_not_digit` is stated over the block *with* its
  terminator, which is what makes it true when the block is empty.
  `close_not_ws` and `space_is_ws` are reached through the child-loop
  induction at every node's last child, not only at arity zero.

- and the head lemma the spec gives as the readable replacement for
  `Geb.Rose.exists_print_eq_cons`, which neither count includes, with
  the two forms of the skip fact its two consumers need:

```lean
theorem print_head {k : Nat} (r : Rose k) :
    ∃ c cs, print r = c :: cs ∧ (c = '(' ∨ (Csexp.charDigit c).isSome)

theorem skipWs_print_append {k : Nat} (r : Rose k) (rest : List Char) :
    skipWs (print r ++ rest) = print r ++ rest

theorem skipWs_print {k : Nat} (r : Rose k) : skipWs (print r) = print r
```

  The append form is the one `parseChildren_print`'s cons case needs,
  where the child is followed by the rest of the block; `skipWs_print`
  is its `rest = []` instance under `List.append_nil`, and is what
  `parse` needs. Both are consumers of `print_head` — the spec's single
  replacement for `Geb.Rose.exists_print_eq_cons` — together with
  `digit_not_ws` and `open_not_ws`.

- [ ] **Step 1: Write the fifteen statements and check they elaborate**

Write each statement exactly as given above. The grouping above is by
role, not by dependency. Write the four `by decide` facts
(`open_ne_close`, `open_not_ws`, `close_not_ws`, `space_is_ws`) first,
since they depend on nothing and Steps 2–5 do not place them, then
the rest in the order Steps 2–5 prove them —
`skipWs_decOf_append` needs `decOf_eq_cons`, `decOf_head_digit` and
`digit_not_ws`, all of which the role grouping lists after it.

Do **not** use `sorry` to hold the proofs open:
`weak.warningAsError = true` makes `lake build` fail on one, so it
cannot distinguish a well-formed statement from a broken one. Check
elaboration with the `lean-lsp` MCP
(`lean_diagnostic_messages` on the file, `lean_goal` at the proof
position) as each statement is written, and prove them in the steps
below before the first `lake build`.

`open_ne_close`, `open_not_ws`, `close_not_ws` and `space_is_ws` are
`by decide`. The two `decide`s about `(` are `open_ne_close` and
`open_not_ws`.

- [ ] **Step 2: Prove `readNat_append`**

From `Csexp.readDigits_append` (whose hypotheses are that every
character of the first list is a digit, and the delimiting condition on
the remainder), `Csexp.decOf_all_digits`, `Csexp.decOf_ne_nil` — which
discharges `readNat`'s emptiness guard, exactly as
the local `have` block inside `Csexp.readVerbatim_append` consumes it
in `Geb/Internal/ConcreteSyntax.lean` — and `Csexp.digitsVal_decOf`.
Read that `have` block first; it inlines the same fact this lemma
factors out.

- [ ] **Step 3: Prove the three digit-versus-character facts**

`digit_not_open` and `digit_not_close` have the shape
`(Csexp.charDigit c).isSome → c ≠ x`; `digit_not_ws` concludes
`isWs c = false`, whitespace being a four-character class.

None of the three yields to `omega`, which does not evaluate
`Char.toNat`. `digit_not_open` and `digit_not_close` need no case
analysis either: `rintro rfl` then `absurd h (by decide)`. Only
`digit_not_ws` needs the digit range, by casing on
`Csexp.charDigit`'s definition and closing with `decide` or `simp` on
the character.

- [ ] **Step 4: Prove the two `decOf` facts, then `skipWs_decOf_append`**

`decOf_eq_cons` is `Csexp.decOf_ne_nil` (`≠ []`) turned into a cons by
`List.exists_cons_of_ne_nil` or a `cases` on the list.
`decOf_head_digit` is `Csexp.decOf_all_digits` applied to that head,
which is a member of `decOf n` by the cons equation. Both are factored
out because three later proofs need them: this step,
`print_head`'s zero branch in Step 5, and `parseAux_print`'s
arity-zero branch in Task 6 Step 2.

`skipWs_decOf_append` then follows: `decOf_eq_cons` gives a head,
`decOf_head_digit` gives that it is a digit, and `digit_not_ws` makes
`skipWs_cons`'s `if` take the `else` branch.

- [ ] **Step 5: Prove the head lemma, both skip forms and the block lemma**

`print_head` destructures `r` as `⟨⟨i, n⟩, f⟩` and splits on `n`: at
zero the head is `decOf i.val`'s, a digit by `decOf_eq_cons` and
`decOf_head_digit` from Step 4; at
`n + 1` it is `'('` by `print_succ`. `Rose.Shape` has no `Rose.ind`, so
destructure it directly, as the four existing proofs that do so.

`skipWs_print_append` is `print_head` plus `digit_not_ws` and
`open_not_ws` — neither possible head is whitespace, so `skipWs_cons`
takes its `else` branch on `print r ++ rest`, whose head is `print r`'s
because `print r` is non-empty. `skipWs_print` follows by
`List.append_nil`.

`block_append_head_not_digit` is stated over the block with its `')'`
terminator so that the empty-block case is the `')'` case, discharged
by `Csexp.charDigit ')' = none`; the non-empty case's head is the
`' '` of `' ' :: print t`.

- [ ] **Step 6: Build**

Run: `lake build Geb.Internal.ReadableSExpr`
Expected: no errors.

Run: `grep -n sorry Geb/Internal/ReadableSExpr.lean`
Expected: no output.

- [ ] **Step 7: Commit**

```bash
jj commit -m "feat(internal): extend the decimal layer for the readable spelling"
```

---

### Task 4: The parser

**Files:**

- Modify: `Geb/Internal/ReadableSExpr.lean`

**Interfaces:**

- Consumes: `Geb.Rose.parseChildren` (Task 1), `Csexp.readNat`,
  `Geb.Rose.ofList`, `Geb.Rose.node`, `Fin.elim0`, and `skipWs`
  (Task 2). All but `skipWs` come from `Geb.Internal.ConcreteSyntax`
  or core, already dependencies.
- Produces:
  - `parseStep (k : Nat)
    (childParse : List Char → Option (Rose k × List Char))
    (loopFuel : Nat) : List Char → Option (Rose k × List Char)`
  - `parseAux (k : Nat) : Nat → List Char → Option (Rose k × List Char)`
  - `parseAux_succ (k f : Nat) :
    parseAux k (f + 1) = parseStep k (parseAux k f) (f + 1)` (`@[simp]`,
    `rfl`)
  - `parse (k : Nat) (cs : List Char) : Option (Rose k)`
  - one equation lemma per non-empty `parseStep` branch:
    `parseStep_open` (by `rfl`) and `parseStep_other` (by `if_neg`)

- [ ] **Step 1: Define `parseStep` with all four strip sites**

Three of the four strips are retraction-critical; the fourth, after
`(`, is not, and buys only the `( 0 1 )` lax family. Keep all four:
the grammar makes the strip after `(` look like the load-bearing one,
and it is the one that is not.

```lean
/-! ## Parser -/

/-- One layer of the recursive descent. A tree is a bare numeral or a
parenthesized list, so this branches on the first character. It strips
whitespace at four sites: after `(`, after the label in each branch,
and after the child list. The strip after the parenthesized branch's
label is the one the grammar makes least obvious:
`Rose.parseChildren` tests its input's head against `')'` immediately,
so it must be called on stripped input or `(0 1 2)` fails at its first
child. `parseStep` is called on stripped input and returns a stripped
remainder; that invariant is what lets the shared loop be reused. -/
def parseStep (k : Nat) (childParse : List Char → Option (Rose k × List Char))
    (loopFuel : Nat) : List Char → Option (Rose k × List Char)
  | [] => none
  | c :: cs =>
    if c = '(' then
      match Csexp.readNat (skipWs cs) with
      | some (m, cs1) =>
        if h : m < k then
          (Rose.parseChildren childParse loopFuel (skipWs cs1)).map
            fun p ↦ (Rose.ofList ⟨m, h⟩ p.1, skipWs p.2)
        else none
      | none => none
    else
      match Csexp.readNat (c :: cs) with
      | some (m, cs1) =>
        if h : m < k then some (Rose.node ⟨m, h⟩ Fin.elim0, skipWs cs1)
        else none
      | none => none
```

The four strips are, in order: `skipWs cs` after `(`; `skipWs cs1`
after the parenthesized branch's label; `skipWs p.2` after the child
list; `skipWs cs1` after the bare-numeral branch's label. The last two
are the returning strips that carry each later child's leading space.

- [ ] **Step 2: Define `parseAux`, its equation lemma and `parse`**

```lean
/-- Recursive descent over the readable spelling. The `Nat` bounds the
recursion and serves in two roles at each layer: undecremented as the
child loop's bound, and decremented as the child parser's fuel. -/
def parseAux (k : Nat) : Nat → List Char → Option (Rose k × List Char) :=
  Nat.rec (motive := fun _ ↦ List Char → Option (Rose k × List Char))
    (fun _ ↦ none) fun f ih ↦ parseStep k ih (f + 1)

@[simp] theorem parseAux_succ (k f : Nat) :
    parseAux k (f + 1) = parseStep k (parseAux k f) (f + 1) := rfl

/-- The parser of the readable spelling, rejecting trailing input. The
leading strip and the stripping invariant together are what let a
leading indent and a trailing newline parse. -/
def parse (k : Nat) (cs : List Char) : Option (Rose k) :=
  match parseAux k cs.length (skipWs cs) with
  | some (r, []) => some r
  | _ => none
```

- [ ] **Step 3: Add one equation lemma per non-empty branch**

`simp only [parseStep, …]`, the form `parseAux_print` will use, does not
reduce past the `c = '('` test when the scrutinee is
`Csexp.readNat (skipWs cs)`. State both branches:

```lean
theorem parseStep_open (k : Nat)
    (childParse : List Char → Option (Rose k × List Char))
    (loopFuel : Nat) (cs : List Char) :
    parseStep k childParse loopFuel ('(' :: cs)
      = match Csexp.readNat (skipWs cs) with
        | some (m, cs1) =>
          if h : m < k then
            (Rose.parseChildren childParse loopFuel (skipWs cs1)).map
              fun p ↦ (Rose.ofList ⟨m, h⟩ p.1, skipWs p.2)
          else none
        | none => none := rfl

theorem parseStep_other (k : Nat)
    (childParse : List Char → Option (Rose k × List Char))
    (loopFuel : Nat) (c : Char) (cs : List Char) (hc : c ≠ '(') :
    parseStep k childParse loopFuel (c :: cs)
      = match Csexp.readNat (c :: cs) with
        | some (m, cs1) =>
          if h : m < k then some (Rose.node ⟨m, h⟩ Fin.elim0, skipWs cs1)
          else none
        | none => none := if_neg hc
```

- [ ] **Step 4: Build**

Run: `lake build Geb.Internal.ReadableSExpr`
Expected: no errors.

- [ ] **Step 5: Evaluate the round trip and the four strip claims**

Temporary module `GebTests/Internal/ScratchParse.lean`, built with
`lake build GebTests.Internal.ScratchParse`, per Task 1 Step 5.
Task 2 Step 7 deletes its own file, so the module is restated whole
here:

```lean
module
public import Geb.Internal.ReadableSExpr
public meta import Geb.Internal.ReadableSExpr  -- shake: keep; #guard needs it
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

open Geb
def scratchTree : Rose 8 :=
  Rose.node 0 ![Rose.node 1 ![], Rose.node 2 ![],
    Rose.node 3 ![Rose.node 4 ![]], Rose.node 5 ![], Rose.node 6 ![],
    Rose.node 7 ![]]

#guard Rsexp.parse 8 (Rsexp.print scratchTree) == some scratchTree
#guard (Rsexp.parse 8 ['(', '0', ' ', '1', ')']).isSome
#guard Rsexp.parse 8 ['(', ' ', '0', ' ', '1', ' ', ')']
    == Rsexp.parse 8 ['(', '0', ' ', '1', ')']
```

The second assertion anchors the rest: every check below compares two
`parse` calls, and a parser returning `none` unconditionally would
satisfy all of them. Keep `![…]` in the `def` and out of every
`#guard`, per Task 8 Step 1. Inputs are `List Char` literals here as
in the committed test module.
Check that `(0(1))`, `( 0 1 )`, `(0  1)`, `(0 1 )`, a leading indent
and a trailing newline all parse, that `(6)` and `6` give the same
tree, that `007` gives `7`, that `(01)` gives the childless node `1`,
and that `()`, `(())`, empty input, whitespace-only input, `(0 1`, `)`
and a label at or above `k` are all rejected. Delete the file
afterwards.

This step duplicates assertions Task 8 commits. It exists because the
parser should be exercised when it is written rather than four tasks
later; the committed home for them is Task 8.

- [ ] **Step 6: Commit**

```bash
jj commit -m "feat(internal): parse the readable rose spelling"
```

---

### Task 5: The child-loop retraction lemma

**Files:**

- Modify: `Geb/Internal/ReadableSExpr.lean`

**Interfaces:**

- Consumes: `Geb.Rose.parseChildren_succ_close`,
  `Geb.Rose.parseChildren_succ_cons`, `print_head`,
  `block_append_head_not_digit`, `digit_not_close`, `digit_not_ws`,
  `close_not_ws`, `space_is_ws`, `open_ne_close`,
  `skipWs_print_append`, `skipWs_cons`.
- Produces:

```lean
theorem parseChildren_print {k : Nat}
    (childParse : List Char → Option (Rose k × List Char)) :
    ∀ (ts : List (Rose k)) (fuel : Nat) (rest : List Char),
      (∀ t ∈ ts, ∀ r : List Char,
        (∀ c cs, r = c :: cs → Csexp.charDigit c = none) →
        childParse (print t ++ r) = some (t, skipWs r)) →
      ts.length < fuel →
      Rose.parseChildren childParse fuel
          (skipWs ((ts.map (fun t ↦ ' ' :: print t)).flatten ++ ')' :: rest))
        = some (ts, rest)
```

The loop's argument is **skipped**. `parseStep` calls it on `skipWs cs1`
and every `parseStep` return is stripped, so the loop never sees a
leading space — not on entry and not on any recursive call. Stated over
the unstripped block the lemma is false: the head is then `' '`, and
`Rose.parseChildren_succ_cons` hands `childParse` a list beginning with
that space, where the premise speaks only of `childParse (print t ++ r)`.

The loop is `Geb.Rose.parseChildren`; inside `namespace Geb.Rsexp` the
bare name resolves to nothing and `autoImplicit = false`
(`lakefile.toml`) turns that into an error rather than an implicit
binder, so the `Rose.` prefix is required here as it is in Task 4's
`parseStep`.

The spec's two changes against `Geb.Rose.parseChildren_print` are
that the `childParse` premise gains the delimiting hypothesis and
returns `skipWs r`, and that its own input is skipped. A third
difference follows from this printer: the child spelling is
`' ' :: print t`. The conclusion is `rest`, not
`skipWs rest` — the loop returns what follows the closing parenthesis
without stripping it; `parseStep` strips that.

- [ ] **Step 1: Write the statement and check it elaborates**

Use the `lean-lsp` MCP (`lean_diagnostic_messages`) rather than
`lake build`, which fails on an outstanding `sorry` under
`weak.warningAsError = true`. What this checks is that the statement
typechecks against the relocated loop.

- [ ] **Step 2: Prove the nil case**

The block is empty, so the input is `skipWs (')' :: rest)`. `')'` is
not whitespace (`close_not_ws`), so that reduces to `')' :: rest` and
`parseChildren_succ_close` closes it, giving the unstripped `rest`.
This is why the block lemma is stated with its terminator.

- [ ] **Step 3: Prove the cons case**

The input is `skipWs ((' ' :: print t) ++ …)`. `space_is_ws` steps the
skip past the separator, and `skipWs_print_append` stops it at the
child: neither possible head of `print t` is whitespace, so the skip
consumes the space and nothing more. The exposed head is `print t`'s,
which is not `')'` — `open_ne_close` in the parenthesized case,
`digit_not_close` in the numeral case, by `print_head` — so
`parseChildren_succ_cons` applies and the premise is applied to the
child's own spelling. Discharge the child's delimiting hypothesis from
what follows it: `' '` at the next child or `')'` at the last, neither
a digit. `childParse` returns `skipWs` of the remainder, which is
exactly the induction hypothesis's input.

`close_not_ws` and `space_is_ws` are reached here at every node's last
child, not only at arity zero.

- [ ] **Step 4: Build**

Run: `lake build Geb.Internal.ReadableSExpr`
Expected: no errors.

- [ ] **Step 5: Commit**

```bash
jj commit -m "feat(internal): prove the readable child-loop retraction"
```

---

### Task 6: The retraction law and its corollaries

**Files:**

- Modify: `Geb/Internal/ReadableSExpr.lean`

**Interfaces:**

- Consumes: everything from Tasks 2–5, plus `Geb.Retraction`,
  `Geb.format`, `Geb.format_idem`, `Geb.print_injective` from
  `Geb.Internal.ConcreteSyntax`.
- Produces:
  - `parseAux_print`, exactly as the spec states it
  - `parse_print {k : Nat} (r : Rose k) : parse k (print r) = some r`
  - `retraction (k : Nat) : Retraction (parse k) (print (k := k))`
  - `format_idem`, `print_injective`

- [ ] **Step 1: Write the `parseAux_print` statement**

```lean
theorem parseAux_print {k : Nat} (r : Rose k) :
    ∀ (f : Nat) (rest : List Char), (print r).length ≤ f →
      (∀ c cs, rest = c :: cs → Csexp.charDigit c = none) →
      parseAux k f (print r ++ rest) = some (r, skipWs rest)
```

Writing `some (r, rest)` is false and the delimiting hypothesis does
not save it: at `k = 10`, `r = Rose.node 5 ![]` and `rest = [' ']`, the
space is not a digit and `parseAux 10 1 "5 "` returns `some (r, [])`.

- [ ] **Step 2: Prove the arity-zero branch**

`print r` is `decOf i.val`, so `parseStep`'s `c = '('` test must be
shown to fail — that is `digit_not_open` on `decOf`'s head, the fourth
of the five decimal lemmas, with `decOf_head_digit` supplying its
hypothesis. Then `readNat_append` reads the label, and
the returning strip gives `skipWs rest`. Reconcile the node with
`congrArg (Rose.node i) (funext fun j ↦ j.elim0)`, per this plan's
Decision 1. After rewriting with `readNat_append`, a bare
`simp only []` is still needed to reduce the exposed `match`, as
`Csexp.parseAst_printAst` already does in
`Geb/Internal/ConcreteSyntax.lean`.

- [ ] **Step 3: Prove the parenthesized branch**

Rewrite with `print_succ`, then `parseStep_open`. The strip after `(`
is discharged by `skipWs_decOf_append`, which exists for this site
alone; the other two skip facts, `skipWs_print_append` and
`skipWs_print`, are over `print` rather than `decOf`. `readNat_append` reads the
label, its delimiting hypothesis discharged by the block's leading
`' '` at arity `≥ 1`. Then `parseChildren_print` with the fuel bound.

The arity bound is `L = 2 + |decOf i| + Σⱼ(1 + Lⱼ)` with
`|decOf i| ≥ 1` by `Csexp.decOf_ne_nil`, though the bound needs only
`≥ 0`, and needs `List.length_flatten` and the sum bound as
the canonical proof does. Each block element is `' ' :: print t`, a
cons by construction, so `List.length_cons` replaces the canonical
proof's appeal to `Rose.exists_print_eq_cons` in the positivity side
condition. The child's own obligation `Lⱼ ≤ g` comes from
`' ' :: print t` being an element of the block before flattening, so
`1 + Lⱼ` is one summand of `L`.

Use `change`, not `show`, for any goal restatement.

- [ ] **Step 4: Prove `parse_print`**

Instantiate `rest = []`, where the delimiting hypothesis is vacuous and
`skipWs [] = []`. The entry point strips before running `parseAux`, so
`skipWs_print` is what makes the input `parseAux` receives equal
`print r`. The fuel is `(print r).length` by construction.

- [ ] **Step 5: Add the three corollaries by the existing skeleton**

```lean
/-- `Geb.Retraction` at the readable spelling. -/
theorem retraction (k : Nat) : Retraction (parse k) (print (k := k)) :=
  parse_print

/-- `Geb.format_idem` at the readable spelling. -/
theorem format_idem (k : Nat) (c : List Char) :
    (format (parse k) print c).bind (format (parse k) print)
      = format (parse k) print c :=
  Geb.format_idem _ _ (retraction k) c

/-- `Geb.print_injective` at the readable spelling. -/
theorem print_injective (k : Nat) : Function.Injective (print (k := k)) :=
  Geb.print_injective _ _ (retraction k)
```

Copy the exact statement shapes from
`Geb.Rose.retraction`, `Geb.Rose.format_idem` and
`Geb.Rose.print_injective` in `Geb/Internal/CanonicalSExpr.lean`,
which instantiate the same
skeleton.

- [ ] **Step 6: Build and check for `sorry`**

Run `lake build Geb.Internal.ReadableSExpr`, then
`grep -n sorry Geb/Internal/ReadableSExpr.lean` as a separate command
— chained with `&&`, the expected outcome (no match) exits non-zero.
Expected: build clean, `grep` silent.

- [ ] **Step 7: Commit**

```bash
jj commit -m "feat(internal): prove the readable spelling's retraction"
```

---

### Task 7: The `Ast` composites

**Files:**

- Modify: `Geb/Internal/ReadableSExpr.lean`

**Interfaces:**

- Consumes: `Geb.Ast.toRose`, `Geb.Ast.ofRose`, `Geb.Ast.ofRose_toRose`,
  and Task 6's `parse_print`.
- Produces: `Rsexp.printViaRose {k : Nat} : Ast k → List Char`,
  `Rsexp.parseViaRose (k : Nat) : List Char → Option (Ast k)`,
  `Rsexp.parseViaRose_printViaRose`.

The names follow `Geb.Ast.printViaRose`/`parseViaRose`, the canonical
module's composites through the same bijection. `Geb.Csexp.printAst` is
a *direct* printer, so `printAst` here would invert the established
meaning. There is no direct `Ast` printer: dropping `leaf` and `fork`
removes the only thing one would have expressed.

- [ ] **Step 1: Define the two composites**

```lean
/-- The readable spelling of an `Ast k`, through the rose bijection. -/
def printViaRose {k : Nat} (a : Ast k) : List Char := print a.toRose

/-- The parser matching `printViaRose`. -/
def parseViaRose (k : Nat) (cs : List Char) : Option (Ast k) :=
  (parse k cs).map Ast.ofRose
```

Copy the exact shape from `Geb.Ast.printViaRose` and
`Geb.Ast.parseViaRose` in `Geb/Internal/CanonicalSExpr.lean`.

- [ ] **Step 2: Prove the composite retraction**

```lean
theorem parseViaRose_printViaRose {k : Nat} (a : Ast k) :
    parseViaRose k (printViaRose a) = some a
```

From `parse_print` and `Ast.ofRose_toRose`, as
`Geb.Ast.parseViaRose_printViaRose` in
`Geb/Internal/CanonicalSExpr.lean` does.

- [ ] **Step 3: Build**

Run: `lake build Geb.Internal.ReadableSExpr`
Expected: no errors.

- [ ] **Step 4: Commit**

```bash
jj commit -m "feat(internal): spell an Ast readably through the rose bijection"
```

---

### Task 8: The test module

**Files:**

- Create: `GebTests/Internal/ReadableSExpr.lean`
- Modify: `GebTests/Internal.lean` (one import)

**Interfaces:**

- Consumes: everything the library module exports.
- Produces: no declarations other than fixtures; the module is
  assertions.

- [ ] **Step 1: Write the header and the three imports**

The rule is that a `#guard` whose argument calls a non-`meta`
declaration **from another module of this package** needs a
`public meta import` of that module. That reaches the module under
test. It does **not** reach `Mathlib.Data.Fin.VecNotation`, which is
mathlib's and not this package's. Keep `![…]` out of `#guard`
arguments all the same — the spec records that a `#guard` whose
argument contains it fails to elaborate without a meta import, and the
assertions below need none: `![…]` appears only in `sampleRose`, a
`def` of this module, exactly as at
`GebTests/Internal/CanonicalSExpr.lean:89`. And since Step 4 uses no
`sexp`, `GebTests.Internal.ConcreteSyntax` is not imported at all.
Three import lines:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.ReadableSExpr  -- shake: keep; #guard needs it
public meta import Geb.Internal.ReadableSExpr  -- shake: keep; #guard needs it
public import Mathlib.Data.Fin.VecNotation
```

`lake shake` accepts exactly this set.

- [ ] **Step 2: Write the module docstring**

State what the assertions add over the theorems: the printer's
spelling, which the `@[simp]` lemmas pin but no theorem evaluates; the
round trip evaluated; the three lax families; the formatter; and the
rejection paths. Record that inputs are `List Char` because core's
`String.toList` depends on `Classical.choice`, which
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Constructive-only
requires be minimised, and that a `#guard` is not a declaration, so
`GebMeta.detectNonstandardAxiom` would not catch a leak there.

Follow `GebTests/Internal/ConcreteSyntax.lean` for the form: its prose
is at `:14-42` and its `## Main definitions`, `## References` and
`## Tags` at `:44-58`. `## Tags` is mandatory here too — keep every
line at or under 100 characters, which `mathlibStandardSet` enforces
as an error.

- [ ] **Step 3: Add the fixture and the spelling assertion**

```lean
@[expose] public section

open Geb

/-- A node of six children, third of them itself a node. -/
def sampleRose : Rose 8 :=
  Rose.node 0 ![Rose.node 1 ![], Rose.node 2 ![],
    Rose.node 3 ![Rose.node 4 ![]], Rose.node 5 ![], Rose.node 6 ![],
    Rose.node 7 ![]]

#guard String.ofList (Rsexp.print sampleRose) == "(0 1 2 (3 4) 5 6 7)"
```

- [ ] **Step 4: Add the round trip and the lax families**

```lean
#guard Rsexp.parse 8 (Rsexp.print sampleRose) == some sampleRose

-- pin that each compared input parses: every assertion below is an
-- equality of two `parse` calls, which two `none`s would satisfy
#guard (Rsexp.parse 8 ['(', '0', ' ', '1', ')']).isSome

-- whitespace variants the printer never emits
#guard Rsexp.parse 8 ['(', '0', ' ', ' ', '1', ')'] == Rsexp.parse 8 ['(', '0', ' ', '1', ')']
#guard Rsexp.parse 8 ['(', '0', ' ', '1', ' ', ')'] == Rsexp.parse 8 ['(', '0', ' ', '1', ')']
#guard (Rsexp.parse 8 ['(', '0', ' ', '(', '1', ')', ')']).isSome
#guard Rsexp.parse 8 ['(', '0', '(', '1', ')', ')']
    == Rsexp.parse 8 ['(', '0', ' ', '(', '1', ')', ')']
#guard Rsexp.parse 8 ['(', ' ', '0', ' ', '1', ' ', ')'] == Rsexp.parse 8 ['(', '0', ' ', '1', ')']
#guard Rsexp.parse 8 [' ', '(', '0', ' ', '1', ')', '\n'] == Rsexp.parse 8 ['(', '0', ' ', '1', ')']

-- a parenthesized childless node
#guard (Rsexp.parse 8 ['6']).isSome
#guard Rsexp.parse 8 ['(', '6', ')'] == Rsexp.parse 8 ['6']

-- leading zeros, which `Csexp.digitsVal` already accepts
#guard (Rsexp.parse 8 ['7']).isSome
#guard Rsexp.parse 8 ['0', '0', '7'] == Rsexp.parse 8 ['7']

-- `(01)` is a reinterpretation, not a rejection: the childless node 1
#guard (Rsexp.parse 8 ['1']).isSome
#guard Rsexp.parse 8 ['(', '0', '1', ')'] == Rsexp.parse 8 ['1']
```

The spec observes that `sexp` from `GebTests.Internal.ConcreteSyntax`
is reusable here, unlike the canonical atom fixtures. This plan does
not reuse it. `sexp body = '(' :: (body ++ [')'])`, so
`sexp ['0', ' ', '1']` reduces to the same list literal the assertion
would compare it against: the assertion would constrain nothing, and
it would be the sole justification for two committed imports.
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost decides
this. Every input below is a `List Char` literal.

- [ ] **Step 5: Add the formatter assertion**

The composite that rewrites `( 6 )` to `6` and `007` to `7` is
`Geb.format`, and `Rsexp.format_idem` states its output is a fixed
point. `format` returns an `Option (List Char)`, so assert the rewrite
of `(0 1 2 (3 4) 5 (6) 7)` to `(0 1 2 (3 4) 5 6 7)` as an equality of
`Option String`, mapping `String.ofList` over the result.

- [ ] **Step 6: Add the rejection paths**

```lean
#guard Rsexp.parse 8 ['(', '0', ' ', '1'] == none          -- unterminated
#guard Rsexp.parse 3 ['9'] == none                          -- label ≥ k
#guard Rsexp.parse 8 [')'] == none                          -- unopened
#guard Rsexp.parse 8 ['0', ' ', 'x'] == none                -- trailing input
#guard Rsexp.parse 8 ['(', ')'] == none                     -- no head numeral
#guard Rsexp.parse 8 ['(', '(', ')', ')'] == none           -- no head numeral
#guard Rsexp.parse 8 ([] : List Char) == none               -- entry at zero fuel
#guard Rsexp.parse 8 [' ', ' '] == none                     -- empty-input branch
```

The last two are distinct paths: empty input exercises the entry point
at zero fuel, whitespace-only input reaches `parseStep`'s empty-input
branch at positive fuel.

- [ ] **Step 7: Add the import to the test directory index**

In `GebTests/Internal.lean`, add
`import GebTests.Internal.ReadableSExpr` in alphabetical order.

- [ ] **Step 8: Build and run**

Run: `lake build GebTests && lake test`
Expected: no errors; every `#guard` passes. A failing `#guard` is a
build error, so `lake build GebTests` is the gate. Note that a build
aborts at the first failing module, so a clean run of a *later* module
proves nothing about an earlier failure — read the whole output.

- [ ] **Step 9: Commit**

```bash
jj commit -m "test(internal): exercise the readable spelling's parser"
```

---

### Task 9: Persistent documentation

The spec's § Persistent documentation list is **not exhaustive**, and
three review rounds each found sites missing from it. Do not work from
the list alone.

**Files:** `docs/concrete-syntaxes.md`, `docs/index.md`,
`docs/references.bib`, `docs/references.md`, `TODO.md`,
`Geb/Internal/CanonicalSExpr.lean`, `Geb/Internal/ConcreteSyntax.lean`.

- [ ] **Step 1: Run the sweep the spec prescribes**

Over `docs/concrete-syntaxes.md`, `docs/index.md`, `TODO.md`,
`docs/references.bib`, `docs/references.md`, and the Lean library and
test modules entire — module docstrings, declaration docstrings and
section comments alike — find every occurrence of:

- a cardinal number qualifying a noun;
- a list of the syntax modules, of the discharged retractions, or of
  the imports;
- an enumeration of the stages;
- the strings `parseChildren`, `either module`, `both`, `two modules`,
  `three syntaxes`, `Rose.Arity`, `linear`, `repairs`,
  `second data model`.

Settle each against the state after this stage. Record the list before
editing.

- [ ] **Step 2: Re-measure the theorem counts**

Run, over each of `ConcreteSyntax.lean`, `CanonicalSExpr.lean` and
`ReadableSExpr.lean` under `Geb/Internal/`:

```bash
grep -cE "^(@\[[^]]*\] )?theorem " <file>
```

The current counts are 52 and 20; Task 1 moves two theorems between the
first two, and this stage adds a third module. `docs/index.md` carries
per-module censuses with axiom breakdowns, and
`docs/concrete-syntaxes.md` repeats the counts at three further points
in the file, two in § Local verification and one in § Roadmap.

Re-derive the axiom breakdowns rather than adjusting the old ones.
`docs/index.md` states them as "Of the module's 52 theorems, 11 depend
on no axioms, 8 on `propext` alone, …", so the numbers come from a
`#print axioms` sweep over every theorem of all three library modules.
Do that in a temporary module under `GebTests/Internal/` carrying one
`#print axioms` per declaration, and read the results off the build
output. `#print axioms` needs fully-qualified names, and the three
modules re-open several namespaces, so generate the commands rather
than typing them — this tracks `namespace`/`end` and emits one line
per theorem:

Give the generated lines a header — the module declares nothing, so
unlike Task 2 Step 7 it needs no `@[expose] public section`:

```lean
module
public import Geb.Internal.ReadableSExpr
public import Geb.Internal.CanonicalSExpr
```

```bash
python3 - <<'EOF' > /tmp/axioms-body.txt
import re, sys
for f in ["Geb/Internal/ConcreteSyntax.lean",
          "Geb/Internal/CanonicalSExpr.lean",
          "Geb/Internal/ReadableSExpr.lean"]:
    ns = []
    for line in open(f):
        m = re.match(r"namespace (\S+)", line)
        if m: ns.append(m.group(1)); continue
        if re.match(r"end (\S+)", line) and ns and line.split()[1] == ns[-1]:
            ns.pop(); continue
        m = re.match(r"(?:@\[[^]]*\] )?theorem ([A-Za-z_][\w']*)", line)
        if m: print("#print axioms " + ".".join(ns + [m.group(1)]))
EOF
```

Check the emitted line count against the `grep -cE` totals above before
building; a mismatch means the namespace tracking missed a `section`
or an `end` that closes no namespace. The module goes under `GebTests`
for the reason Task 1 Step 5 gives: `lakefile.toml` disables
`linter.hashCommand` for that library alone. Delete the file
afterwards.

- [ ] **Step 3: Edit `docs/concrete-syntaxes.md`**

Condense the spec's § Survey of readable S-expression formats — a
section of the spec, not of this file — into `docs/concrete-syntaxes.md`
§ Format-by-format evaluation; record the Geb profile decisions for the
readable form beside the canonical form's, in the profile-decisions
block of § Canonical S-expressions (RFC 9804); add the stage row to
§ Roadmap and move 1b to `after 1a′`; correct § Roadmap's opening
sentence from "three syntaxes" to four, its stage-1b gloss, whose
whitespace half this stage writes, and its stage-2 gloss, which says
"JSON and the csexp advanced form acquire string escaping" and that
"[w]hich csexp form carries the annotated syntax is not yet settled" —
the readable form's atoms are not length-prefixed either, so it joins
both; extend § Evaluating the candidates' table; add the
readable spelling to § One tree, every recommended encoding; update
§ Status, § Local verification (module lists, counts, import census,
the architecture-theorems list, "either module", "All four build"),
§ The bootstrap set (the uncounted threshold, recorded together with
the fact that the grammar adopted is not the one that threshold names;
the readability bullet; the CBOR threshold; the adopted order; the
`{csexp, JSON core}` pair; and the framing sentence "Two considerations
bear on the order, and both favour the JSON core profile first", which
the readability consideration being met earlier weakens),
§ The canonical grammar as a data type, § Relation to existing
repository content, § Complexity note, § Temper, and § References.
Also correct § Status's scope statement, which currently declares
§ Format-by-format evaluation inherited text.

Stage 1d's gloss needs no edit: it stands verbatim with a fourth
retraction preceding it.

Record beside the canonical form's profile decisions only the
format-level facts about the readable form: the label spelling, the
three families in which the decoder is laxer than the printer, and the
`k`-bound divergence. The four dimension values § Decisions this plan
settles fixes are parser arrangement, not a format profile, so they do
not belong in that block; their contract-level content is committed in
the module and declaration docstrings instead, as § Decisions this plan
settles records.

- [ ] **Step 4: Edit the remaining documents**

`docs/index.md`: the new module, the censuses and breakdowns, and
§ Design documents' list of implementing modules.
`docs/references.bib`: already carries [R7RS], [EDN] and [RFC8259]
from Task 2 Step 8; check them rather than add them.
`docs/references.md`: pointers for `sexplib`, `janestreet/sexp`, Real
World OCaml's data-serialization chapter, parinfer, paredit and
`zv/sexpr`, which are tooling and exposition rather than citable
literature.
`TODO.md`: the module, and § Deferred's six items, which the spec's
deletion in Task 11 would otherwise lose — indentation and the
constraint that only parinfer's Paren Mode composes with a retraction
law; atom quoting and escaping at stage 2; named labels; comments;
commas as whitespace; and reading hand-written text as a `String`,
which no choice-free conversion currently supports. Also
§ Prose-conformance pass
over the concrete-syntax survey (scope and the `.bib` tally);
§ Concrete-syntax prototype (module list and "the first syntax over a
second data model").

- [ ] **Step 5: Edit the two Lean module docstrings**

`Geb/Internal/CanonicalSExpr.lean`: `## Main definitions` calls the
parsers "built from `Rose.parseChildren`", and the implementation
notes' second paragraph opens "A rose node's arity is unbounded, so
`Rose.parseChildren` reads until the closing parenthesis".
`Geb/Internal/ConcreteSyntax.lean`: `## Main definitions` gains
`Rose.parseChildren`; the module docstring's summary describes the
module as carrying the format-independent core and one worked concrete
syntax, and a loop shared by two spellings falls under neither clause;
`Rose.Arity`'s docstring, the module docstring's § Implementation
notes, and `docs/concrete-syntaxes.md` § Local verification's first
fact about the encoding each enumerate the proofs needing the family
reducible, and the readable `parseAux_print` makes all three
undercounts; the § Choice-free finite enumerations section comment and
`Rose.instFinEnumArity`'s docstring both say "two"/"Both" of the
`GebTests` syntax modules.

- [ ] **Step 6: Regenerate TOCs and lint**

Run: `doctoc --update-only . && markdownlint-cli2 '**/*.md'`
Expected: "Everything is OK" and 0 issues.

- [ ] **Step 7: Rebuild, since docstrings are compiled**

Run: `lake build && lake build GebTests`
Expected: no errors.

- [ ] **Step 8: Commit**

```bash
jj commit -m "doc(concrete-syntax): record the readable spelling"
```

---

### Task 10: The pre-push gate

- [ ] **Step 1: Run the full checklist**

Run: `scripts/pre-push.sh`
Expected: every step passes. The script runs, among others,
`lake exe cache get`, `lake build`, `lake test`, `lake lint`,
`lake build GebTests`, `lake lint -- GebTests`, `lake shake`, the
import lint, `markdownlint-cli2 '**/*.md'`, the TOC check, the
`scripts/tests/*.sh` self-tests, and `scripts/check-commit-msg.sh`
over the branch's commits — which is the gate on this plan's
commit-message constraint.

- [ ] **Step 2: Fix and re-run until clean**

`lake lint` runs `GebMeta.detectNonstandardAxiom`; a `Classical.choice`
leak in a *declaration* fails here. `lake shake` reports unused
imports; `-- shake: keep` on an import line suppresses one that is
needed only by a `#guard`.

- [ ] **Step 3: Verify no `sorry` survives**

Run: `grep -rn "\bsorry\b" Geb/ GebTests/ | grep -v sorryAx`
Expected: no output. The plain `grep -rn sorry Geb/ GebTests/` is not
usable as a gate: `GebTests/Internal/AxiomLinter.lean` legitimately
mentions `sorryAx` at seven lines, so that form reports a failure on a
clean tree.

- [ ] **Step 4: Commit any fixes**

Only if Steps 2 or 3 changed anything. On the expected outcome — a
clean run — there is nothing to commit and this step is skipped;
`jj status` says which.

```bash
jj commit -m "chore(internal): satisfy the pre-push checklist"
```

---

### Task 11: Remove the transient documents

Specs and plans record how the current state was reached, not what it
is, so the branch ends by removing them
([CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape). They
remain reachable in history.

- [ ] **Step 1: Delete both files**

```bash
rm docs/superpowers/specs/2026-08-03-readable-sexpr-design.md
rm docs/superpowers/plans/2026-08-07-readable-sexpr.md
```

- [ ] **Step 2: Confirm nothing committed references them or their sections**

The spec's own section names are the trap: a docstring citing
`§ Grammar` or `§ Shape` reads naturally while the spec is in the tree
and dangles the moment this step deletes it. Sweep the committed Lean
and Markdown for a section-sign reference to a spec section name, not
only for the filename:

```bash
grep -rnE "§ (Problem|Roadmap position|Survey of readable|How far the formats agree|Why not the RFC 9804|Why not sexplib|The syntax|Shape|Grammar|Printer|Where the decoder|Proof obligations|The delimiting|What the decimal|The child loop|Alternatives considered|Lean shape|Persistent documentation|Deferred|Recorded consequences)" \
  Geb/ GebTests/ docs/ TODO.md README.md --include=*.lean --include=*.md
```

Expected: no hit that resolves to the spec. Sections of
`docs/concrete-syntaxes.md` and RFC/R7RS section numbers are fine.

- [ ] **Step 3: Confirm nothing committed references the files**

Run: `grep -rn "readable-sexpr" --include=*.md --include=*.lean . | grep -vE '^\./(\.jj|\.lake)'`
Expected: no output. A surviving reference means persistent
documentation was left pointing at a transient file.

- [ ] **Step 4: Commit**

```bash
jj commit -m "doc: remove the readable-spelling spec and plan"
```

- [ ] **Step 5: Re-run the commit-message gate over the whole branch**

Task 10 Step 1 ran `scripts/pre-push.sh` before this task's commit
existed, so its `scripts/check-commit-msg.sh` step has not seen that
subject — nor Task 10 Step 4's, on the paths where that step commits.
The script reads subjects from stdin, so run it as `pre-push.sh` does:

```bash
jj log --no-graph -r 'fork_point(main | @)..@ ~ merges()' \
  -T 'description.first_line() ++ "\n"' | bash scripts/check-commit-msg.sh
```

Expected: every subject conforms. Invoked with nothing on stdin the
script validates nothing.

- [ ] **Step 6: Hand the branch to the user for line-by-line review**

Do not push. [AGENTS.md](../../../AGENTS.md) requires the user's
line-by-line review before any `jj git push`, first-creation pushes
included.

---

## Self-review

**Spec coverage.** § Problem, § Roadmap position and § Survey of
readable S-expression formats → Task 9 Step 3, which condenses the
survey and edits the roadmap, with Task 2 Step 1 carrying the
interoperation argument into the module docstring. § Status → Tasks 0 and 11, which
commit the two transient documents and then remove them. § Shape and
§ Printer → Task 2; § Grammar's lexical layer → Task 2's `isWs`, its
phrase layer → Task 4's `parse`, `parseStep` and `parseAux`. § Where
the decoder is laxer → Tasks 4 and 8, and Task 9 Step 3, which records
the three lax families and the `k`-bound divergence. § Proof
obligations → Tasks 1 and 4 for its four parser layers, Task 2 for the
whitespace skip it sets apart from them, Task 6 for the
childless-branch reconciliation. § The delimiting
hypothesis → Tasks 5 and 6. § What the decimal layer supplies →
Task 3. § The child loop is reused → Tasks 1 and 5,
with its four unpredicted implementation details in Task 3 (the
`omega` failure), Task 4 Step 3 (an equation lemma per branch),
Task 6 Step 2 (the bare `simp only []`) and Global Constraints
(`change`, not `show`). § Alternatives considered → Decision 2 above
and Task 9. § Lean shape → Tasks 1, 2, 4, 5, 6, 7, 8 and 9: it fixes the module's
imports and the relocation as well as the declarations. § Persistent
documentation → Task 9, and Task 2 Step 8 for the bibliography
entries the module's own citations need. § Deferred and § References
→ Task 9 Step 4, which lands the six deferrals in `TODO.md` and the
tooling pointers in `docs/references.md`.
§ Recorded consequences → Task 9, and Task 2 Step 1, whose module
docstring commits the delimiting-hypothesis and `skipWs`
consequences. The two choices the spec delegates are settled in
§ Decisions this plan settles.

**Placeholders.** The proof steps in Tasks 3, 5 and 6 give statements
verbatim and name the exact lemmas and tactic shapes rather than a
finished script. That is deliberate and is the one thing an implementer
must develop against the compiler. Every definition, statement and
import line is given as Lean, as is every assertion but one: Task 8
Step 5's formatter rewrite is described rather than written out,
because its exact spelling depends on how `Geb.format` is instantiated
at this syntax. Task 8 Step 2's test-module docstring is likewise
described rather than written; Task 2 Step 1's library docstring is
given in full. Both must carry the mandatory `## Tags` section.

**Type consistency.** `print`, `parse`, `parseStep`, `parseAux`,
`skipWs`, `isWs`, `printViaRose`, `parseViaRose` carry the same
signatures wherever they appear. `parse` takes `(k : Nat)` explicitly,
the alphabet bound and not a fuel. `parseChildren_print`'s conclusion is
`rest`; `parseAux_print`'s is `skipWs rest`; these differ deliberately
and consistently across Tasks 5 and 6.
