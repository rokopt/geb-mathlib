---
paths:
  - "**/*.lean"
---

# Lean coding conventions

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Authoritative upstream guides (mathlib)](#authoritative-upstream-guides-mathlib)
  - [Commit messages (from `commit.html`)](#commit-messages-from-commithtml)
  - [Coding style (see also mathlib's `style.html`)](#coding-style-see-also-mathlibs-stylehtml)
  - [Naming conventions (see also mathlib's `naming.html`)](#naming-conventions-see-also-mathlibs-naminghtml)
  - [Documentation (see also mathlib's `doc.html`)](#documentation-see-also-mathlibs-dochtml)
- [Authoritative upstream guides (CSLib)](#authoritative-upstream-guides-cslib)
- [Comment and docstring rules](#comment-and-docstring-rules)
- [Lean 4 module system](#lean-4-module-system)
- [Lake / build workflow](#lake--build-workflow)
- [Coding technique](#coding-technique)
  - [Constructive-only](#constructive-only)
  - [Proof guidelines](#proof-guidelines)
  - [Higher-order constructions](#higher-order-constructions)
  - [Recursion and induction through recursors](#recursion-and-induction-through-recursors)
  - [One step at a time](#one-step-at-a-time)
  - [Structure and typeclass patterns](#structure-and-typeclass-patterns)
- [Constructive-only Lean code](#constructive-only-lean-code)
- [sorry, admit, and underscores](#sorry-admit-and-underscores)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Applies whenever a `.lean` file is open or being edited.

## Authoritative upstream guides (mathlib)

These are the binding upstream references for `Geb/Mathlib/`
content. Adversarial reviewers must check our `Geb/Mathlib/`
content for violations against each:

- Contributing index:
  `https://leanprover-community.github.io/contribute/index.html`
- Commit messages:
  `https://leanprover-community.github.io/contribute/commit.html`
- Coding style:
  `https://leanprover-community.github.io/contribute/style.html`
- Naming conventions:
  `https://leanprover-community.github.io/contribute/naming.html`
- Documentation conventions:
  `https://leanprover-community.github.io/contribute/doc.html`

Bullet-point highlights extracted from each guide appear below.
The full guides supersede this digest; re-fetch and re-verify
on every adversarial-review round (the guides are subject to
revision by the leanprover-community).

### Commit messages (from `commit.html`)

The commit-message convention (format, the
`feat | fix | doc | style | refactor | test | chore | perf | ci`
type list, imperative present tense, no-capital/no-period subject,
and documented footers) is stated once in
`docs/rules/ci-and-workflow.md` § Commit-message convention; it
binds every commit, not only `.lean` changes.

**Adversarial-reviewer instruction**: scan every commit message
in the plan and the actual git history for indicative or
past-tense verbs ("Adds", "Carries", "Pins", "Creates", "Sets",
"Adopted"), capitalised first letters of subjects, trailing
periods, and out-of-list types; flag each occurrence.

### Coding style (see also mathlib's `style.html`)

- Indentation: 2 spaces; no tabs.
- Line length: 100 characters maximum (matches mathlib's
  `mathlibStandardSet` linter setting).
- One declaration per line; no semicolons separating
  declarations.
- Use Unicode notation where mathlib does (e.g., `∀`, `∃`, `→`,
  `↦`, `⟨ ⟩`, `≤`, `≥`, `≠`, `∈`, `⊆`).
- `pp.unicode.fun = true` is set project-wide in
  `lakefile.toml`.
- `autoImplicit = false` and `relaxedAutoImplicit = false` are
  set; declare every variable explicitly.
- Section / namespace structure: open and close namespaces
  explicitly; do not mix `namespace X` blocks with content
  outside them in the same file.
- Anonymous constructors `⟨ ... ⟩` and structure projections
  `.x` are preferred where unambiguous.
- Copyright header per mathlib's style guide:
  `Copyright (c) <year> <author names>. All rights reserved.`,
  the Apache-2.0 license line, and
  `Authors: <comma-separated names>`. Contributor names appear
  here in mathlib's named-author form; see
  CONTRIBUTING.md § Style and references for the scoped
  exception to the generic-user-reference rule.

**Adversarial-reviewer instruction**: scan our `.lean` files
for indentation drift, lines exceeding 100 characters,
multi-declaration lines, ASCII forms where mathlib uses Unicode,
and namespace/section nesting violations.

### Naming conventions (see also mathlib's `naming.html`)

- `UpperCamelCase` for names denoting `Prop`s or `Type`s:
  `structure`, `class`, `inductive`, type-class arguments,
  Sort-valued constants, and `def`s returning a `Prop` or
  `Type` (e.g. predicates). Functions are named as their
  return values.
- `snake_case` for the names of proof terms
  (`theorem` / `lemma`).
- `lowerCamelCase` for terms of other types: `def`s returning
  values, `example`s, variables, anonymous constructors, and
  tactic names. An explicitly named `instance` is a term of its
  class and follows the same rules (`snake_case` when the class
  is `Prop`-valued).
- Compound names follow the pattern
  `<subject>_<verb>_<object>` or `<verb>_<subject>` for
  theorems (e.g., `add_comm`, `mul_assoc`,
  `Nat.succ_lt_succ`).
- Theorem names stating an equivalence use the infix `_iff_`
  (`even_iff_two_dvd`).
- Do not include the namespace in the declaration body's
  identifiers; rely on `namespace` to scope.
- Discharging operator: `_left`, `_right`, `_self`, `_of_…`,
  `_iff_…` follow specific positional conventions; check the
  upstream guide for the full table before naming.

**Adversarial-reviewer instruction**: scan our `.lean` files
for ALL_CAPS or `snake_case` identifiers, namespace prefixes
inside declarations, and non-standard operator suffixes; flag
each occurrence with a pointer to the upstream rule.

### Documentation (see also mathlib's `doc.html`)

- `/-! … -/` module docstring is mandatory after imports;
  required sections (in order), each present when it has
  content and omitted (never a placeholder) when vacuous:
  `# Title`, brief summary, `## Main definitions`,
  `## Main statements`, `## Notation`,
  `## Implementation notes`, `## References`, and `## Tags`.
  `## Tags` is mandatory for modules with substantive content
  (index stubs omit it) and lists only keywords for the
  module's major theme — universal properties of the file's
  development, nothing transient. The section mandates are
  deliberate local strengthenings of mathlib's doc guide,
  which marks `## Main definitions` and `## Main statements`
  optional.
- `/-- … -/` declaration docstring is mandatory for every
  `def`, `structure`, `class`, `instance`, every field of a
  `structure`/`class`, and every theorem of public interest.
- Markdown is supported in docstrings; LaTeX via `$…$` (inline)
  and `$$…$$` (display).
- Cross-references use `` `Foo.bar` `` for identifiers;
  doc-gen4 renders them as links.
- Literature citations reference a key in `docs/references.bib`
  in `[Key]` form; the `## References` section lists the cited
  keys. The bibliographic detail lives only in the `.bib`.
- No development-history references in docstrings (e.g.,
  "previously did X"); history is for commit logs.

**Adversarial-reviewer instruction**: scan our `.lean` files
for missing module/declaration docstrings, missing required
sections in module docstrings, history-references inside
docstrings, and post-hoc axiom-celebration.

## Authoritative upstream guides (CSLib)

These are the binding upstream references for `Geb/Cslib/`
content. Adversarial reviewers must check our `Geb/Cslib/`
content against the contribution guide:

- Contribution guide:
  `https://github.com/leanprover/cslib/blob/main/CONTRIBUTING.md`

CSLib generally follows mathlib's style and documentation
conventions; verify CSLib-targeted code against the mathlib
guides above as well. CSLib-specific constraints (mandatory
`Cslib.Init` import, notation locality, `lake shake` minimised
imports, stronger reuse principle, narrower PR-title types,
pre-coordination on Zulip for major work) live in
`docs/rules/upstream-eligible.md` § CSLib-specific
constraints.

## Comment and docstring rules

Local docstring rules. These are deliberate strengthenings of
mathlib's doc guide (which requires docstrings only for
definitions and major theorems) and bind as written:

- The `/-! … -/` module docstring is mandatory after imports,
  with the section list and non-vacuous reading stated in
  § Documentation above.
- `/-- … -/` docstrings are mandatory for every `def`,
  `structure`, `class`, and `instance`, every field of a
  `structure`/`class`, and every theorem of public interest.
- Markdown and LaTeX as in § Documentation; no
  development-history references.
- **Empty lines inside declarations are lint-discouraged**; use a
  brief comment (`-- ...`) as a structural separator if needed.

## Lean 4 module system

Every `.lean` file declares itself as a module using the `module`
keyword after the copyright block. Imports re-exported to
downstream users (typically the case for index/umbrella files
and for content needed by callers of this module) use
`public import`; imports whose contents are used only internally
use plain `import`.

## Lake / build workflow

- Always use `lake build` and `lake test`. Avoid `lake clean`
  (it forces a full mathlib rebuild). Never use `lake env lean`
  (it fails to pick up options from `lakefile.toml` and produces
  spurious errors).
- In a fresh worktree, run `lake exe cache get` before the first
  `lake build` to pull mathlib's precompiled artifacts. Without
  this, lake falls back to building mathlib from source (hours of
  work).

## Coding technique

### Constructive-only

No `noncomputable`. Minimise `Classical`, accepting it only
when we can confirm that a mathlib concept that we are reusing
is responsible.

Avoid `Quotient.out` / `Quot.out`; both require `Classical.choice`.
Use the constructive `Quotient` / `Quot` API
(`mk` / `lift` / `ind` / `sound`) instead.

### Proof guidelines

- **First errors first.** When `lake build` reports multiple
  errors or warnings, fix the first one before later ones. Later
  errors may be caused by earlier ones, or fixes for them may
  depend on earlier fixes.
- **Underscores expose holes.** When you want to see the type of
  a goal you're working on, insert `_` (underscore). Building
  produces an "unsolved goals" error and prints the goal type.
- **`#check`** to inspect the type of an expression in-place.
- **One definition at a time.** When developing a new module,
  write one definition / function / theorem and get it completely
  working (no underscores, no `sorry`, clearly corresponding to
  its intended meaning) before moving to the next. Building a
  whole module at once produces compounding misconceptions.
- **Work both forwards and backwards.** Forward: how do the
  inputs / locals build toward the goal? Backward: what previous
  step would let us reach the goal? Often the easiest path is
  from both directions toward the middle.
- **One proof step at a time when stuck.** If a multi-step
  rewrite or compound tactic fails, decompose into single steps
  and re-check the goal at each. Recombine after each step works
  individually.
- **Factoring-out-lemmas technique.** When a proof gets stuck:
  identify a good intermediate goal — either a forward step you
  can prove, or a backward step that would let you reach the
  overall goal. Factor out two lemmas (current → intermediate,
  intermediate → overall) as `_` placeholders, dispatch the
  overall goal by transitivity to confirm they compose, then
  prove each lemma separately. Recurse if the lemmas themselves
  are still too large.
- **Stuck-and-ask template.** When unable to fill an underscore,
  making no progress, or not understanding what's wrong: pause
  and explain (1) what you're trying to accomplish, (2) what
  problems you're encountering, (3) what you've tried, (4) why
  you're stuck on a particular underscore. Don't silently abandon
  the task.

### Higher-order constructions

Be suspicious of piece-by-piece constructions. For example, when
constructing a functor, always seek a way to build it out of
compositions of existing functors and functorial operations on
functor categories rather than writing explicit object maps,
morphism maps, and functor-law proofs — higher-order operations
provide all of those at once. The same applies broadly: prefer
composition of established abstractions over hand-rolling. See
`docs/process.md` § Code is cost for the rationale.

### Recursion and induction through recursors

All recursion and induction is expressed through recursors — functions
taking non-recursive step functions as arguments, confining the recursion
to their own verified internals. This covers mathlib's recursors
(`WType.elim`, `WType.rec`), Lean's auto-generated ones (`casesOn`, `rec`,
`brecOn`), and recursors defined here by wrapping those (e.g. an induction
principle on a W-type subtype). Consequently:

- No `induction` / `induction'` tactics; drive a proof's recursion with an
  explicit recursor application, reserving `cases` / `casesOn` for
  non-recursive case analysis.
- No `def` that calls itself; no `termination_by` / well-founded
  self-recursion.
- No `structure` or `inductive` that contains an instance of itself.
  Self-reference is expressed as a W-type of the appropriate form
  (mathlib's `WType`, or the slice or presheaf W-types built here), so the
  recursion is carried by that type's recursor.

The purpose is to keep every datatype and every recursion expressed as a
polynomial functor and its recursor. So presented, a datatype participates
in the category of polynomial functors: it composes with the standard
combinators, it can be assembled à la carte, and every morphism between two
such datatypes takes one uniform form — a natural transformation of
polynomial functors. Explicit recursion forfeits this: a self-referential
datatype sits outside the framework, cannot reuse the shared combinators,
and forces bespoke, hand-written maps out of it. Keeping definitions
`noncomputable`-free (§ Constructive-only Lean code) is then a corollary,
since `WType.elim` folds are code-generatable.

### One step at a time

Definitions and proofs are written as small compositions, one
step at a time, so each intermediate step yields a reusable
component. See `docs/process.md` § Code is cost for the
rationale.

### Structure and typeclass patterns

- **`@[ext]` reflex.** Always add `@[ext]` to structure
  definitions (when it compiles) so extensionality lemmas
  auto-generate.
- **Standard derivations.** When defining a structure, derive
  `Inhabited` / `DecidableEq` / `Repr` where applicable.
- **`extends` is composition, not OO inheritance** — appropriate
  when a structure builds on another by adding fields. See
  [FP-in-Lean: Structures and Inheritance](https://leanprover.github.io/functional_programming_in_lean/functor-applicative-monad/inheritance.html).
- **Sigma-type pattern for dependent fields.** When a structure
  has later fields that depend on earlier ones, define an
  independent struct first, then a dependent struct, then
  combine via sigma type (preferably with `extends`). Allows
  operations on independent components separately.
- **Typeclass-instance pattern.** Define the interface as a
  structure with the typeclass's fields; define the typeclass
  with a single field containing an interface instance; functions
  taking / returning the typeclass have an interface-version that
  the typeclass-version wraps. Separates interface (mathematical
  object) from typeclass resolution (isolating resolution errors).
- **Factor out structure components into separate definitions.**
  Makes type signatures explicit.
- **Universe-polymorphic.** Make universe levels as polymorphic
  as compiles. A declaration's type should be maximally
  polymorphic while remaining readable and free of auto-bound
  (`u_1`-style) universe variables; the two bullets below cover
  the cases that violate this.
- **Ascribe a structure's result sort.** Lean synthesises a
  structure's universe field-by-field into a left-nested `max`
  (e.g. `Type (max (max (uA + 1) (uB + 1)) uD)`). An explicit
  result ascription replaces it with the written, flat form
  `Type (max (uA + 1) (uB + 1) uD)`. The ascription precedes
  `extends` in current syntax:
  `structure S (..) : Type .. extends P where`. A `def` result
  type elaborates flat already and needs no ascription.
- **Pin parent universes in `extends`.** `extends Parent dom`
  leaves the parent's remaining universe parameters
  unconstrained, so the elaborator auto-binds fresh `u_1`-style
  variables; `autoImplicit false` does not catch this, since the
  levels come from the parent's polymorphism, not an unbound
  identifier. Write `extends Parent.{uA, uB, uD} dom` to bind
  them to declared names. Explicit `.{..}` arguments elsewhere
  (`(F : Parent.{uA, uB} dom)`) never leak. Hover preserves
  declared names, so it reveals leaks that `#check` (which
  renames every level to `u_N`) hides.
- **Check for unused `universe` / `variable` declarations** after
  editing files that introduce or modify them; remove unused
  ones.
- **Non-negotiable interfaces for formalising pre-existing objects**:
  When formalising a specific mathematical object, the
  interface (objects, primitive constructors, generators) is
  fixed by the external mathematical source. Implementation
  strategies (proof techniques, auxiliary inductives, named
  composites) may change freely; weakening the interface of
  a standard mathematical concept to ease implementation is
  always wrong.
- **Compositional tests.** Where possible, calculate one value
  per test, assert it matches the expectation, return the value
  for reuse in other tests. Reduces duplication; chains tests
  together.

## Constructive-only Lean code

- No `noncomputable` anywhere.
- Minimise `Classical`; flag/justify each invocation in our own
  code.
- The `GebMeta.detectNonstandardAxiom` `@[env_linter]` fails
  `lake lint` when any `Geb` or `GebTests` declaration depends on
  an axiom outside its permitted set. The permitted set is
  `{propext, Quot.sound}` by default; declarations defined in the
  exact modules listed in `GebMeta.classicalAllowedModules`
  additionally permit `Classical.choice` (and only
  `Classical.choice`). The allowlist exists so thin wrappers over
  mathlib's `Classical.choice`-dependent category theory (e.g.
  `Over`) can reuse it while the constructive core stays strict.
  It runs in CI and the pre-push checklist;
  `scripts/tests/test-axiom-linter.sh` smoke-tests it.

## sorry, admit, and underscores

- **`sorry`** is permitted between commits as a stand-in while
  working with a development tool that requires placeholders
  during proof development (e.g.,
  `lean4:sorry-filler-deep`, `lean4:autoprove`). It is never
  permitted in committed code.
- **`admit`** is never permitted, not even between commits.
  Use `sorry` (audited as above) when a placeholder is needed.
- When no tool specifically requires `sorry` and we just need
  a placeholder for an unfilled term or hypothesis, use an
  underscore (`_`). Underscores are considered errors by elaboration,
  highlighting what is missing.
