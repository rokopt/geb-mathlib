---
paths:
  - "Geb/Mathlib.lean"
  - "Geb/Mathlib/**"
  - "GebTests/Mathlib.lean"
  - "GebTests/Mathlib/**"
  - "Geb/Cslib.lean"
  - "Geb/Cslib/**"
  - "GebTests/Cslib.lean"
  - "GebTests/Cslib/**"
  - "GebLang/**"
  - "GebTests/Lang.lean"
  - "GebTests/Lang/**"
---

# Upstream-eligible content rules

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Authoring](#authoring)
- [Two-track development](#two-track-development)
- [Floodgate test](#floodgate-test)
- [Subtree import rules](#subtree-import-rules)
- [CSLib-specific constraints](#cslib-specific-constraints)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Applies to anything under `Geb/Mathlib/`, `GebTests/Mathlib/`,
`Geb/Cslib/`, `GebTests/Cslib/`, `GebLang/`, or `GebTests/Lang/`,
and to the `GebTests/Lang.lean` index. The `GebLang.lean` umbrella
is excluded: it is a library root, the peer of `Geb.lean` and
`GebTests.lean`, rather than a subtree index like `GebTests/Lang.lean`,
so the content rules, addressed to a location's own files, do not
bind it.

Work in the file globs this rule applies to is also bound by
[CONTRIBUTING.md § Submission policy](../../CONTRIBUTING.md),
which governs LLM-generated code in upstream-eligible content
(mandatory disclosure and line-by-line understanding).

## Authoring

For upstream-eligible subtrees, AI authoring follows
[AGENTS.md § AI authoring (upstream-eligible work)](../../AGENTS.md):
an agent may draft, and the user commits only after understanding
every line, being able to justify each design decision to
reviewers without AI, and disclosing tool use.
Work under `Geb/Prototypes/` is reviewed by the user at commit
time without that upstream justification bar.

## Two-track development

`Geb/Prototypes/` holds prototypes: code that works out a
construction the language is to have, established far enough to
show how the construction goes, without its written form being
settled as the one to keep. A prototype may build on
upstream-quality code in `Geb/Mathlib/`, `Geb/Cslib/` or
`GebLang/` without itself meeting that bar. While its expression
is provisional it is not upstream-eligible.
The split is driven by whether a module's expression is settled,
and by dependency-readiness, not by authorship: AI-drafted and
human-written code follow the same rules in every subtree.

When a prototype's expression is settled and the code is brought
to upstream quality:

1. Port it into `Geb/Mathlib/Foo.lean`, `Geb/Cslib/Foo.lean` or
   `GebLang/Foo.lean` depending on the upstream target, satisfying
   the subtree import rules below. `Geb/Mathlib/` is not exclusively
   mathlib4-targeted: where the import rules below leave no
   alternative, a module there may instead target Lean core or
   Batteries, a destination open per `TODO.md` § Upstream
   destination of core- and Batteries-targeted content. `GebLang/`
   is destination-open per module in a second sense: its modules
   carry the Geb language's core data structures and ship to mathlib
   or to Cslib according to each module's own import closure
   (§ Subtree import rules).
2. When the upstream PR is accepted and we re-pin to a fresh
   master that includes it, migrate dependents by rebasing.
   The prototype is then removed.

## Floodgate test

At all times, the repository must be ready to ship
dependency-ordered PRs on short notice with no source-code changes.
After any non-trivial change, ask whether it breaks extraction.
Extraction is dependency-ordered through `GebLang/` rather than
independent between the subtrees: a module's within-repository
dependencies ship first, each retargeted by its own import closure,
mathlib-track when the closure reaches no `Cslib.*` and Cslib-track
otherwise. `scripts/lint-imports.sh` bounds each module's direct
imports and `scripts/check-transitive-imports.sh` bounds the
closures, so a `Geb/Mathlib/` module cannot acquire a Cslib-track
dependency unnoticed.

## Subtree import rules

Each upstream-eligible location has an allowed-import list and one or
more self-prefixes that must not appear outside the module path of an
import line. A test root mirrors its source root: it additionally
imports its own sibling modules, and forbids leakage of both the
source self-prefix and the test self-prefix. Source roots cannot
import test modules. `GebLang/` and its mirror `GebTests/Lang/` are
locations in this sense without being subtrees of `Geb/`.

| Subtree | Allowed imports | Self-prefixes (no leakage) |
| --- | --- | --- |
| `Geb/Mathlib/` | `Mathlib.*`, `Batteries.*`, `Geb.Mathlib.*`, `GebLang.*` | `Geb.Mathlib.`, `GebLang.` |
| `GebTests/Mathlib/` | `Mathlib.*`, `Batteries.*`, `Geb.Mathlib.*`, `GebTests.Mathlib.*`, `GebLang.*` | `Geb.Mathlib.`, `GebTests.Mathlib.`, `GebLang.` |
| `Geb/Cslib/` | `Mathlib.*`, `Batteries.*`, `Cslib.*`, `Geb.Cslib.*`, `Geb.Mathlib.*`, `GebLang.*` | `Geb.Cslib.`, `Geb.Mathlib.`, `GebLang.` |
| `GebTests/Cslib/` | `Mathlib.*`, `Batteries.*`, `Cslib.*`, `Geb.Cslib.*`, `GebTests.Cslib.*`, `Geb.Mathlib.*`, `GebLang.*` | `Geb.Cslib.`, `GebTests.Cslib.`, `Geb.Mathlib.`, `GebLang.` |
| `GebLang/` | `Mathlib.*`, `Batteries.*`, `Cslib.*`, `GebLang.*` (plus `Cslib.Init` when the file imports any `Cslib.*`) | `GebLang.` |
| `GebTests/Lang/` | `Mathlib.*`, `Batteries.*`, `Cslib.*`, `GebLang.*`, `GebTests.Lang.*` (plus `Cslib.Init` when the file imports any `Cslib.*`) | `GebLang.`, `GebTests.Lang.` |

`Batteries.*` is admitted to every upstream-eligible location because
mathlib depends on Batteries and imports its modules directly, and
Cslib does the same, so a Batteries import survives extraction to
either upstream. Batteries modules that no `Mathlib.*` module imports
are reachable no other way.

A second rationale binds the mathlib-targeted subtrees alone. The
restriction to these prefixes can force a module into `Geb/Mathlib/`
whose target is Lean core or Batteries, a dependency of a
`Geb/Mathlib/` module being unable to live in `Geb/Prototypes/`, and
such a module is not extracted to mathlib4 at all. Its destination is
open, per `TODO.md` § Upstream destination of core- and
Batteries-targeted content.

Every allowed-import list makes a fixed exception for
`Lean.DocString.Syntax` and `GebMeta`, matched as exact module paths
rather than as namespace prefixes, so a submodule of either is not
admitted. They are the imports of a literate module: the first when
its imports do not otherwise reach the module whose syntax its Verso
role markup records a compile-time use of, which `lake shake`
requires imported, and the second, as a `meta import`, for the
`{cite}` docstring role (`docs/rules/lean-coding.md` § Literate
modules). Extraction removes both import lines, per
`scripts/extract-pr.sh`'s `strip_line` function: neither has meaning
upstream.

`GebLang/` and `GebTests/Lang/` carry a conditional form of Cslib's
`Cslib.Init` requirement: a module that imports any `Cslib.*` module,
in any of the four import forms, imports `Cslib.Init` itself, and a
module that imports none is not forced to. Only a plain or `public`
import of `Cslib.Init` satisfies the requirement, matching the two
Cslib subtrees' unconditional form. The direct-import form suffices
because Cslib's own check is transitive: a Cslib-track module
importing only extracted `GebLang` siblings inherits `Cslib.Init`
through them.

A `GebTests/Lang/` module's sibling imports do not cross tracks. A
Cslib-track test importing a mathlib-track sibling would need the
Cslib test tree to import mathlib's, which no upstream ordering makes
compile; `scripts/check-transitive-imports.sh` rejects it.

Bare umbrella imports (`import Mathlib`, `import Batteries`,
`import Cslib`) are forbidden — extraction requires specific module
imports.

A self-prefix appears **only** in the module path of any permitted
import. An import line's trailing comment is checked like any other
prose. Do not use a self-prefix in:

- namespace declarations
  (`namespace Computability.Primrec`,
   not `namespace Geb.Mathlib.Computability.Primrec`),
- declaration bodies / fully-qualified-name references
  (use `open` or the bare name),
- docstrings or comments.

`scripts/lint-imports.sh` enforces these rules and
`scripts/check-transitive-imports.sh` enforces the closure rules
above them; the smoke tests are
`scripts/tests/test-lint-imports.sh` and
`scripts/tests/test-check-transitive-imports.sh`.

The cross-subtree boundary follows the upstream dependency
relationship, in one direction. mathlib does not depend on Cslib, so
`Geb/Mathlib/` files cannot import from `Cslib.*` or `Geb.Cslib.*`,
and no `GebLang` module they import may reach `Cslib.*` either.
Cslib does depend on mathlib, so `Geb/Cslib/` files may import
`Geb.Mathlib.*` and `GebLang.*` of either track: a mathlib-track
dependency ships first and the Cslib PR follows once it merges and
Cslib's mathlib pin advances, while a Cslib-track one ships to Cslib
alongside it. `Geb/Prototypes/` may import from any of the above, with
no list to amend.

## CSLib-specific constraints

Cslib's `CONTRIBUTING.md` adds the following requirements beyond
mathlib's style. They bind files in `Geb/Cslib/` and
`GebTests/Cslib/`, and Cslib-track modules of `GebLang/` and
`GebTests/Lang/`, which ship to Cslib and so carry them at authoring
time:

- **Import `Cslib.Init`**: every Cslib-targeted file imports
  `Cslib.Init`, which configures Cslib's default linting and
  tactics. Cslib's CI runs `lake exe checkInitImports`. In
  `GebLang/` and `GebTests/Lang/` the requirement is conditional on
  the file importing any `Cslib.*` module (§ Subtree import rules).
- **Local notation**: notation that could apply to multiple
  types is either locally scoped (`local notation`,
  `scoped notation`) or introduced via a typeclass — not as
  bare top-level `notation`.
- **Minimised imports**: CSLib's CI runs `lake shake` to ensure
  no unused imports. Our repo-wide pre-push and CI check (see
  `docs/rules/lean-coding.md` § Lean 4 module system) satisfies
  this for both upstream targets.
- **PR-title categories**: CSLib's PR-title types are mathlib's set
  (`docs/rules/ci-and-workflow.md` § Commit-message convention)
  minus `ci`. When filing a PR upstream to CSLib, the title's
  leading category is one of these.
- **Pre-coordination on Zulip**: cross-cutting abstractions,
  typeclasses, notation schemes, foundational frameworks, and
  major refactorings are discussed on the CSLib Zulip channel
  before significant implementation work, per CSLib's
  CONTRIBUTING.md.

CSLib's full contribution guide is linked from
`docs/rules/lean-coding.md` § Authoritative upstream guides
(CSLib).
