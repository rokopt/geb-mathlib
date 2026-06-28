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
`Geb/Cslib/`, or `GebTests/Cslib/`.

Work in the file globs this rule applies to is also bound by
[CONTRIBUTING.md § Submission policy](../../CONTRIBUTING.md),
which governs LLM-generated code in upstream-eligible content
(mandatory disclosure and line-by-line understanding).

## Authoring

For upstream-eligible subtrees, AI authoring follows
[AGENTS.md § AI authoring (upstream-eligible work)](../../AGENTS.md):
an agent may draft, and the user commits only after understanding
every line, being able to justify each design decision to
reviewers without AI, and disclosing tool use. Work under
`Geb/Internal/` is reviewed by the user at commit time without
that upstream justification bar.

## Two-track development

`Geb/Internal/` holds code that is not (yet) upstream-eligible:
work in progress not yet at mathlib/CSLib quality, explorations
that build on upstream-quality code in `Geb/Mathlib/` or
`Geb/Cslib/` without themselves meeting that bar, and code too
specialized to this project to be in scope for either upstream.
The split is driven by quality, scope, and dependency-readiness,
not by authorship: AI-drafted and human-written code follow the
same rules in every subtree.

When Internal content is later brought to upstream quality:

1. Port it into `Geb/Mathlib/Foo.lean` or `Geb/Cslib/Foo.lean`
   depending on the upstream target, satisfying the subtree
   import rules below.
2. When the upstream PR is accepted and we re-pin to a fresh
   master that includes it, migrate dependents via `jj rebase`.
   The Internal version is then removed.

## Floodgate test

At all times, the repo must be ready to ship dependency-ordered
PRs on short notice with no source-code changes. After any
non-trivial change, ask: "does this break extraction?" Each
upstream subtree's extractability is independent of the other
(the strict import rules below ensure this).

## Subtree import rules

Each upstream-eligible subtree has an allowed-import list and one or
more self-prefixes that must not appear outside `^import` lines. A
test root mirrors its source root: it additionally imports its own
`GebTests.<subtree>.*` siblings, and forbids leakage of both the
source self-prefix and the test self-prefix. Source roots cannot
import test modules.

| Subtree | Allowed imports | Self-prefixes (no leakage) |
| --- | --- | --- |
| `Geb/Mathlib/` | `Mathlib.*`, `Geb.Mathlib.*` | `Geb.Mathlib.` |
| `GebTests/Mathlib/` | `Mathlib.*`, `Geb.Mathlib.*`, `GebTests.Mathlib.*` | `Geb.Mathlib.`, `GebTests.Mathlib.` |
| `Geb/Cslib/` | `Mathlib.*`, `Cslib.*`, `Geb.Cslib.*` | `Geb.Cslib.` |
| `GebTests/Cslib/` | `Mathlib.*`, `Cslib.*`, `Geb.Cslib.*`, `GebTests.Cslib.*` | `Geb.Cslib.`, `GebTests.Cslib.` |

Bare umbrella imports (`import Mathlib`, `import Cslib`) are
forbidden — extraction requires specific module imports.

A self-prefix appears **only** in `^import` lines that
reference siblings in the same subtree. Do NOT use a self-prefix in:

- namespace declarations
  (`namespace Computability.Primrec`,
   not `namespace Geb.Mathlib.Computability.Primrec`),
- declaration bodies / fully-qualified-name references
  (use `open` or the bare name),
- docstrings or comments.

`scripts/lint-imports.sh` enforces these rules; the smoke test is
`scripts/tests/test-lint-imports.sh`.

The cross-subtree boundary follows the upstream dependency
relationship: mathlib does not depend on CSLib (so `Geb/Mathlib/`
files cannot import from `Cslib.*` or `Geb.Cslib.*`), and CSLib
depends on mathlib only through the upstream `Mathlib.*` modules
(so `Geb/Cslib/` files cannot import from `Geb.Mathlib.*` —
unupstreamed mathlib-targeted content is not yet available to a
CSLib PR). `Geb/Internal/` may import from any of the above.

## CSLib-specific constraints

CSLib's `CONTRIBUTING.md` adds the following requirements beyond
mathlib's style. Files in `Geb/Cslib/` (and `GebTests/Cslib/`):

- **Import `Cslib.Init`**: every CSLib-targeted file imports
  `Cslib.Init`, which configures CSLib's default linting and
  tactics. CSLib's CI runs `lake exe checkInitImports`.
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
