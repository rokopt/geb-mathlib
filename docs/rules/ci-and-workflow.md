---
paths:
  - ".github/workflows/**"
  - "scripts/**"
---

# CI and workflow conventions

Applies to GitHub Actions workflow files and scripts.

## Commit-message convention (mathlib-derived)

See `https://leanprover-community.github.io/contribute/commit.html`
for mathlib's full convention.

```text
<type>(<optional-scope>): <subject>

<body>

<footers>
```

Types: `feat | fix | doc | style | refactor | test | chore | perf | ci`.
Imperative present tense, no capital, no trailing period. Subject
under 72 characters when possible.

Documented footers: `Closes #123, #456`, `BREAKING CHANGE: ...`,
`- [ ] depends on: #XXXX`. Mathlib's published convention does not
include `Moves:` or `Deletions:`, so nor does ours.

## Pre-push checklist

Run by `scripts/pre-push.sh`:

1. `lake exe cache get` populates the full mathlib olean cache
   (mirroring CI's `leanprover/lean-action`), then `lake build`
   succeeds locally. The cache fetch is required because `lake
   build` alone fetches only the oleans `Geb` imports; the
   `lake shake` smoke test (item 5) injects an arbitrary mathlib
   import and needs that module's olean present, which after a
   toolchain bump it otherwise would not be.
2. `lake test` succeeds locally.
3. `lake lint` quiet.
4. `lake shake --add-public --keep-implied --keep-prefix Geb GebTests`
   quiet.
5. `scripts/tests/test-lake-shake.sh` passes.
6. `scripts/lint-imports.sh` quiet.
7. `scripts/tests/test-lint-imports.sh` passes.
8. `scripts/hooks/tests/test-block-mutating-git.sh` passes.
9. `markdownlint-cli2 '**/*.md'` quiet.
10. The axiom env_linter (`GebMeta.detectNonstandardAxiom`) runs
    under `lake lint`: `Geb` is covered by item 3's `lake lint`,
    and `GebTests` by an added `lake lint -- GebTests` step (after
    `lake build GebTests`). It fails when any declaration depends
    on an axiom outside `{propext, Quot.sound}`.
    `scripts/tests/test-axiom-linter.sh` smoke-tests the linter.
11. (PR-candidate) reminder about no-LLM-text rule for PR
    descriptions; affirmative confirmation required.
12. (Lean-content) `lean4:golf` ran on changed proofs;
    `lean4:review` ran on the diff.
13. (PR-candidate) `pr-review-toolkit:review-pr` ran.
14. User reviewed the diff line-by-line.

## Action pinning policy

All third-party actions in `.github/workflows/*.yml` are pinned to
a specific commit SHA, with the SHA followed by a comment naming
the corresponding tag for human readers. Dependabot
(`.github/dependabot.yml`) opens a pull request bumping the SHA and
its tag comment when an action publishes a new release; review the
upstream release notes before merging.
