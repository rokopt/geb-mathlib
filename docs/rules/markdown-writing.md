---
paths:
  - "**/*.md"
---

# Markdown writing conventions

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Markdownlint cleanliness](#markdownlint-cleanliness)
- [Tables of contents](#tables-of-contents)
- [Link conventions](#link-conventions)
- [Prose style](#prose-style)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Applies to all `.md` files.

## Markdownlint cleanliness

Every Markdown document we author passes `markdownlint-cli2`
against `.markdownlint-cli2.jsonc` (shared with the VSCode
markdownlint extension). Machine-emitted logs that are not
authored documentation are excluded from the lint via the
`ignores` list in `.markdownlint-cli2.jsonc`.

Run `markdownlint-cli2 '**/*.md'` before each commit step that
touches Markdown.

## Tables of contents

Every committed Markdown document with more than one `##`
heading carries an auto-maintained table of contents at the top.
We use `doctoc` (`<!-- START doctoc -->` / `<!-- END doctoc -->`
markers). The pre-push checklist verifies the in-place TOCs are
up to date (`doctoc --dryrun --update-only .`, which exits
non-zero if any existing TOC would change and skips files
without markers); regenerate locally with
`doctoc --update-only .` and re-commit. To add a TOC to a file
that doesn't yet have one, run `doctoc <file>` once to insert the
markers, then commit.

## Link conventions

- Internal links use repo-relative paths
  (`[name](docs/foo.md)`), not absolute or local-machine paths.
- External links use full URLs.
- Dead-link checks are not currently automated; verify manually
  when adding links to external resources.

## Prose style

- Formal, precise, mathematical, dry, unopinionated.
- Avoid value-laden adjectives ("key", "important", "crucial",
  "elegant", "beautiful", "neat", "clever", "powerful",
  "interesting", "insight" used as labels).
- Generic user references ("the user" / "they" / "them"); no
  first names, email, or autobiographical detail. The exception
  is a designated project point of contact (e.g. the maintainer
  named for Code-of-Conduct or security reporting): a specific
  name and email are appropriate there, since they identify a
  project role rather than a contributor.

See `docs/process.md` § Style guidelines for full rationale.
