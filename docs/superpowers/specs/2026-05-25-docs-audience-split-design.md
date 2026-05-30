# Documentation audience split

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Goal](#goal)
- [Motivation](#motivation)
- [End-state architecture](#end-state-architecture)
  - [Entry-point files](#entry-point-files)
  - [Canonical rule text under `docs/rules/`](#canonical-rule-text-under-docsrules)
  - [`.claude/rules/*.md` (symlinks + Claude-only delta files)](#clauderulesmd-symlinks--claude-only-delta-files)
  - [No subtree `AGENTS.md` files](#no-subtree-agentsmd-files)
- [Audience assignment](#audience-assignment)
  - [CONTRIBUTING.md (universal contributor rules)](#contributingmd-universal-contributor-rules)
  - [AGENTS.md (additions for all AI agents on top of CONTRIBUTING)](#agentsmd-additions-for-all-ai-agents-on-top-of-contributing)
  - [CLAUDE.md (Claude-specific deltas)](#claudemd-claude-specific-deltas)
  - [docs/rules/lean-coding.md (canonical)](#docsruleslean-codingmd-canonical)
  - [docs/rules/upstream-eligible.md (canonical)](#docsrulesupstream-eligiblemd-canonical)
  - [docs/rules/markdown-writing.md (canonical)](#docsrulesmarkdown-writingmd-canonical)
  - [docs/rules/ci-and-workflow.md (canonical)](#docsrulesci-and-workflowmd-canonical)
  - [.claude/rules/ (post-reorg)](#clauderules-post-reorg)
- [Suggested entry-point outlines](#suggested-entry-point-outlines)
  - [CONTRIBUTING.md outline](#contributingmd-outline)
  - [AGENTS.md outline](#agentsmd-outline)
  - [CLAUDE.md outline](#claudemd-outline)
  - [Audience-narrowing-preface template](#audience-narrowing-preface-template)
- [Touchpoints on existing files](#touchpoints-on-existing-files)
- [Non-goals](#non-goals)
- [Implementation approach](#implementation-approach)
- [Verification](#verification)
- [References](#references)

<!-- END doctoc -->

## Goal

Redistribute existing documentation across three audience-shaped
entry-point files (`CONTRIBUTING.md`, `AGENTS.md`, `CLAUDE.md`) so
that each rule lives in the file appropriate to its audience.

The total committed rule content does not change. Only its
distribution, cross-references, and the audience-narrowing
prefaces of the new entry files change.

## Motivation

Most of the project's process and coding rules apply to every
contributor (human, Claude, or another AI tool), but the current
layout puts the bulk of them in Claude-specific locations
(`CLAUDE.md`, `.claude/rules/*.md`). A contributor working
without Claude is given no obvious place to find the rules that
bind their work; a contributor using a non-Claude AI tool has no
manifest that the tool would read by convention.

The fix is to separate audience from canonical text:

- Canonical, audience-agnostic rule text lives in `docs/rules/`.
- Each entry-point file (`CONTRIBUTING.md`, `AGENTS.md`,
  `CLAUDE.md`) declares its audience and references the rules
  that bind that audience.
- The `.claude/rules/*.md` path-scoped loader keeps its Claude
  Code-specific YAML `paths:` mechanism but delegates rule text
  to `docs/rules/` via filesystem symlinks (which Claude Code
  explicitly supports in `.claude/rules/`, per
  `https://code.claude.com/docs/en/memory#share-rules-across-projects-with-symlinks`).

`AGENTS.md` is the convention documented at `https://agents.md/`
for AI coding tools that read it by default. The convention is
not a normative schema (the canonical page describes the format
as "simply standard Markdown that different coding agents can
parse" with "no required fields"); in particular, no `@`-prefix
import directive is defined. An open discussion of whether to
add one is at `https://github.com/agentsmd/agents.md/issues/11`.
The convention is stewarded by the Agentic AI Foundation under
the Linux Foundation (per agents.md/'s own about text).

## End-state architecture

### Entry-point files

```text
CONTRIBUTING.md   humans (standalone; no import directives; lists
                  docs/rules/ as binding; cross-references
                  AGENTS.md / CLAUDE.md for AI-assisted contribution)

AGENTS.md         AI agents in general (pure AGENTS-convention
                  markdown; inlines its own agent-specific rules;
                  uses prose pointers to docs/rules/<topic>.md for
                  path-scoped universal rules; uses a prose pointer
                  to CONTRIBUTING.md for the universal contributor
                  rules; carries no @import directives, since the
                  AGENTS.md convention defines none)

CLAUDE.md         Claude specifically (short; @imports both
                  AGENTS.md and CONTRIBUTING.md directly; inlines
                  Claude-only deltas)
```

Loading at Claude Code session start: `CLAUDE.md` loads, which
`@imports` both `AGENTS.md` and `CONTRIBUTING.md` as separate
first-hop imports (no recursion through AGENTS.md, since
recursion would require an `@import` inside AGENTS.md and that
directive is not part of the AGENTS.md convention — see
`https://github.com/agentsmd/agents.md/issues/11`). The session
sees the always-on rule set with no duplication. Expected size
growth over the current 217-line `CLAUDE.md` is modest (added
entry-point structure: audience prefaces, References sections);
the enforceable bound is in the Verification section.

Claude additionally loads `.claude/rules/<topic>.md` (which is a
symlink to `docs/rules/<topic>.md`) when its path glob fires, and
loads any Claude-only delta file (e.g. `.claude/rules/lean-coding-claude.md`)
that shares the same path glob. The total post-expansion context
budget grows by the size of one path-scoped file pair per
matching file edit.

For non-Claude AI tools that read `AGENTS.md` natively, the
session sees: (1) the agent-specific rules inlined; (2) a prose
pointer to `CONTRIBUTING.md` ("Every contributor is also bound
by [CONTRIBUTING.md](CONTRIBUTING.md); read it before reading
the rest of this file") near the top of AGENTS.md; (3) prose
pointers ("See [docs/rules/lean-coding.md](docs/rules/lean-coding.md)")
for the path-scoped rule files. Tools that follow markdown links
(near-universal capability) reach `CONTRIBUTING.md` and the
per-topic rule files directly. Tools that do not follow links
are bound only by what is literally in `AGENTS.md`; this is a
known reduction in fidelity for those tools and applies to both
the universal rules in `CONTRIBUTING.md` and the path-scoped
rules in `docs/rules/`.

For human contributors, `CONTRIBUTING.md` is the entry point;
the rules in `docs/rules/` bind them and are linked from
`CONTRIBUTING.md`.

### Canonical rule text under `docs/rules/`

```text
docs/
  index.md          (existing)
  process.md        (existing — references updated)
  references.md     (existing)
  rules/
    lean-coding.md
    upstream-eligible.md
    markdown-writing.md
    ci-and-workflow.md
  superpowers/      (existing)
```

Each `docs/rules/<topic>.md` carries YAML `paths:` frontmatter
documenting which file globs the rule applies to. All four
current `.claude/rules/<topic>.md` files already have `paths:`
frontmatter; the symlink moves preserve it. Humans reading the
file see the frontmatter as metadata (it documents the rule's
scope); non-Claude AI tools ignore it; Claude Code reads it via
the symlink described below.

### `.claude/rules/*.md` (symlinks + Claude-only delta files)

Each `.claude/rules/<topic>.md` is a filesystem symlink to
`../../docs/rules/<topic>.md`. The `paths:` frontmatter in the
target file drives Claude Code's path-scoped loading.

Where a topic has Claude-only additions, they live in a sibling
file `.claude/rules/<topic>-claude.md` with the same `paths:`
glob. Both files load when the glob matches; the canonical rule
text and the Claude-only delta enter context together.

Post-reorg layout of `.claude/rules/`:

```text
.claude/rules/
  lean-coding.md         (symlink -> ../../docs/rules/lean-coding.md)
  lean-coding-claude.md  (Claude-only: lean4 sub-skill mapping;
                          Claude-tool notes for Lake / build)
  upstream-eligible.md   (symlink -> ../../docs/rules/upstream-eligible.md)
  markdown-writing.md    (symlink -> ../../docs/rules/markdown-writing.md)
  ci-and-workflow.md     (symlink -> ../../docs/rules/ci-and-workflow.md)
  ci-and-workflow-claude.md (Claude-only: hook-script conventions)
```

### No subtree `AGENTS.md` files

Path-scoping is expressed as subsections inside the root
`AGENTS.md` ("## When editing .lean files",
"## When editing files under Geb/Mathlib/ or Geb/Cslib/"). This
is a deliberate design choice: nested `AGENTS.md` files (which
the convention at `https://agents.md/` supports as its
recommended monorepo pattern) would each require either inlining
the shared rule text or chasing the only-nearest semantic with
imports. A single root file with path-scoped subsections is
simpler to keep in sync, matches the existing
`docs/rules/<topic>.md` decomposition one-to-one, and defers the
subtree-fan-out option until friction arises.

## Audience assignment

Each section below lists every rule statement in the source
files that the listed audience inherits. Implicit defaults are
not used; every section of every source file is named.

### CONTRIBUTING.md (universal contributor rules)

Sourced from `CLAUDE.md`:

- `§ Project status` — full content.
- `§ Rules` — LLM-contribution policy; no LLM-drafted text in
  mathlib-facing channels; one concern per branch; generic user
  references; code is cost / reuse process code / reuse
  abstractions / avoid the ad-hoc; cite the literature; document
  only the persistent.
- `§ Rules` — the one-line `No noncomputable; minimise Classical`
  bullet (the operationalization stays in `docs/rules/lean-coding.md`;
  the policy bullet is repeated here because the policy is
  project-wide, not Lean-coding-specific).
- `§ Phase-driven workflow` — the "Each phase produces an
  artifact" sentence (this is process binding every contributor,
  not skill-specific).
- `§ Repo structure (one-line)` — full content.
- `§ Style guidelines` — full content, including avoid
  colloquialisms.
- `§ sorry, admit, and underscores` — policy statements (the
  Lean-specific operationalization stays in
  `docs/rules/lean-coding.md`).
- `§ Specs and plans live on the feature branch` — full content.
- `§ Floodgate test` — full content.
- `§ Tooling` — full content, excluding the Skills line.
- `§ References` — adapted to point at the new fan-out.
- `§ sorry, admit, and underscores` — a one-line cross-reference
  ("Lean placeholder syntax: see docs/rules/lean-coding.md §
  sorry, admit, and underscores."). The full text moves to
  `docs/rules/lean-coding.md`.

Sourced from `README.md`:

- `§ Contributing` — Setup and Working subsections move here; the
  `§ Contributing` section of `README.md` becomes a one-line
  pointer.

### AGENTS.md (additions for all AI agents on top of CONTRIBUTING)

Sourced from `CLAUDE.md`:

- `§ Rules` — no `jj git push` without user line-by-line review.
- `§ Phase-driven workflow` — adversarial review of specs and
  plans (as a principle, with the re-fetch-the-upstream-guides
  instruction moved with it); verify agent claims against
  authoritative sources (principle).

Sourced from `.claude/rules/upstream-eligible.md`:

- `§ Authoring modes` — table rows (a) and (b).
- `§ Credentialing-PR checkpoint` — the agent-asks-user phrasing.

`AGENTS.md` additionally carries the path-scoped manifest
(per-topic prose pointer to `docs/rules/<topic>.md`) and a
prose pointer to `CONTRIBUTING.md` near the top. It does not
carry an `@import` directive: the AGENTS.md convention defines
none, and Claude's loading of `CONTRIBUTING.md` is handled
directly by an `@CONTRIBUTING.md` import in `CLAUDE.md` itself,
not by recursion through `AGENTS.md`.

### CLAUDE.md (Claude-specific deltas)

Top of file: `@AGENTS.md` and `@CONTRIBUTING.md`, on separate
lines, so each is a first-hop import (no reliance on recursion
through AGENTS.md).

Sourced from `CLAUDE.md`:

- `§ Rules` — no raw mutating `git` subcommands (PreToolUse hook
  is Claude-specific).
- `§ Rules` — `.remember/*.md` markdownlint discipline.
- `§ Phase-driven workflow` — the always-on skill table.
- `§ Phase-driven workflow` — the pointer to
  `lean4` sub-skill mapping (updated to point at
  `.claude/rules/lean-coding-claude.md`).
- `§ Tooling` — the Skills line.
- `§ When to consider creating a project-specific skill` — full
  content.
- `§ References` — adapted to point at the new fan-out.

### docs/rules/lean-coding.md (canonical)

Sourced from `.claude/rules/lean-coding.md`:

- `§ Authoritative upstream guides (mathlib)` — full content
  (this becomes the canonical home; the duplicate URL list in
  the current `CLAUDE.md § Mathlib upstream guides` is removed
  from `CLAUDE.md` since the cross-reference is sufficient).
- `§ Authoritative upstream guides (CSLib)` — full content; the
  cross-pointer to `.claude/rules/upstream-eligible.md § CSLib-specific
  constraints` becomes `docs/rules/upstream-eligible.md § CSLib-specific
  constraints`.
- `§ Comment and docstring rules` — full content. (Note: this
  section overlaps with the `§ Documentation` subsection of the
  upstream-guides digest. The overlap is preserved as-is; a
  follow-on branch may deduplicate per the one-concern-per-branch
  rule.)
- `§ Lean 4 module system` — full content.
- `§ Lake / build workflow` — the lake build / lake test / lake
  clean / lake env lean rules (the bash-process-substitution and
  Write-tool notes are Claude-tool-specific and move to
  `.claude/rules/lean-coding-claude.md`).
- `§ Coding technique` — full content (constructive-only, proof
  guidelines, higher-order constructions, one step at a time,
  structure and typeclass patterns).

Sections from `.claude/rules/lean-coding.md` *not* sourced here
(they move to `.claude/rules/lean-coding-claude.md` as the
Claude-only delta): `§ lean4 sub-skill mapping`; the
bash-process-substitution and Write-tool notes inside `§ Lake /
build workflow`. These are enumerated explicitly so the
"every section of every source file is named" discipline at the
top of this audience-assignment section is satisfied.

Sourced from `CLAUDE.md`:

- `§ Constructive-only Lean code` — full content (the project-wide
  one-line policy statement remains in `CONTRIBUTING.md`; the
  Lean-specific operationalization lives here).
- `§ sorry, admit, and underscores` — full content moves here
  (all three bullets reference Lean syntax — `sorry`, `admit`,
  `_` — so the split between "policy" and "operationalization"
  is artificial; the whole section is Lean-specific and lives
  here). `CONTRIBUTING.md` carries a one-line cross-reference
  ("Lean placeholder syntax: see docs/rules/lean-coding.md §
  sorry, admit, and underscores."). The "while working with
  skills that need it" clause is restated tool-agnostically as
  "while working with a development tool that requires
  placeholders during proof development" (Non-goals exception 3).

### docs/rules/upstream-eligible.md (canonical)

Sourced from `.claude/rules/upstream-eligible.md`, all sections
except the explicitly-extracted ones:

- `§ Authoring modes` — the current file has a two-row table
  (modes (a) and (b)) plus a parenthetical sentence describing
  mode (c). The post-reorg `docs/rules/upstream-eligible.md §
  Authoring modes` is restructured to a three-row table (modes
  (a), (b), (c)) with mode-(c) row content derived from the
  current parenthetical; rows (a) and (b) move to AGENTS.md.
  Mode (c) is described in `docs/process.md § Two-track
  development` as part of this reorganization (the current
  process.md describes the two-track Internal-vs-upstream split
  in Track-1/Track-2 language without naming mode (c)
  explicitly; the addition is a one-sentence parenthetical
  naming mode (c) as the AI-authoring posture for Track 1).
- `§ Two-track development` — full content. The duplication with
  `docs/process.md § Two-track development` is preserved as-is
  (the `docs/process.md` entry is rationale; the rule file
  states the procedure).
- `§ Credentialing-PR checkpoint` — the user-weighing factors
  remain here as canonical content; the agent-asks-user phrasing
  moves to AGENTS.md.
- `§ Floodgate test` — full content. The duplication with
  `CONTRIBUTING.md § Floodgate test` is preserved as-is (the
  `CONTRIBUTING.md` entry is the project-wide policy; the rule
  file states the per-edit application).
- `§ Subtree import rules` — full content.
- `§ CSLib-specific constraints` — full content; the
  cross-pointer to `.claude/rules/lean-coding.md § Lean 4
  module system` becomes `docs/rules/lean-coding.md § Lean 4
  module system`.

LLM-contribution policy is not duplicated here; the canonical
statement is in `CONTRIBUTING.md`. A one-line cross-reference
to `CONTRIBUTING.md § LLM-contribution policy` is added at the
top of `docs/rules/upstream-eligible.md` because the policy
specifically binds work in subtrees this file is path-scoped to.

### docs/rules/markdown-writing.md (canonical)

Sourced from `.claude/rules/markdown-writing.md`: full content
verbatim (including the existing `paths: ["**/*.md"]`
frontmatter). No Claude-only delta exists.

Note: this file's `§ Prose style` subsection (formal/precise/dry;
avoid value-laden adjectives; generic user references) overlaps
the style block that moves to `CONTRIBUTING.md § Style and
references`. This overlap is preserved as-is (see Non-goals
preserved-overlaps list).

### docs/rules/ci-and-workflow.md (canonical)

Sourced from `.claude/rules/ci-and-workflow.md`:

- `§ Commit-message convention (mathlib-derived)` — full content,
  plus a one-line cross-reference added to the upstream guide:
  "See `https://leanprover-community.github.io/contribute/commit.html`
  for mathlib's full convention." This preserves the
  "binding for commit messages" claim currently in `CLAUDE.md §
  Mathlib upstream guides` (which is removed by Non-goals
  exception 4); see Non-goals exception 7.
- `§ Pre-push checklist` — full content.
- `§ Action pinning policy` — full content.

The `§ Hook-script conventions` section is Claude-specific and
moves to `.claude/rules/ci-and-workflow-claude.md`.

### .claude/rules/ (post-reorg)

- `lean-coding.md` — symlink to `../../docs/rules/lean-coding.md`.
- `lean-coding-claude.md` — Claude-only delta. `paths:` matches
  `**/*.lean`. Contents: `## lean4 sub-skill mapping` (table from
  `.claude/rules/lean-coding.md`); `## Lake / build workflow,
  Claude-tool notes` (bash process substitution warning, Write
  tool guidance).
- `upstream-eligible.md` — symlink to
  `../../docs/rules/upstream-eligible.md`. No Claude-only delta
  file.
- `markdown-writing.md` — symlink to
  `../../docs/rules/markdown-writing.md`. No Claude-only delta
  file.
- `ci-and-workflow.md` — symlink to
  `../../docs/rules/ci-and-workflow.md`.
- `ci-and-workflow-claude.md` — Claude-only delta. `paths:`
  matches `.github/workflows/**` and `scripts/**`. Contents:
  `## Hook-script conventions` (Claude Code's hook contract).

## Suggested entry-point outlines

These outlines define the heading structure of the new files so
two implementers would produce the same file. Wording inside
each subsection follows the audience-narrowing-preface template
below.

### CONTRIBUTING.md outline

Heading-name gloss in parentheses maps each new subsection to
the rules under it (so two implementers produce the same file):

```text
# Contributing to geb-mathlib
## Audience
## Project status
## Setup
## Working
## Rules
  ### Concern shape
    (one concern per branch; specs and plans on feature branch)
  ### Code is cost
    (code is cost; reuse process code; reuse abstractions;
     avoid the ad-hoc; document only the persistent)
  ### Submission policy
    (LLM-contribution policy; no LLM-drafted user-facing text;
     cite the literature)
  ### Style and references
    (generic user references; style guidelines including avoid
     colloquialisms; pointer to docs/rules/markdown-writing.md)
  ### Constructive-only
    (one-line: no noncomputable; minimise Classical; pointer to
     docs/rules/lean-coding.md for operationalization)
  ### Floodgate test
    (full text from CLAUDE.md § Floodgate test)
  ### Each phase produces an artifact
    (single sentence from CLAUDE.md § Phase-driven workflow)
## Repo structure
## Tooling
## References
```

### AGENTS.md outline

Each `### When editing ...` subsection under
`## Path-scoped rules` is exactly one paragraph: a single
sentence of intent stating which kinds of edits are covered,
followed by the prose pointer `See [docs/rules/<topic>.md](docs/rules/<topic>.md)`
for the full text. No rule body is inlined under these
subsections.

```text
# AGENTS.md
## Audience
(prose pointer: "Every contributor is also bound by
 [CONTRIBUTING.md](CONTRIBUTING.md); read it before reading the
 rest of this file." No @import directive — the AGENTS.md
 convention does not define one.)
## Agent-specific rules
  ### No `jj git push` without user line-by-line review
    (full text from CLAUDE.md § Rules bullet)
  ### Adversarial review of specs and plans
    (principle extracted from CLAUDE.md § Phase-driven workflow,
     including the re-fetch-the-upstream-guides instruction)
  ### Verify agent claims
    (principle extracted from CLAUDE.md § Phase-driven workflow)
  ### AI authoring modes (for upstream-eligible work)
    (rows (a) and (b) of the modes table from
     .claude/rules/upstream-eligible.md, kept in table format
     per Non-goals exception 6)
  ### Credentialing-PR checkpoint (agent behavior)
    (agent-asks-user phrasing from
     .claude/rules/upstream-eligible.md § Credentialing-PR
     checkpoint)
## Path-scoped rules
  ### When editing .lean files
    (one sentence + pointer to docs/rules/lean-coding.md)
  ### When editing files under Geb/Mathlib/ or Geb/Cslib/
    (one sentence + pointer to docs/rules/upstream-eligible.md)
  ### When editing .md files
    (one sentence + pointer to docs/rules/markdown-writing.md)
  ### When editing files under scripts/ or .github/workflows/
    (one sentence + pointer to docs/rules/ci-and-workflow.md)
## References
```

### CLAUDE.md outline

`CLAUDE.md` is produced by extracting the universal and
agent-general content out of the current file (leaving the
Claude-specific sections in place at their current heading
level), then making four small edits: delete the duplicate
`## Mathlib upstream guides` section; replace the project-intro
paragraph with a `## Audience` preface carrying the two
`@import` directives; update `## References`; update the
`lean4` sub-skill pointer's path. The surviving sections are
not reorganized or reheadered — reorganizing content that is
already correct would add review burden and diff-envelope noise
without benefit.

The `## Audience` section carries both `@import` directives.
Anthropic's memory documentation describes imports as "expanded
and loaded into context at launch alongside the CLAUDE.md that
references them" (`https://code.claude.com/docs/en/memory` §
Import additional files); the docs do not explicitly state
position-independence of the import directive, but session-start
expansion implies the placement of the import lines is a
readability concern for human readers rather than a load-order
concern for Claude.

Resulting structure (surviving sections shown at their existing
heading level):

```text
# geb-mathlib
## Audience            (new; preface + @AGENTS.md + @CONTRIBUTING.md)
## Rules               (two surviving Claude-specific bullets)
## Phase-driven workflow   (skill table + lean4 pointer)
## Tooling             (Skills line)
## When to consider creating a project-specific skill
## References          (updated to the new fan-out)
```

### Audience-narrowing-preface template

Each entry-point file's `## Audience` section follows this
template (one paragraph; substitute audience and cross-references):

> This file binds `{audience}`. The rules below supplement
> `{parent-files}`, which apply unconditionally. `{sibling-files}`
> add further rules for `{sibling-audience}`.

(Curly braces denote placeholders; markdown angle-bracket
parsers would consume `<…>` as inline HTML.)

For `CONTRIBUTING.md`: audience = "every contributor"; parent =
"(none — this is the top-level contributor file)"; siblings =
"AGENTS.md, CLAUDE.md".

For `AGENTS.md`: audience = "AI coding agents in general";
parent = "CONTRIBUTING.md"; siblings = "CLAUDE.md".

For `CLAUDE.md`: audience = "Claude Code"; parent =
"CONTRIBUTING.md, AGENTS.md"; siblings = "(none)".

## Touchpoints on existing files

- `README.md § Process`: the current per-file enumeration (which
  lists `CLAUDE.md` and each `.claude/rules/*.md` file) is
  replaced by a brief enumeration of the new fan-out
  (`CONTRIBUTING.md`, `AGENTS.md`, `CLAUDE.md`, `docs/rules/`).
- `README.md § Contributing`: becomes a one-line pointer to
  `CONTRIBUTING.md` (the Setup and Working subsections move to
  `CONTRIBUTING.md`).
- `TODO.md`: the `Project-specific geb-development skill`
  trigger updates its rule-locations list to enumerate the new
  fan-out: `CONTRIBUTING.md`, `AGENTS.md`, `CLAUDE.md`,
  `docs/process.md`, `docs/rules/*.md`, `.claude/rules/*.md`.
- `docs/process.md`: the opening sentence ("This document
  records *why* each rule in `CLAUDE.md` and `.claude/rules/*.md`
  exists") updates to enumerate the new entry-point files.
  Cross-references in the body (at lines 3-4, 105, 120, 201 of
  the current file) update accordingly. The `§ Two-track
  development` section is extended to describe mode (c) so the
  cross-pointer from `docs/rules/upstream-eligible.md` resolves.
- `scripts/` and `.github/workflows/`: verified to not reference
  `CLAUDE.md`, `.claude/rules`, or any of the moved-from
  locations by name. No changes needed.
- The `See also .claude/rules/markdown-writing.md` pointer in
  the current `CLAUDE.md § Style guidelines` becomes
  `See also docs/rules/markdown-writing.md` (carried into
  `CONTRIBUTING.md § Style and references`).

## Non-goals

- No rule content changes. Permitted rewording is limited to:
  (1) cross-reference path updates;
  (2) audience-narrowing prefaces in the new entry files
  (per the template above);
  (3) making one specific clause tool-agnostic — the "while
  working with skills that need it" clause in the `sorry, admit,
  and underscores` rule restates as "while working with a
  development tool that requires placeholders during proof
  development";
  (4) removing the duplicate `Mathlib upstream guides` URL list
  from `CLAUDE.md` since the canonical list lives in
  `docs/rules/lean-coding.md`;
  (5) one-sentence parenthetical added to `docs/process.md §
  Two-track development` naming mode (c) as the AI-authoring
  posture for Track 1 (per § Audience assignment, mode-(c)
  description fix);
  (6) structural reformatting of the Authoring-modes block: the
  current parenthetical sentence describing mode (c) in
  `.claude/rules/upstream-eligible.md § Authoring modes` is
  promoted to a third table row in
  `docs/rules/upstream-eligible.md § Authoring modes`; rows (a)
  and (b) move to `AGENTS.md § AI authoring modes` as a
  two-row table (matching the source's table format, so the
  byte-level diff-envelope check sees only relocation, not
  format change);
  (7) adding a one-line cross-reference to the upstream commit-
  message guide URL inside `docs/rules/ci-and-workflow.md §
  Commit-message convention` ("See
  `https://leanprover-community.github.io/contribute/commit.html`
  for mathlib's full convention."), preserving the
  "binding for commit messages" claim currently in `CLAUDE.md §
  Mathlib upstream guides` that is removed by exception (4).
  Any rewording beyond these seven categories is out of scope
  and blocks the diff-envelope check in the Verification section.
- No skill changes.
- No CI changes.
- No `lake` / build / Lean code changes.
- No introduction of per-subtree `AGENTS.md` files.
- No introduction of architecture decision records, journal
  directories, or other new doc-tree extensions.
- No deduplication of the existing overlaps inside the rule
  files (Comment-and-docstring rules overlap with Documentation
  subsection of upstream-guides digest; Two-track development
  appears in both rule file and process.md; Floodgate test
  appears in both CONTRIBUTING.md and upstream-eligible.md;
  `markdown-writing.md § Prose style` overlaps with
  `CONTRIBUTING.md § Style and references`). These predate this
  branch; the one-concern-per-branch rule reserves them for
  follow-on work.
- New deliberate cross-listings (not deduplication candidates):
  (i) `No LLM-drafted text in mathlib-facing channels` lives
  canonically in `CONTRIBUTING.md` (the rule frames a
  contribution policy that binds humans-who-use-AI as well as
  agents) AND is mirrored in `AGENTS.md` with an enforcement
  line because the rule is among the most-binding for AI agents
  and inlining maximizes fidelity for non-Claude tools that do
  not follow markdown links to `CONTRIBUTING.md`.
  (ii) `LLM-contribution policy` lives canonically in
  `CONTRIBUTING.md` and is referenced from
  `AGENTS.md` with a one-line cross-reference for the same
  reason.
  These cross-listings are deliberate preserved overlaps and
  are accepted by the Verification "no new duplications" check
  on the same basis as the predating overlaps above.

## Implementation approach

Commits are kept small and have one job each. Two commit shapes:

1. **Move-or-symlink commits**: relocate a file (or create a
   symlink) and update every cross-reference. No content edits
   beyond the path update. Each such commit is reviewable by
   checking that the set of file moves matches the set of
   reference updates.
2. **Chunk-move commits**: lift a single rule block (or a small
   related group of rule blocks) from its current home to its
   new home. No path-rename, no other content edits.

Destination files are created as empty skeletons (audience
preface, heading structure per the outlines, no rule content)
in dedicated scaffolding commits before any topic-move commit
extracts content into them. This avoids any state in which a
chunk has left its old home but has no destination file ready
to receive it; every topic-move commit operates between files
that already exist.

Commit-message type: `doc` for all commits in this series.
`.claude/rules/` is documentation (markdown) even though Claude
Code uses it as configuration; `chore` is reserved for
non-documentation maintenance.

A possible commit ordering follows. The order may be revised at
plan-writing time; the principle is that earlier commits should
unblock later commits without leaving intermediate states in
which the rule set is incomplete.

1. **Scaffolding**: create skeletons of `CONTRIBUTING.md`,
   `AGENTS.md`, `.claude/rules/lean-coding-claude.md`, and
   `.claude/rules/ci-and-workflow-claude.md`. Each skeleton has
   its audience preface and heading structure per the outlines,
   no rule content yet. The two Claude-only delta skeletons
   carry their `paths:` frontmatter. (`docs/rules/` is not
   created here — an empty directory is not a trackable
   artifact; it comes into existence in the first topic move.)
2. **markdown-writing**: move `.claude/rules/markdown-writing.md`
   to `docs/rules/markdown-writing.md` (the file already carries
   `paths: ["**/*.md"]` frontmatter; the move preserves it).
   Add the symlink `.claude/rules/markdown-writing.md ->
   ../../docs/rules/markdown-writing.md`. Update all
   cross-references. (Simplest topic, no Claude-only delta.)
3. **upstream-eligible**: move `.claude/rules/upstream-eligible.md`
   to `docs/rules/upstream-eligible.md`, restructuring the
   Authoring-modes section per Non-goals exception 6 (three-row
   table with mode-(c) row promoted from the current
   parenthetical); add symlink. Extract the AGENTS.md-bound
   chunks (authoring-modes rows (a)/(b); credentialing-PR
   checkpoint's agent-asks-user phrasing) directly into the
   `AGENTS.md` skeleton's `### AI authoring modes` and
   `### Credentialing-PR checkpoint` subsections. Update all
   cross-references.
4. **ci-and-workflow**: move `.claude/rules/ci-and-workflow.md`
   to `docs/rules/ci-and-workflow.md`; add symlink. Extract
   `§ Hook-script conventions` directly into
   `.claude/rules/ci-and-workflow-claude.md`. Update all
   cross-references.
5. **lean-coding**: move `.claude/rules/lean-coding.md` to
   `docs/rules/lean-coding.md`; add symlink. Extract `lean4`
   sub-skill mapping and Lake-Claude-tool notes directly into
   `.claude/rules/lean-coding-claude.md`. Update all
   cross-references.
6. **CONTRIBUTING.md content**: extract universal rules from
   `CLAUDE.md` and `README.md § Contributing` into the
   `CONTRIBUTING.md` skeleton, per the audience-assignment
   inventory. "Extract" means deleting from the source files as
   the content is added to CONTRIBUTING.md (not copying); the
   source files end up missing the extracted sections. Cross-
   reference updates in other files are deferred to step 9.
7. **AGENTS.md content (from CLAUDE.md)**: extract remaining
   agent-general rules from `CLAUDE.md` (no `jj git push`;
   adversarial review principle; verify agent claims principle)
   into the `AGENTS.md` skeleton. Same extract-don't-copy
   semantics as step 6. Add the path-scoped manifest sections
   (one-sentence + prose pointer to each
   `docs/rules/<topic>.md`). Cross-reference updates deferred
   to step 9.
8. **CLAUDE.md rewrite**: after steps 6 and 7, `CLAUDE.md` has
   had universal and agent-general rules removed and retains
   only Claude-specific sections (plus stale framing text from
   the old structure). This step rewrites the remnant into the
   thin Claude-specific form per the outline: `## Audience`
   preface; `@AGENTS.md` and `@CONTRIBUTING.md` near the top
   on separate lines as first-hop imports; retained
   Claude-only sections.
9. **Touchpoints and cross-references**: update `README.md`,
   `TODO.md`, and `docs/process.md` so every cross-reference
   to a now-relocated rule points at its new home. Add the
   one-sentence mode-(c) parenthetical to `docs/process.md §
   Two-track development` (Non-goals exception 5). Add the
   one-line upstream-commit-message-URL cross-reference to
   `docs/rules/ci-and-workflow.md § Commit-message convention`
   (Non-goals exception 7) — this is in `docs/rules/` rather
   than in a touchpoint file but is grouped here because it
   is a single-line content addition, not a section move.
10. **Verification**: run `scripts/pre-push.sh` (which subsumes
    `markdownlint-cli2` and `doctoc --dryrun --update-only .`).
    Adversarial-review the resulting tree.

## Verification

The reorganization is correct when, after the final commit:

- Every rule statement present in `CLAUDE.md` or
  `.claude/rules/*.md` before the reorganization is present in
  its assigned new home, and at most one canonical home (the
  preserved overlaps listed in Non-goals are accepted; no new
  duplications are introduced).
- The three entry-point files form a clean chain: a reader
  starting from any of them can reach every rule that binds
  their audience by following the cross-references or
  `@import` directives.
- `scripts/pre-push.sh` succeeds end to end (which covers
  `markdownlint-cli2`, the `doctoc --dryrun --update-only .`
  check, `lake build`, `lake test`, the lint scripts, and the
  axiom check).
- The post-reorg always-on context (the bytes of
  `CONTRIBUTING.md` + `AGENTS.md` + `CLAUDE.md` after `@import`
  expansion) does not exceed twice the size of the current
  `CLAUDE.md` (217 lines). This is a one-time, post-implementation
  check.
- The diff-envelope check: concatenate
  `(CONTRIBUTING.md, AGENTS.md, CLAUDE.md, docs/rules/*.md,
  .claude/rules/*-claude.md)` (the `.claude/rules/*.md` symlinks
  resolve to `docs/rules/*.md`, which would be double-counted;
  exclude them from the concatenation) and compare against the
  pre-reorg concatenation of `(CLAUDE.md, .claude/rules/*.md,
  the moved subsections of README.md, the moved subsections of
  docs/process.md)`. Apply `markdownlint-cli2 --fix` to both
  sets before comparing so the diff is invariant under whitespace,
  list-marker, and blank-line normalization. The post-normalization
  diff should be empty modulo the seven Non-goals exceptions
  ((a)-(g) below correspond one-to-one to Non-goals exceptions
  (1)-(7)) plus the cross-listings:
  (a) cross-reference path updates; (b) audience-narrowing
  prefaces per the template; (c) the one tool-agnostic
  rewording in the `sorry, admit, and underscores` rule;
  (d) the removal of the duplicate `Mathlib upstream guides`
  URL list from `CLAUDE.md`; (e) the one-sentence mode-(c)
  parenthetical in `docs/process.md § Two-track development`;
  (f) the structural reformatting of the Authoring-modes block
  (parenthetical mode-(c) sentence promoted to a third table row
  in `docs/rules/upstream-eligible.md`; rows (a) and (b) migrated
  to `AGENTS.md § AI authoring modes` as a two-row table);
  (g) the one-line cross-reference to
  `https://leanprover-community.github.io/contribute/commit.html`
  added to `docs/rules/ci-and-workflow.md § Commit-message
  convention`;
  (h) the deliberate cross-listings in `AGENTS.md` enumerated
  in the Non-goals "deliberate cross-listings" subsection: the
  enforcement-line mirror of the No-LLM-drafted-text rule and
  the one-line cross-reference to the LLM-contribution policy.

## References

- AGENTS.md convention: `https://agents.md/`.
- Claude Code memory and `.claude/rules/`:
  `https://code.claude.com/docs/en/memory`.
- Mathlib contribution conventions:
  `https://leanprover-community.github.io/contribute/index.html`.
- Project rules currently at `CLAUDE.md` and
  `.claude/rules/*.md`.
- Project rationale at `docs/process.md`.
