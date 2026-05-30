# Documentation audience split implementation plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [File structure (target end-state)](#file-structure-target-end-state)
- [Workflow notes (read before starting)](#workflow-notes-read-before-starting)
- [Task 0: Commit the plan](#task-0-commit-the-plan)
- [Task 1: Scaffolding commit](#task-1-scaffolding-commit)
- [Task 2: Move markdown-writing.md to docs/rules/](#task-2-move-markdown-writingmd-to-docsrules)
- [Task 3: Move upstream-eligible.md with table restructure and AGENTS.md extractions](#task-3-move-upstream-eligiblemd-with-table-restructure-and-agentsmd-extractions)
- [Task 4: Move ci-and-workflow.md with hook extraction and commit-URL addition](#task-4-move-ci-and-workflowmd-with-hook-extraction-and-commit-url-addition)
- [Task 5: Move lean-coding.md with skill-mapping and Lake-tool extractions](#task-5-move-lean-codingmd-with-skill-mapping-and-lake-tool-extractions)
- [Task 6: Extract universal rules from CLAUDE.md and README.md into CONTRIBUTING.md](#task-6-extract-universal-rules-from-claudemd-and-readmemd-into-contributingmd)
- [Task 7: Extract agent-general rules into AGENTS.md, add manifest](#task-7-extract-agent-general-rules-into-agentsmd-add-manifest)
- [Task 8: Reduce CLAUDE.md to Claude-specific deltas](#task-8-reduce-claudemd-to-claude-specific-deltas)
- [Task 9: Touchpoints and cross-references](#task-9-touchpoints-and-cross-references)
- [Task 10: Verification](#task-10-verification)
- [Done](#done)

<!-- END doctoc -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Redistribute existing documentation across three
audience-shaped entry-point files (`CONTRIBUTING.md`,
`AGENTS.md`, `CLAUDE.md`) with canonical rule text under
`docs/rules/` and `.claude/rules/` symlinks plus Claude-only
delta files. No rule content changes beyond the seven Non-goals
exceptions in the spec.

**Architecture:** `CLAUDE.md` `@imports` both `AGENTS.md` and
`CONTRIBUTING.md` directly. `AGENTS.md` carries no `@import`
(the AGENTS.md convention defines none) and uses prose pointers
to `CONTRIBUTING.md` and `docs/rules/<topic>.md`. Each
`.claude/rules/<topic>.md` is a filesystem symlink to
`../../docs/rules/<topic>.md`. Path-scoped Claude-only deltas
live in `.claude/rules/<topic>-claude.md` siblings.

**Tech Stack:** `jj` v0.41+ (colocated mode), `markdownlint-cli2`,
`doctoc`, `lake` (for the final verification only). No Lean
source changes.

**Spec reference:**
`docs/superpowers/specs/2026-05-25-docs-audience-split-design.md`.
Read it before starting; the audience-assignment section is the
authoritative inventory of what moves where.

---

## File structure (target end-state)

Files created (new):

- `CONTRIBUTING.md` (repo root) — universal contributor rules.
- `AGENTS.md` (repo root) — AI-agent rules; no `@import`.
- `docs/rules/` directory.
- `docs/rules/lean-coding.md` — canonical lean-coding rules.
- `docs/rules/upstream-eligible.md` — canonical upstream-eligible
  rules.
- `docs/rules/markdown-writing.md` — canonical markdown-writing
  rules.
- `docs/rules/ci-and-workflow.md` — canonical CI/workflow rules.
- `.claude/rules/lean-coding-claude.md` — Claude-only delta
  (lean4 sub-skill mapping; bash-process-substitution and
  Write-tool notes from Lake / build workflow).
- `.claude/rules/ci-and-workflow-claude.md` — Claude-only delta
  (Hook-script conventions).

Files becoming symlinks (replacing regular files):

- `.claude/rules/lean-coding.md` → `../../docs/rules/lean-coding.md`.
- `.claude/rules/upstream-eligible.md` → `../../docs/rules/upstream-eligible.md`.
- `.claude/rules/markdown-writing.md` → `../../docs/rules/markdown-writing.md`.
- `.claude/rules/ci-and-workflow.md` → `../../docs/rules/ci-and-workflow.md`.

Files modified:

- `CLAUDE.md` — rewritten to thin Claude-specific form.
- `README.md` — `§ Process` and `§ Contributing` updated.
- `TODO.md` — `Project-specific geb-development skill` trigger
  updated.
- `docs/process.md` — opening sentence + cross-references updated;
  mode-(c) parenthetical added to `§ Two-track development`.

Files NOT touched: `Geb/`, `GebTests/`, `Geb.lean`, `GebTests.lean`,
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `LICENSE`,
`scripts/`, `.github/workflows/`, `docs/index.md`,
`docs/references.md`, `docs/superpowers/specs/`,
`docs/superpowers/runbooks/`.

---

## Workflow notes (read before starting)

- All commits are made via `jj`. Each task ends with `jj describe`
  to set the message and (where relevant) `jj new` to start a
  fresh child commit for the next task.
- We are on bookmark `doc/audience-split`. Each task's commit
  advances the bookmark via `jj bookmark set doc/audience-split -r @`
  (run inside the task's final step).
- After each file edit, run `markdownlint-cli2 <path>` on the
  changed files to catch lint errors immediately. The final
  task (Task 10) runs the full `scripts/pre-push.sh` end-to-end.
- Commit-message type for every task: `doc`. No
  process-history in commit message bodies (no "iteration N",
  "round N", "after review", etc.) — see
  `docs/process.md § Document only the persistent` and the
  `feedback_commit_messages.md` auto-memory.
- The spec's seven Non-goals exceptions enumerate every
  permitted rewording. Anything else is out of scope and blocks
  the diff-envelope check in Task 10.
- **Resumability within a task**: if a step fails after a partial
  edit, fix in place and re-run subsequent steps in the same
  `jj` change. Do not `jj describe` until the task is complete.
  If a task must be abandoned, `jj abandon @` discards the
  in-progress change; the previous task's commit (set by
  `jj describe` then advanced by `jj new`) is preserved.
- The plan file itself
  (`docs/superpowers/plans/2026-05-27-docs-audience-split.md`)
  must be committed before Task 1 begins (in a commit between
  the spec commit and Task 1's commit). The plan-commit step
  is described below as "Task 0".

---

## Task 0: Commit the plan

**Goal:** Commit this plan file on `doc/audience-split` between
the spec commit and Task 1's commit. (This task exists because
the plan was written in the placeholder child commit created
after the spec commit; before Task 1 begins, the plan must
itself be a tracked commit.)

- [ ] **Step 1: Verify the plan file is the only change in the
  working copy**

```bash
jj status
```

Expected: `docs/superpowers/plans/2026-05-27-docs-audience-split.md`
is the only `A` (added) file; no other modifications.

- [ ] **Step 2: Describe and advance**

```bash
jj describe -m "$(cat <<'EOF'
doc: add audience-split implementation plan

Specify task-by-task execution of the documentation
audience-split spec: scaffolding, four topic moves with
extractions, CONTRIBUTING.md and AGENTS.md content
populations, CLAUDE.md rewrite, and touchpoint updates.

Each task produces one commit on bookmark doc/audience-split.
EOF
)"
jj bookmark set doc/audience-split -r @
jj new
```

---

## Task 1: Scaffolding commit

**Goal:** Create skeletons of every destination file
(CONTRIBUTING.md, AGENTS.md, and the two Claude-only delta
files): audience prefaces and heading structure, no rule
content.

**Files:**

- Create: `CONTRIBUTING.md`
- Create: `AGENTS.md`
- Create: `.claude/rules/lean-coding-claude.md`
- Create: `.claude/rules/ci-and-workflow-claude.md`

- [ ] **Step 1: Verify clean working copy after Task 0**

```bash
jj status
jj log -r '@ | trunk()' --no-graph -T 'change_id.short() ++ " " ++ bookmarks ++ " | " ++ description.first_line() ++ "\n"'
```

Expected: working copy is empty; parent is the plan commit
(Task 0) on bookmark `doc/audience-split`; the spec commit is
the parent of that. If the working copy has stray changes,
investigate before proceeding.

- [ ] **Step 2: Create `CONTRIBUTING.md` skeleton**

Use the audience-narrowing preface template from the spec. The
file's content is the heading structure with the audience-preface
filled in; rule subsections under `## Rules` are empty (one-line
"populated in subsequent tasks" placeholders are NOT permitted
per the spec's no-placeholder rule — leave the subsections as
just headings).

Write file `CONTRIBUTING.md`:

```markdown
# Contributing to geb-mathlib

<!-- START doctoc -->
<!-- END doctoc -->

## Audience

This file binds every contributor (human or AI). It is the
top-level contributor document; the rules in `docs/rules/`
also bind every contributor for the file globs documented
in each rule's `paths:` frontmatter. `AGENTS.md` and
`CLAUDE.md` add further rules for AI-assisted contribution
and for Claude Code specifically.

## Project status

## Setup

## Working

## Rules

### Concern shape

### Code is cost

### Submission policy

### Style and references

### Constructive-only

### Floodgate test

### Each phase produces an artifact

## Repo structure

## Tooling

## References
```

- [ ] **Step 3: Create `AGENTS.md` skeleton**

Write file `AGENTS.md`:

```markdown
# AGENTS.md

<!-- START doctoc -->
<!-- END doctoc -->

## Audience

This file binds AI coding agents in general. The rules below
supplement `CONTRIBUTING.md`, which applies unconditionally.
`CLAUDE.md` adds further rules for Claude Code specifically.

Every contributor is also bound by
[CONTRIBUTING.md](CONTRIBUTING.md); read it before reading the
rest of this file.

## Agent-specific rules

### No `jj git push` without user line-by-line review

### Adversarial review of specs and plans

### Verify agent claims

### AI authoring modes (for upstream-eligible work)

### Credentialing-PR checkpoint (agent behavior)

## Path-scoped rules

### When editing .lean files

### When editing files under Geb/Mathlib/ or Geb/Cslib/

### When editing .md files

### When editing files under scripts/ or .github/workflows/

## References
```

- [ ] **Step 4: Create `.claude/rules/lean-coding-claude.md` skeleton**

Write file `.claude/rules/lean-coding-claude.md`:

```markdown
---
paths:
  - "**/*.lean"
---

# Lean coding — Claude-only additions

Applies whenever a `.lean` file is open or being edited.
Additions specific to Claude Code, on top of the canonical
`docs/rules/lean-coding.md`.

## lean4 sub-skill mapping

## Lake / build workflow — Claude-tool notes
```

- [ ] **Step 5: Create `.claude/rules/ci-and-workflow-claude.md` skeleton**

Write file `.claude/rules/ci-and-workflow-claude.md`:

```markdown
---
paths:
  - ".github/workflows/**"
  - "scripts/**"
---

# CI and workflow — Claude-only additions

Applies to GitHub Actions workflow files and scripts. Additions
specific to Claude Code, on top of the canonical
`docs/rules/ci-and-workflow.md`.

## Hook-script conventions
```

- [ ] **Step 6: Run markdownlint on the new files**

```bash
markdownlint-cli2 CONTRIBUTING.md AGENTS.md .claude/rules/lean-coding-claude.md .claude/rules/ci-and-workflow-claude.md
```

Expected: no errors on these files. If errors appear, fix
inline before commit.

- [ ] **Step 7: Run doctoc on files with multiple `##` headings**

```bash
doctoc --update-only CONTRIBUTING.md AGENTS.md
```

Expected: TOCs populated in both files. Note: at this point the
skeletons have empty `##` and `###` sections (no body content
yet); the TOC anchors point at empty section bodies. This is
expected behaviour for the scaffolding commit; subsequent tasks
populate the section bodies and doctoc reruns will refresh the
TOC.

- [ ] **Step 8: Verify with markdownlint after doctoc**

```bash
markdownlint-cli2 CONTRIBUTING.md AGENTS.md
```

Expected: still no errors.

- [ ] **Step 9: Commit**

```bash
jj describe -m "$(cat <<'EOF'
doc: scaffold CONTRIBUTING.md, AGENTS.md, and Claude-only delta files

Create skeletons of the new entry-point files (CONTRIBUTING.md,
AGENTS.md) and the Claude-only delta files
(.claude/rules/lean-coding-claude.md,
.claude/rules/ci-and-workflow-claude.md) with audience prefaces
and heading structure.
EOF
)"
jj bookmark set doc/audience-split -r @
jj new
```

---

## Task 2: Move markdown-writing.md to docs/rules/

**Goal:** Move `.claude/rules/markdown-writing.md` to
`docs/rules/markdown-writing.md` and replace `.claude/rules/markdown-writing.md`
with a symlink. Update all cross-references throughout the
project.

**Files:**

- Move: `.claude/rules/markdown-writing.md` →
  `docs/rules/markdown-writing.md`
- Create symlink: `.claude/rules/markdown-writing.md` →
  `../../docs/rules/markdown-writing.md`
- Cross-reference updates: any file mentioning
  `.claude/rules/markdown-writing.md` updates to
  `docs/rules/markdown-writing.md`.

- [ ] **Step 1: Inventory cross-references**

```bash
grep -rn '\.claude/rules/markdown-writing\.md' --include='*.md' --include='*.sh' --include='*.yml' .
```

Record the paths and line numbers. Expected hits include
`CLAUDE.md`, `README.md`, `docs/process.md`. (No hits in
`scripts/` or `.github/workflows/` per spec § Touchpoints; if
hits appear there, flag for the user before proceeding.)

- [ ] **Step 2: Move the file**

```bash
mkdir -p docs/rules
mv .claude/rules/markdown-writing.md docs/rules/markdown-writing.md
jj diff --summary
```

Verify:

```bash
ls -la .claude/rules/markdown-writing.md docs/rules/markdown-writing.md 2>&1
```

Expected: `docs/rules/markdown-writing.md` exists;
`.claude/rules/markdown-writing.md` no longer exists.

- [ ] **Step 3: Create the symlink**

```bash
ln -s ../../docs/rules/markdown-writing.md .claude/rules/markdown-writing.md
```

Verify:

```bash
ls -la .claude/rules/markdown-writing.md
readlink .claude/rules/markdown-writing.md
```

Expected: symlink pointing at `../../docs/rules/markdown-writing.md`.

- [ ] **Step 4: Update cross-references**

For each hit from Step 1, edit the file to replace
`.claude/rules/markdown-writing.md` with
`docs/rules/markdown-writing.md`. Use `Edit` tool, not sed, so
each change is reviewable.

- [ ] **Step 5: Run markdownlint on touched files**

```bash
markdownlint-cli2 docs/rules/markdown-writing.md $(grep -lrn 'docs/rules/markdown-writing\.md' --include='*.md' .)
```

Expected: no errors.

- [ ] **Step 6: Commit**

```bash
jj describe -m "$(cat <<'EOF'
doc: move markdown-writing rules to docs/rules/

Move .claude/rules/markdown-writing.md to docs/rules/ as the
canonical home; replace the .claude/rules/ entry with a symlink
so Claude Code's path-scoped loader continues to find it.

Update cross-references throughout the project.
EOF
)"
jj bookmark set doc/audience-split -r @
jj new
```

---

## Task 3: Move upstream-eligible.md with table restructure and AGENTS.md extractions

**Goal:** Move `.claude/rules/upstream-eligible.md` to
`docs/rules/upstream-eligible.md` with the Authoring-modes
section restructured to a three-row table; extract rows (a)/(b)
and the agent-asks-user phrasing of the credentialing-PR
checkpoint into the AGENTS.md skeleton.

**Files:**

- Move: `.claude/rules/upstream-eligible.md` →
  `docs/rules/upstream-eligible.md`
- Create symlink: `.claude/rules/upstream-eligible.md` →
  `../../docs/rules/upstream-eligible.md`
- Modify: `docs/rules/upstream-eligible.md` — restructure
  Authoring-modes table (Non-goals exception 6); add LLM-policy
  cross-reference at top; update cross-pointer to
  lean-coding.md.
- Modify: `AGENTS.md` — populate `### AI authoring modes` with
  rows (a)/(b) two-row table; populate
  `### Credentialing-PR checkpoint (agent behavior)` with the
  agent-asks-user phrasing.

- [ ] **Step 1: Inventory cross-references**

```bash
grep -rn '\.claude/rules/upstream-eligible\.md' --include='*.md' --include='*.sh' --include='*.yml' .
```

- [ ] **Step 2: Move the file via `jj`**

```bash
mv .claude/rules/upstream-eligible.md docs/rules/upstream-eligible.md
jj diff --summary
```

- [ ] **Step 3: Create the symlink**

```bash
ln -s ../../docs/rules/upstream-eligible.md .claude/rules/upstream-eligible.md
```

- [ ] **Step 4: Restructure the Authoring-modes section**

Read `docs/rules/upstream-eligible.md` to confirm current
structure. The current section has a two-row table (modes (a)
and (b)) plus a parenthetical sentence about mode (c).

Edit the file: expand the table to three rows. The parenthetical
sentence becomes the source content for the mode-(c) row. The
parenthetical itself is removed (its content is now in the
table).

Current table (will be replaced):

```markdown
| Authoring mode | Triggered by | AI agent may | User must |
| --- | --- | --- | --- |
| (a) User-driven | Credentialing-PR candidate | Suggest in natural language only | Write every line |
| (b) Co-authoring | Other upstream-eligible work | Draft provisional code | Read, rewrite, commit when fully understood |

(Mode (c), hands-off draft by AI agent + commit-time review, applies under
`Geb/Internal/` and is described in `docs/process.md`.)
```

Replace with:

```markdown
| Authoring mode | Triggered by | AI agent may | User must |
| --- | --- | --- | --- |
| (a) User-driven | Credentialing-PR candidate | Suggest in natural language only | Write every line |
| (b) Co-authoring | Other upstream-eligible work | Draft provisional code | Read, rewrite, commit when fully understood |
| (c) Hands-off draft | Work under `Geb/Internal/` | Draft autonomously | Review at commit time; described in `docs/process.md § Two-track development` |
```

- [ ] **Step 5: Update the CSLib cross-pointer**

The current text at `.claude/rules/upstream-eligible.md` (now
moved to `docs/rules/upstream-eligible.md`) ends `§ CSLib-specific
constraints` with: "`.claude/rules/lean-coding.md § Lean 4 module
system`". Replace `.claude/rules/` with `docs/rules/` in that
pointer.

- [ ] **Step 6: Add LLM-policy cross-reference at top**

Add a one-line cross-reference near the top of
`docs/rules/upstream-eligible.md` (after the file's main heading
and any audience preface), before the first major section:

```markdown
Work in the file globs this rule applies to is bound by
[CONTRIBUTING.md § LLM-contribution policy](../../CONTRIBUTING.md)
(LLM-generated code restrictions on upstream-eligible content).
```

- [ ] **Step 7: Extract AGENTS.md-bound chunks**

Cut from `docs/rules/upstream-eligible.md`:

- The full `### AI authoring modes` subsection content (the
  table) — but keep mode (c) row in the file; move only the
  (a) and (b) rows to AGENTS.md.
- The agent-asks-user phrasing inside `§ Credentialing-PR
  checkpoint` (the sentence "Before starting any work in
  `Geb/Mathlib/` or `Geb/Cslib/` whose only dependencies are
  the targeted upstream (i.e., a true PR-candidate with no
  in-flight geb-mathlib deps), the AI agent asks: 'Is this the
  credentialing PR for this upstream?'").

Paste into `AGENTS.md`:

Under `### AI authoring modes (for upstream-eligible work)`,
insert the two-row table:

```markdown
| Authoring mode | Triggered by | AI agent may | User must |
| --- | --- | --- | --- |
| (a) User-driven | Credentialing-PR candidate | Suggest in natural language only | Write every line |
| (b) Co-authoring | Other upstream-eligible work | Draft provisional code | Read, rewrite, commit when fully understood |
```

Under `### Credentialing-PR checkpoint (agent behavior)`, insert
the agent-asks-user sentence verbatim.

After cutting, the `docs/rules/upstream-eligible.md § Authoring
modes` section retains only the mode-(c) row in its table (which
is now a one-row table). Add a one-line cross-reference at the
top of that section pointing at AGENTS.md for modes (a) and (b):

```markdown
Modes (a) and (b) apply to AI-agent contributions and live in
[AGENTS.md § AI authoring modes (for upstream-eligible work)](../../AGENTS.md).
The mode (c) row below applies to AI-agent work under
`Geb/Internal/`.
```

- [ ] **Step 8: Update other cross-references**

For each hit from Step 1, replace `.claude/rules/upstream-eligible.md`
with `docs/rules/upstream-eligible.md` in non-symlink contexts.

- [ ] **Step 9: Run markdownlint**

```bash
markdownlint-cli2 docs/rules/upstream-eligible.md AGENTS.md $(grep -lrn 'docs/rules/upstream-eligible\.md\|AGENTS\.md' --include='*.md' . | sort -u)
```

Expected: no errors.

- [ ] **Step 10: Run doctoc on AGENTS.md (TOC may need refresh)**

```bash
doctoc --update-only AGENTS.md
markdownlint-cli2 AGENTS.md
```

- [ ] **Step 11: Commit**

```bash
jj describe -m "$(cat <<'EOF'
doc: move upstream-eligible rules to docs/rules/

Move .claude/rules/upstream-eligible.md to docs/rules/ as the
canonical home; replace the .claude/rules/ entry with a
symlink.

Restructure the Authoring-modes section into a three-row table
naming mode (c) explicitly. Extract authoring-modes rows (a)
and (b) and the agent-asks-user phrasing of the credentialing-PR
checkpoint into AGENTS.md (these rules are agent-specific).

Add a cross-reference to CONTRIBUTING.md § LLM-contribution
policy at the top, since the policy specifically binds work in
the subtrees this rule applies to.
EOF
)"
jj bookmark set doc/audience-split -r @
jj new
```

---

## Task 4: Move ci-and-workflow.md with hook extraction and commit-URL addition

**Goal:** Move `.claude/rules/ci-and-workflow.md` to
`docs/rules/ci-and-workflow.md`; extract the Hook-script
conventions section into the `.claude/rules/ci-and-workflow-claude.md`
skeleton; add the one-line commit-message URL cross-reference
(Non-goals exception 7).

**Files:**

- Move: `.claude/rules/ci-and-workflow.md` →
  `docs/rules/ci-and-workflow.md`
- Create symlink: `.claude/rules/ci-and-workflow.md` →
  `../../docs/rules/ci-and-workflow.md`
- Modify: `docs/rules/ci-and-workflow.md` — remove
  `§ Hook-script conventions`; add commit-message URL
  cross-reference.
- Modify: `.claude/rules/ci-and-workflow-claude.md` — populate
  `## Hook-script conventions` with the extracted content.

- [ ] **Step 1: Inventory cross-references**

```bash
grep -rn '\.claude/rules/ci-and-workflow\.md' --include='*.md' --include='*.sh' --include='*.yml' .
```

- [ ] **Step 2: Move via `jj`**

```bash
mv .claude/rules/ci-and-workflow.md docs/rules/ci-and-workflow.md
jj diff --summary
```

- [ ] **Step 3: Create symlink**

```bash
ln -s ../../docs/rules/ci-and-workflow.md .claude/rules/ci-and-workflow.md
```

- [ ] **Step 4: Add commit-message URL cross-reference (Non-goals exception 7)**

Edit `docs/rules/ci-and-workflow.md`. At the top of `§
Commit-message convention (mathlib-derived)`, add the one-line
cross-reference:

```markdown
See `https://leanprover-community.github.io/contribute/commit.html`
for mathlib's full convention.
```

(Placed after the section heading and before the format
codeblock, so a reader sees the upstream URL first.)

- [ ] **Step 5: Extract `§ Hook-script conventions`**

Cut the `## Hook-script conventions` section (heading + body, up
to but not including the next `##` heading, which is `## Action
pinning policy`) from `docs/rules/ci-and-workflow.md`.

Paste it into `.claude/rules/ci-and-workflow-claude.md` under
the existing `## Hook-script conventions` skeleton heading
(replace the empty heading with the full extracted content).

- [ ] **Step 6: Update other cross-references**

For each hit from Step 1, replace `.claude/rules/ci-and-workflow.md`
with `docs/rules/ci-and-workflow.md`.

- [ ] **Step 7: Run markdownlint**

```bash
markdownlint-cli2 docs/rules/ci-and-workflow.md .claude/rules/ci-and-workflow-claude.md $(grep -lrn 'docs/rules/ci-and-workflow\.md' --include='*.md' . | sort -u)
```

Expected: no errors.

- [ ] **Step 8: Commit**

```bash
jj describe -m "$(cat <<'EOF'
doc: move ci-and-workflow rules to docs/rules/

Move .claude/rules/ci-and-workflow.md to docs/rules/ as the
canonical home; replace the .claude/rules/ entry with a
symlink.

Extract § Hook-script conventions into
.claude/rules/ci-and-workflow-claude.md (Claude Code's hook
contract is Claude-specific).

Add a one-line cross-reference to mathlib's upstream commit-
message convention URL at the top of § Commit-message
convention, preserving the "binding for commit messages" claim
that the move from CLAUDE.md § Mathlib upstream guides removes.
EOF
)"
jj bookmark set doc/audience-split -r @
jj new
```

---

## Task 5: Move lean-coding.md with skill-mapping and Lake-tool extractions

**Goal:** Move `.claude/rules/lean-coding.md` to
`docs/rules/lean-coding.md`; extract `§ lean4 sub-skill mapping`
and the Claude-tool notes from `§ Lake / build workflow` into
the `.claude/rules/lean-coding-claude.md` skeleton.

**Files:**

- Move: `.claude/rules/lean-coding.md` →
  `docs/rules/lean-coding.md`
- Create symlink: `.claude/rules/lean-coding.md` →
  `../../docs/rules/lean-coding.md`
- Modify: `docs/rules/lean-coding.md` — remove `§ lean4
  sub-skill mapping`; remove bash-process-substitution and
  Write-tool notes from `§ Lake / build workflow`.
- Modify: `.claude/rules/lean-coding-claude.md` — populate
  `## lean4 sub-skill mapping` and `## Lake / build workflow
  — Claude-tool notes`.

- [ ] **Step 1: Inventory cross-references**

```bash
grep -rn '\.claude/rules/lean-coding\.md' --include='*.md' --include='*.sh' --include='*.yml' .
```

- [ ] **Step 2: Move via `jj`**

```bash
mv .claude/rules/lean-coding.md docs/rules/lean-coding.md
jj diff --summary
```

- [ ] **Step 3: Create symlink**

```bash
ln -s ../../docs/rules/lean-coding.md .claude/rules/lean-coding.md
```

- [ ] **Step 4: Extract `§ lean4 sub-skill mapping`**

Cut the `## lean4 sub-skill mapping` section (heading + table, up
to but not including the next `##` heading, which is `## Lake /
build workflow`) from `docs/rules/lean-coding.md`. Paste into
`.claude/rules/lean-coding-claude.md` under the existing
`## lean4 sub-skill mapping` skeleton heading (replace empty
heading with full extracted content).

- [ ] **Step 5: Extract Claude-tool notes from `§ Lake / build workflow`**

In `docs/rules/lean-coding.md § Lake / build workflow`, identify
the two bullets that are Claude-tool-specific (see spec § docs/rules/lean-coding.md):

- The bullet about `bash` process substitution triggering manual
  approval prompts.
- The bullet about using the `Write` tool rather than shell
  commands for experimental code.

Cut these two bullets from `docs/rules/lean-coding.md § Lake /
build workflow`.

Paste them into `.claude/rules/lean-coding-claude.md` under
`## Lake / build workflow — Claude-tool notes` (replace empty
heading with the two bullets).

- [ ] **Step 6: Update other cross-references**

For each hit from Step 1, replace `.claude/rules/lean-coding.md`
with `docs/rules/lean-coding.md`.

- [ ] **Step 7: Run markdownlint**

```bash
markdownlint-cli2 docs/rules/lean-coding.md .claude/rules/lean-coding-claude.md $(grep -lrn 'docs/rules/lean-coding\.md' --include='*.md' . | sort -u)
```

Expected: no errors.

- [ ] **Step 8: Commit**

```bash
jj describe -m "$(cat <<'EOF'
doc: move lean-coding rules to docs/rules/

Move .claude/rules/lean-coding.md to docs/rules/ as the
canonical home; replace the .claude/rules/ entry with a
symlink.

Extract § lean4 sub-skill mapping (Claude-skill-specific) and
the bash-process-substitution / Write-tool bullets from § Lake
/ build workflow (Claude-tool-specific) into
.claude/rules/lean-coding-claude.md.
EOF
)"
jj bookmark set doc/audience-split -r @
jj new
```

---

## Task 6: Extract universal rules from CLAUDE.md and README.md into CONTRIBUTING.md

**Goal:** Populate the `CONTRIBUTING.md` skeleton with universal
rules per the spec's CONTRIBUTING.md inventory. Extract content
from `CLAUDE.md` (deleting as we go) and from `README.md §
Contributing` (Setup and Working subsections).

**Files:**

- Modify: `CONTRIBUTING.md` — populate sections per the
  spec inventory.
- Modify: `CLAUDE.md` — delete the extracted sections.
- Modify: `README.md` — delete the Setup and Working
  subsections from `§ Contributing`; replace with a one-line
  pointer.

Cross-reference updates in OTHER files are deferred to Task 9.

- [ ] **Step 1: Re-read the spec's CONTRIBUTING.md inventory**

Open
`docs/superpowers/specs/2026-05-25-docs-audience-split-design.md
§ Audience assignment > § CONTRIBUTING.md (universal contributor
rules)` and confirm the full list of sourced sections. The
inventory enumerates: § Project status, § Rules (LLM-contribution
policy; no LLM-drafted text; one concern per branch; generic
user references; code-is-cost cluster; cite the literature;
document only the persistent), § Rules one-line constructive
bullet, § Phase-driven workflow "Each phase produces an artifact"
sentence, § Repo structure (one-line), § Style guidelines, §
sorry/admit/underscores one-line cross-reference, § Specs and
plans live on the feature branch, § Floodgate test, § Tooling
(excluding Skills line), § References (adapted), and README.md
Setup and Working.

- [ ] **Step 2: Move § Project status to `CONTRIBUTING.md`**

Cut `## Project status` (heading + body, up to but not including
the next `##` heading, which is `## Rules`) from `CLAUDE.md`.
Paste into `CONTRIBUTING.md § Project status` (replace the empty
heading).

- [ ] **Step 3: Move universal § Rules bullets to `CONTRIBUTING.md`**

The current `CLAUDE.md § Rules` is a single bullet list. Enumerate
each bullet by its exact bold-headed name and destination:

- `**LLM-contribution policy**` (multi-paragraph) → MOVE to
  `CONTRIBUTING.md § Rules § Submission policy`.
- `**No \`jj git push\` without user line-by-line review.**` →
  DO NOT MOVE (Task 7 moves this to AGENTS.md).
- `**No LLM-drafted text in mathlib-facing channels.**` →
  MOVE to `CONTRIBUTING.md § Rules § Submission policy`.
- `**No raw mutating \`git\` subcommands.**` (including the
  PreToolUse-hook explanation) → DO NOT MOVE (stays in
  CLAUDE.md per spec — Claude-tool-specific).
- `**One concern per branch.**` → MOVE to
  `CONTRIBUTING.md § Rules § Concern shape`.
- `**Generic user references in committed text.**` → MOVE to
  `CONTRIBUTING.md § Rules § Style and references`.
- `**No \`noncomputable\` anywhere; minimise \`Classical\`.**`
  (the one-line policy bullet) → MOVE to `CONTRIBUTING.md §
  Rules § Constructive-only`.
- `**Code is cost.**` → MOVE to `CONTRIBUTING.md § Rules § Code
  is cost`.
- `**Reuse existing process code.**` → MOVE to
  `CONTRIBUTING.md § Rules § Code is cost`.
- `**Reuse existing abstractions.**` → MOVE to
  `CONTRIBUTING.md § Rules § Code is cost`.
- `**Avoid the ad-hoc.**` → MOVE to `CONTRIBUTING.md § Rules §
  Code is cost`.
- `**Cite the literature when transcribing.**` → MOVE to
  `CONTRIBUTING.md § Rules § Submission policy`.
- `**Document only the persistent.**` → MOVE to
  `CONTRIBUTING.md § Rules § Code is cost`.
- `` `.remember/*.md` must be markdownlint-clean ... `` (the
  unboldhead bullet about .remember/) → DO NOT MOVE (stays in
  CLAUDE.md per spec — .remember/ is Claude-plugin-specific).

For each MOVE bullet: cut the bullet from `CLAUDE.md § Rules`
and paste under the named CONTRIBUTING.md subsection. Preserve
the bullet's body text verbatim including any cross-references
to `docs/process.md`.

For each bullet to be moved, cut from CLAUDE.md and paste into
`CONTRIBUTING.md § Rules` under the appropriate subsection per
the spec's outline glosses:

- § Concern shape: one concern per branch; specs and plans on
  feature branch (the latter from Step 8 below).
- § Code is cost: code is cost; reuse process code; reuse
  abstractions; avoid the ad-hoc; document only the persistent.
- § Submission policy: LLM-contribution policy; no LLM-drafted
  user-facing text; cite the literature.
- § Style and references: generic user references; (style
  guidelines from Step 6 below).
- § Constructive-only: one-line no-noncomputable bullet
  (operationalization in `docs/rules/lean-coding.md`).
- § Floodgate test: (from Step 9 below).
- § Each phase produces an artifact: (from Step 5 below).

- [ ] **Step 4: Move § Repo structure to `CONTRIBUTING.md`**

In current `CLAUDE.md`, the section is `## Repo structure
(one-line)`. Cut the heading and body from `CLAUDE.md`; paste
under `CONTRIBUTING.md § Repo structure` (the "(one-line)"
qualifier is dropped — the CONTRIBUTING.md skeleton uses just
`## Repo structure`, treating the qualifier as a label drift
under cross-reference-path-update permission per Non-goals
exception 1).

- [ ] **Step 5: Move "Each phase produces an artifact" sentence**

The current `CLAUDE.md § Phase-driven workflow`, immediately
after the skill-mapping table and the `lean4` sub-skill pointer,
contains this paragraph (quoted exactly):

> Each phase produces an artifact. Specs and plans are
> adversarially-reviewed before execution begins (see
> `docs/process.md` § Adversarial review). Verify agent claims
> against authoritative sources before committing them to
> artifacts; include citations.

Three sentence-destinations:

- "Each phase produces an artifact." → MOVE to `CONTRIBUTING.md
  § Rules § Each phase produces an artifact` (this step).
- "Specs and plans are adversarially-reviewed before execution
  begins (see `docs/process.md` § Adversarial review)." → MOVE
  to `AGENTS.md § Agent-specific rules § Adversarial review of
  specs and plans` (Task 7).
- "Verify agent claims against authoritative sources before
  committing them to artifacts; include citations." → MOVE to
  `AGENTS.md § Agent-specific rules § Verify agent claims`
  (Task 7).

This step (Task 6 Step 5) moves ONLY the first sentence.

The skill-mapping table and the `lean4` sub-skill pointer stay
in CLAUDE.md per the CLAUDE.md inventory.

- [ ] **Step 6: Move § Style guidelines to `CONTRIBUTING.md`**

Cut `## Style guidelines` (heading + body, up to but not
including the next `##` heading, which is `## Mathlib upstream
guides` — note: the "Avoid colloquialisms and metaphors" paragraph
is part of `§ Style guidelines`'s body) from `CLAUDE.md`. Paste
into
`CONTRIBUTING.md § Rules > § Style and references`. Update the
existing `See also .claude/rules/markdown-writing.md` pointer to
`See also docs/rules/markdown-writing.md`.

- [ ] **Step 7: Move sorry/admit/underscores section; add one-line pointer**

ONLY a one-line cross-reference goes into CONTRIBUTING.md; the
full section moves to `docs/rules/lean-coding.md` (per spec
audience-assignment line 326-334).

(a) In `CONTRIBUTING.md § Rules § Constructive-only`, append:

```markdown
Lean placeholder syntax: see
[docs/rules/lean-coding.md § sorry, admit, and underscores](docs/rules/lean-coding.md).
```

(b) Cut the entire `## sorry, admit, and underscores` section
from `CLAUDE.md` (heading and body, up to but not including the
next `##` heading, which is `## Specs and plans live on the
feature branch`). Paste into `docs/rules/lean-coding.md` as a
new top-level section, restating the "while working with skills
that need it" clause as "while working with a development tool
that requires placeholders during proof development" per
Non-goals exception 3.

- [ ] **Step 8: Move § Specs and plans live on the feature branch**

Cut `## Specs and plans live on the feature branch` (heading +
body, up to but not including the next `##` heading, which is
`## Floodgate test`) from `CLAUDE.md`. Paste into `CONTRIBUTING.md
§ Rules § Concern shape`.

- [ ] **Step 9: Move § Floodgate test**

Cut `## Floodgate test` (heading + body, up to but not including
the next `##` heading, which is `## Tooling`) from `CLAUDE.md`.
Paste into `CONTRIBUTING.md § Rules § Floodgate test`.

- [ ] **Step 10: Move § Tooling (excluding Skills line)**

In `CLAUDE.md § Tooling`, identify the Skills bullet line(s)
and DO NOT MOVE it. Cut the rest of `## Tooling` (heading + the
non-Skills bullets) and paste into `CONTRIBUTING.md § Tooling`.

- [ ] **Step 11: Move README.md `§ Contributing` Setup and Working subsections**

In `README.md`, identify `## Contributing § Setup` and `## §
Working`. Cut their full content (headings + bodies). Paste into
`CONTRIBUTING.md § Setup` and `CONTRIBUTING.md § Working`.

In `README.md § Contributing`, replace the body with a one-line
pointer:

```markdown
## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md).
```

- [ ] **Step 12: Move § Constructive-only Lean code to docs/rules/lean-coding.md**

Cut `## Constructive-only Lean code` (heading + body, up to but
not including the next `##` heading; after Step 7 cut `##
sorry, admit, and underscores`, the next `##` is `## Specs and
plans live on the feature branch`) from `CLAUDE.md`. Paste
into `docs/rules/lean-coding.md` as a new top-level `##
Constructive-only Lean code` section, parallel to the existing
top-level sections (`## Authoritative upstream guides (mathlib)`,
etc.).

Note: `docs/rules/lean-coding.md` already contains a `###
Constructive-only` subsection under `## Coding technique`
(inherited from the move in Task 5). The new top-level
`## Constructive-only Lean code` section is preserved
alongside it as a separate, deliberately-overlapping section
(the CLAUDE.md content discusses the `scripts/check-axioms.sh`
tooling specifically, while the existing subsection discusses
`Quotient.out` / `Quot.out` constructive avoidance). The
overlap is preserved-as-is, like other overlaps listed in
the spec's Non-goals preserved-overlaps subsection.

- [ ] **Step 13: Populate `CONTRIBUTING.md § References`**

Replace the empty `## References` section in CONTRIBUTING.md
with a reference list adapted to the new fan-out:

```markdown
## References

- [docs/rules/](docs/rules/) — path-scoped rule files binding
  every contributor for the file globs in each rule's `paths:`
  frontmatter.
- [docs/process.md](docs/process.md) — rationale for every rule.
- [docs/references.md](docs/references.md) — Lean library and
  mathematical reference catalog.
- [docs/index.md](docs/index.md) — implemented mathematical
  content in topological order.
- [AGENTS.md](AGENTS.md), [CLAUDE.md](CLAUDE.md) — additional
  rules for AI-assisted contribution.
```

- [ ] **Step 14: Run markdownlint and doctoc**

```bash
doctoc --update-only CONTRIBUTING.md CLAUDE.md README.md
markdownlint-cli2 CONTRIBUTING.md CLAUDE.md README.md docs/rules/lean-coding.md
```

Expected: no errors.

- [ ] **Step 15: Commit**

```bash
jj describe -m "$(cat <<'EOF'
doc: move universal contributor rules into CONTRIBUTING.md

Extract universal contributor rules from CLAUDE.md and the
Setup/Working subsections from README.md § Contributing into
CONTRIBUTING.md. Replace README.md § Contributing with a
one-line pointer to CONTRIBUTING.md.

Move the § sorry, admit, and underscores section and the §
Constructive-only Lean code section to docs/rules/lean-coding.md
as their canonical home (CONTRIBUTING.md carries a one-line
cross-reference for the former).

Cross-reference updates in other files are deferred to a later
commit.
EOF
)"
jj bookmark set doc/audience-split -r @
jj new
```

---

## Task 7: Extract agent-general rules into AGENTS.md, add manifest

**Goal:** Populate the `AGENTS.md` skeleton with agent-general
rules per the spec's AGENTS.md inventory, plus the path-scoped
manifest sections (one-sentence + prose pointer per topic) and
the cross-listings (No-LLM-drafted-text enforcement line;
LLM-contribution-policy cross-reference).

**Files:**

- Modify: `CLAUDE.md` — delete extracted sections.
- Modify: `AGENTS.md` — populate Agent-specific rules and
  Path-scoped rules sections.

Cross-reference updates in OTHER files are deferred to Task 9.

- [ ] **Step 1: Move "No `jj git push` without user review" bullet**

Cut the bullet from `CLAUDE.md § Rules` and paste into
`AGENTS.md § Agent-specific rules > § No jj git push without
user line-by-line review` (replace empty heading with bullet
content).

- [ ] **Step 2: Move adversarial-review principle**

After Task 6 Step 5 moved "Each phase produces an artifact" out,
the current `CLAUDE.md § Phase-driven workflow` paragraph reads
(quoted exactly):

> Specs and plans are adversarially-reviewed before execution
> begins (see `docs/process.md` § Adversarial review). Verify
> agent claims against authoritative sources before committing
> them to artifacts; include citations.

Cut the first sentence ("Specs and plans are adversarially-
reviewed before execution begins (see `docs/process.md` §
Adversarial review).") and paste under `AGENTS.md § Agent-
specific rules § Adversarial review of specs and plans`.

Also move the re-fetch-the-upstream-guides instruction from the
current `CLAUDE.md § Mathlib upstream guides` (the sentence
"Re-fetch the guides on every adversarial-review round; they
are subject to upstream revision.") into the same AGENTS.md
subsection. (Per spec § Audience assignment: "the re-fetch-the-
upstream-guides instruction moved with it".)

- [ ] **Step 3: Move verify-agent-claims principle**

Cut the second sentence ("Verify agent claims against
authoritative sources before committing them to artifacts;
include citations.") from `CLAUDE.md § Phase-driven workflow`
and paste under `AGENTS.md § Agent-specific rules § Verify
agent claims`.

- [ ] **Step 4: Populate path-scoped manifest sections**

For each `### When editing ...` subsection under `## Path-scoped
rules` in `AGENTS.md`, insert one sentence of intent followed by
a prose pointer. Suggested text:

```markdown
### When editing .lean files

Lean style, naming, docstring, and module-system rules bind
every .lean file in this repository.
See [docs/rules/lean-coding.md](docs/rules/lean-coding.md) for
the full text.

### When editing files under Geb/Mathlib/ or Geb/Cslib/

Additional upstream-eligibility rules apply (import rules,
authoring modes, subtree boundaries).
See [docs/rules/upstream-eligible.md](docs/rules/upstream-eligible.md)
for the full text.

### When editing .md files

Markdown-writing conventions (markdownlint, TOC, link
conventions, prose style) bind every committed .md file.
See [docs/rules/markdown-writing.md](docs/rules/markdown-writing.md)
for the full text.

### When editing files under scripts/ or .github/workflows/

CI and workflow conventions (commit-message format, pre-push
checklist, action pinning) apply to scripts and workflow files.
See [docs/rules/ci-and-workflow.md](docs/rules/ci-and-workflow.md)
for the full text.
```

- [ ] **Step 5: Add cross-listings (Non-goals "deliberate cross-listings" subsection)**

Per the spec's Non-goals subsection on deliberate cross-listings,
add to AGENTS.md:

(i) An enforcement line for the No-LLM-drafted-text rule. Insert
under a new subsection in `## Agent-specific rules` (or as a
trailing note in the audience preface):

```markdown
### No LLM-drafted text in mathlib-facing channels (enforcement)

Do not draft PR descriptions, Zulip messages, or GitHub
issue/PR comments. These are user-authored per
[CONTRIBUTING.md § Submission policy](CONTRIBUTING.md).
```

(ii) A one-line cross-reference to the LLM-contribution policy
(suggested placement: near the top of `## Agent-specific rules`
or in the audience preface):

```markdown
Work in upstream-eligible subtrees is governed by
[CONTRIBUTING.md § Submission policy](CONTRIBUTING.md), which
restricts LLM-generated code.
```

- [ ] **Step 6: Populate `AGENTS.md § References`**

```markdown
## References

- [CONTRIBUTING.md](CONTRIBUTING.md) — universal contributor
  rules.
- [docs/rules/](docs/rules/) — path-scoped rule files binding
  every contributor for the file globs in each rule's `paths:`
  frontmatter.
- [docs/process.md](docs/process.md) — rationale for every rule.
- [CLAUDE.md](CLAUDE.md) — Claude-specific additions on top of
  this file.
```

- [ ] **Step 7: Run markdownlint and doctoc**

```bash
doctoc --update-only AGENTS.md CLAUDE.md
markdownlint-cli2 AGENTS.md CLAUDE.md
```

Expected: no errors.

- [ ] **Step 8: Commit**

```bash
jj describe -m "$(cat <<'EOF'
doc: move agent-general rules into AGENTS.md

Extract agent-general rules from CLAUDE.md (no jj git push
without user review; adversarial review of specs and plans
principle; verify agent claims principle) into AGENTS.md.

Populate § Path-scoped rules with per-topic prose pointers to
the corresponding docs/rules/<topic>.md files; populate the
deliberate cross-listings (No-LLM-drafted-text enforcement
line; LLM-contribution-policy cross-reference).

Cross-reference updates in other files are deferred to a later
commit.
EOF
)"
jj bookmark set doc/audience-split -r @
jj new
```

---

## Task 8: Reduce CLAUDE.md to Claude-specific deltas

**Goal:** After Tasks 6–7 extracted universal and agent-general
content, `CLAUDE.md` is a partially-emptied file whose surviving
sections are already correct and in place. This task makes four
small edits — it does NOT reorganize or reheader the surviving
sections (they stay at their current heading level). Each step
is an independent, small diff.

**Files:**

- Modify: `CLAUDE.md`.

- [ ] **Step 1: Confirm the post-extraction state of `CLAUDE.md`**

```bash
cat CLAUDE.md
```

Expected surviving content (in original order):

- `# geb-mathlib` title + intro paragraph (intro edited in
  Step 3).
- `## Rules` — only two bullets survive: the bullet about no
  raw mutating `git` (with its PreToolUse hook), and the
  `.remember/*.md` markdownlint bullet. All other bullets are
  absent (moved in Task 6/7).
- `## Phase-driven workflow` — skill table and the `lean4`
  sub-skill pointer survive; the "Each phase produces an
  artifact / adversarially-reviewed / Verify agent claims"
  sentences are absent (moved in Task 6/7).
- `## Mathlib upstream guides` — still present in full (deleted
  in Step 2 below). Note: the "Re-fetch the guides ..." sentence
  was already moved to AGENTS.md in Task 7, so it is absent from
  this section by now.
- `## Tooling` — only the Skills bullet survives.
- `## When to consider creating a project-specific skill` —
  present in full.
- `## References` — present (updated in Step 5 below).

If any section that should be absent is still present, return
to Task 6 / Task 7 and fix before proceeding.

- [ ] **Step 2: Delete `## Mathlib upstream guides`**

Cut the entire `## Mathlib upstream guides` section (heading +
body, up to but not including the next `##` heading) from
`CLAUDE.md`. Per Non-goals exception 4, the canonical URL list
lives in `docs/rules/lean-coding.md § Authoritative upstream
guides (mathlib)`; no replacement pointer is needed in
`CLAUDE.md` (the path-scoped rule loads it when editing `.lean`
files, and `AGENTS.md § When editing .lean files` points to it).

- [ ] **Step 3: Replace the intro paragraph with an Audience preface**

The current intro paragraph reads:

> A Lean 4 + mathlib formalisation of Geb. See `README.md` for
> the project's identity and `docs/process.md` for the rationale
> behind each rule below.

It is project front-matter ("the rationale behind each rule
below") that no longer fits — most rules have moved out. Replace
the paragraph (keep the `# geb-mathlib` H1) with:

```markdown
## Audience

This file binds Claude Code. It supplements
[CONTRIBUTING.md](CONTRIBUTING.md) and [AGENTS.md](AGENTS.md),
which apply to every contributor and every AI agent
respectively; the rules below are the Claude-specific additions.

@AGENTS.md
@CONTRIBUTING.md
```

The `@AGENTS.md` and `@CONTRIBUTING.md` lines are first-hop
imports (AGENTS.md carries no `@import` of its own; CLAUDE.md
imports both directly).

- [ ] **Step 4: Update the `lean4` sub-skill pointer's path**

In the surviving `## Phase-driven workflow` section, the pointer
currently reads "lives in `.claude/rules/lean-coding.md` §
`lean4` sub-skill mapping". The `lean4` sub-skill mapping moved
to the Claude-only delta file in Task 5, so update the path to
`.claude/rules/lean-coding-claude.md` (cross-reference-path
update, Non-goals exception 1).

- [ ] **Step 5: Update `## References`**

The current `## References` enumerates `docs/process.md`,
`docs/references.md`, and the `.claude/rules/` files. Replace
its body with the new fan-out:

```markdown
## References

- [CONTRIBUTING.md](CONTRIBUTING.md) — universal contributor
  rules (auto-loaded via @import above).
- [AGENTS.md](AGENTS.md) — AI-agent additions on top of
  CONTRIBUTING (auto-loaded via @import above).
- [docs/rules/](docs/rules/) — path-scoped rule files.
- [.claude/rules/](.claude/rules/) — Claude Code's path-scoped
  loader: symlinks to docs/rules/ plus the two Claude-only
  delta files.
- [docs/process.md](docs/process.md) — rationale for every rule.
```

- [ ] **Step 6: Update the project-specific-skill trigger's reference list**

In `## When to consider creating a project-specific skill`, the
current text refers only to `CLAUDE.md` and `docs/process.md`.
Update the in-text reference to the new fan-out ("don't fit
`CONTRIBUTING.md`, `AGENTS.md`, `CLAUDE.md`, `docs/process.md`,
`docs/rules/*.md`, or existing `.claude/rules/*.md`"),
cross-reference-path update per Non-goals exception 1.

- [ ] **Step 7: Run markdownlint**

```bash
markdownlint-cli2 CLAUDE.md
```

Expected: no errors. (Do NOT run `doctoc` on `CLAUDE.md`: it has
no TOC markers today, and adding a TOC is out of scope for this
reorganization. The pre-push doctoc check skips files without
markers.)

- [ ] **Step 8: Verify line counts and post-expansion budget**

```bash
wc -l CLAUDE.md CONTRIBUTING.md AGENTS.md
```

Expected: `CLAUDE.md` smaller than the original 217 lines; the
sum of `CONTRIBUTING.md`, `AGENTS.md`, and `CLAUDE.md` should
not exceed 434 lines (twice the original `CLAUDE.md`, per spec
Verification budget — this is the post-`@import`-expansion
Claude session-start context).

- [ ] **Step 9: Commit**

```bash
jj describe -m "$(cat <<'EOF'
doc: reduce CLAUDE.md to Claude-specific deltas

Delete the § Mathlib upstream guides URL list (canonical copy
in docs/rules/lean-coding.md). Replace the project-intro
paragraph with an audience preface and the @AGENTS.md /
@CONTRIBUTING.md first-hop imports. Update the lean4 sub-skill
pointer and the References and project-specific-skill sections
to the new fan-out.

Surviving Claude-specific sections (§ Rules, § Phase-driven
workflow, § Tooling, § When to consider creating a
project-specific skill) keep their place and heading level.
EOF
)"
jj bookmark set doc/audience-split -r @
jj new
```

---

## Task 9: Touchpoints and cross-references

**Goal:** Update `README.md § Process`, `TODO.md`, and
`docs/process.md` so every cross-reference to a now-relocated
rule points at its new home. Add the one-sentence mode-(c)
parenthetical to `docs/process.md § Two-track development`.

**Files:**

- Modify: `README.md` — `§ Process` per-file enumeration
  replaced.
- Modify: `TODO.md` — `Project-specific geb-development skill`
  trigger rule-locations updated.
- Modify: `docs/process.md` — opening sentence updated; mode-(c)
  parenthetical added to § Two-track development;
  cross-references in body updated.

- [ ] **Step 1: Update `README.md § Process`**

Read the current `README.md § Process` section. It enumerates
`CLAUDE.md` and each `.claude/rules/*.md` file. Replace with a
brief enumeration of the new fan-out:

```markdown
## Process

The contributor-binding rules live in three audience-shaped
entry-point files at the repo root:

- [CONTRIBUTING.md](CONTRIBUTING.md) — universal contributor
  rules (humans + AI agents).
- [AGENTS.md](AGENTS.md) — additions for AI coding agents in
  general.
- [CLAUDE.md](CLAUDE.md) — Claude Code-specific additions.

Path-scoped rules live in [docs/rules/](docs/rules/):

- `lean-coding.md` — applies to all `.lean` files.
- `upstream-eligible.md` — applies under `Geb/Mathlib/`,
  `Geb/Cslib/`, `GebTests/Mathlib/`, and `GebTests/Cslib/`.
- `markdown-writing.md` — applies to all `.md` files.
- `ci-and-workflow.md` — applies to `.github/workflows/` and
  `scripts/`.

Claude Code's path-scoped loader at
[.claude/rules/](.claude/rules/) consists of symlinks to the
canonical files in `docs/rules/` plus Claude-only delta files
for additions specific to Claude.
```

- [ ] **Step 2: Update `TODO.md` `Project-specific geb-development skill` trigger**

Locate the trigger bullet beginning "Project-specific
geb-development skill". Update the rule-locations enumeration
to:

```markdown
- **Project-specific `geb-development` skill**: when recurring
  patterns accumulate that fit neither `CONTRIBUTING.md`,
  `AGENTS.md`, `CLAUDE.md`, `docs/process.md`,
  `docs/rules/*.md`, nor existing `.claude/rules/*.md`. Default
  is to wait for friction.
```

- [ ] **Step 3: Update `docs/process.md` opening sentence**

The current first non-heading sentence reads: "This document
records *why* each rule in `CLAUDE.md` and `.claude/rules/*.md`
exists." Replace with:

```markdown
This document records *why* each rule in `CONTRIBUTING.md`,
`AGENTS.md`, `CLAUDE.md`, `docs/rules/*.md`, and
`.claude/rules/*.md` exists. The rules themselves live in
those files; this document explains the motivation behind each.
Read it when you need to understand the reason for a rule,
propose a change, or weigh how to apply a rule in an
unfamiliar situation.
```

- [ ] **Step 4: Update specific `docs/process.md` cross-references**

Run:

```bash
grep -n 'CLAUDE\.md\|\.claude/rules' docs/process.md
```

The current `docs/process.md` has these references (line numbers
are pre-reorg; verify with the grep output):

- Line 3-4 (opening sentence "each rule in `CLAUDE.md` and
  `.claude/rules/*.md`") — already updated in Step 3 above.
- Line 105 ("the rule statement lives in `CLAUDE.md` § Style
  guidelines") — UPDATE to `CONTRIBUTING.md § Rules § Style
  and references`.
- Line 120 ("`docs/process.md` (this file) contains the
  rationale for each rule that binds development") — no
  CLAUDE.md reference; leave.
- Line 201 ("Multi-layered enforcement: hard rule in
  `CLAUDE.md`, pre-push reminder in `scripts/pre-push.sh`, PR
  template checkbox, user-review-before-push gate.") — UPDATE
  to `CONTRIBUTING.md § Rules § Submission policy` (the
  no-LLM-drafted-text policy moves to CONTRIBUTING.md with
  cross-listed enforcement in AGENTS.md).

For any other grep hits not listed above, decide using these
rules:

- References to a rule that moved to CONTRIBUTING.md → update
  to `CONTRIBUTING.md`.
- References to a rule that moved to AGENTS.md → update to
  `AGENTS.md`.
- References to a Claude-only delta → keep `CLAUDE.md` or
  `.claude/rules/<topic>-claude.md`.
- References to a path-scoped rule → update to
  `docs/rules/<topic>.md`.

Note: the existing `docs/process.md § Verify agent claims`
section remains as rationale. Task 7 added the rule-statement
to AGENTS.md; process.md is unchanged for that section beyond
any necessary cross-reference updates.

- [ ] **Step 5: Add mode-(c) parenthetical (Non-goals exception 5)**

In `docs/process.md § Two-track development`, add a one-sentence
parenthetical naming mode (c). Suggested wording (place at the
end of the section's existing prose):

```markdown
The AI-agent posture for Track 1 — drafting autonomously under
`Geb/Internal/` with user review at commit time — is called
mode (c) in the AI authoring-modes table at
`docs/rules/upstream-eligible.md § Authoring modes`.
```

- [ ] **Step 6: Run markdownlint and doctoc**

```bash
doctoc --update-only README.md TODO.md docs/process.md
markdownlint-cli2 README.md TODO.md docs/process.md
```

Expected: no errors.

- [ ] **Step 7: Commit**

```bash
jj describe -m "$(cat <<'EOF'
doc: update README, TODO, and process.md cross-references

Update README.md § Process per-file enumeration to point at the
new three-entry-point + docs/rules/ fan-out. Update TODO.md §
Project-specific geb-development skill trigger's rule-locations
list. Update docs/process.md opening sentence and body
cross-references to enumerate the new entry-point files.

Add a one-sentence parenthetical to docs/process.md § Two-track
development naming mode (c) as the AI-authoring posture for
Track 1, resolving the dangling pointer from
docs/rules/upstream-eligible.md § Authoring modes.
EOF
)"
jj bookmark set doc/audience-split -r @
jj new
```

---

## Task 10: Verification

**Goal:** Run the full pre-push checklist end-to-end against the
post-reorg working tree. Confirm no markdownlint errors, no
doctoc TOC drift, no `lake build` / `lake test` regression, and
no broken cross-references.

This task does NOT result in a commit unless a fix is needed.
If everything passes, the verification's success is the
"commit" (the prior 9 commits are the actual work).

- [ ] **Step 1: Run `scripts/pre-push.sh`**

```bash
scripts/pre-push.sh
```

Expected: every step passes. If any step fails, the failure
identifies the file and the issue; fix and re-run.

Common failure modes to watch for:

- `markdownlint-cli2`: a moved section may carry stale
  cross-references or markdown formatting issues. Fix inline.
- `doctoc --dryrun --update-only .`: a TOC may be out of sync.
  Run `doctoc --update-only <file>` to regenerate.
- `lake build` / `lake test`: should not be affected by this
  reorg (no Lean source touched). If a failure appears,
  investigate the unrelated cause.
- `scripts/lint-imports.sh`: should not be affected. If a
  failure appears, investigate the unrelated cause.
- `bash scripts/check-axioms.sh Geb/ GebTests/`: should not be
  affected.

- [ ] **Step 2: Run the diff-envelope check**

Concatenate the post-reorg authoritative-rule content and
compare against the pre-reorg authoritative content. Pre-reorg
revision is the spec commit's parent (which is `main`'s tip at
start of work). Use `main@-` semantics that are stable against
bookmark drift, or pin to the change-id of the spec commit's
parent if `main` may advance during the work.

```bash
# Pin the pre-reorg revision once, at start of Task 10
PRE_REORG=$(jj log -r 'doc/audience-split & ~description("doc: ")' --no-graph -T 'change_id ++ "\n"' | head -1)
# (Alternative: PRE_REORG=$(jj log -r 'main' --no-graph -T 'change_id ++ "\n"' | head -1)
# if main has not advanced during the work.)
echo "PRE_REORG=$PRE_REORG"

# Post-reorg concatenation (excluding the .claude/rules/ symlinks)
cat CONTRIBUTING.md AGENTS.md CLAUDE.md docs/rules/*.md .claude/rules/*-claude.md > /tmp/post-reorg.md

# Pre-reorg concatenation. The bulk is CLAUDE.md plus the four
# .claude/rules/ files. CONTRIBUTING.md also receives content
# from README.md (the Setup and Working subsections) and a few
# sentences from CLAUDE.md/process.md cross-references; that
# content has no pre-reorg counterpart in this concatenation, so
# it will show as post-side additions (see Expected note below).
jj file show -r "$PRE_REORG" CLAUDE.md > /tmp/pre-reorg.md
for f in markdown-writing.md upstream-eligible.md ci-and-workflow.md lean-coding.md; do
  jj file show -r "$PRE_REORG" .claude/rules/$f >> /tmp/pre-reorg.md
done

# Normalize both with markdownlint --fix using the repo config.
# markdownlint-cli2 discovers .markdownlint-cli2.jsonc by walking up from
# the file's directory. /tmp/ has no config, so pass it explicitly.
markdownlint-cli2 --config .markdownlint-cli2.jsonc --fix /tmp/post-reorg.md /tmp/pre-reorg.md 2>&1 || true

# Diff
diff /tmp/pre-reorg.md /tmp/post-reorg.md > /tmp/envelope-diff || true
less /tmp/envelope-diff
```

Expected: the diff is non-empty (substantial relocation). Every
difference must be explainable as one of: (1) one of the seven
Non-goals exception categories plus the cross-listings (category
(h) of the Verification tolerance list); or (2) a post-side
addition sourced from `README.md § Contributing` (Setup/Working)
or from `docs/process.md`, which are not in the pre-reorg
concatenation above — verify each such addition against the
corresponding pre-reorg `README.md`/`docs/process.md` content by
hand. Any difference outside those
categories must be explained or reverted.

- [ ] **Step 3: Verify symlinks resolve correctly**

```bash
for f in .claude/rules/{lean-coding,upstream-eligible,markdown-writing,ci-and-workflow}.md; do
  echo "=== $f ==="
  readlink -f "$f"
  test -L "$f" && echo "is symlink" || echo "NOT SYMLINK — fix"
done
```

Expected: each entry is a symlink that resolves to
`docs/rules/<topic>.md`.

- [ ] **Step 4: Verify `paths:` frontmatter on canonical files**

```bash
for f in docs/rules/{lean-coding,upstream-eligible,markdown-writing,ci-and-workflow}.md; do
  echo "=== $f ==="
  head -10 "$f"
done
```

Expected: each file starts with YAML frontmatter:

- `lean-coding.md`: `paths: ["**/*.lean"]`
- `upstream-eligible.md`: `paths:` listing `Geb/Mathlib.lean`,
  `Geb/Mathlib/**`, `GebTests/Mathlib.lean`, `GebTests/Mathlib/**`,
  `Geb/Cslib.lean`, `Geb/Cslib/**`, `GebTests/Cslib.lean`,
  `GebTests/Cslib/**`.
- `markdown-writing.md`: `paths: ["**/*.md"]`
- `ci-and-workflow.md`: `paths: [".github/workflows/**",
  "scripts/**"]`

- [ ] **Step 5: Verify CLAUDE.md `@import` directives**

```bash
grep -n '^@' CLAUDE.md
```

Expected: two lines, `@AGENTS.md` and `@CONTRIBUTING.md`, on
separate lines (first-hop imports).

- [ ] **Step 6: Verify AGENTS.md has no `@import` directives**

```bash
grep -n '^@' AGENTS.md
```

Expected: no matches. AGENTS.md uses prose pointers, not
`@import`.

- [ ] **Step 7: Confirm bookmark and commit history**

```bash
jj log -r 'main..doc/audience-split' --no-graph -T 'change_id.short() ++ " " ++ bookmarks ++ " | " ++ description.first_line() ++ "\n"'
```

Expected: 9 commits on top of `main`, each with a `doc:` prefix
and a short subject, ending at the bookmark `doc/audience-split`.

- [ ] **Step 8: If everything passes, hand off for user review**

The branch `doc/audience-split` is ready for the user's
line-by-line review per the project's "no `jj git push` without
user line-by-line review" rule. Do not push.

Surface to the user:

- Bookmark name and commit count.
- Output of `scripts/pre-push.sh` confirming all checks pass.
- Result of the diff-envelope check (categories of differences,
  confirming all fall within the seven exceptions + cross-listings).
- Any open questions or borderline calls made during execution.

---

## Done

After Task 10 passes, the implementation is complete. The
branch awaits user review and push. Subsequent activity (push,
PR creation, merge to `main`, regenerate `integration`) happens
under user-driven control per project process.
