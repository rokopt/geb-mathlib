# Style-standardization implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Execute the workstream specified in
[the style-standardization spec](../specs/2026-07-16-style-standardization-design.md):
a rules-doc alignment commit followed by four per-aspect style
rounds over all committed `.lean` files, on topic branch
`style/mathlib-conventions`.

**Architecture:** Task 1 edits the rules documents inline. Tasks
2-5 each open one jj commit, dispatch one fresh-context subagent
for one style aspect, verify with the full pre-push checklist,
and close. Task 6 closes the branch (final checks, spec/plan
removal, final-review skills, hand-off to the user).

**Tech Stack:** Lean 4 / lake, jj (colocated), `scripts/pre-push.sh`,
`markdownlint-cli2`, `doctoc`, Claude subagents (Agent tool),
`curl` for the live guides.

## Global constraints

Copied from the spec; every task implicitly includes them.

- All VCS mutations via `jj`; no raw mutating `git` subcommands.
- No push at any point; the user reviews the completed branch
  line-by-line first. The `style/` prefix does not trigger
  pre-push's PR-candidate reminders, so this rule is enforced by
  this plan, not tooling.
- Every commit description: subject line per the commit-message
  convention (`docs/rules/ci-and-workflow.md`) plus a body
  summarizing the changes, surfaced-tie resolutions, and any
  cross-round repairs. `jj describe` runs before
  `scripts/pre-push.sh` so the checklist validates the subject;
  the body is session-enforced (the automated check reads only
  the first line).
- A task never closes with `scripts/pre-push.sh` failing.
- Mathematical content preserved exactly: the theorem-set and
  every interface unchanged up to identifier renaming. No
  `noncomputable`; constructive discipline and permitted-axiom
  policy untouched (`GebMeta.classicalAllowedModules` entries
  change only to track module renames).
- Rule content whose application would alter a statement or
  interface (normal-form restatements, missing `@[ext]` or
  derivations, `public import` visibility changes) is recorded
  as a `TODO.md` note, not applied.
- Subagents run with no worktree isolation, in this working
  copy; they surface ties (two defensible conforming
  resolutions) and out-of-round violations instead of resolving
  them silently; the session resolves ties and records them in
  the commit body.
- The live guides are re-fetched at the start of every round.
- Build via `lake build` / `lake test`; never `lake env lean`;
  avoid `lake clean`.
- A violation owned by an earlier round and discovered later is
  fixed in the discovering round's commit and noted in its body
  — never repaired into a closed non-head commit.
- A reported genuine local-rule-vs-guide incompatibility is
  escalated to the user for decision (spec § Authoritative
  references); neither the subagent nor the session resolves
  it, and the affected fixes wait for the answer.
- The construction-discipline sections of
  `docs/rules/lean-coding.md` (§ Coding technique, § Recursion
  and induction through recursors, § Higher-order
  constructions, § One step at a time, and § Structure and
  typeclass patterns beyond the items Task 3's scope names) are
  outside this workstream (spec § Goal); no round applies them,
  and the step-4 diff inspection rejects edits made under them.

---

### Task 1: Rules-doc alignment commit

**Files:**

- Modify: `docs/rules/lean-coding.md` (§ Naming conventions,
  § Coding style, § Documentation, § Comment and docstring rules)
- Modify: `CONTRIBUTING.md` (§ Style and references)
- Modify: `docs/rules/markdown-writing.md` (§ Prose style)
- Modify: `docs/process.md` (§ Generic user references)
- Modify: `TODO.md` (§ Triggers)

**Interfaces:**

- Consumes: the spec's § Authoritative references decisions.
- Produces: local rules documents that agree with the live
  guides; tasks 2-5 pass these files to their subagents as
  binding local rules.

- [ ] **Step 1: Open the commit**

Confirm with `jj log` that `@` is an empty, undescribed
working-copy commit directly atop the plan commit; if it holds
leftover changes, `jj squash` them into their commit first. That
working-copy commit *is* the alignment commit — do not run
`jj new` here: jj always has a working-copy commit, and
`jj new` from this state would strand an undescribed interior
commit that no checklist step catches (the message check skips
empty subjects) but `jj git push` refuses.

- [ ] **Step 2: Fix the case-convention digest error**

In `docs/rules/lean-coding.md` § Naming conventions, replace:

```markdown
- `snake_case` for `Prop`-valued definitions
  (`theorem`, `lemma`).
- `lowerCamelCase` for `def`, `instance`, `example`,
  variables, anonymous constructors, and tactic names.
- `UpperCamelCase` for `structure`, `class`, `inductive`,
  type-class arguments, and Sort-valued constants.
```

with:

```markdown
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
```

In the same section, replace:

```markdown
- Predicates use the suffix `_iff_…` to indicate "if and only
  if" relationships (`even_iff_two_dvd`).
```

with:

```markdown
- Theorem names stating an equivalence use the infix `_iff_`
  (`even_iff_two_dvd`).
```

(the old bullet labeled a `snake_case` theorem name a
"predicate", contradicting the corrected case rule above).

- [ ] **Step 3: State the header form in the coding-style digest**

In `docs/rules/lean-coding.md` § Coding style, append to the
section's bullet list — immediately before the
`**Adversarial-reviewer instruction**` paragraph — the bullet:

```markdown
- Copyright header per mathlib's style guide:
  `Copyright (c) <year> <author names>. All rights reserved.`,
  the Apache-2.0 license line, and
  `Authors: <comma-separated names>`. Contributor names appear
  here in mathlib's named-author form; see
  CONTRIBUTING.md § Style and references for the scoped
  exception to the generic-user-reference rule.
```

- [ ] **Step 4: Add the non-vacuous reading and the Tags rule**

In `docs/rules/lean-coding.md` § Documentation, replace the
first bullet:

```markdown
- `/-! … -/` module docstring is mandatory after imports;
  required sections (in order): `# Title`, brief summary,
  `## Main definitions`, `## Main statements`,
  `## Notation` (if any), `## Implementation notes` (if any),
  `## References` (if any), and `## Tags`.
```

with:

```markdown
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
```

- [ ] **Step 5: Restate the docstring mandates outside the digest**

In `docs/rules/lean-coding.md` § Comment and docstring rules,
replace:

```markdown
The module/declaration docstring requirements (mandatory module
docstring with its required sections, mandatory declaration
docstrings, Markdown + LaTeX, and no development-history
references) are stated above in § Documentation (see also
mathlib's `doc.html`). One additional local rule:

- **Empty lines inside declarations are lint-discouraged**; use a
  brief comment (`-- ...`) as a structural separator if needed.
```

with:

```markdown
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
```

- [ ] **Step 6: Scope the generic-user-reference rule (three files)**

In `CONTRIBUTING.md` § Style and references, at the end of the
"Generic user references in committed text" bullet, append:

```markdown
  A second exception is `.lean` copyright headers, which follow
  mathlib's named-author form
  (`Copyright (c) <year> <names>. All rights reserved.` /
  `Authors: <names>`): the names identify authorship as mathlib
  requires and are exempt from this rule.
```

In `docs/rules/markdown-writing.md` § Prose style, at the end of
the "Generic user references" bullet, append:

```markdown
  (`.lean` copyright headers are exempt; they follow mathlib's
  named-author form per `docs/rules/lean-coding.md`).
```

In `docs/process.md` § Generic user references, append the
paragraph:

```markdown
`.lean` copyright headers are a second exception: mathlib's
style guide prescribes named authors in the copyright and
`Authors:` lines, and upstream-eligible files keep that form.
The header names identify authorship for upstream submission,
not autobiographical detail.
```

- [ ] **Step 7: Remove the retired TODO.md trigger**

In `TODO.md` § Triggers, delete the entry:

```markdown
- **Update `Authors:` lines as content authors arrive**: every
  `.lean` file ships with `Authors: The geb-mathlib contributors`.
  When a contributor authors substantive content in a file,
  update that file's `Authors:` line to credit them by name.
```

- [ ] **Step 8: Lint the edited Markdown**

Run: `doctoc --update-only .` then `markdownlint-cli2 '**/*.md'`.
Expected: `Summary: 0 error(s)`.

- [ ] **Step 9: Describe, run the checklist, close**

Run:

```bash
jj describe -m "$(cat <<'EOF'
doc: align style rules with live mathlib guides

Correct the naming digest's case rule (Prop/Type-denoting names
are UpperCamelCase; proof-term names are snake_case), state the
mathlib header form, add the non-vacuous section reading and the
Tags rule, restate the docstring mandates outside the superseded
digest, scope the generic-user-reference rule to exempt .lean
copyright headers, and remove the retired placeholder-Authors
trigger from TODO.md.
EOF
)"
bash scripts/pre-push.sh
```

Expected: every checklist step passes. On failure, repair in
this commit and re-run until it passes.

---

### Task 2: Round 1 — naming conventions

**Files:**

- Modify: any of the 43 committed `.lean` files; `docs/index.md`,
  `TODO.md`, `docs/rules/*.md` where renamed names are cited;
  `GebMeta.lean` `classicalAllowedModules` and `scripts/tests/`
  fixtures on module renames.

**Interfaces:**

- Consumes: Task 1's corrected rules docs.
- Produces: final declaration and module names; every later
  round operates on these names.

- [ ] **Step 1: Open the round**

Run: `jj new`. Confirm empty working copy.

- [ ] **Step 2: Fetch the live guides**

Fetch each losslessly with `curl -fsSL <url> -o <file>` into the
session scratchpad directory (WebFetch summarizes through a
bounded model and can truncate long pages — the guides are the
round's top authority and must be complete):

- `https://leanprover-community.github.io/contribute/naming.html`
- `https://raw.githubusercontent.com/leanprover/cslib/main/CONTRIBUTING.md`

The subagent receives the fetched file paths and reads them as
its first action.

- [ ] **Step 3: Dispatch the naming subagent**

Dispatch one general-purpose subagent (no isolation) with this
prompt, substituting the fetched guide file paths and the file
list
from `git ls-files '*.lean'`:

```text
You are executing round 1 (naming conventions) of the
style-standardization branch in this repository's working copy.
Apply mathlib's naming conventions to every committed .lean file,
editing files directly in this working copy.

Inputs, in order of authority where they disagree (strictest
local rule wins on points the guide leaves open; surface any
genuine incompatibility — do not resolve it):
1. The live naming guide (fetched file, path below; read it
   first).
2. The CSLib guide (fetched file, path below) for Geb/Cslib/ and
   GebTests/Cslib/ files.
3. The binding local rules: read docs/rules/lean-coding.md,
   docs/rules/upstream-eligible.md,
   docs/rules/markdown-writing.md, CONTRIBUTING.md § Style and
   references, and docs/process.md § Avoid colloquialisms and
   metaphors.
4. The spec's ownership rules: read
   docs/superpowers/specs/2026-07-16-style-standardization-design.md
   §§ Goal, Authoritative references, Process decisions, Rounds,
   Round protocol. Per § Goal, the construction-discipline
   sections of docs/rules/lean-coding.md are outside this
   workstream's scope; apply only its naming, coding-style, and
   documentation rules. Per § Process decisions, mathlib conventions
   apply strictly to every identifier, including vocabulary
   settled in earlier review cycles (e.g. the IndRec IR*
   identifiers); no identifier is exempt as previously settled.

Scope, from the spec: case conventions (UpperCamelCase for
Prop/Type-denoting names including predicate defs; snake_case
for theorem names; lowerCamelCase otherwise), theorem-name
grammar, suffix conventions, namespace-prefix rules, variable
naming, American-English identifier spelling, and module (file)
renames where a module name violates the conventions. Do NOT
touch: header/import layout, docstring structure or prose
(rounds 2-4 own those), or anything that changes a statement or
interface beyond renaming.

For every rename, update every reference site: uses in Geb/,
GebTests/, GebMeta.lean; backtick cross-references inside
docstrings (the compiler does not check these); declaration
names cited in committed Markdown (docs/index.md, TODO.md,
docs/rules/*.md). For a module rename, also rename its
GebTests/ mirror in lockstep, update
GebMeta.classicalAllowedModules, scripts/tests/ fixtures, and
file paths in committed Markdown.

Before finishing: run `lake build` and `lake test`; both must
pass. Then report: (a) every rename as old → new with the rule
applied, (b) findings with two defensible conforming
resolutions — pick neither; list the options, (c) violations you
noticed that belong to other rounds, (d) any genuine
local-vs-guide incompatibility, (e) findings whose fix would
alter a statement or interface, for TODO.md deferral. Your final message is a data
report, not prose for a human.

[PATH TO FETCHED naming.html]
[PATH TO FETCHED CSLIB CONTRIBUTING.md]
[FILE LIST]
```

- [ ] **Step 4: Verify the round**

Session work, in order:

1. Resolve any surfaced ties against the guide text; apply the
   chosen resolution; note each in the commit body.
2. For each old identifier in the report, grep repository-wide
   in fully-qualified and final-component form; fix or justify
   every remaining occurrence (component-form hits filtered
   manually for false positives).
3. Inspect `jj diff` against the report (verify-agent-claims);
   give particular attention to files the build-time linters do
   not cover: `GebMeta.lean`, `Geb/Cslib.lean`,
   `Geb/Internal.lean`, `GebTests/Cslib.lean`,
   `GebTests/Internal.lean`, `GebTests/Internal/*`.
4. Check `GebMeta.classicalAllowedModules` manually if any
   module was renamed (no automated check covers a renamed
   allowlisted module that does not exercise `Classical.choice`).
5. Add any reported interface-altering findings to `TODO.md` as
   notes on follow-on work. Reported violations of other
   aspects are forwarded to their owning later rounds (each
   later task's dispatch includes the forwarded list); they are
   not fixed here.
6. Escalate any reported local-rule-vs-guide incompatibility to
   the user before closing the round (global constraint).

- [ ] **Step 5: Describe, run the checklist, close**

```bash
jj describe -m "$(cat <<'EOF'
refactor: rename declarations to mathlib naming conventions

<body: summary of renames, tie resolutions, out-of-round
violations forwarded to later rounds — written from the actual
report>
EOF
)"
bash scripts/pre-push.sh
```

Expected: full pass. On failure, repair in this commit (fresh
subagent if large) and re-run until it passes.

---

### Task 3: Round 2 — coding style

**Files:**

- Modify: any committed `.lean` file; `TODO.md` for deferral
  notes.

**Interfaces:**

- Consumes: final names from Task 2; Task 1's rules docs.
- Produces: style-conformant layout that rounds 3-4 must
  preserve (their rewrites stay within the 100-character limit
  and header form).

- [ ] **Step 1: Open the round**

Run: `jj new`.

- [ ] **Step 2: Fetch the live guides**

As Task 2 step 2 (`curl -fsSL` into the scratchpad; subagent
reads the files first):

- `https://leanprover-community.github.io/contribute/style.html`
- `https://leanprover-community.github.io/contribute/doc.html`
  (overlap: header/import/module-docstring region)
- `https://raw.githubusercontent.com/leanprover/cslib/main/CONTRIBUTING.md`

- [ ] **Step 3: Dispatch the coding-style subagent**

Same dispatch pattern as Task 2 — additionally substituting
the forwarded-findings list from earlier rounds — with this
scope section:

```text
You are executing round 2 (coding style) of the
style-standardization branch in this repository's working copy.
Apply mathlib's coding-style guide to every committed .lean
file, editing files directly in this working copy.

Inputs and authority order: as in the spec (read
docs/superpowers/specs/2026-07-16-style-standardization-design.md
§§ Goal, Authoritative references, Rounds, Round protocol —
§ Goal excludes the construction-discipline sections of
docs/rules/lean-coding.md from this workstream), the live
style guide (fetched file, path below; read it first), the
doc guide (fetched file, path below) for the
header/import overlap (docstring presence and structure belong
to round 3 — leave them), the CSLib guide (fetched file, path
below), and the binding
local rules files listed in the spec's round protocol step 1.

Scope: indentation, the 100-character line limit, Unicode
notation, one declaration per line, namespace/section layout
that changes no declared or fully-qualified name,
anonymous-constructor and projection preferences, the
empty-lines-inside-declarations rule, header layout — including
applying the named-author header adopted by the alignment
commit: the copyright line becomes
`Copyright (c) 2026 Terence Rokop. All rights reserved.` and the
Authors line becomes `Authors: Terence Rokop` in every .lean
file — and import layout. Also: unused `universe` / `variable`
declarations and similar no-interface local code-state rules.

Do NOT apply content whose application would alter a statement
or interface: normal-form or statement restructuring, missing
@[ext] or derivations, public import visibility changes —
record each such finding for a TODO.md note instead. Do not
touch docstring structure or prose.

The forwarded-findings block at the end lists violations
earlier rounds noticed that this round owns: address each, and
include each item's resolution in your report.

Before finishing: run `lake build` and `lake test`; both must
pass. Report: (a) the fix classes applied and where,
(b) surfaced ties, (c) out-of-round violations noticed,
(d) TODO.md-deferral findings, (e) any genuine incompatibility.

[PATH TO FETCHED style.html]
[PATH TO FETCHED doc.html]
[PATH TO FETCHED CSLIB CONTRIBUTING.md]
[FILE LIST]
[FORWARDED FINDINGS FROM EARLIER ROUNDS]
```

- [ ] **Step 4: Verify the round**

As Task 2 step 4 items 1, 3, and 6 (no renames expected: any
rename found here belongs to round 1 and is fixed in this commit
with a note, per the spec's step 7 — and Task 2 step 4 items 2
and 4, the repository-wide rename grep and the
`classicalAllowedModules` check, run for any such rename).
Confirm the report resolves every forwarded finding. Add
the
reported deferral findings to `TODO.md` as notes on follow-on
work; forward reported round-3/4 violations to those rounds'
dispatches.

- [ ] **Step 5: Describe, run the checklist, close**

```bash
jj describe -m "$(cat <<'EOF'
style: conform to mathlib coding style

<body: fix classes, header adoption, tie resolutions, deferred
TODO.md items — written from the actual report>
EOF
)"
bash scripts/pre-push.sh
```

Expected: full pass; repair-in-commit loop on failure.

---

### Task 4: Round 3 — documentation form

**Files:**

- Modify: any committed `.lean` file; `docs/references.bib` where
  a citation needs a key added or corrected; `TODO.md` for
  deferral notes.

**Interfaces:**

- Consumes: final names (Task 2), style-conformant layout
  (Task 3).
- Produces: structurally conformant docstrings that Task 5
  rewrites only semantically.

- [ ] **Step 1: Open the round**

Run: `jj new`.

- [ ] **Step 2: Fetch the live guides**

As Task 2 step 2 (`curl -fsSL` into the scratchpad; subagent
reads the files first):

- `https://leanprover-community.github.io/contribute/doc.html`
- `https://leanprover-community.github.io/contribute/style.html`
  (overlap region; header/imports belong to round 2 — a
  violation noticed there is fixed here and noted, not
  systematically restyled)
- `https://raw.githubusercontent.com/leanprover/cslib/main/CONTRIBUTING.md`

- [ ] **Step 3: Dispatch the documentation-form subagent**

Same dispatch pattern as Task 2 — additionally substituting
the forwarded-findings list from earlier rounds — with this
scope section:

```text
You are executing round 3 (documentation form) of the
style-standardization branch in this repository's working copy.
Bring every docstring into structural conformance, editing files
directly in this working copy.

Inputs and authority order: per the spec (read
docs/superpowers/specs/2026-07-16-style-standardization-design.md
§§ Goal, Authoritative references, Rounds, Round protocol —
§ Goal excludes the construction-discipline sections of
docs/rules/lean-coding.md from this workstream), the live
doc guide (fetched file, path below; read it first), the style
guide (fetched file, path below) — consulted for the overlap
region without restyling it, and binding on your own rewrites:
every docstring you touch must conform to the style guide's
mechanical rules (100-character lines, indentation) — the
CSLib guide (fetched file, path below), and the binding
local rules files
listed in the spec's round protocol step 1. The local docstring
mandates are stricter than the live guide and bind: module
docstring with required sections in order under the non-vacuous
reading; docstrings for every def, structure, class, instance,
field, and theorem of public interest; ## Tags mandatory for
modules with substantive content (index stubs omit it),
theme-level keywords only.

Scope: module docstring presence, section list, and section
order; mandatory declaration/field/instance docstrings; backtick
cross-references in `Foo.bar` form (never prefixed with
Geb.Mathlib. or Geb.Cslib. in the upstream subtrees); literature
citations in [Key] form backed by docs/references.bib — a
citation needing a new or corrected key updates the .bib, and
any added or altered attribution must first be verified against
the primary source (theoremsearch / arXiv tooling), per
AGENTS.md § Verify agent claims; no development-history
references. Do not restyle header/import layout; do not rewrite
docstring semantics beyond what form requires (round 4 owns
accuracy). Do not apply content whose fix would alter a
statement or interface — record each such finding for TODO.md
deferral instead.

The forwarded-findings block at the end lists violations
earlier rounds noticed that this round owns: address each, and
include each item's resolution in your report.

Before finishing: run `lake build` and `lake test`; both must
pass. Report: (a) files changed and the form rules applied,
(b) citations added/corrected with their primary-source
verification, (c) surfaced ties, (d) out-of-round violations,
(e) any genuine incompatibility, (f) findings whose fix would
alter a statement or interface, for TODO.md deferral.

[PATH TO FETCHED doc.html]
[PATH TO FETCHED style.html]
[PATH TO FETCHED CSLIB CONTRIBUTING.md]
[FILE LIST]
[FORWARDED FINDINGS FROM EARLIER ROUNDS]
```

- [ ] **Step 4: Verify the round**

As Task 2 step 4 items 1, 3, and 6 — plus items 2 and 4
whenever a cross-round repair renames anything. Confirm the
report resolves every forwarded finding. Independently
verify every
added or altered citation against its primary source before
accepting it (verify-agent-claims applies doubly to
attributions). Add reported interface-altering findings to
`TODO.md`; a reported violation owned by an earlier round is
verified and fixed in this commit with a note in the body, per
the spec's step 7; forward reported round-4 items to Task 5's
dispatch.

- [ ] **Step 5: Describe, run the checklist, close**

```bash
jj describe -m "$(cat <<'EOF'
doc: conform docstrings to mathlib documentation form

<body: form-rule classes applied, sections added/reordered,
citations touched and their verification, tie resolutions —
written from the actual report>
EOF
)"
bash scripts/pre-push.sh
```

Expected: full pass; repair-in-commit loop on failure.

---

### Task 5: Round 4 — docstring content accuracy

**Files:**

- Modify: any committed `.lean` file; `TODO.md` for deferral
  notes; `docs/references.bib` where a confirmed cross-round
  citation repair requires it.

**Interfaces:**

- Consumes: structurally conformant docstrings (Task 4).
- Produces: docstrings that accurately describe their
  declarations and modules; the branch's final Lean state.

- [ ] **Step 1: Open the round**

Run: `jj new`.

- [ ] **Step 2: Re-fetch the guides**

Same fetches as Task 4 step 2 (re-fetched per the spec even
though round 3 just used them).

- [ ] **Step 3: Dispatch the accuracy subagent**

Same dispatch pattern as Task 2 — additionally substituting
the forwarded-findings list from earlier rounds — with this
scope section:

```text
You are executing round 4 (docstring content accuracy) of the
style-standardization branch in this repository's working copy.
Check every docstring — declaration, field, and module —
semantically against what it documents, editing files directly
in this working copy.

Authority: the Lean statement of each documented declaration,
and for a module docstring the module's actual contents (the
summary and ## Main definitions / ## Main statements listings
must describe the declarations the module actually contains).
Your rewrites must preserve the form rules of the doc guide
(fetched file, path below; read it first) and the style
guide's mechanical rules (100-char
lines etc.), and the binding local rules files listed in the
spec's round protocol step 1 (read
docs/superpowers/specs/2026-07-16-style-standardization-design.md
§§ Goal, Authoritative references, Rounds, Round protocol —
§ Goal excludes the construction-discipline sections of
docs/rules/lean-coding.md from this workstream). Prose
follows CONTRIBUTING.md § Style and references: formal, dry,
no value-laden adjectives, no colloquialisms.

Rewrite docstrings that are inaccurate, vacuous, or misdescribe
their declaration or module. Do not change any Lean statement.
Do not add or remove citations without primary-source
verification (report them instead).

The forwarded-findings block at the end lists violations
earlier rounds noticed that this round owns: address each, and
include each item's resolution in your report.

Before finishing: run `lake build` and `lake test`; both must
pass. Report: (a) every docstring rewritten, with the
inaccuracy it had, (b) surfaced ties, (c) out-of-round
violations, (d) any citation issues found but not changed,
(e) findings whose fix would alter a statement or interface,
for TODO.md deferral, (f) any genuine local-vs-guide
incompatibility.

[PATH TO FETCHED doc.html]
[PATH TO FETCHED style.html]
[PATH TO FETCHED CSLIB CONTRIBUTING.md]
[FILE LIST]
[FORWARDED FINDINGS FROM EARLIER ROUNDS]
```

- [ ] **Step 4: Verify the round**

As Task 2 step 4 items 1, 3, and 6 — plus items 2 and 4
whenever a cross-round repair renames anything — confirming the
report resolves every forwarded finding — and except that
ties here are
resolved against the declaration's statement rather than the
guide text, per the spec's round protocol step 5 — with each
rewritten docstring spot-checked against its declaration's actual statement. Add
reported interface-altering findings to `TODO.md`. Reported
citation issues are verified by the session against primary
sources and, when confirmed, fixed in this commit with a note;
other earlier-round violations likewise, per the spec's step 7.

- [ ] **Step 5: Describe, run the checklist, close**

```bash
jj describe -m "$(cat <<'EOF'
doc: correct docstring content

<body: rewrites and the inaccuracies fixed, tie resolutions —
written from the actual report>
EOF
)"
bash scripts/pre-push.sh
```

Expected: full pass; repair-in-commit loop on failure.

---

### Task 6: Close the branch

**Files:**

- Delete: `docs/superpowers/specs/2026-07-16-style-standardization-design.md`,
  `docs/superpowers/plans/2026-07-17-style-standardization.md`

**Interfaces:**

- Consumes: the five completed commits.
- Produces: the reviewable branch, checks passing at the tip.

- [ ] **Step 1: Post-round-4 checklist**

Run: `jj new` (terminal commit), then `bash scripts/pre-push.sh`
on the completed aspect commits. A repair found here is made in
the terminal commit and squashed into the round-4 commit with
`jj squash` (its parent, whose only descendant at that point is
the terminal commit being squashed, so no other commit is
rewritten);
amend the round-4 body to note the repaired aspect; re-run until
it passes. If a repair renames anything, Task 2 step 4 items 2
and 4 (the repository-wide old-identifier grep and the
`classicalAllowedModules` check) run before the checklist
re-run; the same applies to Step 2's review-driven repairs.

- [ ] **Step 2: Final-review skills**

While the round-4 commit is still the head aspect commit, run
`lean4:review` over the branch diff and
`pr-review-toolkit:review-pr` on the branch, per CLAUDE.md's
pre-push phase. Fix any accepted findings via Step 1's path: the
fix is made in the terminal commit, squashed into the round-4
commit, noted in its body, and the checklist re-run until it
passes.

- [ ] **Step 3: Remove the spec and plan**

In the terminal commit, delete the two files, run
`doctoc --update-only .` and `markdownlint-cli2 '**/*.md'`, then:

```bash
jj describe -m "$(cat <<'EOF'
chore: remove transient spec and plan

Remove the style-standardization spec and plan per
CONTRIBUTING § Concern shape; they remain reachable in history.
EOF
)"
```

- [ ] **Step 4: Final checklist at the tip**

Run: `jj new` then `bash scripts/pre-push.sh`. A message failure
in a removal commit is repaired with `jj describe` on it; a
content failure (which can concern only the removal commits) by
squashing the fix into the head removal commit. Re-run until a
full pass covers the final state.

- [ ] **Step 5: Hand off**

Present the branch to the user for line-by-line review. Do not
push. After user approval the user directs the push and PR.
