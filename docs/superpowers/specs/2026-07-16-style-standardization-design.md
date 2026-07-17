# Style-standardization design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Goal](#goal)
- [Authoritative references](#authoritative-references)
- [Process decisions](#process-decisions)
- [Rounds](#rounds)
- [Round protocol](#round-protocol)
- [Branch shape](#branch-shape)
- [Constraints](#constraints)

<!-- END doctoc -->

## Goal

Bring every committed `.lean` file into conformance with the
style-relevant content of the project's Lean coding rules
([docs/rules/lean-coding.md](../../rules/lean-coding.md)) — its
naming, coding-style, and documentation rules — and with
mathlib's naming, coding-style, and documentation guides, before
the code base grows further. The rules file's
construction-discipline sections (§ Coding technique,
§ Recursion and induction through recursors, § Higher-order
constructions, § One step at a time, and § Structure and
typeclass patterns beyond the items § Rounds item 2 names)
govern how code is built rather than its surface style; they are
outside this workstream's scope and remain enforced by ordinary
development review. The review covers all `.lean` files:
`Geb/`, `GebTests/`, `GebMeta.lean`, and the root index files.
Non-`.lean` files are in scope where the work requires them: the
style rules documents (`docs/rules/`, `CONTRIBUTING.md`,
`docs/process.md`) in the rules-doc alignment commit, committed
Markdown citing renamed declarations or module paths (e.g.
`docs/index.md`), `docs/references.bib` where a citation
requires a key added or corrected, `scripts/tests/` fixtures
where a rename changes a referenced module or declaration name,
and `TODO.md` where a round records follow-on notes on deferred
interface-altering content. This enumeration covers the reference sites present
today; any other file surfaced by the round protocol's
repository-wide rename grep (e.g. `lakefile.toml` or CI
workflows, which currently carry only library-level names) is
likewise in scope for exactly the referencing update.

## Authoritative references

The binding upstream guides, re-fetched live at the start of every
review round and every adversarial-review round:

- Naming conventions:
  `https://leanprover-community.github.io/contribute/naming.html`
- Coding style:
  `https://leanprover-community.github.io/contribute/style.html`
- Documentation conventions:
  `https://leanprover-community.github.io/contribute/doc.html`
- CSLib contribution guide, binding `Geb/Cslib/` content (per
  `docs/rules/lean-coding.md` § Authoritative upstream guides
  (CSLib); currently index stubs only):
  `https://github.com/leanprover/cslib/blob/main/CONTRIBUTING.md`.
  CSLib follows mathlib's conventions, so the same rounds own
  its content; each round's subagent receives this guide
  alongside the round's mathlib guide.

Local rules in
[docs/rules/lean-coding.md](../../rules/lean-coding.md) apply in
addition. A rules-doc alignment commit (see § Branch shape)
precedes the rounds: continued standardization requires the
local style documents to agree with the live guides, so the
divergences this spec identifies are fixed on this branch rather
than deferred. The alignment commit:

- Replaces the digest's erroneous "`snake_case` for
  `Prop`-valued definitions" with the live guide's rule: names
  denoting `Prop`s or `Type`s are `UpperCamelCase` (including
  predicates — `def`s returning a `Prop` or `Type`); the names
  of proof terms (`theorem`s) are `snake_case`.
- Restates the docstring mandates as local rules outside the
  superseded digest: the mandatory module docstring with its
  required sections, and mandatory declaration, field, and
  instance docstrings. These are deliberate local strengthenings
  of the live doc guide (which marks `## Main definitions` and
  `## Main statements` optional and requires docstrings only for
  definitions and major theorems), stated under the non-vacuous
  reading: a module docstring carries each required section for
  which content exists, in the required order, and a module with
  nothing to list under a section omits it rather than carrying
  a placeholder (an index stub has no `## Main definitions`; a
  module with no theorems has no `## Main statements`).
- Makes `## Tags` mandatory for modules with substantive content
  (index stubs and similar vacuous modules omit it), restricted
  to keywords for the module's major theme — the universal
  properties of the development in the file, nothing about
  transient details — so the list does not go stale. Tags remain
  mechanically removable en masse, without conflicting with
  executable-code changes, should upstream request their
  removal.
- Adopts mathlib's named-author copyright header in full: the
  `Authors:` line lists contributor names
  (`Authors: The geb-mathlib contributors` becomes
  `Authors: Terence Rokop` in the current tree, with further
  contributors appended in mathlib's comma-separated form as
  they contribute), and the copyright line names the holder in
  mathlib's form
  (`Copyright (c) 2026 The geb-mathlib contributors. All rights
  reserved.` becomes
  `Copyright (c) 2026 Terence Rokop. All rights reserved.`).
  `CONTRIBUTING.md` § Style and references
  (and the parallel prose-rule statements in
  `docs/rules/markdown-writing.md` and `docs/process.md`) are
  scoped so the generic-user-reference rule does not apply to
  copyright headers. The `TODO.md` § Triggers entry describing
  the retired placeholder-Authors policy is removed in the same
  commit.

Precedence during the rounds, after the alignment commit:

- A local rule stricter than the live guide — requiring what the
  guide leaves optional or does not address — binds as written.
- No known incompatibility remains between the local rules and
  the live guides. (The doc guide's recommendation of
  fully-qualified backtick names is not in conflict with
  `docs/rules/upstream-eligible.md`'s self-prefix prohibition:
  in the upstream subtrees a declaration's fully-qualified name
  carries no `Geb.Mathlib.` / `Geb.Cslib.` prefix, so both rules
  are satisfiable at once.) If a round discovers a new
  incompatibility, it is surfaced to the user for decision
  rather than resolved by the subagent or the session;
  divergence from mathlib is accepted only where a fundamental
  property of Geb forces it.

## Process decisions

- Subagents apply fixes directly; the user reviews the completed
  branch line-by-line before any push.
- Mathlib conventions apply strictly everywhere, including
  vocabulary settled in earlier review cycles (e.g. the IndRec
  `IR*` identifiers). No identifier is exempt as previously
  settled.
- Aspects run as a strict sequence of fresh-context subagent
  rounds, one commit per round, so each later round sees the
  previous rounds' results and no two writers touch the tree
  concurrently.
- Naming runs first: renames touch the most lines, and every
  later pass then operates on final names.

## Rounds

| Round | Aspect | Upstream guide | Commit type |
| --- | --- | --- | --- |
| 1 | Naming conventions | `naming.html` | `refactor` |
| 2 | Coding style | `style.html` | `style` |
| 3 | Documentation form | `doc.html` | `doc` |
| 4 | Docstring content accuracy | none (semantic) | `doc` |

Each round's scope is the full content of its live upstream
guide plus the applicable local rules, bounded by § Constraints:
guide content whose application would alter a statement or an
interface beyond identifier renaming (e.g. the style guide's
normal-form and statement-restructuring advice) is not applied
on this branch; such findings are recorded as `TODO.md` notes on
follow-on work. The content lists below are illustrative, not
exhaustive.

1. **Naming**: case conventions per the live guide — a name
   denoting a `Prop` or a `Type` is `UpperCamelCase` (including a
   `def` returning a `Prop` or `Type`, e.g. a predicate); the
   name of a proof term (a `theorem`) is `snake_case`; other
   terms are `lowerCamelCase` — plus theorem-name grammar, suffix
   conventions (`_left`, `_of_`, `_iff_`, ...), and
   namespace-prefix violations. (The local digest's summary
   "`snake_case` for `Prop`-valued definitions" conflated
   proof-term names with `Prop`-denoting names; the rules-doc
   alignment commit corrects it before this round runs, per
   § Authoritative references.) Module (file) renames are in
   scope where a module name violates the conventions. Renames
   update every reference site: `GebTests/`, `GebMeta.lean`,
   backtick cross-references inside docstrings (which neither
   the compiler nor `lake build` checks), and declaration names
   cited in committed Markdown (`docs/index.md`, `TODO.md`, and
   the `docs/rules/` files, which cite `GebMeta` declarations;
   this enumeration is illustrative — the repository-wide grep
   in the round protocol is the authoritative check). A module
   rename additionally
   updates `GebMeta.classicalAllowedModules`, `scripts/tests/`
   fixtures, and file paths cited in committed Markdown; the
   allowlist update is verified manually, since no automated
   check fails when an allowlisted module that does not
   currently exercise `Classical.choice` is renamed. A renamed
   source module's `GebTests/` mirror is renamed in lockstep,
   preserving the mirrored-structure discipline and the
   symmetry of paired source/test allowlist entries.
2. **Coding style**: indentation, 100-character line limit,
   Unicode notation, one declaration per line, namespace/section
   hygiene, anonymous-constructor and projection preferences, the
   empty-lines-inside-declarations rule. Round 2 applies the
   named-author header adopted by the alignment commit — both
   the copyright line and the `Authors:` line — across the
   `.lean` files as part of its header-layout ownership. Round 2 additionally
   owns the local code-state rules of
   `docs/rules/lean-coding.md` that no live guide covers and
   whose application alters no statement or interface: unused
   `universe` / `variable` declarations and similar. Local-rule
   content whose application would add or alter an interface —
   missing `@[ext]` attributes or standard derivations, and
   import-visibility corrections under § Lean 4 module system
   (`public import` vs `import` changes what a module re-exports
   to importers) — is deferred to `TODO.md` notes, like
   interface-altering guide content.
3. **Documentation form**: module docstrings present with the
   required sections in the required order, declaration and field
   docstrings present where mandatory, `` `Foo.bar` ``
   cross-references, literature citations in `[Key]` form backed
   by `docs/references.bib`, no development-history references.
   `docs/references.bib` is in scope where a citation requires a
   key added or corrected; any added or altered attribution is
   first verified against the primary source with paper-search
   tooling, per AGENTS.md § Verify agent claims.
4. **Docstring content accuracy**: each docstring — declaration,
   field, and module — checked semantically against what it
   documents; inaccurate or vacuous docstrings rewritten. This
   round has no round-specific upstream guide; its authority is
   the Lean statement of each documented declaration, and for a
   module docstring the module's actual contents (the summary
   and the `## Main definitions` / `## Main statements` listings
   must describe the declarations the module actually
   contains).

Where the live guides overlap (the style and doc guides both
cover the copyright header, imports, and module docstrings),
ownership follows the aspect for each round's systematic pass:
header and import layout belong to round 2; docstring presence
and structure belong to round 3, and the round-2 subagent is
instructed to leave them to round 3 (round 3 has not yet run).
The round-3 subagent does not systematically restyle header and
import layout; a violation it notices there — like any earlier
round's content surviving into a later round — is handled per
§ Round protocol step 7 (fixed in the discovering round's
commit and noted), not by reopening the earlier round.
Between rounds 1 and 2: round 1 owns every naming-subject rule
wherever it appears — fixes that change fully-qualified names,
namespace-related changes to declared names and `namespace`
blocks (whether or not fully-qualified names change), variable
naming conventions (stated in both live guides), and
identifier spelling (American English, per the naming guide) —
while round 2's namespace/section hygiene covers only layout
restructuring that leaves declared names and fully-qualified
names unchanged; spelling in docstring prose belongs to rounds
3-4. On declaration-name form the binding rules are narrow: the
local digest governs namespace references inside declaration
bodies, and `docs/rules/upstream-eligible.md` prohibits the
subtree self-prefixes. The naming guide prescribes when names
carry dots (namespaces, automatically generated names,
projector-notation cases) and how namespaced names appear
inside lemma names — content round 1 owns — but does not
prohibit the `def Foo.bar` form itself, so that form is not by
itself a violation.

## Round protocol

1. For rounds 1-3, the session fetches the round's upstream
   guide live and passes its current text, the binding local
   rules (`docs/rules/lean-coding.md`,
   `docs/rules/upstream-eligible.md`,
   `docs/rules/markdown-writing.md` (passed to every round,
   since any round may record `TODO.md` notes),
   `CONTRIBUTING.md` § Style and references,
   and the colloquialism rule in `docs/process.md`), the file
   list, and this spec's
   § Authoritative references, § Rounds ownership rules (which
   govern where those inputs disagree), and § Round protocol to a
   fresh-context subagent (no worktree isolation; the subagent works in this
   working copy). Because the style and doc guides overlap on
   the header/import/module-docstring region, round 2's subagent
   additionally receives the live doc guide and round 3's the
   live style guide; the § Rounds ownership rules determine
   which round applies which content. Round 4's subagent
   receives the same input set as round 3, with the guides
   re-fetched at the start of the round per § Authoritative
   references (so its rewrites conform to the form rules round 3
   enforced); its semantic authority is the declarations and
   module contents themselves. Rounds 3
   and 4 rewrites remain subject to the style guide's mechanical
   rules. The build-time style linters (the `weak.linter.*`
   options in `lakefile.toml`) are inert in any module that does
   not transitively import Mathlib — `GebMeta.lean`, the
   `Geb/Cslib.lean`, `Geb/Internal.lean`, `GebTests/Cslib.lean`,
   and `GebTests/Internal.lean` index stubs, and the
   `GebTests/Internal/` modules — so for those files the step-3
   inspection checks the mechanical rules manually; the linters
   enforce them everywhere else.
2. The subagent examines all `.lean` files in scope and applies
   fixes.
3. Checks before commit: `scripts/pre-push.sh` passes in full
   (build, test, both lint trees, `lake shake`, import lint,
   script self-tests, Markdown lint, and TOC freshness). After a
   round that renames, each old identifier is additionally
   grepped for repository-wide, in both fully-qualified and
   final-component form (the component-form hits are filtered
   manually for false positives, since docstrings may reference
   a declaration by a short or namespace-relative name); any
   remaining occurrence is fixed or justified. The session
   inspects the diff against the subagent's report before
   committing (verify-agent-claims).
   Edits to the modules that do not transitively import Mathlib
   (enumerated in step 1) receive particular attention in that
   inspection, since the build-time style linters are inert
   there; `GebMeta.lean` is additionally excluded from both
   `lake lint` invocations, a separate mechanism covering the
   environment linters.
4. When a check fails after the subagent's pass, the session
   repairs the tree directly, dispatching a fresh subagent for
   repairs too large to make inline. All work — the subagent's
   pass and any repairs — accumulates in the round's
   working-copy commit, so no rearrangement is needed. A round
   never closes with a failing check.
5. Each subagent is instructed (as part of its step-1 inputs,
   which include this § Round protocol) to surface, rather than
   silently resolve, a finding with two defensible
   convention-conforming resolutions; the session resolves each
   surfaced tie against the guide text (rounds 1-3) or the
   declaration's statement (round 4) and records the resolution
   in the commit message.
6. Each round occupies exactly one commit. A round opens with
   `jj new` (an empty working-copy commit on top of the previous
   round's commit); its description is set with `jj describe`
   before the checklist runs, so the checklist's commit-message
   check (covering `fork_point(main | @)..@ ~ merges()`, which
   includes a described working-copy commit) validates the
   round's own message; the next round's `jj new` closes it.
   Every description comprises a subject line in the commit
   convention and a body summarizing the round's changes,
   surfaced-tie resolutions, and any cross-round repairs — a
   subject line alone is not sufficient. The automated check
   validates the subject line only
   (`scripts/check-commit-msg.sh` receives
   `description.first_line()`); the body requirement is enforced
   by the session and verified in the user's line-by-line
   review.
   After round 4 closes (terminal `jj new`, before the
   spec/plan-removal commits), the full checklist runs on the
   completed aspect commits; a repair found then is made in the
   terminal working-copy commit and squashed into the round-4
   commit with `jj squash` (its parent, whose only descendant at
   that point is the terminal commit being squashed, so no other
   commit is rewritten), the round-4 message is
   amended to note the repaired aspect, and the checklist is
   re-run until it passes on the final state. The
   spec/plan-removal commits (which touch only
   `docs/superpowers/` files) are then added, and the full
   checklist runs once more on the branch tip immediately before
   the user's review, covering every commit's message; a failure
   at that point can concern only the removal commits and is
   repaired by `jj describe` on the offending commit for a
   message failure (a description-only rewrite changes no
   content, so it cannot produce conflicts) or by squashing into
   the head removal commit for a content failure, again
   re-running until a full pass covers the final state.
7. A violation owned by an earlier round and discovered later
   (by a later round's subagent or the final checklist run) is
   fixed in the discovering round's commit and noted in that
   commit's message. It is not repaired into the owning commit:
   rewriting an intermediate commit whose lines later rounds
   also touched — the normal case, since every round covers the
   same files — produces conflict commits, which the recommended
   `git.private-commits = 'conflicts()'` configuration rejects
   at push. Repairs arising from the post-round-4 and final
   checklist runs follow step 6: each is squashed into the
   then-current head commit, which has no descendants, so the
   conflict hazard above does not arise.

## Branch shape

Topic branch `style/mathlib-conventions` off `main`, ordered per
CONTRIBUTING § Concern shape:

1. Spec and plan commits (with adversarial-review iterations).
2. The rules-doc alignment commit (`doc` type) applying the
   § Authoritative references corrections and decisions to
   `docs/rules/lean-coding.md`, `CONTRIBUTING.md`, the parallel
   prose-rule statements, and the retired `TODO.md` trigger. The
   alignment commit follows the same discipline as a round:
   described (subject plus body) with `jj describe`, and
   `scripts/pre-push.sh` passes at it before round 1 opens.
3. The four aspect commits.
4. Commits removing the spec and plan.

No push before the user's line-by-line review. The `style/`
prefix is not among the prefixes `scripts/pre-push.sh` treats as
PR-candidates (`feat/`, `fix/`, `refactor/`, `migrate/`), so its
PR-candidate reminders do not fire for this branch; the
review-before-push requirement is therefore stated here rather
than relied on from tooling.

## Constraints

- The mathematical content is preserved exactly: the theorem-set
  and every interface are unchanged up to identifier renaming.
- The constructive discipline and the permitted-axiom policy are
  untouched; `GebMeta.classicalAllowedModules` entries change
  only to track module renames.
- No new mathematical definitions are introduced; the
  transcription-or-novel marking required for mathematical specs
  is not applicable.
