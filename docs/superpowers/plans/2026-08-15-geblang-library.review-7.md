# Library plan, adversarial review round 7: response

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verdict](#verdict)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [What the round established](#what-the-round-established)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewer: a seventh fresh general-purpose agent, no conversation
context, which verified each of round 6's changes by applying it and
reading the result, then read the plan end to end and ran every
command it gives.

## Verdict

Round 7: **CONVERGED**. No blocker, no serious, two minor, two
cosmetic-taste, no spec defect.

This is the plan's first clean round. Both minor findings are fixed
and one cosmetic-taste finding is rejected with its reason.

## Minor

Both fixed.

- M1, round 6's list-marker correction replaced a sentence in the
  rule-document bullet without re-flowing the rest, leaving a
  22-character line between two full ones. Re-flowed. This class of
  defect has now appeared in five consecutive rounds and no tool
  catches it: `markdownlint`, `doctoc` and Vale are all blind to a
  short line inside a filled paragraph, so it is caught only by
  reading. The remaining short lines in the plan were checked and are
  natural wraps before an unbreakable code span.
- M2, the executor-context bullet on the mathlib linters named
  `GebLang/Basic.lean` alone. The reviewer traced the closures: none
  of the four Lean files this plan creates has mathlib in its import
  closure, `GebMeta` not carrying it either, so the linters run on
  none of them. An executor could have read the bullet as implying
  the other three were tooling-checked. The bullet now says all four.

## Cosmetic-taste

- C1, § Global constraints stated the marker choice as an inference
  from all three markers working, where the reason is repository
  convention. Fixed; both statements of it now use the same
  connective.
- C2, `scripts/literate.sh`'s header says CI runs its build verb,
  which becomes true two commits later on the same branch.
  **Rejected.** `scripts/manual.sh` carries the identical sentence
  about `doc-build.yml`, the statement is true at branch end and at
  every merged state, and the header describes the script's role
  rather than the branch's progress. The reviewer graded it
  defensible as written and raised it only for the class.

## What the round established

The reviewer confirmed round 6's corrections and found them sound:
Verso accepts `*`, `-` and `+`, and both Lean sources elaborate with
`-` bullets under the full option set; `CanonicalSExpr.lean`'s two
sample declarations do reference a third module, so only its `#guard`s
reference the annotated imports; `@[expose] public section` is
exclusive outside `Geb/Mathlib/` and the majority inside it; the
`mk_all-check` deferral's three pulled-forward instances match the
spec's sweep list exactly; and the `doctoc` step's claims hold, with
`doctoc --update-only .` a byte-level no-op on the applied tree.

It also checked several things no earlier round had: Vale run
differentially against the applied files, which shows no new alert;
a TOML parse confirming `doc.verso` binds to `GebLang` and sets no
option on `GebMeta`; Lake's own documentation of driver-argument
order, which is what makes the `[Geb, GebLang]` lint output correct;
`lake shake --keep-prefix` being a bare flag, so the widened
invocation is a three-module list; that nothing this plan adds falls
inside `scripts/lint-imports.sh`'s scanned roots, so the floodgate is
untouched until plan 2; and that `GebTests/Mathlib.lean` matches the
index form Task 2 models itself on.

Two commands cannot be run without creating the library:
`lake build :literateHtml`, whose facet reads `literate.toml` from the
package root, and `lake build GebLang:docs`, a cold doc-gen4 build.
Both costs are documented in the plan's § Executor context.

The standing escalations are unchanged and consistently stated in all
three places they appear: the pinned doc-gen4 does not render Verso
module docstrings, which contradicts the spec's § Context and its
§ Standards and rule documents, and the spec's "acceptable to both
pipelines" sentence cannot be written as worded.
