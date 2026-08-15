# GebLang literate design: adversarial review, round 4

Reviewer: fresh-context agent, 2026-08-15. Focus: end-to-end
coherence of the round-3 restructure (the deferred consumption
cluster). Sources: the full spec and prior review records; the
repository's scripts, workflows, lakefile, umbrellas, and rule
documents; the verso checkout (including the `v4.28.0`/`v4.29.0`
tags); the pinned doc-gen4 and Cslib checkouts;
`teorth/analysis` re-fetched. Every prior-round claim it
spot-checked held, and it discharged three posed coherence
questions from the sources: the forced-mathlib-track sentence is
temporally sound (the allowance and the check land together),
the conditional `Cslib.Init` rule is expressible inside
`check_subtree`'s existing per-file loop, and § Verification is
consistent with the deferral.

Verdict: not converged (no blocker; two serious findings, both
re-synchronization edits). Every finding is addressed below; the
spec edits land in this round's commit.

## Findings and responses

Serious.

1. § Goal was not re-synchronized with the restructure: it
   stated "every existing subtree may import it" as current fact
   and claimed "both extraction pipelines" for this workstream.
   Fixed: the Goal states the gating (`Geb/Internal/` and its
   mirror now; the upstream-eligible subtrees once the cluster
   lands) and names the two documentation pipelines, with
   extraction tooling listed among the deferrals.
2. The rule-table widening in `docs/rules/upstream-eligible.md`
   sat on the wrong side of the deferral line: widening the four
   existing rows now would falsify the file's statement that
   `lint-imports.sh` enforces its table. Fixed: the table gains
   only the honest `GebLang` row now; the row widening is
   deferred with the consumption cluster, and the pending change
   is described in the floodgate prose with its activation point
   and in `TODO.md`.

Minor.

1. Which import forms trigger the conditional `Cslib.Init` rule
   was unspecified. Fixed: all four forms trigger it.
2. Whether the `GebTests/Lang/` entry carries the conditional
   was unstated. Fixed: it does.
3. The test entry's leakage prefixes were unstated. Fixed:
   `GebTests.Lang.` beside `GebLang.`, per the mirror pattern.
4. "an `import Cslib` line" named the bare-umbrella form; the
   trigger is any `Cslib.*` import line. Fixed.
5. The `paths:` extension's exclusion of the `GebLang.lean`
   umbrella was silent. Fixed: stated, with the reason (the
   umbrella imports `GebMeta` and is exempt from the content
   rules) and the deviation from the umbrella-plus-directory
   pattern named.
