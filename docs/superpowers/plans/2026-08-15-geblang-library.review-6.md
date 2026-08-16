# Library plan, adversarial review round 6: response

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verdict](#verdict)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [Clean](#clean)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewer: a sixth fresh general-purpose agent, no conversation
context, which verified each of round 5's seven changes by applying
it and reading the result, then read the plan end to end.

## Verdict

Round 6: NOT CONVERGED. No blocker, one serious, three minor, two
cosmetic-taste.

Every finding is fixed. All seven of round 5's changes were confirmed
correct, which is the first round in which no fix had to be redone.

## Serious

**S1, the Verso list-marker constraint is false, and the plan commits
it to a persistent rule document.** Fixed. The plan asserted in four
places that a Verso list item starts with `*` and not with `-`. Lean's
Verso parser accepts `*`, `-` and `+` alike:
`UnorderedListType.all = [.asterisk, .dash, .plus]`
(`Lean/DocString/Parser.lean:290`), and the parser's own error names
all three. Verified by elaborating the placeholder with `-` bullets
under the full option set plus `-Dweak.warningAsError=true`: exit 0.

Three consequences, all now repaired. The claim was headed for
`docs/rules/lean-coding.md`, where it would have bound the next
`GebLang` author, and `AGENTS.md` § Verify agent claims exists for
exactly this. It was the sole stated reason the two new sources used
`*` where every other module in the repository uses `-`, so the plan
was introducing a style divergence on a false premise; both sources
now use `-`. And Task 1 Step 5 pointed the executor at a parse-failure
mode that cannot occur.

The plan now says what is true: role syntax is what the two docstring
dialects differ in, all three markers open a list, and this library
writes `-` as the rest of the repository does.

## Minor

Each is fixed.

- M1, the `@[expose] public section` justification named the wrong
  precedent. Measured: `Geb/Mathlib/` is the only subtree where the
  plain form occurs at all, and even there `@[expose]` is the
  majority; `Geb/Internal/` and `GebTests/` use it exclusively. The
  choice stands, with the true attribution.
- M2, the `mk_all-check` deferral appealed to spec allocation, which
  the plan contradicts three times over: the spec's enumeration-sweep
  list also names three instances this plan edits. The real reason is
  given instead, that those three sit inside paragraphs this plan
  must re-flow anyway.
- M3, five short lines stranded mid-paragraph, two of them created by
  round 5's own fixes. Re-flowed. `markdownlint` and the 80-column
  rule are both blind to this, which is why it keeps recurring.

## Cosmetic-taste

Both fixed.

- C1, `CanonicalSExpr.lean` described as containing only `#guard`s; it
  also declares two samples, which reference a third module rather
  than either annotated import. The operative fact is now stated
  directly.
- C2, a `doctoc` branch describing an unreachable state:
  `--update-only` skips files without markers, so it cannot give a
  file markers.

## Clean

The reviewer confirmed by execution: all four Lean sources elaborate
with zero diagnostics and both negative controls reproduce; every
before-text matches exactly once and all nine edited files read
coherently; every doc-gen4, Lean-core and Verso citation is exact;
`lake build -v | grep ':default'`, `lake query --help`,
`lake build verso-serve`, the usage path, both workflow parses,
`bash -n`, `shellcheck` and the coverage-scan simulation all behave as
the plan states; and § File structure's file list is exactly the union
of the six tasks' own lists.

It recorded one spec inaccuracy already known and already corrected
in the plan's own comment: § Context has the literate target filter
running before any module is fetched, where the facet fetches every
library's module list first and gates only the per-module facets. The
compilation-bounding conclusion the spec draws from it holds.
