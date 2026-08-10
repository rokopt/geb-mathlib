# Ranked-alphabet tree encoding implementation plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
- [File structure](#file-structure)
- [Namespace and section structure](#namespace-and-section-structure)
- [Declaration inventory](#declaration-inventory)
- [Findings established by building](#findings-established-by-building)
- [The image characterisation](#the-image-characterisation)
- [The two-symbol alphabet](#the-two-symbol-alphabet)
- [The test mirrors](#the-test-mirrors)
- [The commits](#the-commits)
- [Deferred](#deferred)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

**Goal:** Encode the term algebra of any finite ranked alphabet as a
bitstring, decide the image of that encoding by a single right-to-left scan,
and exhibit the existing `BinTree` encoding as the two-symbol instance.

**Architecture:** A ranked alphabet names a finitary polynomial functor whose
shape type is `Fin card`, and its term algebra is that functor's W-type, as
`BinTree` is the W-type of `BinTree.Direction`. Each symbol is spelled by a
fixed-width block of bits followed by its children's spellings, which agrees
with `BinTree.print` at width one. Validity is a fold whose state carries an
incomplete block, the count of pending subterms and a liveness flag. The image
is characterised through that scan, as `BinTree.valid_iff_exists_print` is
characterised through `depth` and `ok`.

**Tech Stack:** Lean 4 (v4.33.0-rc2), mathlib, `lake build`, `lake test`,
`lake lint`, `lake shake`.

This plan records branch B1 of
[the design](../specs/2026-08-09-ranked-tree-recognizers-design.md). B2 to B5
are separate branches and are not started here.

This document was written as a forecast and rewritten from the committed
code. Where the two disagreed the code is authoritative; the forecast's
superseded proof scripts are not preserved.

## Global constraints

- No `noncomputable`; minimise `Classical`. Every new module is held to the
  axiom set `{propext, Quot.sound}` and is not added to
  `GebMeta.classicalAllowedModules`. `lake lint` confirms this for `Geb` and
  `GebTests`, and `valid_iff_exists_spell`, `valid_iff_isSome_parse`,
  `spell_injective` and `Binary.valid_iff` were additionally read
  individually.
- All recursion and induction through recursors. No `induction` tactic, no
  self-calling `def`, no `termination_by`, no self-referential `inductive`.
- Bound `Fin` and `Nat` arithmetic by `omega` or by cases, per
  [docs/rules/lean-coding.md](../../rules/lean-coding.md) § Constructive-only
  Lean code: the choice-dependent and choice-free lemmas of `Nat`'s division
  and order API interleave under no separating convention.
- `Geb/Mathlib/` may import only `Mathlib.*`, `Batteries.*`, `Geb.Mathlib.*`.
  The prefix `Geb.Mathlib.` appears only on `^import` lines.
- Every `.lean` file: `module` keyword after the copyright block, the mathlib
  copyright header, a module docstring with `# Title`, a summary, and every
  mandatory section that has content, `## Tags` included; a `/-- … -/`
  docstring on every `def`, `structure`, `instance`, every structure field,
  and every theorem of public interest. The unfolding lemmas `size_mk`,
  `spell_mk`, `parseAux_succ`, `scanFrom_nil`, `scanFrom_cons`,
  `scanFinal_nil` and `scanFinal_cons` carry none, matching
  `Geb/Mathlib/Data/Tree/Preorder.lean`. `decodeBits_cons` and
  `parseChildren_succ` do carry one: each names why its `def` has no
  generated equation lemma, which is not evident from the statement.
- 100-column lines, two-space indent, `UpperCamelCase` for `Prop` and `Type`,
  `lowerCamelCase` for values, `snake_case` for theorems.
- No `sorry` in any commit; no `native_decide` anywhere.
- Tests are named `theorem`s and the `def`s they are stated at, matching
  `GebTests/Mathlib/Data/Tree/Preorder.lean`. No anonymous `example` (the
  axiom linter does not audit one).
- VCS is `jj`. Never a mutating `git` subcommand. No push without
  line-by-line review by the user.

## File structure

| File | Responsibility |
| --- | --- |
| `Geb/Mathlib/Data/Tree/Ranked/Basic.lean` | the alphabet, the term algebra, `size`, the induction principle |
| `Geb/Mathlib/Data/Tree/Ranked/Code.lean` | symbol codes, their decoding, the arity lookup, the round trip |
| `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` | the spelling, the descent, the scan, validity, the bijection |
| `Geb/Mathlib/Data/Tree/Ranked/Binary.lean` | the two-symbol alphabet and its equivalence with `BinTree` |
| `Geb/Mathlib/Data/Tree/Ranked.lean` | index over `{Basic,Code,Preorder,Binary}` |
| `Geb/Mathlib/Data/Tree.lean` | gains one `public import` |
| `GebTests/Mathlib/Data/Tree/Ranked/{Basic,Code,Preorder,Binary}.lean` | mirrors |
| `GebTests/Mathlib/Data/Tree/Ranked.lean` | test index |
| `GebTests/Mathlib/Data/Tree.lean` | gains one `import` |
| `docs/index.md`, `TODO.md` | module entries, follow-on work |

The declaration `RankedAlphabet` is named apart from the directory holding it,
as `Data/Tree/Binary.lean` holds `BinTree`.

Import lists, as committed and as `lake shake` accepts them:

- `Ranked/Basic.lean`: `Mathlib.Data.W.Basic`.
- `Ranked/Code.lean`: `Geb.Mathlib.Data.Tree.Ranked.Basic`,
  `Mathlib.Algebra.GroupWithZero.Nat`. The forecast named
  `Mathlib.Data.Nat.Bitwise`; `Nat.testBit` and its lemmas are reachable
  without it, and `pow_succ'` is not.
- `Ranked/Preorder.lean`: `Geb.Mathlib.Data.Tree.Ranked.Code`,
  `Mathlib.Algebra.BigOperators.Ring.List` (for `List.sum_map_mul_left`),
  `Mathlib.Computability.Encoding`.
  `Mathlib.Algebra.Order.BigOperators.Group.List` is absent: it was to supply
  `List.le_sum_of_mem`, which routes through ordered-algebra instances the
  axiom rules warn about, and `size_le_sum_ofFn` proves the needed bound
  directly instead.
- `Ranked/Binary.lean`: `Geb.Mathlib.Data.Tree.Ranked.Preorder`,
  `Geb.Mathlib.Data.Tree.Preorder`, `Mathlib.Data.Fin.VecNotation`.
- Test modules `import` their subject module and `public import`
  `GebTests.Mathlib.Data.Tree.Ranked.Basic` for the shared fixtures. Only the
  `Basic` mirror declares a `RankedAlphabet` literal, so only it imports
  `Mathlib.Data.Fin.VecNotation`.

## Namespace and section structure

`Basic.lean`, `Code.lean` and `Preorder.lean` each open `namespace
RankedAlphabet` and `public section` once and close with `end` /
`end RankedAlphabet`. `Binary.lean` opens `namespace RankedAlphabet.Binary`;
`binRanked` was moved there from the root during review, the root being
reserved for `RankedAlphabet` itself. `Scan` is declared inside
`RankedAlphabet`, as `RankedAlphabet.Scan`. The test
mirrors use `@[expose] public section` for the fixture module and
`set_option linter.privateModule false` for the other three.

No library module declares a name in the root namespace except
`RankedAlphabet` itself. The mirrors declare their fixtures and assertions at
the root, matching the merged `GebTests/Mathlib/Data/Tree/Preorder.lean`.

## Declaration inventory

Every declaration committed. Namespace `RankedAlphabet` is elided.

| File | Declarations |
| --- | --- |
| Basic | `RankedAlphabet` (root, fields `card width width_pos card_le_two_pow_width arity`), `Term`, `Term.mk`, `Term.size`, `size_mk`, `Term.induction`, `size_le_sum_ofFn` |
| Code | `code`, `decodeBits`, `decodeBits_cons`, `arOf`, `length_code`, `mod_two_mul`, `decodeBits_code`, `arOf_decodeBits_code`, `getElem_code_eq`, `testBit_decodeBits` |
| Preorder, encoding | `spell`, `spell_mk`, `length_spell` |
| Preorder, descent | `decodeBlock`, `parseChildren`, `parseChildren_succ`, `parseStep`, `parseAux`, `parseAux_succ`, `parse` |
| Preorder, retraction | `decodeBlock_code_append`, `parseChildren_flatten`, `parseAux_spell`, `parse_spell`, `encoding`, `spell_injective` |
| Preorder, converse | `decodeBlock_eq_some`, `parseChildren_eq_some`, `parseAux_eq_some`, `parse_eq_some_iff` |
| Preorder, scan | `Scan`, `scanStep`, `scanFrom`, `scanFinal`, `validBool`, `Valid`, its `DecidablePred` instance, `scanFrom_nil`, `scanFrom_cons`, `scanFinal_nil`, `scanFinal_cons`, `scanFrom_append`, `scanFrom_not_live`, `scanFrom_short`, `scanFrom_code`, `scanFrom_flatten`, `scanFrom_spell`, `valid_spell` |
| Preorder, image | `add_one_mod`, `scanStep_eq_of_live`, `length_buf_scanFinal_of_live`, `exists_code_of_scanFrom_live`, `eq_nil_of_live_of_buf_nil_of_depth_eq_zero`, `exists_children_append_of_le_depth`, `exists_spell_append_of_live_of_buf_nil_of_one_le_depth`, `exists_spell_of_valid`, `valid_iff_exists_spell`, `valid_iff_isSome_parse` |
| Binary | `binRanked`, `leafSym`, `nodeSym`, `leaf`, `node`, `code_leafSym`, `code_nodeSym`, `spell_leaf`, `spell_node`, `ofBinTree`, `toBinTree`, `toBinTree_ofBinTree`, `ofBinTree_toBinTree`, `termEquiv`, `spell_termEquiv`, `valid_iff` |

The forecast named `getElem_take_eq_testBit` and
`width_le_length_of_one_le_depth` as separate lemmas; `decodeBlock_eq_some`
and `exists_spell_append_of_live_of_buf_nil_of_one_le_depth` establish those
bounds inline. It named `buf_length_scanFinal`, delivered as
`length_buf_scanFinal_of_live`.

Review removed three declarations that earned nothing and moved two.
`width_le_length_spell` had no consumer, `parse_spell` taking its fuel bound
from `length_spell` directly; `Scan` derived `DecidableEq` and `Repr`, neither
of which anything used and the first of which the module's own implementation
note explains why it avoids. `size_le_sum_ofFn` is about `Term.size` and
`List.ofFn` alone and moved to `Basic.lean`; `getElem_code_eq` is about `code`
and `Nat.testBit` alone and moved to `Code.lean`.

## Findings established by building

Each cost a failed build. A departure from one of them will not compile.

1. **`Valid` is `validBool w = true`, not a `Scan` equation.** The derived
   `DecidableEq Scan` does not reduce under `decide` at a symbolic fold. A
   `Bool`-valued function with a `= true` wrapper does. The obstruction is a
   `Decidable` instance that does not itself reduce — not the use of a
   decidable test: `decodeBlock` branches on a `dite` over a decidable
   conjunction and reduces.
2. **`scanStep` matches on `Bool` values**, following finding 1: the state's
   `live` field is a `Bool`, and matching it keeps the fold reducing.
3. **`Term.mk R i ch`, never `R.Term.mk i ch`.** Generalized field notation
   resolves `R.Term` first, and a `Type` carries no `mk`.
4. **`![…]` needs `Mathlib.Data.Fin.VecNotation`**, or `![0, 2]` parses as
   boolean negation applied to a list.
5. **`0 < width` is required**, and what it discharges is
   `t.size ≤ (spell t).length`, via `t.size ≤ width * t.size` — the fuel
   `parse` hands `parseAux`. It is also what makes peeling a block shorten the
   word in the image characterisation's `Nat.rec`.
6. **A symbol index must carry an assigned bound proof.** `binRanked.arity i`
   reduces for a literal index, so `Fin (arity ⟨0, h⟩)` is `Fin 0` and
   `Fin (arity ⟨1, h⟩)` is `Fin 2` — but only once `h` is assigned. Written
   inline, `⟨0, by decide⟩` leaves `h` an unassigned metavariable while the
   child family elaborates, and the family's domain is then neither. `leafSym`
   and `nodeSym` name the two indices. Against an index that is itself a
   pattern variable the situation is different again: the goal
   `0 < binRanked.arity ⟨1, h⟩` carries the free variable `h`, which `decide`
   refuses, and presents the arity as an atom, which `omega` cannot unfold, so
   the bound is ascribed with `show (0 : ℕ) < 2` and proved against the
   definitionally equal closed goal. The forecast's `by decide +revert` is not
   the working form in either situation.
7. **`Nat.land` is not exposed, so a block does not reduce during
   elaboration.** `code_leafSym` and `code_nodeSym` are proved by `decide`,
   which the kernel evaluates, not by `rfl`; and every downstream spelling
   rewrites through them rather than reducing `code`.
8. **`Nat.mod_mul` depends on `Classical.choice`**, and `omega` cannot
   discharge a residue identity whose modulus is a variable. `mod_two_mul` and
   `add_one_mod` replace the two the development needs, proved from
   `Nat.div_add_mod`, `Nat.mul_add_mod`, `Nat.mod_eq_of_lt` and
   `Nat.mod_self`, all choice-free. Expect the same trap in any further `Nat`
   division reasoning.
9. **`decide` on `parse w = some t` is available but not used.** mathlib has
   no `DecidableEq (WType …)`; `Geb/Mathlib/Data/W/Basic.lean` supplies one
   for `[DecidableEq α] [∀ a, FinEnum (β a)]`. The mirrors state the descent's
   value through `Option.map` of the spelling anyway, which costs neither that
   import nor the `FinEnum` instances its `decide` would reduce through. The
   forecast's claim that no instance exists is wrong.
10. **`linter.flexible` and `linter.unnecessarySeqFocus` are errors here.** A
    bare `simp` that modifies the goal must be terminal, and `tac1 <;> tac2`
    where `tac1` leaves one goal fails.
11. **`linter.style.show` rejects a `show` that changes the goal.** Where a
    goal is restated up to definitional unfolding, the tactic is `change`.
12. **Sweep budgets are per-computation, not per-word-count.**
    `set_option maxRecDepth 100000 in decide` is valid in tactic position and
    is what the 511-word sweeps need. The count is not what decides it: at 127
    words the `validBool`-against-`parse` sweep closes at the default depth
    while `length_wordsUpTo_six`, which builds the same enumeration, does not.
    The forecast's "127 words works at the default" was measured on one of the
    two and generalised. `native_decide` is banned (compiler-trust axiom).

## The image characterisation

`spell` is prefix notation and `scanFrom` is a `foldr`, so the head symbol's
block sits at the word's left end and is the block the scan reads last. The
step therefore splits off the leading block: `w = w.take width ++ w.drop
width`, whence `scanFinal w = scanFrom (w.take width) (scanFinal (w.drop
width))` by `scanFrom_append`. A trailing-block split yields a suffix
decomposition, which is not what the goal asks for, and neither piece is
`scanFinal` of anything.

The pieces, in dependency order:

- `add_one_mod` — the residue of a successor, in terms of the residue.
- `scanStep_eq_of_live` — one step that leaves the scan live either
  accumulated the bit or completed a block, popping the symbol's arity and
  pushing one. Proved once by cases on `s.live`, on
  `decide ((b :: s.buf).length = R.width)`, on `R.arOf …` and on
  `decide (r ≤ s.depth)`; the three dead branches close by
  `simp only [scanStep, …] at h` reducing the hypothesis to `false = true`.
  It is the single case analysis of `scanStep`, and the next three lemmas are
  its only consumers.
- `length_buf_scanFinal_of_live` — a live scan's incomplete block holds the
  word's length modulo the width, so block boundaries align with the word's
  right end.
- `exists_code_of_scanFrom_live` — the converse of `scanFrom_code`: a live
  scan over a full block exhibits that block as a symbol's code. The symbol is
  `⟨decodeBits blk, _⟩` and `code i = blk` follows by `List.ext_getElem` from
  `getElem_code_eq` and `testBit_decodeBits`, as in `decodeBlock_eq_some`.
- `eq_nil_of_live_of_buf_nil_of_depth_eq_zero` — a live scan with no
  incomplete block and nothing pending has read nothing.
- `exists_children_append_of_le_depth` — a live scan with at least `k`
  pending subterms has `k` spellings as a prefix. It takes the one-subterm
  extraction as a hypothesis `ih`, as `parseChildren_flatten` takes the
  descent's, so that both recursions sit at one explicit `ℕ` bound and no
  well-founded recursion is needed.
- `exists_spell_append_of_live_of_buf_nil_of_one_le_depth` — the `Nat.rec`
  over that bound. Its step establishes `width ≤ w.length` from
  `w.length % width = 0` and `w ≠ []`, splits the leading block, recovers the
  head symbol, and applies the previous lemma at that symbol's arity.
- `exists_spell_of_valid`, `valid_iff_exists_spell`, `valid_iff_isSome_parse`
  — the characterisation and its reading as a decision procedure.

## The two-symbol alphabet

`binRanked` is `⟨2, 1, Nat.one_pos, by decide, ![0, 2]⟩`. `ofBinTree` and
`toBinTree` are `WType.elim` folds; `toBinTree` matches the head index as
`⟨0, _⟩`, `⟨1, _⟩` and `⟨n + 2, h⟩`, discharging the last from
`show n + 2 < 2 from h`. `termEquiv` packages the two with
`toBinTree_ofBinTree` and `ofBinTree_toBinTree`.

`spell_termEquiv` is an equality of words, so the two encodings are one
function up to the equivalence rather than two bijections onto one language;
`valid_iff` follows from it through `valid_iff_exists_spell` and
`BinTree.valid_iff_exists_print`.

No W-type congruence along an equivalence of polynomial functors exists in
mathlib or in this repository, so the equivalence is built at the concrete
alphabet. Defining one in general is a separate concern and a separate branch.

## The test mirrors

`GebTests/Mathlib/Data/Tree/Ranked/Basic.lean` declares the shared fixtures
and is `public import`ed by the other three. `sampleAlphabet` is
`⟨4, 2, by decide, by decide, ![0, 1, 2, 3]⟩`, whose `card` is `2 ^ width`, so
every one of its blocks spells a symbol; `narrowAlphabet` is
`⟨3, 2, by decide, by decide, ![0, 1, 2]⟩`, whose `card` is below `2 ^ width`,
so the block `[true, true]` spells none and the scan's remaining rejection is
reachable from a word. Review added the second alphabet: with only the first,
no assertion in the suite reached that rejection, and a scan that ignored
`card_le_two_pow_width` would have passed every one. The fixtures also declare
the symbol indices `sampleSym0` and `sampleSym2`, the terms `sampleNullary`
and `sampleBinary`, and `wordsUpTo`, the words over `Bool` of at most a given
length; `size_sampleNullary` and `size_sampleBinary` give their node counts,
and `length_wordsUpTo_six` and `length_wordsUpTo_eight` pin the enumeration's
size, so a `wordsUpTo` that dropped words could not silently weaken the sweeps.

The `Code` mirror asserts the blocks of the two named symbols
(`code_sampleSym0`, `code_sampleSym2`), the value a block denotes
(`decodeBits_code_sampleSym2`), the arity it carries (`arOf_zero`,
`arOf_two`), the absence of an arity beyond the alphabet (`arOf_four`) and a
block entry as a bit of the value (`testBit_decodeBits_sampleSym2`).

The `Preorder` mirror asserts the spelling of each worked term, the descent's
value on each, `Valid` on the two spellings, and the scan's four rejections: a
word carrying two terms, a word ending mid-block, an underflowing word, and —
at `narrowAlphabet` — a word whose block spells no symbol, with
`valid_narrow_nullary` alongside it so that rejection separates the two
alphabets rather than rejecting everything. It then sweeps `validBool` against
`Option.isSome ∘ parse` over every word of length at most eight, at both
alphabets. Review raised the bound from six: the accepted words of length at
most six are four in number and use arities zero, one and two only, so
`sampleAlphabet`'s arity-three symbol went unexercised, its shortest accepted
word having length eight.

The `Binary` mirror asserts the spelling of `binarySample`'s image under
`termEquiv`, the value `BinTree.print` gives there, and the agreement of
`binRanked.validBool` with `decide (BinTree.Valid ·)` over every word of
length at most eight. Review removed two assertions that restated
`code_leafSym` and `code_nodeSym` verbatim, statement and proof, rather than
stating anything at a fixture.

The descent's value is asserted through `Option.map` of the spelling rather
than against the term. The spelling is a `List Bool`, so no
`DecidableEq (WType _)` instance is needed; `Geb/Mathlib/Data/W/Basic.lean`
supplies one that would serve, at the cost of an import and of the `FinEnum`
instances its `decide` would then reduce through.

## The commits

On top of `feat(tree): add the ranked-alphabet encoding and its descent`,
which delivered `Basic.lean`, `Code.lean` and `Preorder.lean` up to
`valid_spell`, and `doc(tree): hand off the ranked-encoding branch`, which
added the second, superseded plan document
`2026-08-10-ranked-tree-handoff.md`:

1. `fix(tree): minimise the code module's imports`
2. `feat(tree): characterise the ranked encoding's image`
3. `feat(tree): exhibit binary trees as ranked terms`
4. `test(tree): mirror the ranked encoding and its descent`
5. `doc(tree): catalogue the ranked encoding modules`
6. `fix(tree): apply the confirming review round`
7. `doc(tree): record the branch's follow-on work`

The handoff document, this plan and the specification are all removed in the
branch's final commit, per
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape.

Commit 6 applies one confirming adversarial round — three fresh reviewers, on
Lean correctness, process conformance and design coherence, with the code
rather than a document as the artifact under test. Each reported no blocker.
The two serious findings, both in persistent artifacts, were a false
dependency line in `docs/index.md` and the specification's claim that the
modules carry a `## References` section; the § Deferred entry below records the
second. The rest were the test-coverage, dead-declaration, module-placement,
docstring and import-order items named above and in § Deferred.

The full check — `lake build`, `lake test`, `lake lint`,
`lake lint -- GebTests`, `lake shake --add-public --keep-implied
--keep-prefix Geb GebTests`, `scripts/lint-imports.sh`, the Markdown checks
and `scripts/pre-push.sh` — passes.

## Deferred

- **The `## References` section the specification promised.** The
  specification classed `spell` as a transcription of prefix (Łukasiewicz)
  notation and committed the modules to naming it in `## References`, while
  citing as precedent the merged `Geb/Mathlib/Data/Tree/Preorder.lean`, which
  implements the same encoding at width one and names prefix notation in prose
  with no citation. Review found the two artifacts contradicting each other.
  Resolved by amending the specification rather than the code: `spell` is a
  fixed-width block encoding of a ranked term algebra whose idea is prefix
  notation but whose definition transcribes no source's, so under
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature when
  transcribing it owes prose context and not a `[Key]`. No Ranked module
  carries a `## References` section.
- **`docs/references.bib` gains no entry.** The three works the design cites
  for context — `BenoitDemaineMunroRamanRamanRao2005`, `Mehlhorn1980`,
  `BraunmuhlVerbeek1983` — are cited by nothing committed. Each is added by
  the branch that first cites it. `BarringtonCorbett1989` stays out on the
  separate ground that neither its bibliographic detail nor its
  DLOGTIME-uniform TC⁰ claim has been verified against the article.
- **The placement of `mod_two_mul` and `add_one_mod`.** Both are facts about
  `ℕ` with no ranked-alphabet content, and both sit in `namespace
  RankedAlphabet`, where `open RankedAlphabet` presents them bare beside
  `Nat`'s own residue API. The repository's pattern for supplements to a
  mathlib module is a module mirroring its path, as
  `Geb/Mathlib/Data/Vector/OfFn.lean` and `Geb/Mathlib/Logic/Equiv/Basic.lean`
  do, which would put them under `Geb/Mathlib/Data/Nat/`. That move spans a
  commit older than this branch's concern and is recorded in `TODO.md`.
- **mathlib's `FirstOrder.Language` was considered and not used.**
  `Mathlib/ModelTheory/Basic.lean`'s `Language` indexes function symbols by
  arity (`Functions : ℕ → Type`) rather than naming a fixed symbol count, so
  there is no `Fin card` for a fixed-width block to spell, and
  `Mathlib/ModelTheory/Syntax.lean`'s `Term α` is the free algebra on a
  variable set rather than the closed term algebra. Neither matches what the
  encoding needs, and the W-type presentation is the repository's stated
  discipline for a self-referential datatype.
- **No W-type congruence along an equivalence of polynomial functors** exists
  in mathlib or here, so `termEquiv` is built at the concrete alphabet, which
  is how `Mathlib/Data/W/Constructions.lean` builds `WType Natβ ≃ ℕ` and
  `WType (Listβ γ) ≃ List γ`. Since B4 deletes `BinTree`, a general congruence
  would be built and immediately discarded.
- The design's `Scanner`, `Fold`, the absorption of `BinTree`, and the
  time-and-space bound are branches B2 to B5, recorded in `TODO.md`.
