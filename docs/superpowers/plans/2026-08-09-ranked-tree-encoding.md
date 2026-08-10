# Ranked-alphabet tree encoding implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task. Steps
> use checkbox (`- [ ]`) syntax for tracking.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global Constraints](#global-constraints)
- [File structure](#file-structure)
- [Namespace and section structure](#namespace-and-section-structure)
- [Declaration inventory](#declaration-inventory)
- [Findings that bind the implementation](#findings-that-bind-the-implementation)
- [Tasks](#tasks)
  - [Task 1: The ranked alphabet and its term algebra](#task-1-the-ranked-alphabet-and-its-term-algebra)
  - [Task 2: Codes and their round trip](#task-2-codes-and-their-round-trip)
  - [Task 3: The spelling](#task-3-the-spelling)
  - [Task 4: The recursive descent](#task-4-the-recursive-descent)
  - [Task 5: The retraction](#task-5-the-retraction)
  - [Task 6: The descent reads only spellings](#task-6-the-descent-reads-only-spellings)
  - [Task 7: The scanning validity predicate](#task-7-the-scanning-validity-predicate)
  - [Task 8: Every spelling is valid](#task-8-every-spelling-is-valid)
  - [Task 9: Block alignment and sticky failure](#task-9-block-alignment-and-sticky-failure)
  - [Task 10: Every valid word is a spelling](#task-10-every-valid-word-is-a-spelling)
  - [Task 11: The binary alphabet](#task-11-the-binary-alphabet)
  - [Task 12: Bibliography](#task-12-bibliography)
  - [Task 13: Indices, documentation and the full check](#task-13-indices-documentation-and-the-full-check)
  - [Task 14: Record follow-on work and retire the transient artifacts](#task-14-record-follow-on-work-and-retire-the-transient-artifacts)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

**Goal:** Encode the term algebra of any finite ranked alphabet as a
bitstring, decide the image of that encoding by a single right-to-left
scan, and exhibit the existing `BinTree` encoding as the two-symbol
instance.

**Architecture:** A ranked alphabet names a finitary polynomial functor
whose shape type is `Fin card`, and its term algebra is that functor's
W-type, as `BinTree` is the W-type of `BinTree.Direction`. Each symbol is
spelled by a fixed-width block of bits followed by its children's
spellings, which agrees with `BinTree.print` at width one. Validity is a
fold whose state carries an incomplete block, the count of pending subterms
and a liveness flag. The image is characterised through a fuel-bounded
recursive descent, as `BinTree.valid_iff_exists_print` is.

**Tech Stack:** Lean 4 (v4.33.0-rc2), mathlib, `lake build`, `lake test`,
`lake lint`, `lake shake`.

This plan implements branch B1 of
[the design](../specs/2026-08-09-ranked-tree-recognizers-design.md).
B2 to B5 are separate plans and are not started here.

## Global Constraints

- No `noncomputable`; minimise `Classical`. Every new module is held to the
  axiom set `{propext, Quot.sound}` and is **not** added to
  `GebMeta.classicalAllowedModules`.
- All recursion and induction through recursors. No `induction` tactic, no
  self-calling `def`, no `termination_by`, no self-referential `inductive`.
- **Bound `Fin` and `Nat` arithmetic by `omega` or by cases**, per
  [docs/rules/lean-coding.md](../../rules/lean-coding.md) § Constructive-only
  Lean code: the choice-dependent and choice-free lemmas of `Nat`'s division
  and order API interleave under no separating convention. Where this plan
  names such a lemma, the axiom check of that task's build step is what
  decides whether it may stay.
- `Geb/Mathlib/` may import only `Mathlib.*`, `Batteries.*`,
  `Geb.Mathlib.*`. The prefix `Geb.Mathlib.` appears only on `^import`
  lines — never in `namespace`, declaration bodies, docstrings or comments.
- Every `.lean` file: `module` keyword after the copyright block, the
  mathlib copyright header, a module docstring with `# Title`, a summary,
  and every mandatory section that has content, `## Tags` included; a
  `/-- … -/` docstring on every `def`, `structure`, `instance`, every
  structure field, and every theorem of public interest. Unfolding lemmas
  (`size_mk`, `spell_mk`, `parseAux_succ`, `scanFrom_nil`, `scanFrom_cons`)
  are exempt, matching `Geb/Mathlib/Data/Tree/Preorder.lean`.
- 100-column lines, two-space indent, `UpperCamelCase` for `Prop` and
  `Type`, `lowerCamelCase` for values, `snake_case` for theorems.
- No `sorry` in any commit; no `native_decide` anywhere.
- No empty lines inside a declaration; a brief `-- …` comment separates
  instead.
- Commit messages: `type(scope): imperative subject`, lowercase, no
  trailing period, type from
  `feat | fix | doc | style | refactor | test | chore | perf | ci`.
- Tests are named `def`s returning `Bool` plus named `theorem`s, matching
  `GebTests/Mathlib/Data/Tree/Preorder.lean` and
  `GebTests/Mathlib/Computability/Cobham/Tree.lean`. No anonymous
  `example` (the axiom linter does not audit one). `#guard` is available in
  `GebTests` but is not used here.
- VCS is `jj`. Never a mutating `git` subcommand. No push without
  line-by-line review by the user.

## File structure

| File | Responsibility |
| --- | --- |
| `Geb/Mathlib/Data/Tree/Ranked/Basic.lean` | the alphabet, the term algebra, `size`, the induction principle |
| `Geb/Mathlib/Data/Tree/Ranked/Code.lean` | symbol codes, their decoding, the arity lookup, the round trip |
| `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` | the spelling, the descent, the scan, validity, the bijection |
| `Geb/Mathlib/Data/Tree/Ranked/Binary.lean` | the two-symbol alphabet and the specialisations to `BinTree` |
| `Geb/Mathlib/Data/Tree/Ranked.lean` | index over the four |
| `Geb/Mathlib/Data/Tree.lean` | gains one `public import` |
| `GebTests/Mathlib/Data/Tree/Ranked/{Basic,Code,Preorder,Binary}.lean` | mirrors |
| `GebTests/Mathlib/Data/Tree/Ranked.lean` | test index |
| `GebTests/Mathlib/Data/Tree.lean` | gains one `import` |
| `docs/references.bib`, `docs/index.md`, `TODO.md` | citations, module entries, follow-on work |

The declaration `RankedAlphabet` is named apart from the directory holding
it, as `Data/Tree/Binary.lean` holds `BinTree`.

Import lists, in full:

- `Ranked/Basic.lean`: `public import Mathlib.Data.W.Basic`.
- `Ranked/Code.lean`: `public import Geb.Mathlib.Data.Tree.Ranked.Basic`,
  `public import Mathlib.Data.Nat.Bitwise`.
- `Ranked/Preorder.lean`: `public import Geb.Mathlib.Data.Tree.Ranked.Code`,
  `public import Mathlib.Algebra.Order.BigOperators.Group.List` (for
  `List.le_sum_of_mem`), `public import Mathlib.Algebra.BigOperators.Group.List`
  (for `List.sum_map_mul_left`).
- `Ranked/Binary.lean`: `public import Geb.Mathlib.Data.Tree.Ranked.Preorder`,
  `public import Geb.Mathlib.Data.Tree.Preorder`,
  `public import Mathlib.Data.Fin.VecNotation`.
- Test modules import their subject module; `Code`, `Preorder` and `Binary`
  tests additionally import `GebTests.Mathlib.Data.Tree.Ranked.Basic` for
  the shared fixtures, and none of them imports `Mathlib.Data.Fin.VecNotation`
  (only the `Basic` test declares a `Ranked` literal).

If a build reports one of those imports removable, `lake shake` is right and
the lemma it was added for is not in fact used; drop it rather than
suppressing.

## Namespace and section structure

`Preorder.lean` opens `namespace RankedAlphabet` and `public section` once,
in Task 3, and closes with `end` / `end RankedAlphabet` at the foot of the
file. Tasks 4 to 10 each append **above those two closing lines**, inside
the section. No later task re-opens the namespace. `Scan` is declared
inside it, as `RankedAlphabet.Scan`. The other three modules each open and
close their own namespace within their own task.

Nothing in this plan declares a name in the root namespace except
`RankedAlphabet` itself.

## Declaration inventory

Every declaration the tasks produce. Namespace `RankedAlphabet` is elided
from the names below except where a declaration sits elsewhere.

| Declaration | Task | File |
| --- | --- | --- |
| `RankedAlphabet` (root), fields `card width width_pos card_le_two_pow_width arity` | 1 | Basic |
| `Term`, `Term.mk`, `Term.size`, `Term.induction`, `size_mk` | 1 | Basic |
| `code`, `decodeBits`, `decodeBits_cons`, `arOf` | 2 | Code |
| `length_code`, `decodeBits_code`, `arOf_decodeBits_code` | 2 | Code |
| `testBit_decodeBits` | 6 | Code |
| `spell`, `spell_mk`, `length_spell`, `width_le_length_spell` | 3 | Preorder |
| `decodeBlock`, `parseChildren`, `parseChildren_succ`, `parseStep`, `parseAux`, `parseAux_succ`, `parse` | 4 | Preorder |
| `decodeBlock_code_append`, `parseChildren_flatten`, `parseAux_spell`, `parse_spell` | 5 | Preorder |
| `getElem_code_eq`, `getElem_take_eq_testBit`, `decodeBlock_eq_some`, `parseChildren_eq_some`, `parseAux_eq_some`, `parse_eq_some_iff`, `spell_injective` | 6 | Preorder |
| `Scan`, `scanStep`, `scanFrom`, `scanFinal`, `validBool`, `Valid`, its `DecidablePred` instance, `scanFrom_nil`, `scanFrom_cons`, `scanFrom_append` | 7 | Preorder |
| `scanFrom_code`, `scanFrom_flatten`, `scanFrom_spell`, `valid_spell` | 8 | Preorder |
| `scanFrom_not_live`, `buf_length_scanFinal`, `width_le_length_of_one_le_depth` | 9 | Preorder |
| `exists_spell_append_of_live_of_buf_nil_of_one_le_depth`, `eq_nil_of_live_of_buf_nil_of_depth_eq_zero`, `exists_spell_of_valid`, `valid_iff_exists_spell`, `valid_iff_isSome_parse` | 10 | Preorder |
| `binRanked` (root), `Binary.leaf`, `Binary.node`, `Binary.termEquiv`, `Binary.spell_termEquiv`, `Binary.valid_iff` | 11 | Binary |

## Findings that bind the implementation

Each was established by running the code. A task that departs from one of
them will not build.

1. **`Valid` is `validBool w = true`, not a `Scan` equation.** The derived
   `DecidableEq Scan` does not reduce under `decide` at a symbolic fold. A
   `Bool`-valued function with a `= true` wrapper does, and it is the idiom
   `BinTree.ok` already uses. The obstruction is a `Decidable` instance
   that does not itself reduce — **not** the use of a decidable test.
   `decodeBlock` branches on a `dite` over a decidable conjunction and
   reduces; `parse_short`, `parse_trailing` and a 127-word sweep through
   `parse` all close by `decide` at default settings.
2. **`scanStep` matches on `Bool` values.** This follows finding 1 rather
   than a rule about `dite`: the state's `live` field is a `Bool`, and
   matching it keeps the fold reducing.
3. **`![…]` needs `Mathlib.Data.Fin.VecNotation`.** Without it `![0, 2]`
   parses as boolean negation applied to a list, and the error names `Bool`
   rather than the notation.
4. **`0 < width` is required**, and what it discharges is
   `t.size ≤ (spell t).length`, via `t.size ≤ width * t.size` — the fuel
   `parse` hands `parseAux`. It is also what makes a block peel shorten the
   word in Task 10's `Nat.rec`. It is not needed for a
   "fuel dominates the remaining length" invariant; no proof here uses one.
5. **A term at a concrete alphabet needs its arity to reduce.**
   `fun i ↦ i.elim0` fails (`Fin (R.arity ⟨0, _⟩)` against `Fin 0`), and so
   does `by omega` (`arity ⟨0, _⟩` is an opaque atom). The working form is
   `fun i ↦ absurd i.isLt (by decide +revert)`. A cast whose target is a
   metavariable also fails, so `Binary.node` names its target explicitly.
6. **`decide` cannot be used on `parse w = some t`.** mathlib has no
   `DecidableEq (WType …)`, so the instance does not synthesise. Assertions
   about the descent are stated through `Option.isSome` or by mapping
   `spell` over the result.
7. **The width-one specialisation holds.** `binRanked.validBool` agrees
   with `decide (BinTree.Valid ·)` on every one of the 2047 words of length
   at most ten. At 511 words the check needs `set_option maxRecDepth 100000`;
   at 127 words it does not.
8. **`simp` is a flexible tactic and `linter.flexible` is an error here.**
   A `simp […]` that modifies the goal and is followed by another tactic
   fails the build. Use `simp only [...]` with a named lemma list.

## Tasks

Task bodies below give the file, the interfaces, and the code. Each task
ends with `lake build` of its module **and** `lake lint`, so an axiom
regression is caught at the task that causes it rather than at Task 13.

### Task 1: The ranked alphabet and its term algebra

**Files:** create `Geb/Mathlib/Data/Tree/Ranked/Basic.lean` and
`GebTests/Mathlib/Data/Tree/Ranked/Basic.lean`.

**Interfaces:**

- Consumes: `Mathlib.Data.W.Basic`.
- Produces: `RankedAlphabet` with its five fields, `RankedAlphabet.Term`,
  `Term.mk`, `Term.size`, `size_mk`, `Term.induction`. Every later task
  consumes the first two; Tasks 3, 5, 8, 10 consume `Term.induction`;
  Task 3 consumes `Term.size` and `size_mk`.

- [ ] **Step 1: Write the failing test**

Create `GebTests/Mathlib/Data/Tree/Ranked/Basic.lean`. Its imports are
`Geb.Mathlib.Data.Tree.Ranked.Basic` and `Mathlib.Data.Fin.VecNotation`;
its module docstring is titled `# The ranked alphabet on a worked
signature`, summarises that it fixes the fixtures the sibling test modules
share and states `size` on two of their terms, lists `sampleAlphabet`,
`sampleNullary` and `sampleBinary` under `## Main definitions`, describes
the assertions under `## Main statements`, and carries
`## Tags`: `ranked alphabet, term algebra, W-type`.

The three fixtures are `public` because the `Code`, `Preorder` and `Binary`
test modules import them; a non-`public` declaration in a `module` is not
visible to an importer.

```lean
/-- Four symbols of arities zero to three, spelled by two bits each. The
sibling test modules share this alphabet. -/
public def sampleAlphabet : RankedAlphabet := ⟨4, 2, by decide, by decide, ![0, 1, 2, 3]⟩

/-- The nullary symbol's term. `by decide +revert` is what discharges the
empty child family; see finding 5. -/
public def sampleNullary : sampleAlphabet.Term :=
  sampleAlphabet.Term.mk ⟨0, by decide⟩ (fun i ↦ absurd i.isLt (by decide +revert))

/-- The binary symbol applied to two nullary terms. -/
public def sampleBinary : sampleAlphabet.Term :=
  sampleAlphabet.Term.mk ⟨2, by decide⟩ (fun _ ↦ sampleNullary)

/-- A nullary term has one node. -/
theorem size_sampleNullary : sampleNullary.size = 1 := by decide

/-- A binary term over two nullary terms has three nodes. -/
theorem size_sampleBinary : sampleBinary.size = 3 := by decide
```

- [ ] **Step 2: Run to verify it fails**

```bash
lake build GebTests.Mathlib.Data.Tree.Ranked.Basic
```

Expected: FAIL, `unknown module Geb.Mathlib.Data.Tree.Ranked.Basic`.

- [ ] **Step 3: Write the module**

Create `Geb/Mathlib/Data/Tree/Ranked/Basic.lean` with the mathlib copyright
header, `module`, `public import Mathlib.Data.W.Basic`, and a module
docstring titled `# Ranked alphabets and their term algebras` covering:
that a ranked alphabet names finitely many symbols each with an arity and a
block of one common width; that its term algebra is the W-type of the
finitary polynomial functor whose shape type is `Fin card`; that the
unlabelled binary trees of `Data/Tree/Binary.lean` are its two-symbol
instance. `## Main definitions` lists `RankedAlphabet`, `Term`, `Term.mk`,
`Term.size`; `## Main statements` lists `Term.induction`;
`## Implementation notes` records what `width_pos` discharges (finding 4),
why `Term` is `@[expose]` (without it `WType.mk` applications against
`Fin (R.arity i)` do not elaborate across the module boundary), and why
`Term.mk` exists (finding 5); `## Tags`:
`ranked alphabet, term algebra, W-type, polynomial functor, arity`.

```lean
/-- A ranked alphabet: `card` symbols, each spelled by a block of `width`
bits and each carrying an arity. `card_le_two_pow_width` admits an alphabet
whose size is not a power of two, at the price of blocks that spell no
symbol. -/
@[ext] public structure RankedAlphabet where
  /-- The number of symbols. -/
  card : ℕ
  /-- The number of bits spelling one symbol. -/
  width : ℕ
  /-- Every symbol's block is non-empty. Without it a term's spelling can be
  shorter than its node count, and the descent's fuel no longer suffices. -/
  width_pos : 0 < width
  /-- Every symbol has a block of the common width. -/
  card_le_two_pow_width : card ≤ 2 ^ width
  /-- The arity of each symbol. -/
  arity : Fin card → ℕ

namespace RankedAlphabet

public section

/-- The term algebra of a ranked alphabet. -/
@[expose] def Term (R : RankedAlphabet) : Type :=
  WType fun i : Fin R.card ↦ Fin (R.arity i)

/-- The term with head symbol `i` and children `ch`. Named rather than
using `WType.mk` directly so that a caller writes the arity once. -/
@[expose] def Term.mk (R : RankedAlphabet) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) : R.Term :=
  WType.mk i ch

/-- The number of nodes of a term. -/
@[expose] def Term.size {R : RankedAlphabet} : R.Term → ℕ :=
  WType.elim ℕ fun x ↦ (List.ofFn x.2).sum + 1

/-- Induction in the `Term.mk` presentation, so that a proof driven by it
need not mention the underlying shape and direction families. -/
theorem Term.induction {R : RankedAlphabet} {motive : R.Term → Prop}
    (hmk : ∀ i ch, (∀ d, motive (ch d)) → motive (R.Term.mk i ch)) :
    ∀ t, motive t :=
  WType.rec (motive := motive) fun i ch ih ↦ hmk i ch ih

@[simp] theorem size_mk {R : RankedAlphabet} (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) :
    (R.Term.mk i ch).size = (List.ofFn fun d ↦ (ch d).size).sum + 1 := rfl

end

end RankedAlphabet
```

- [ ] **Step 4: Build, test and lint**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Basic GebTests.Mathlib.Data.Tree.Ranked.Basic && lake lint
```

Expected: PASS. If `@[ext]` does not compile on `RankedAlphabet` (the
`arity` field is dependent on `card`), drop the attribute and record why in
`## Implementation notes`.

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Basic.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Basic.lean \
  -m "feat(tree): add ranked alphabets and their term algebras"
```

### Task 2: Codes and their round trip

**Files:** create `Geb/Mathlib/Data/Tree/Ranked/Code.lean` and
`GebTests/Mathlib/Data/Tree/Ranked/Code.lean`.

**Interfaces:**

- Consumes: `RankedAlphabet` from Task 1.
- Produces: `code`, `decodeBits`, `decodeBits_cons`, `arOf`, `length_code`,
  `decodeBits_code`, `arOf_decodeBits_code`. Tasks 3 to 10 consume them.
  `decodeBits_cons` is the equation lemma every later `rw` on `decodeBits`
  needs: `decodeBits` is a bare `List.rec`, so Lean generates no
  `decodeBits (b :: l) = …` equation of its own.

- [ ] **Step 1: Write the failing test**

Create `GebTests/Mathlib/Data/Tree/Ranked/Code.lean`, importing
`Geb.Mathlib.Data.Tree.Ranked.Code` and
`GebTests.Mathlib.Data.Tree.Ranked.Basic`, with `open RankedAlphabet` so
that `decodeBits` resolves. Module docstring titled `# Codes on a worked
signature`, `## Main statements` describing the assertions,
`## Tags`: `ranked alphabet, code, binary representation`.

```lean
open RankedAlphabet

/-- The codes are the two-bit binary representations, least significant bit
first. -/
theorem code_zero : sampleAlphabet.code ⟨0, by decide⟩ = [false, false] := by decide

/-- The code of the symbol of arity one. -/
theorem code_one : sampleAlphabet.code ⟨1, by decide⟩ = [true, false] := by decide

/-- The code of the symbol of arity three. -/
theorem code_three : sampleAlphabet.code ⟨3, by decide⟩ = [true, true] := by decide

/-- Every code decodes to its own symbol. -/
theorem decodeBits_code_all :
    ((List.finRange 4).all fun i ↦
      decodeBits (sampleAlphabet.code i) == i.val) = true := by decide

/-- A block outside the alphabet has no arity. -/
theorem arOf_out_of_range : sampleAlphabet.arOf 4 = none := by decide

/-- A block inside the alphabet has the arity the table gives. -/
theorem arOf_in_range : sampleAlphabet.arOf 2 = some 2 := by decide
```

- [ ] **Step 2: Run to verify it fails**

```bash
lake build GebTests.Mathlib.Data.Tree.Ranked.Code
```

Expected: FAIL, `unknown module Geb.Mathlib.Data.Tree.Ranked.Code`.

- [ ] **Step 3: Write the module**

Create `Geb/Mathlib/Data/Tree/Ranked/Code.lean` with the header, `module`,
the two imports from § File structure, and a module docstring titled
`# Symbol codes` describing the least-significant-bit-first block and its
decoding. `## Main definitions`: `code`, `decodeBits`, `arOf`.
`## Main statements`: `decodeBits_cons`, `length_code`, `decodeBits_code`,
`arOf_decodeBits_code`, `testBit_decodeBits`. `## Implementation notes`:
that `decodeBits` is a `List.rec` and so has no generated equation lemma,
which is why `decodeBits_cons` is stated. `## Tags`:
`ranked alphabet, code, binary representation, decoding`.

```lean
namespace RankedAlphabet

public section

/-- The block spelling a symbol: its index in binary, least significant bit
first, padded to the alphabet's width. -/
@[expose] def code (R : RankedAlphabet) (i : Fin R.card) : List Bool :=
  (List.range R.width).map fun j ↦ i.val.testBit j

/-- The value a block denotes, its head the least significant bit. -/
@[expose] def decodeBits : List Bool → ℕ :=
  List.rec 0 fun b _ ih ↦ 2 * ih + (if b then 1 else 0)

theorem decodeBits_cons (b : Bool) (l : List Bool) :
    decodeBits (b :: l) = 2 * decodeBits l + (if b then 1 else 0) := rfl

/-- The arity of the symbol a block denotes, absent at a block denoting
none. -/
@[expose] def arOf (R : RankedAlphabet) (v : ℕ) : Option ℕ :=
  if h : v < R.card then some (R.arity ⟨v, h⟩) else none

/-- Every block has the alphabet's width. -/
@[simp] theorem length_code (R : RankedAlphabet) (i : Fin R.card) :
    (R.code i).length = R.width := by
  simp only [code, List.length_map, List.length_range]

/-- A block decodes to the symbol it spells. The bound `i.val < 2 ^ width`
comes from `card_le_two_pow_width`, and is what makes the padding
lossless. -/
theorem decodeBits_code (R : RankedAlphabet) (i : Fin R.card) :
    decodeBits (R.code i) = i.val := by
  have hlt : i.val < 2 ^ R.width := Nat.lt_of_lt_of_le i.isLt R.card_le_two_pow_width
  have key : ∀ (n : ℕ) (v : ℕ),
      decodeBits ((List.range n).map fun j ↦ v.testBit j) = v % 2 ^ n := by
    refine Nat.rec (motive := fun n ↦ ∀ v : ℕ,
        decodeBits ((List.range n).map fun j ↦ v.testBit j) = v % 2 ^ n)
      (fun v ↦ by simp only [List.range_zero, List.map_nil, decodeBits, Nat.pow_zero,
        Nat.mod_one])
      (fun n ihn v ↦ ?_)
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Function.comp_def, Nat.succ_eq_add_one, Nat.testBit_add_one]
    rw [decodeBits_cons, ihn (v / 2), Nat.testBit_zero, pow_succ', Nat.mod_mul]
    rcases Nat.mod_two_eq_zero_or_one v with h | h <;> (simp only [h]; try omega)
  rw [code, key, Nat.mod_eq_of_lt hlt]

/-- A block spelling a symbol has that symbol's arity. -/
theorem arOf_decodeBits_code (R : RankedAlphabet) (i : Fin R.card) :
    R.arOf (decodeBits (R.code i)) = some (R.arity i) := by
  rw [decodeBits_code, arOf, dif_pos i.isLt]

end

end RankedAlphabet
```

- [ ] **Step 4: Build, test and lint**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Code GebTests.Mathlib.Data.Tree.Ranked.Code && lake lint
```

Expected: PASS. `decodeBits_code` names `pow_succ'`, `Nat.mod_mul`,
`Nat.testBit_add_one` and `Nat.mod_two_eq_zero_or_one`; if `lake lint`
reports `Classical.choice`, it is one of those, and the Global Constraint
on `Nat` arithmetic applies — replace the offending step with a bound over
named hypotheses closed by `omega`.

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Code.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Code.lean \
  -m "feat(tree): add symbol codes and their round trip"
```

### Task 3: The spelling

**Files:** create `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` and
`GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean`.

**Interfaces:**

- Consumes: `Term.mk`, `Term.size`, `size_mk`, `Term.induction`, `code`,
  `length_code`.
- Produces: `spell`, `spell_mk`, `length_spell`, `width_le_length_spell`.
  Tasks 5, 6, 8, 10, 11 consume them.

- [ ] **Step 1: Write the failing test**

Create `GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean`, importing
`Geb.Mathlib.Data.Tree.Ranked.Preorder` and
`GebTests.Mathlib.Data.Tree.Ranked.Basic`. It declares no `Ranked`
literal, so it does **not** import `Mathlib.Data.Fin.VecNotation`. Module
docstring titled `# The ranked preorder encoding on worked terms`, with
`## Main statements` and `## Tags`:
`ranked alphabet, preorder, prefix notation, encoding, scan`.

```lean
/-- A nullary term is spelled by its block alone. -/
theorem spell_sampleNullary : sampleAlphabet.spell sampleNullary = [false, false] := by
  decide

/-- A binary term is spelled by its block and its children's spellings. -/
theorem spell_sampleBinary :
    sampleAlphabet.spell sampleBinary = [false, true, false, false, false, false] := by
  decide

/-- A spelling's length is the width times the node count. -/
theorem length_spell_sampleBinary :
    (sampleAlphabet.spell sampleBinary).length = 2 * sampleBinary.size := by decide
```

- [ ] **Step 2: Run to verify it fails**

```bash
lake build GebTests.Mathlib.Data.Tree.Ranked.Preorder
```

Expected: FAIL, `unknown module Geb.Mathlib.Data.Tree.Ranked.Preorder`.

- [ ] **Step 3: Write the module's opening and first section**

Create `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` with the header,
`module`, the three imports from § File structure, and a module docstring
titled `# The preorder encoding of ranked terms`. It summarises that a
symbol is spelled by its block followed by its children's spellings, that
the encoding is a bijection onto the words satisfying `Valid`, and that a
`boundedRec` processes a list from its far end so a symbol is applied after
its children. `## References` names the idea transcribed — prefix
(Łukasiewicz) notation — as `Data/Tree/Preorder.lean` does in prose.
Later tasks append their own entries to `## Main definitions`,
`## Main statements` and `## Implementation notes`. `## Tags`:
`ranked alphabet, preorder, prefix notation, encoding, retraction, scan`.

Open `namespace RankedAlphabet` and `public section` here, and close with
`end` / `end RankedAlphabet` at the foot. Tasks 4 to 10 insert above those
two lines.

```lean
/-- The preorder encoding: a symbol's block followed by its children's
spellings, in index order. -/
@[expose] def spell (R : RankedAlphabet) : R.Term → List Bool :=
  WType.elim (List Bool) fun x ↦ R.code x.1 ++ (List.ofFn x.2).flatten

@[simp] theorem spell_mk (R : RankedAlphabet) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) :
    R.spell (R.Term.mk i ch) = R.code i ++ (List.ofFn fun d ↦ R.spell (ch d)).flatten :=
  rfl

/-- A spelling's length is the alphabet's width times the term's node
count, so the input length is fuel enough for the descent to read anything
`spell` emits. -/
theorem length_spell (R : RankedAlphabet) (t : R.Term) :
    (R.spell t).length = R.width * t.size :=
  Term.induction (motive := fun t ↦ (R.spell t).length = R.width * t.size)
    (fun i ch ih ↦ by
      rw [spell_mk, List.length_append, length_code, size_mk, Nat.mul_add, Nat.mul_one,
        Nat.add_comm (R.width * _) R.width]
      congr 1
      rw [List.length_flatten, List.map_ofFn]
      simp only [Function.comp_def, ih]
      rw [show (List.ofFn fun x ↦ R.width * (ch x).size)
            = List.map (fun b ↦ R.width * b) (List.ofFn fun d ↦ (ch d).size) by
          rw [List.map_ofFn]; rfl, List.sum_map_mul_left, List.map_id']) t

/-- A spelling is at least one block long. -/
theorem width_le_length_spell (R : RankedAlphabet) (t : R.Term) :
    R.width ≤ (R.spell t).length := by
  rw [length_spell]
  refine Nat.le_mul_of_pos_right _ ?_
  refine Term.induction (motive := fun t ↦ 0 < t.size) (fun i ch _ ↦ ?_) t
  rw [size_mk]
  omega
```

- [ ] **Step 4: Build, test and lint**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Preorder \
  GebTests.Mathlib.Data.Tree.Ranked.Preorder && lake lint
```

Expected: PASS. The `Nat.add_comm` rewrite before `congr 1` is
load-bearing: without it `congr 1` pairs `R.width` with `R.width * S` and
leaves the unprovable `R.width = R.width * S`.

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Preorder.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean \
  -m "feat(tree): add the preorder spelling of ranked terms"
```

### Task 4: The recursive descent

**Files:** modify `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` (above the
closing `end`s) and its test module.

**Interfaces:**

- Consumes: `arOf`, `Term.mk`, `decodeBits`.
- Produces: `decodeBlock`, `parseChildren`, `parseChildren_succ`,
  `parseStep`, `parseAux`, `parseAux_succ`, `parse`. Tasks 5, 6, 10
  consume them. `parseChildren_succ` is the equation lemma Task 5's `rw`
  needs, `parseChildren` being a `Nat.rec`.

- [ ] **Step 1: Write the failing test**

Append (finding 6 governs the form — no `decide` on `= some t`):

```lean
/-- The descent reads a nullary term, and reads back the word it consumed. -/
theorem parse_spell_sampleNullary :
    ((sampleAlphabet.parse [false, false]).map sampleAlphabet.spell
      == some [false, false]) = true := by decide

/-- The descent rejects a word one block short of a child. -/
theorem parse_short : sampleAlphabet.parse [false, true] = none := by decide

/-- The descent rejects trailing input. -/
theorem parse_trailing :
    sampleAlphabet.parse [false, false, false, false] = none := by decide
```

- [ ] **Step 2: Run to verify it fails**

```bash
lake build GebTests.Mathlib.Data.Tree.Ranked.Preorder
```

Expected: FAIL, `unknown identifier 'RankedAlphabet.parse'`.

- [ ] **Step 3: Write the descent**

```lean
/-- Read one block: the symbol it spells and the unconsumed remainder,
absent when the word is short of a block or the block spells no symbol. -/
@[expose] def decodeBlock (R : RankedAlphabet) (w : List Bool) :
    Option (Fin R.card × List Bool) :=
  if h : decodeBits (w.take R.width) < R.card ∧ R.width ≤ w.length then
    some (⟨decodeBits (w.take R.width), h.1⟩, w.drop R.width)
  else none

/-- Read `n` children in index order, delegating each to `child`. -/
@[expose] def parseChildren {R : RankedAlphabet}
    (child : List Bool → Option (R.Term × List Bool)) :
    (n : ℕ) → List Bool → Option ((Fin n → R.Term) × List Bool) :=
  Nat.rec (fun w ↦ some (Fin.elim0, w))
    fun _ ih w ↦
      match child w with
      | none => none
      | some (t, w₁) =>
        match ih w₁ with
        | none => none
        | some (f, w₂) => some (Fin.cons t f, w₂)

theorem parseChildren_succ {R : RankedAlphabet}
    (child : List Bool → Option (R.Term × List Bool)) (n : ℕ) (w : List Bool) :
    parseChildren child (n + 1) w =
      (match child w with
       | none => none
       | some (t, w₁) =>
         match parseChildren child n w₁ with
         | none => none
         | some (f, w₂) => some (Fin.cons t f, w₂)) := rfl

/-- One layer of the recursive descent: read one block, then as many
children as its symbol's arity. -/
@[expose] def parseStep (R : RankedAlphabet)
    (child : List Bool → Option (R.Term × List Bool)) (w : List Bool) :
    Option (R.Term × List Bool) :=
  match R.decodeBlock w with
  | none => none
  | some (i, rest) =>
    match parseChildren child (R.arity i) rest with
    | none => none
    | some (f, rest') => some (R.Term.mk i f, rest')

/-- Recursive descent bounded by an explicit `ℕ`. -/
@[expose] def parseAux (R : RankedAlphabet) :
    ℕ → List Bool → Option (R.Term × List Bool) :=
  Nat.rec (fun _ ↦ none) fun _ ih ↦ R.parseStep ih

theorem parseAux_succ (R : RankedAlphabet) (f : ℕ) :
    R.parseAux (f + 1) = R.parseStep (R.parseAux f) := rfl

/-- The decoding, rejecting trailing input. -/
@[expose] def parse (R : RankedAlphabet) (w : List Bool) : Option R.Term :=
  match R.parseAux w.length w with
  | some (t, []) => some t
  | _ => none
```

Add to `## Implementation notes`:

> `parseAux` recurses on an explicit `ℕ` bound rather than on its input:
> each child is parsed from a remainder the previous call computes, which
> is not a structural subterm. `parse` supplies the input's length, and
> `length_spell` with `width_pos` shows that bound admits every word
> `spell` emits, `t.size ≤ R.width * t.size` being what `parse_spell`
> discharges. `parseChildren` and `decodeBits` are recursors rather than
> equation-compiled definitions, so neither has generated equation lemmas;
> `parseChildren_succ` and `decodeBits_cons` are stated for the rewrites
> that need them.

- [ ] **Step 4: Build, test and lint**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Preorder \
  GebTests.Mathlib.Data.Tree.Ranked.Preorder && lake lint
```

Expected: PASS. `decodeBlock`'s `dite` is over `Nat.decLt` and `Nat.decLe`,
both of which reduce, so the three assertions close by `decide` (finding 1).

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Preorder.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean \
  -m "feat(tree): add the recursive descent for ranked spellings"
```

### Task 5: The retraction

**Files:** modify `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` and its test
module.

**Interfaces:**

- Consumes: `parseAux`, `parseAux_succ`, `parseChildren_succ`,
  `decodeBlock`, `decodeBits_code`, `length_code`, `length_spell`,
  `width_le_length_spell`, `Term.induction`, `size_mk`.
- Produces: `decodeBlock_code_append`, `parseChildren_flatten`,
  `parseAux_spell`, `parse_spell`. Tasks 6 and 10 consume `parse_spell`.

- [ ] **Step 1: Write the failing test**

```lean
/-- The descent inverts the spelling on the binary term. -/
theorem parse_spell_sampleBinary :
    ((sampleAlphabet.parse (sampleAlphabet.spell sampleBinary)).map
      sampleAlphabet.spell == some (sampleAlphabet.spell sampleBinary)) = true := by
  decide
```

- [ ] **Step 2: Run to verify it builds**

```bash
lake build GebTests.Mathlib.Data.Tree.Ranked.Preorder
```

Expected: PASS. This is a sanity anchor on Tasks 3 and 4, not a red test;
the lemmas' failure mode is a build error at Step 4.

- [ ] **Step 3: Write the lemmas, in this order**

```lean
/-- A block followed by anything is read as its own symbol, leaving what
follows. -/
theorem decodeBlock_code_append (R : RankedAlphabet) (i : Fin R.card)
    (rest : List Bool) : R.decodeBlock (R.code i ++ rest) = some (i, rest) := by
  have htake : (R.code i ++ rest).take R.width = R.code i := by
    rw [← length_code R i, List.take_left]
  have hdrop : (R.code i ++ rest).drop R.width = rest := by
    rw [← length_code R i, List.drop_left]
  have hlen : R.width ≤ (R.code i ++ rest).length := by
    rw [List.length_append, length_code]
    omega
  simp only [decodeBlock, htake, hdrop,
    dif_pos (show decodeBits (R.code i) < R.card ∧ R.width ≤ (R.code i ++ rest).length
      from ⟨by rw [decodeBits_code]; exact i.isLt, hlen⟩)]
  congr 1
  exact Prod.ext (Fin.val_injective (decodeBits_code R i)) rfl

/-- Reading `n` children off the concatenation of their spellings returns
them and the remainder. -/
theorem parseChildren_flatten (R : RankedAlphabet) {n : ℕ} (ch : Fin n → R.Term)
    (ih : ∀ d f rest, (ch d).size ≤ f →
      R.parseAux f (R.spell (ch d) ++ rest) = some (ch d, rest))
    (f : ℕ) (rest : List Bool) (hf : ∀ d, (ch d).size ≤ f) :
    parseChildren (R.parseAux f) n
      ((List.ofFn fun d ↦ R.spell (ch d)).flatten ++ rest) = some (ch, rest) := by
  refine Nat.rec (motive := fun n ↦ ∀ (ch : Fin n → R.Term),
    (∀ d f' rest', (ch d).size ≤ f' →
      R.parseAux f' (R.spell (ch d) ++ rest') = some (ch d, rest')) →
    (∀ d, (ch d).size ≤ f) →
    parseChildren (R.parseAux f) n
      ((List.ofFn fun d ↦ R.spell (ch d)).flatten ++ rest) = some (ch, rest))
    ?base ?step n ch ih hf
  · intro ch _ _
    simp only [List.ofFn_zero, List.flatten_nil, List.nil_append, parseChildren]
    exact congrArg (fun g ↦ some (g, rest)) (funext fun d ↦ d.elim0)
  · intro n ihn ch ihch hch
    rw [List.ofFn_succ, List.flatten_cons, List.append_assoc, parseChildren_succ,
      ihch 0 f _ (hch 0)]
    simp only []
    rw [show (fun i : Fin n ↦ ch i.succ) = Fin.tail ch from rfl,
      ihn (Fin.tail ch) (fun d ↦ ihch d.succ) (fun d ↦ hch d.succ)]
    simp only [Fin.cons_self_tail]

/-- The descent inverts the spelling on spelled input, given fuel at least
the term's node count, and returns the unconsumed remainder. -/
theorem parseAux_spell (R : RankedAlphabet) (t : R.Term) :
    ∀ (f : ℕ) (rest : List Bool), t.size ≤ f →
      R.parseAux f (R.spell t ++ rest) = some (t, rest) :=
  Term.induction
    (motive := fun t ↦ ∀ (f : ℕ) (rest : List Bool), t.size ≤ f →
      R.parseAux f (R.spell t ++ rest) = some (t, rest))
    (fun i ch ih f rest hf ↦ by
      cases f with
      | zero => rw [size_mk] at hf; omega
      | succ f =>
        rw [parseAux_succ, spell_mk, List.append_assoc, parseStep,
          decodeBlock_code_append]
        have hchild : ∀ d, (ch d).size ≤ f := by
          intro d
          rw [size_mk] at hf
          have hmem : (ch d).size ∈ List.ofFn fun e ↦ (ch e).size :=
            List.mem_ofFn.mpr ⟨d, rfl⟩
          have := List.le_sum_of_mem hmem
          omega
        simp only []
        rw [parseChildren_flatten R ch ih f rest hchild]) t

/-- The retraction law: the descent recovers every term the encoding
spells. -/
theorem parse_spell (R : RankedAlphabet) (t : R.Term) :
    R.parse (R.spell t) = some t := by
  have hf : t.size ≤ (R.spell t).length := by
    rw [length_spell]
    exact Nat.le_mul_of_pos_left _ R.width_pos
  have h := parseAux_spell R t (R.spell t).length [] hf
  rw [List.append_nil] at h
  rw [parse, h]
```

- [ ] **Step 4: Build and lint**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Preorder && lake lint
```

Expected: PASS. Three steps are load-bearing and were found by running the
code: `parseChildren_flatten` takes `ch` explicitly (passing `ih` into that
slot is a type mismatch); the `simp only []` after
`decodeBlock_code_append` iota-reduces the `match some (i, …)` so the next
rewrite can see `parseChildren`; and the base case uses `simp only` with a
named list rather than `simp`, which `linter.flexible` rejects as an error
(finding 8).

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Preorder.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean \
  -m "feat(tree): prove the descent inverts the ranked spelling"
```

### Task 6: The descent reads only spellings

**Files:** modify `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean`,
`Geb/Mathlib/Data/Tree/Ranked/Code.lean` (adding `testBit_decodeBits` beside
`decodeBits_code`, and its `## Main statements` entry), and the `Preorder`
test module.

**Interfaces:**

- Consumes: `parseAux`, `parseAux_succ`, `parseChildren_succ`,
  `decodeBlock`, `decodeBits_cons`, `parse_spell`, `code`, `length_code`.
- Produces: `testBit_decodeBits` (in `Code.lean`), `getElem_code_eq`,
  `getElem_take_eq_testBit`, `decodeBlock_eq_some`, `parseChildren_eq_some`,
  `parseAux_eq_some`, `parse_eq_some_iff`, `spell_injective`. Task 10
  consumes `parse_eq_some_iff`; nothing in this branch consumes
  `spell_injective`, which is stated because the encoding's injectivity is
  part of the bijection B1 delivers.

- [ ] **Step 1: Write the failing test**

```lean
/-- Distinct terms have distinct spellings, on a worked pair. -/
theorem spell_injective_sample :
    (sampleAlphabet.spell sampleNullary == sampleAlphabet.spell sampleBinary) = false := by
  decide
```

- [ ] **Step 2: Run to verify it builds**

```bash
lake build GebTests.Mathlib.Data.Tree.Ranked.Preorder
```

Expected: PASS, as a sanity anchor.

- [ ] **Step 3: Add `testBit_decodeBits` to `Code.lean`**

```lean
/-- The `n`th bit of a block's value is the block's `n`th entry. -/
theorem testBit_decodeBits : ∀ (bs : List Bool) (n : ℕ) (h : n < bs.length),
    (decodeBits bs).testBit n = bs[n] :=
  List.rec (fun n h ↦ absurd h (by simp))
    (fun b bs ih n h ↦ by
      cases n with
      | zero => rw [decodeBits_cons, Nat.testBit_zero]; cases b <;> simp
      | succ n =>
        rw [decodeBits_cons, Nat.testBit_add_one]
        have hd : (2 * decodeBits bs + (if b then 1 else 0)) / 2 = decodeBits bs := by
          cases b <;> simp <;> omega
        rw [hd, ih n (by simpa using h)]
        simp)
```

- [ ] **Step 4: Write the `Preorder.lean` lemmas**

The model is `BinTree.parseAux_eq_some` and the two lemmas after it in
`Geb/Mathlib/Data/Tree/Preorder.lean`; the difference is that the two
nested child matches become one `parseChildren` induction.

```lean
/-- The `n`th bit of a block is the `n`th bit of the symbol's index. -/
theorem getElem_code_eq (R : RankedAlphabet) (i : Fin R.card) (n : ℕ)
    (h : n < (R.code i).length) : (R.code i)[n] = i.val.testBit n := by
  simp only [code, List.getElem_map, List.getElem_range]

/-- The `n`th bit of a word's leading block is the `n`th bit of that
block's value. -/
theorem getElem_take_eq_testBit (R : RankedAlphabet) (w : List Bool) (n : ℕ)
    (h : n < (w.take R.width).length) :
    (w.take R.width)[n] = (decodeBits (w.take R.width)).testBit n :=
  (testBit_decodeBits (w.take R.width) n h).symm

/-- Whatever a block read returns, it reads that symbol's block. -/
theorem decodeBlock_eq_some (R : RankedAlphabet) {w rest : List Bool}
    {i : Fin R.card} (h : R.decodeBlock w = some (i, rest)) :
    R.code i ++ rest = w := by
  rw [decodeBlock] at h
  split at h
  · rename_i hcond
    have heq := Option.some.inj h
    have hi : decodeBits (w.take R.width) = i.val := congrArg (fun p ↦ (Prod.fst p).val) heq
    have hrest : w.drop R.width = rest := congrArg Prod.snd heq
    have hlen : (R.code i).length = (w.take R.width).length := by
      rw [length_code, List.length_take]
      omega
    have hcode : R.code i = w.take R.width := by
      refine List.ext_getElem hlen ?_
      intro n h₁ h₂
      rw [getElem_code_eq R i n h₁, getElem_take_eq_testBit R w n h₂, hi]
    rw [hcode, ← hrest, List.take_append_drop]
  · contradiction

/-- Whatever `parseChildren` returns, it reads the concatenation of the
children's spellings. -/
theorem parseChildren_eq_some (R : RankedAlphabet) (f : ℕ)
    (ih : ∀ w t rest, R.parseAux f w = some (t, rest) → R.spell t ++ rest = w) :
    ∀ (n : ℕ) (w : List Bool) (g : Fin n → R.Term) (rest : List Bool),
      parseChildren (R.parseAux f) n w = some (g, rest) →
        (List.ofFn fun d ↦ R.spell (g d)).flatten ++ rest = w :=
  Nat.rec
    (fun w g rest h ↦ by
      simp only [parseChildren] at h
      have heq := Option.some.inj h
      have hw : w = rest := congrArg Prod.snd heq
      rw [List.ofFn_zero, List.flatten_nil, List.nil_append, hw])
    (fun n ihn w g rest h ↦ by
      rw [parseChildren_succ] at h
      split at h
      · contradiction
      · rename_i t w₁ h₁
        simp only [] at h
        split at h
        · contradiction
        · rename_i g' w₂ h₂
          have heq := Option.some.inj h
          have hg : Fin.cons t g' = g := congrArg Prod.fst heq
          have hrest : w₂ = rest := congrArg Prod.snd heq
          subst hg
          rw [List.ofFn_succ, List.flatten_cons, List.append_assoc,
            ← hrest, ihn w₁ g' w₂ h₂, ih w t w₁ h₁]
          simp only [Fin.cons_zero, Fin.cons_succ])

/-- Whatever the descent reads, it reads a spelling. -/
theorem parseAux_eq_some (R : RankedAlphabet) :
    ∀ (f : ℕ) (w : List Bool) (t : R.Term) (rest : List Bool),
      R.parseAux f w = some (t, rest) → R.spell t ++ rest = w :=
  Nat.rec
    (fun _ _ _ h ↦ nomatch h)
    (fun f ih w t rest h ↦ by
      rw [parseAux_succ, parseStep] at h
      split at h
      · contradiction
      · rename_i i rest₁ hb
        simp only [] at h
        split at h
        · contradiction
        · rename_i g rest₂ hc
          have heq := Option.some.inj h
          have ht : R.Term.mk i g = t := congrArg Prod.fst heq
          have hrest : rest₂ = rest := congrArg Prod.snd heq
          subst ht
          rw [spell_mk, List.append_assoc, ← hrest,
            parseChildren_eq_some R f ih (R.arity i) rest₁ g rest₂ hc,
            decodeBlock_eq_some R hb])

/-- The descent succeeds exactly on the spellings, returning the term
spelled. -/
theorem parse_eq_some_iff (R : RankedAlphabet) {w : List Bool} {t : R.Term} :
    R.parse w = some t ↔ R.spell t = w := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ parse_spell R t⟩
  rw [parse] at h
  split at h
  · rename_i t' hp
    rw [← Option.some.inj h]
    simpa using parseAux_eq_some R w.length w t' [] hp
  · contradiction

/-- Distinct terms have distinct spellings. -/
theorem spell_injective (R : RankedAlphabet) : Function.Injective R.spell := by
  intro a b h
  have ha := parse_spell R a
  rw [h, parse_spell R b] at ha
  exact (Option.some.inj ha).symm
```

- [ ] **Step 5: Build and lint**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Code \
  Geb.Mathlib.Data.Tree.Ranked.Preorder && lake lint
```

Expected: PASS. Two hazards found by running the code: `subst` on a
hypothesis whose right side is the bound variable `rest` **eliminates**
`rest`, after which the next line cannot name it — hence `← hrest`
rewrites rather than `subst hrest` in both `parseChildren_eq_some` and
`parseAux_eq_some`; and `simp only []` is needed after each `split` that
leaves an unreduced `match some …`.

- [ ] **Step 6: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Preorder.lean \
  Geb/Mathlib/Data/Tree/Ranked/Code.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean \
  -m "feat(tree): prove the ranked descent reads only spellings"
```

### Task 7: The scanning validity predicate

**Files:** modify `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` and its test
module.

**Interfaces:**

- Consumes: `arOf`, `decodeBits`.
- Produces: `Scan`, `scanStep`, `scanFrom`, `scanFinal`, `validBool`,
  `Valid`, its `DecidablePred` instance, `scanFrom_nil`, `scanFrom_cons`,
  `scanFrom_append`. Tasks 8, 9, 10, 11 consume them; branch B2 consumes
  `scanStep` and `Valid`.

- [ ] **Step 1: Write the failing test**

```lean
/-- A nullary term's spelling is valid. -/
theorem valid_sampleNullary : sampleAlphabet.Valid [false, false] := by decide

/-- A binary term's spelling is valid. -/
theorem valid_sampleBinary :
    sampleAlphabet.Valid [false, true, false, false, false, false] := by decide

/-- A word leaving two terms on the stack is rejected. -/
theorem not_valid_two : ¬ sampleAlphabet.Valid [false, false, false, false] := by decide

/-- A word ending mid-block is rejected. -/
theorem not_valid_partial : ¬ sampleAlphabet.Valid [false] := by decide

/-- A word popping more than the stack holds is rejected. -/
theorem not_valid_underflow : ¬ sampleAlphabet.Valid [false, true] := by decide
```

- [ ] **Step 2: Run to verify it fails**

```bash
lake build GebTests.Mathlib.Data.Tree.Ranked.Preorder
```

Expected: FAIL, `unknown identifier 'RankedAlphabet.Valid'`.

- [ ] **Step 3: Write the scan**

`Scan` is declared inside the namespace opened in Task 3.

```lean
/-- The state of the validity scan: the bits of an incomplete block, the
count of pending subterms, and whether the scan has failed. -/
structure Scan where
  /-- The bits of an incomplete block, most recently read first. -/
  buf : List Bool
  /-- The count of pending subterms. -/
  depth : ℕ
  /-- Whether the scan has not yet failed. -/
  live : Bool
deriving DecidableEq, Repr

/-- One step of the scan, reading one bit. A failed state absorbs. An
incomplete block takes the bit; a complete one is decoded, and its symbol
pops its arity and pushes one, failing when the block spells no symbol or
the pending count is short of the arity. -/
@[expose] def scanStep (R : RankedAlphabet) (b : Bool) (s : Scan) : Scan :=
  match s.live with
  | false => s
  | true =>
    match decide ((b :: s.buf).length = R.width) with
    | false => ⟨b :: s.buf, s.depth, true⟩
    | true =>
      match R.arOf (decodeBits (b :: s.buf)) with
      | none => ⟨[], s.depth, false⟩
      | some r =>
        match decide (r ≤ s.depth) with
        | false => ⟨[], s.depth, false⟩
        | true => ⟨[], s.depth - r + 1, true⟩

/-- The scan of a word from a given state. `foldr` reads the word's last
bit first, which is the processing order of a right-to-left scan. -/
@[expose] def scanFrom (R : RankedAlphabet) (w : List Bool) (s : Scan) : Scan :=
  w.foldr R.scanStep s

/-- The scan of a word from the initial state. -/
@[expose] def scanFinal (R : RankedAlphabet) (w : List Bool) : Scan :=
  R.scanFrom w ⟨[], 0, true⟩

/-- Whether a word spells a term: the scan ends live, with no incomplete
block and exactly one pending subterm. -/
@[expose] def validBool (R : RankedAlphabet) (w : List Bool) : Bool :=
  (R.scanFinal w).live && (R.scanFinal w).buf.isEmpty && (R.scanFinal w).depth == 1

/-- A word spells a term. -/
@[expose] def Valid (R : RankedAlphabet) (w : List Bool) : Prop :=
  R.validBool w = true

/-- `Valid` is a `Bool` equation, so membership is decidable. Instance
search does not unfold the `def`, so the instance is supplied. -/
instance (R : RankedAlphabet) : DecidablePred R.Valid :=
  fun _ ↦ inferInstanceAs (Decidable (_ = true))

@[simp] theorem scanFrom_nil (R : RankedAlphabet) (s : Scan) :
    R.scanFrom [] s = s := rfl

@[simp] theorem scanFrom_cons (R : RankedAlphabet) (b : Bool) (w : List Bool)
    (s : Scan) : R.scanFrom (b :: w) s = R.scanStep b (R.scanFrom w s) := rfl

/-- The scan of a concatenation reads the later part first. -/
theorem scanFrom_append (R : RankedAlphabet) (u v : List Bool) (s : Scan) :
    R.scanFrom (u ++ v) s = R.scanFrom u (R.scanFrom v s) :=
  List.rec rfl (fun b w ih ↦ by rw [List.cons_append, scanFrom_cons, ih, scanFrom_cons]) u
```

Add to `## Implementation notes`:

> `scanStep` matches on `Bool` values and `Valid` is a `Bool` equation
> rather than an equation of `Scan`. Both are forced by kernel reduction: a
> derived `DecidableEq` at a symbolic fold leaves `decide` stuck on the
> instance rather than reducing it. A decidable test is not itself the
> obstruction — `decodeBlock` branches on one and reduces.

- [ ] **Step 4: Build, test and lint**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Preorder \
  GebTests.Mathlib.Data.Tree.Ranked.Preorder && lake lint
```

Expected: PASS, all five assertions closing by `decide`.

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Preorder.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean \
  -m "feat(tree): add the scanning validity predicate for ranked words"
```

### Task 8: Every spelling is valid

**Files:** modify `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` and its test
module.

**Interfaces:**

- Consumes: `scanFrom`, `scanFrom_cons`, `scanFrom_append`,
  `arOf_decodeBits_code`, `length_code`, `Term.induction`, `spell_mk`,
  `width_pos`.
- Produces: `scanFrom_code`, `scanFrom_flatten`, `scanFrom_spell`,
  `valid_spell`. Task 10 consumes `scanFrom_spell`; Task 11 consumes
  `valid_spell`.

- [ ] **Step 1: Write the failing test**

```lean
/-- Both sample spellings are valid. -/
theorem valid_spell_samples :
    (sampleAlphabet.validBool (sampleAlphabet.spell sampleNullary) &&
      sampleAlphabet.validBool (sampleAlphabet.spell sampleBinary)) = true := by decide
```

- [ ] **Step 2: Run to verify it builds**

```bash
lake build GebTests.Mathlib.Data.Tree.Ranked.Preorder
```

Expected: PASS, as a sanity anchor.

- [ ] **Step 3: Write the lemmas**

```lean
/-- A word shorter than a block only accumulates. -/
theorem scanFrom_short (R : RankedAlphabet) (d : ℕ) :
    ∀ u : List Bool, u.length < R.width → R.scanFrom u ⟨[], d, true⟩ = ⟨u, d, true⟩ :=
  List.rec (fun _ ↦ rfl)
    (fun b v ih hv ↦ by
      rw [scanFrom_cons, ih (by simpa using Nat.lt_of_succ_lt hv), scanStep]
      simp only []
      rw [decide_eq_false (by simpa using Nat.ne_of_lt hv)])

/-- Reading a symbol's block from a state with no incomplete block and at
least the symbol's arity pending pops that arity and pushes one. -/
theorem scanFrom_code (R : RankedAlphabet) (i : Fin R.card) (d : ℕ)
    (h : R.arity i ≤ d) :
    R.scanFrom (R.code i) ⟨[], d, true⟩ = ⟨[], d - R.arity i + 1, true⟩ := by
  obtain ⟨b, v, hcode⟩ : ∃ b v, R.code i = b :: v := by
    match hc : R.code i with
    | [] =>
      have := length_code R i
      rw [hc] at this
      exact absurd this.symm (Nat.ne_of_gt R.width_pos)
    | b :: v => exact ⟨b, v, rfl⟩
  have hvlen : v.length < R.width := by
    have := length_code R i
    rw [hcode, List.length_cons] at this
    omega
  have hblen : (b :: v).length = R.width := by
    have := length_code R i
    rw [hcode] at this
    exact this
  rw [hcode, scanFrom_cons, scanFrom_short R d v hvlen, scanStep]
  simp only []
  rw [decide_eq_true hblen]
  simp only []
  rw [← hcode, arOf_decodeBits_code]
  simp only []
  rw [decide_eq_true h]

/-- The scan of a list of spellings, each raising the pending count by one,
raises it by their number. -/
theorem scanFrom_flatten (R : RankedAlphabet) (ws : List (List Bool))
    (hw : ∀ u ∈ ws, ∀ d, R.scanFrom u ⟨[], d, true⟩ = ⟨[], d + 1, true⟩) (d : ℕ) :
    R.scanFrom ws.flatten ⟨[], d, true⟩ = ⟨[], d + ws.length, true⟩ :=
  List.rec (motive := fun l ↦ (∀ u ∈ l, ∀ d, R.scanFrom u ⟨[], d, true⟩ =
      ⟨[], d + 1, true⟩) → R.scanFrom l.flatten ⟨[], d, true⟩ = ⟨[], d + l.length, true⟩)
    (fun _ ↦ by simp only [List.flatten_nil, scanFrom_nil, List.length_nil, Nat.add_zero])
    (fun u l ih hl ↦ by
      rw [List.flatten_cons, scanFrom_append,
        ih (fun x hx ↦ hl x (List.mem_cons_of_mem u hx)),
        hl u List.mem_cons_self (d + l.length), List.length_cons]
      congr 1)
    ws hw

/-- A spelling raises the pending count by one, whatever the count before
it. -/
theorem scanFrom_spell (R : RankedAlphabet) (t : R.Term) (d : ℕ) :
    R.scanFrom (R.spell t) ⟨[], d, true⟩ = ⟨[], d + 1, true⟩ :=
  Term.induction
    (motive := fun t ↦ ∀ d, R.scanFrom (R.spell t) ⟨[], d, true⟩ = ⟨[], d + 1, true⟩)
    (fun i ch ih d ↦ by
      rw [spell_mk, scanFrom_append,
        scanFrom_flatten R _ (fun u hu e ↦ by
          obtain ⟨n, hn⟩ := List.mem_ofFn.mp hu
          exact hn ▸ ih n e) d,
        List.length_ofFn, scanFrom_code R i (d + R.arity i) (Nat.le_add_left _ _)]
      congr 1
      omega)
    t d

/-- Every spelling is valid. -/
theorem valid_spell (R : RankedAlphabet) (t : R.Term) : R.Valid (R.spell t) := by
  rw [Valid, validBool, scanFinal, scanFrom_spell R t 0]
  rfl
```

- [ ] **Step 4: Build and lint**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Preorder && lake lint
```

Expected: PASS. Two things were found by running the code: a `simp only []`
is needed after **each** `decide_eq_*` rewrite in `scanFrom_code`, to
iota-reduce the `match`; and `scanFrom_flatten`'s `congr 1` discharges the
arithmetic on its own, so a following `omega` errors with "no goals" —
which `warningAsError` turns into a build failure.

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Preorder.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean \
  -m "feat(tree): prove every ranked spelling is valid"
```

### Task 9: Block alignment and sticky failure

**Files:** modify `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` and its test
module.

**Interfaces:**

- Consumes: `scanStep`, `scanFrom`, `scanFinal`, `scanFrom_append`,
  `scanFrom_short`, `width_pos`.
- Produces: `scanFrom_not_live`, `buf_length_scanFinal`,
  `width_le_length_of_one_le_depth`. Task 10 consumes all three.

These three are what Task 10's induction rests on, and they are stated
apart from it because each is about the scan alone. Without
`buf_length_scanFinal` there is no reason a live scan's block boundaries
align with the word's right end, and Task 10 cannot split a block off.

- [ ] **Step 1: Write the failing test**

```lean
/-- The incomplete block holds the word's length modulo the width, on a
sample of words. -/
def bufLengthCheck : Bool :=
  ((List.range 9).flatMap fun n ↦
    (List.range (2 ^ n)).map fun m ↦ (List.range n).map fun j ↦ m.testBit j).all
    fun w ↦ !(sampleAlphabet.scanFinal w).live ||
      ((sampleAlphabet.scanFinal w).buf.length == w.length % sampleAlphabet.width)

/-- The alignment holds on every word of length at most eight. -/
theorem bufLengthCheck_eq : bufLengthCheck = true := by
  set_option maxRecDepth 100000 in decide
```

- [ ] **Step 2: Run to verify it fails**

```bash
lake build GebTests.Mathlib.Data.Tree.Ranked.Preorder
```

Expected: FAIL, `unknown identifier 'RankedAlphabet.scanFinal'` is already
resolved, so this test builds; it is the red test for Step 3's lemmas only
in the sense that it fails if the alignment claim is false. Confirm it
returns `true` before proving anything.

- [ ] **Step 3: Write the lemmas**

```lean
/-- Failure absorbs: no suffix restores a failed scan. -/
theorem scanFrom_not_live (R : RankedAlphabet) (u : List Bool) (s : Scan)
    (h : s.live = false) : (R.scanFrom u s).live = false :=
  List.rec h (fun b v ih ↦ by rw [scanFrom_cons, scanStep, ih]) u

/-- A live scan's incomplete block holds the word's length modulo the
width: block boundaries align with the word's right end. -/
theorem buf_length_scanFinal (R : RankedAlphabet) (w : List Bool)
    (h : (R.scanFinal w).live = true) :
    (R.scanFinal w).buf.length = w.length % R.width := _

/-- A live scan with something pending has read at least one block. -/
theorem width_le_length_of_one_le_depth (R : RankedAlphabet) (w : List Bool)
    (hlive : (R.scanFinal w).live = true) (hbuf : (R.scanFinal w).buf = [])
    (hd : 1 ≤ (R.scanFinal w).depth) : R.width ≤ w.length := _
```

The two underscores are this task's work, and the plan does not supply
their scripts: round one of adversarial review established that
speculatively written proof scripts in this file were wrong more often than
right, and these two have no `BinTree` model to transpose. They are
developed against the compiler, in this order.

`buf_length_scanFinal` goes by `List.rec` on `w` with the liveness
hypothesis generalised, using `scanStep`'s three branches: the accumulating
branch grows `buf` by one and the word by one; the completing branch
resets `buf` to `[]` exactly when its length reaches `width`; the failing
branches contradict `h` through `scanFrom_not_live`.
`width_le_length_of_one_le_depth` follows from it: an empty `buf` forces
`w.length % R.width = 0`, and `w = []` gives `depth = 0`, contradicting
`hd`, so `w.length` is a positive multiple of `R.width`.

- [ ] **Step 4: Build and lint**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Preorder && lake lint
```

Expected: PASS with no underscore remaining. While developing, leave
underscores rather than `sorry`; the build reports each as an unsolved goal
with its type, which is the intended loop.

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Preorder.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean \
  -m "feat(tree): prove block alignment and sticky failure for the scan"
```

### Task 10: Every valid word is a spelling

**Files:** modify `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` and its test
module.

**Interfaces:**

- Consumes: Task 9's three lemmas, `scanFrom_spell`, `scanFrom_append`,
  `scanFrom_code`, `valid_spell`, `parse_eq_some_iff`, `parse_spell`,
  `decodeBlock`, `arOf`.
- Produces: `exists_spell_append_of_live_of_buf_nil_of_one_le_depth`,
  `eq_nil_of_live_of_buf_nil_of_depth_eq_zero`, `exists_spell_of_valid`,
  `valid_iff_exists_spell`, `valid_iff_isSome_parse`. Task 11 and branch B2
  consume the last two.

The model is `BinTree.exists_print_append_of_ok_of_one_le_depth` and the
three lemmas after it in `Geb/Mathlib/Data/Tree/Preorder.lean`. The
transposition replaces "a leaf bit or a node bit" by "a complete block",
and the two recursive uses by a `Nat.rec` over the arity.

- [ ] **Step 1: Write the failing test**

```lean
/-- Validity and the descent agree on every word of length at most six. -/
def validAgreesWithParse : Bool :=
  ((List.range 7).flatMap fun n ↦
    (List.range (2 ^ n)).map fun m ↦ (List.range n).map fun j ↦ m.testBit j).all
    fun w ↦ sampleAlphabet.validBool w == (sampleAlphabet.parse w).isSome

/-- The agreement holds. -/
theorem validAgreesWithParse_eq : validAgreesWithParse = true := by decide
```

- [ ] **Step 2: Run to verify it builds**

```bash
lake build GebTests.Mathlib.Data.Tree.Ranked.Preorder
```

Expected: PASS at the default recursion depth (127 words). If it does not,
lower the bound from 7 to 5 rather than reaching for `native_decide`, which
introduces a compiler-trust axiom the linter rejects.

- [ ] **Step 3: Write the lemmas**

```lean
/-- A word whose scan ends live, with no incomplete block and a positive
pending count, has a complete spelling as a prefix. Bounded by an explicit
`ℕ` and driven by `Nat.rec`: the arity's worth of recursive uses sit at one
bound, as its `BinTree` model's two do. -/
theorem exists_spell_append_of_live_of_buf_nil_of_one_le_depth (R : RankedAlphabet) :
    ∀ (n : ℕ) (w : List Bool), w.length ≤ n →
      (R.scanFinal w).live = true → (R.scanFinal w).buf = [] →
      1 ≤ (R.scanFinal w).depth →
        ∃ t rest, R.spell t ++ rest = w ∧
          (R.scanFinal rest).live = true ∧ (R.scanFinal rest).buf = [] ∧
          (R.scanFinal rest).depth + 1 = (R.scanFinal w).depth := _

/-- A word whose scan ends live, with no incomplete block and nothing
pending, is empty. -/
theorem eq_nil_of_live_of_buf_nil_of_depth_eq_zero (R : RankedAlphabet)
    (w : List Bool) (hlive : (R.scanFinal w).live = true)
    (hbuf : (R.scanFinal w).buf = []) (hd : (R.scanFinal w).depth = 0) : w = [] := _

/-- Every valid word is a spelling. -/
theorem exists_spell_of_valid (R : RankedAlphabet) {w : List Bool} (h : R.Valid w) :
    ∃ t, R.spell t = w := by
  rw [Valid, validBool] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
  obtain ⟨⟨hlive, hbuf⟩, hd⟩ := h
  obtain ⟨t, rest, he, hlive', hbuf', hd'⟩ :=
    exists_spell_append_of_live_of_buf_nil_of_one_le_depth R w.length w le_rfl hlive hbuf
      (by omega)
  have hz : (R.scanFinal rest).depth = 0 := by omega
  have hnil : rest = [] :=
    eq_nil_of_live_of_buf_nil_of_depth_eq_zero R rest hlive' hbuf' hz
  subst hnil
  exact ⟨t, by simpa using he⟩

/-- The encoding's image is exactly the valid words. -/
theorem valid_iff_exists_spell (R : RankedAlphabet) (w : List Bool) :
    R.Valid w ↔ ∃ t, R.spell t = w :=
  ⟨exists_spell_of_valid R, fun ⟨t, ht⟩ ↦ ht ▸ valid_spell R t⟩

/-- The descent decides validity. -/
theorem valid_iff_isSome_parse (R : RankedAlphabet) (w : List Bool) :
    R.Valid w ↔ (R.parse w).isSome := by
  rw [valid_iff_exists_spell]
  refine ⟨fun ⟨t, ht⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [← ht, parse_spell]; rfl
  · obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
    exact ⟨t, parse_eq_some_iff.mp ht⟩
```

The two underscores are this task's work, developed against the compiler
for the reason Task 9 gives. The decomposition:
`width_le_length_of_one_le_depth` gives `R.width ≤ w.length`, so
`w = w.take (w.length - R.width) ++ blk` with `blk` a full block;
`scanFrom_append` splits the scan there; `buf_length_scanFinal` shows the
prefix's scan has an empty buffer; the block's symbol has an arity `r`, and
`Nat.rec` over `r` peels that many spellings off, each by the induction
hypothesis at the reduced bound. `eq_nil_of_live_of_buf_nil_of_depth_eq_zero`
is a `match` on `w`: a non-empty word ends its scan either mid-block,
contradicting `hbuf` via `buf_length_scanFinal`, or having completed a
block, which pushes and contradicts `hd`.

- [ ] **Step 4: Build and lint**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Preorder && lake lint
```

Expected: PASS with no underscore remaining.

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Preorder.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean \
  -m "feat(tree): characterise the ranked encoding's image"
```

### Task 11: The binary alphabet

**Files:** create `Geb/Mathlib/Data/Tree/Ranked/Binary.lean` and
`GebTests/Mathlib/Data/Tree/Ranked/Binary.lean`.

**Interfaces:**

- Consumes: `valid_iff_exists_spell`, `valid_spell`, `spell`, `Term.mk`,
  `Term.induction`, plus `BinTree`, `BinTree.print`, `BinTree.Valid`,
  `BinTree.valid_iff_exists_print`, `BinTree.induction`.
- Produces: `binRanked`, `Binary.leaf`, `Binary.node`, `Binary.termEquiv`,
  `Binary.spell_termEquiv`, `Binary.valid_iff`. Branch B2 consumes
  `Binary.valid_iff`.

- [ ] **Step 1: Write the failing test**

Create `GebTests/Mathlib/Data/Tree/Ranked/Binary.lean` importing
`Geb.Mathlib.Data.Tree.Ranked.Binary`, with a module docstring titled
`# The binary alphabet on worked trees`, `## Main definitions`
(`binValidAgrees`), `## Main statements`, and `## Tags`:
`ranked alphabet, binary tree, preorder, encoding`.

```lean
open RankedAlphabet.Binary

/-- The width-one alphabet's validity agrees with the existing predicate on
every word of length at most eight. -/
def binValidAgrees : Bool :=
  ((List.range 9).flatMap fun n ↦
    (List.range (2 ^ n)).map fun m ↦ (List.range n).map fun j ↦ m.testBit j).all
    fun w ↦ binRanked.validBool w == decide (BinTree.Valid w)

/-- The agreement holds. -/
theorem binValidAgrees_eq : binValidAgrees = true := by
  set_option maxRecDepth 100000 in decide

/-- The leaf's spelling is the existing one. -/
theorem spell_binLeaf : binRanked.spell leaf = BinTree.print BinTree.leaf := by decide

/-- The two-leaf node's spelling is the existing one. -/
theorem spell_binNode :
    binRanked.spell (node leaf leaf) =
      BinTree.print (BinTree.node BinTree.leaf BinTree.leaf) := by decide
```

- [ ] **Step 2: Run to verify it fails**

```bash
lake build GebTests.Mathlib.Data.Tree.Ranked.Binary
```

Expected: FAIL, `unknown module Geb.Mathlib.Data.Tree.Ranked.Binary`.

- [ ] **Step 3: Write the module**

Create `Geb/Mathlib/Data/Tree/Ranked/Binary.lean` with the header,
`module`, the three imports from § File structure, and a module docstring
titled `# The binary alphabet` stating that the unlabelled binary trees are
the terms of the alphabet of one symbol of arity zero and one of arity two,
that `spell` there is `BinTree.print` transported along `termEquiv`, and
that `Valid` there is `BinTree.Valid`. `## Tags`:
`ranked alphabet, binary tree, preorder, encoding`.

Note the `public section` wrapper: `@[expose]` outside one errors with
"Redundant [expose] attribute, it is meaningful on public definitions
only".

```lean
public section

/-- One symbol of arity zero and one of arity two, each spelled by one bit:
the alphabet whose terms are the unlabelled binary trees. -/
@[expose] def binRanked : RankedAlphabet := ⟨2, 1, Nat.one_pos, by decide, ![0, 2]⟩

namespace RankedAlphabet.Binary

/-- The leaf, at the binary alphabet. -/
@[expose] def leaf : binRanked.Term :=
  binRanked.Term.mk ⟨0, by decide⟩ (fun i ↦ absurd i.isLt (by decide +revert))

/-- The node, at the binary alphabet. The cast's target is named because a
cast into `Fin.cases`'s expected type leaves it a metavariable, at which
`by decide` cannot elaborate. -/
@[expose] def node (l r : binRanked.Term) : binRanked.Term :=
  binRanked.Term.mk ⟨1, by decide⟩ (fun d ↦
    Fin.cases l (fun _ ↦ r)
      (Fin.cast (show binRanked.arity ⟨1, by decide⟩ = 2 by decide) d))

/-- The terms of the binary alphabet are the unlabelled binary trees. -/
@[expose] def termEquiv : binRanked.Term ≃ BinTree where
  toFun := WType.elim BinTree fun x ↦
    Fin.cases (motive := fun i ↦ (Fin (binRanked.arity i) → BinTree) → BinTree)
      (fun _ ↦ BinTree.leaf)
      (fun _ ch ↦ BinTree.node
        (ch (Fin.cast (show (2 : ℕ) = binRanked.arity ⟨1, by decide⟩ by decide) 0))
        (ch (Fin.cast (show (2 : ℕ) = binRanked.arity ⟨1, by decide⟩ by decide) 1)))
      x.1 x.2
  invFun := WType.elim binRanked.Term fun x ↦
    match x with
    | ⟨.leaf, _⟩ => leaf
    | ⟨.node, ch⟩ => node (ch (0 : Fin 2)) (ch (1 : Fin 2))
  left_inv := _
  right_inv := _

/-- The spelling at the binary alphabet is the existing encoding. -/
theorem spell_termEquiv (t : binRanked.Term) :
    binRanked.spell t = BinTree.print (termEquiv t) := _

/-- Validity at the binary alphabet is the existing predicate. -/
theorem valid_iff (w : List Bool) : binRanked.Valid w ↔ BinTree.Valid w := by
  rw [RankedAlphabet.valid_iff_exists_spell, BinTree.valid_iff_exists_print]
  refine ⟨fun ⟨t, ht⟩ ↦ ⟨termEquiv t, ?_⟩, fun ⟨u, hu⟩ ↦ ⟨termEquiv.symm u, ?_⟩⟩
  · rw [← ht, spell_termEquiv]
  · rw [spell_termEquiv, Equiv.apply_symm_apply, hu]

end RankedAlphabet.Binary

end
```

The three underscores are this task's work: `termEquiv`'s two round trips,
each by the corresponding recursor (`Term.induction` one way,
`BinTree.induction` the other), and `spell_termEquiv` by `Term.induction`
with `Fin.cases` on the head symbol's index. `toFun`'s shape is dictated by
finding 5: `binRanked.arity x.1` does not reduce under a hypothesis about
`x.1.val`, so the case analysis is by `Fin.cases` on `x.1` rather than by
`if x.1.val = 0`.

- [ ] **Step 4: Build, test and lint**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Binary \
  GebTests.Mathlib.Data.Tree.Ranked.Binary && lake lint
```

Expected: PASS. `binValidAgrees` at bound 8 covers 511 words and needs
`set_option maxRecDepth 100000`; the same check at bound 10 was run before
this plan was written and returned `true`, so a failure here is a defect in
the transcription rather than in the design.

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Binary.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Binary.lean \
  -m "feat(tree): exhibit the binary trees as a ranked alphabet's terms"
```

### Task 12: Bibliography

**Files:** modify `docs/references.bib`.

**Interfaces:** produces the entries the modules' `## References` sections
and the spec cite. No Lean declaration.

- [ ] **Step 1: Add the three confirmed entries**

`BenoitDemaineMunroRamanRamanRao2005` (Benoit, Demaine, Munro, Raman,
Raman, Srinivasa Rao, *Representing Trees of Higher Degree*, Algorithmica
43(4):275–292, 2005), `Mehlhorn1980` (Mehlhorn, *Pebbling mountain ranges
and its application to DCFL-recognition*, ICALP 1980), and
`BraunmuhlVerbeek1983` (von Braunmühl and Verbeek, *Input-Driven Languages
are Recognized in log n Space*, FCT 1983, LNCS 158:40–51). Each entry
carries a `note` recording what this repository cites it for, matching the
existing entries' shape.

- [ ] **Step 2: Record the unverified entry as follow-on work**

`BarringtonCorbett1989` is **not** added: its bibliographic detail and its
content claim are unverified against the article. Task 14 records it under
`TODO.md` § Citation corrections deferred to their own branch.

- [ ] **Step 3: Check and commit**

```bash
markdownlint-cli2 '**/*.md' && bash scripts/check-md-links.sh
```

```bash
jj commit docs/references.bib -m "doc: cite the succinct-tree and input-driven sources"
```

### Task 13: Indices, documentation and the full check

**Files:** create `Geb/Mathlib/Data/Tree/Ranked.lean` and
`GebTests/Mathlib/Data/Tree/Ranked.lean`; modify
`Geb/Mathlib/Data/Tree.lean`, `GebTests/Mathlib/Data/Tree.lean`,
`docs/index.md`.

- [ ] **Step 1: Write the indices**

Create `Geb/Mathlib/Data/Tree/Ranked.lean` with the header, `module`, the
four `public import`s in dependency order, and the module docstring in the
three-line form `Geb/Mathlib/Data/Tree.lean` uses:

```lean
/-!
# Ranked — index
-/
```

Create `GebTests/Mathlib/Data/Tree/Ranked.lean` with the same shape over
the four test modules, using plain `import`. Add
`public import Geb.Mathlib.Data.Tree.Ranked` to `Geb/Mathlib/Data/Tree.lean`
and the parallel plain `import` to `GebTests/Mathlib/Data/Tree.lean`.

- [ ] **Step 2: Document the modules**

Add one entry per new module to `docs/index.md`, beside the existing
`Data/Tree/Binary.lean` and `Data/Tree/Preorder.lean` entries, in
topological order, each naming what the module defines and states.

- [ ] **Step 3: Build and run the full check**

```bash
lake build && lake test && lake lint && lake shake && bash scripts/lint-imports.sh
```

Expected: all PASS with no warnings. `lake shake` may report an import used
only inside a test assertion; the sanctioned repair is to name the `def`
the assertion is built from, not `-- shake: keep`.

- [ ] **Step 4: Verify the axiom set**

Read `#print axioms` through `lean_verify` on
`RankedAlphabet.valid_iff_exists_spell`, `RankedAlphabet.spell_injective`
and `RankedAlphabet.Binary.valid_iff`. Expected: `[propext, Quot.sound]`
for each. `lake lint` in Step 3 covers every declaration; this step is the
explicit reading of the three the branch exists to deliver.

- [ ] **Step 5: Run the markdown checks and commit**

```bash
doctoc --update-only docs/index.md && markdownlint-cli2 '**/*.md' &&
  bash scripts/check-md-links.sh
```

```bash
jj commit -m "feat(tree): index and document the ranked encoding modules"
```

### Task 14: Record follow-on work and retire the transient artifacts

**Files:** modify `TODO.md`; delete
`docs/superpowers/specs/2026-08-09-ranked-tree-recognizers-design.md` and
`docs/superpowers/plans/2026-08-09-ranked-tree-encoding.md`.

This task is mandatory, not optional: `CONTRIBUTING.md` § Concern shape
orders a branch as spec and plan, then implementation with its persistent
documentation and `TODO.md` notes, then removal of the spec and plan.

- [ ] **Step 1: Rewrite `TODO.md` § Extensions of the tree recognizers**

Replace the four investigations with what survives them, since the spec
that settles them is about to be deleted: item 4 is implemented by this
branch; B2 to B5 remain, with their dependencies and the reason B5 differs
in kind; the spec's Deferred list (the Bellantoni-Cook port with the
labelled and ranked variants and the `safeRec` tree recursor folded in, the
paramorphism over subterm spellings, the fold at an infinite carrier, and
the depth-first unary degree sequence encoding with its adoption condition)
moves here verbatim in substance.

- [ ] **Step 2: Record the two deferred items**

Under `TODO.md` § Citation corrections deferred to their own branch, record
that `BarringtonCorbett1989`'s bibliographic detail and its
DLOGTIME-uniform TC⁰ claim are both unverified, and that the spec's
attribution was to secondary sources.

Add a new item recording the divergence adversarial review surfaced:
`docs/rules/lean-coding.md` § Naming conventions forbids a namespace
prefix in a declaration body, and `Geb/Mathlib/Data/Tree/Preorder.lean`
uses `BinTree.induction (motive := …)` inside `namespace BinTree` at four
sites, as this branch's modules do with `Term.induction`. Either the rule
or the merged code is wrong repo-wide; deciding it belongs on its own
branch, per § Concern shape.

- [ ] **Step 2a: Check the markdown**

```bash
doctoc --update-only TODO.md && markdownlint-cli2 '**/*.md' &&
  bash scripts/check-md-links.sh
```

- [ ] **Step 3: Commit the notes**

```bash
jj commit TODO.md -m "doc(tree): record the follow-on branches and deferrals"
```

- [ ] **Step 4: Remove the spec and plan**

```bash
rm docs/superpowers/specs/2026-08-09-ranked-tree-recognizers-design.md
rm docs/superpowers/plans/2026-08-09-ranked-tree-encoding.md
jj commit -m "doc(tree): remove the transient spec and plan"
```

- [ ] **Step 5: Pre-push checklist**

```bash
bash scripts/pre-push.sh
```

Expected: PASS. Do not push. The branch waits on the user's line-by-line
review, per CONTRIBUTING.md § Working and AGENTS.md § No `jj git push`
without user line-by-line review.
