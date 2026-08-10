# Ranked-alphabet tree encoding implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task. Steps
> use checkbox (`- [ ]`) syntax for tracking.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global Constraints](#global-constraints)
- [File structure](#file-structure)
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
  - [Task 9: Every valid word is a spelling](#task-9-every-valid-word-is-a-spelling)
  - [Task 10: The binary alphabet](#task-10-the-binary-alphabet)
  - [Task 11: Indices, documentation and the full check](#task-11-indices-documentation-and-the-full-check)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

**Goal:** Encode the term algebra of any finite ranked alphabet as a
bitstring, decide the image of that encoding by a single right-to-left
scan, and exhibit the existing `BinTree` encoding as the two-symbol
instance.

**Architecture:** A ranked alphabet is a finitary polynomial functor whose
shape type is `Fin card`, so its term algebra is that functor's W-type, as
`BinTree` is the W-type of `BinTree.Direction`. Each symbol is spelled by a
fixed-width block of bits followed by its children's spellings, which is
`BinTree.print` at width one. Validity is a fold whose state carries an
incomplete block, the count of pending subterms and a liveness flag; at
width one the block is always complete and the state reduces to
`BinTree.ok` and `BinTree.depth`. The image is characterised through a
fuel-bounded recursive descent, as `BinTree.valid_iff_exists_print` is.

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
- `Geb/Mathlib/` may import only `Mathlib.*`, `Batteries.*`,
  `Geb.Mathlib.*`. The prefix `Geb.Mathlib.` appears only on `^import`
  lines — never in `namespace`, declaration bodies, docstrings or comments.
- Every `.lean` file: `module` keyword after the copyright block, the
  mathlib copyright header, a module docstring with `# Title`, a summary,
  and every mandatory section that has content, `## Tags` included; a
  `/-- … -/` docstring on every `def`, `structure`, `instance`, every
  structure field, and every public-interest theorem.
- 100-column lines, two-space indent, `UpperCamelCase` for `Prop` and
  `Type`, `lowerCamelCase` for values, `snake_case` for theorems.
- No `sorry` in any commit. Underscores, not `sorry`, for holes in
  progress.
- No empty lines inside a declaration; a brief `-- …` comment separates
  instead.
- Commit messages: `type(scope): imperative subject`, lowercase, no
  trailing period, type from
  `feat | fix | doc | style | refactor | test | chore | perf | ci`.
- `#guard` belongs to `GebTests` only; `Geb` keeps the ban. A test asserting
  a value that does not reduce in the kernel uses a named `def` returning
  `Bool` and an `example` closed by `decide`, never an anonymous `example`
  (which the axiom linter does not audit).
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
| `docs/index.md` | one entry per new module |

`Code.lean` is separate from `Preorder.lean` because the round trip
`decodeBits_code` is about the alphabet alone and is consumed twice, by the
descent and by the scan; keeping it apart also keeps `Preorder.lean` near
the size of the module it generalises.

## Declaration inventory

Every declaration the tasks produce, so that no task names one a neighbour
does not create.

| Declaration | Task | File | Statement or type |
| --- | --- | --- | --- |
| `Ranked` | 1 | Basic | `structure` with `card width width_pos card_le ar` |
| `Ranked.Term` | 1 | Basic | `Type` |
| `Ranked.mk'` | 1 | Basic | `(i : Fin R.card) → (Fin (R.ar i) → R.Term) → R.Term` |
| `Ranked.Term.size` | 1 | Basic | `R.Term → ℕ` |
| `Ranked.induction` | 1 | Basic | induction in the `mk'` presentation |
| `Ranked.code` | 2 | Code | `Fin R.card → List Bool` |
| `decodeBits` | 2 | Code | `List Bool → ℕ` |
| `Ranked.arOf` | 2 | Code | `ℕ → Option ℕ` |
| `Ranked.length_code` | 2 | Code | `(R.code i).length = R.width` |
| `Ranked.decodeBits_code` | 2 | Code | `decodeBits (R.code i) = i.val` |
| `Ranked.arOf_decodeBits_code` | 2 | Code | `R.arOf (decodeBits (R.code i)) = some (R.ar i)` |
| `Ranked.spell` | 3 | Preorder | `R.Term → List Bool` |
| `Ranked.spell_mk'` | 3 | Preorder | the unfolding at `mk'` |
| `Ranked.length_spell` | 3 | Preorder | `(R.spell t).length = R.width * t.size` |
| `Ranked.width_le_length_spell` | 3 | Preorder | `R.width ≤ (R.spell t).length` |
| `Ranked.decodeBlock` | 4 | Preorder | `List Bool → Option (Fin R.card × List Bool)` |
| `Ranked.parseChildren` | 4 | Preorder | `(child) → (n : ℕ) → List Bool → Option ((Fin n → R.Term) × List Bool)` |
| `Ranked.parseStep` | 4 | Preorder | one descent layer |
| `Ranked.parseAux` | 4 | Preorder | `ℕ → List Bool → Option (R.Term × List Bool)` |
| `Ranked.parse` | 4 | Preorder | `List Bool → Option R.Term` |
| `Ranked.parseAux_spell` | 5 | Preorder | the descent inverts the spelling |
| `Ranked.parse_spell` | 5 | Preorder | `R.parse (R.spell t) = some t` |
| `Ranked.parseAux_eq_some` | 6 | Preorder | whatever the descent reads is a spelling |
| `Ranked.parse_eq_some_iff` | 6 | Preorder | `R.parse w = some t ↔ R.spell t = w` |
| `Ranked.spell_injective` | 6 | Preorder | `Function.Injective R.spell` |
| `Scan` | 7 | Preorder | `structure` with `buf depth live` |
| `Ranked.scanStep` | 7 | Preorder | `Bool → Scan → Scan` |
| `Ranked.scanFrom` | 7 | Preorder | `List Bool → Scan → Scan` |
| `Ranked.scanFinal` | 7 | Preorder | `List Bool → Scan` |
| `Ranked.validBool` | 7 | Preorder | `List Bool → Bool` |
| `Ranked.Valid` | 7 | Preorder | `List Bool → Prop` |
| `Ranked.scanFrom_append` | 7 | Preorder | `scanFrom (u ++ v) s = scanFrom u (scanFrom v s)` |
| `Ranked.scanFrom_flatten` | 8 | Preorder | the fold over a list of spellings |
| `Ranked.scanFrom_spell` | 8 | Preorder | `scanFrom (R.spell t) ⟨[], d, true⟩ = ⟨[], d + 1, true⟩` |
| `Ranked.valid_spell` | 8 | Preorder | `R.Valid (R.spell t)` |
| `Ranked.exists_spell_append` | 9 | Preorder | the fuel-bounded existence argument |
| `Ranked.exists_spell_of_valid` | 9 | Preorder | the converse |
| `Ranked.valid_iff_exists_spell` | 9 | Preorder | the characterisation |
| `Ranked.valid_iff_isSome_parse` | 9 | Preorder | `R.parse` decides `R.Valid` |
| `binRanked` | 10 | Binary | `Ranked` |
| `binRanked.termEquiv` | 10 | Binary | `binRanked.Term ≃ BinTree` |
| `binRanked.spell_termEquiv` | 10 | Binary | `binRanked.spell t = BinTree.print (termEquiv t)` |
| `binRanked.valid_iff` | 10 | Binary | `binRanked.Valid w ↔ BinTree.Valid w` |

## Findings that bind the implementation

Each was established by running the code before this plan was written. A
task that departs from one of them will not build.

1. **`scanStep` matches on `Bool`, never on a decidable proposition.** An
   `if p then _ else _` at a decidable `p` blocks kernel reduction, and
   `decide` on `Valid` then fails with "reduction got stuck at the
   `Decidable` instance". Writing `match decide (…) with | false => … |
   true => …` reduces. The same rule governs `arOf`'s consumers.
2. **`Valid` is `validBool w = true`, not a structure equation.** The
   derived `DecidableEq Scan` does not reduce under `decide` at a symbolic
   fold. A `Bool`-valued function with a `= true` wrapper does, and it is
   the idiom `BinTree.ok` already uses.
3. **`![…]` needs `Mathlib.Data.Fin.VecNotation`.** Without it `![0, 2]`
   parses as boolean negation applied to a list, and the error names `Bool`
   rather than the notation.
4. **`0 < width` is required.** It is what makes each `parseStep` layer
   consume at least one bit before delegating, which is the invariant
   `parse`'s fuel argument rests on. Without it a zero-width alphabet
   spells every term by the empty word.
5. **A term at a concrete alphabet needs its arity to reduce.** Writing
   `WType.mk ⟨0, _⟩ (fun i ↦ i.elim0)` fails with `Fin (binRanked.ar ⟨0, _⟩)`
   against `Fin 0`. `Ranked.mk'` exists for this reason and Task 10 supplies
   `binLeaf` and `binNode` so no test constructs a term by hand.
6. **The width-one specialisation holds.** `binRanked.validBool` agrees
   with `decide (BinTree.Valid ·)` on every one of the 2047 words of length
   at most ten. Task 10 commits that check.

## Tasks

### Task 1: The ranked alphabet and its term algebra

**Files:**

- Create: `Geb/Mathlib/Data/Tree/Ranked/Basic.lean`
- Create: `GebTests/Mathlib/Data/Tree/Ranked/Basic.lean`

**Interfaces:**

- Consumes: `Mathlib.Data.W.Basic`.
- Produces: `Ranked`, `Ranked.Term`, `Ranked.mk'`, `Ranked.Term.size`,
  `Ranked.induction`. Every later task consumes `Ranked` and `Ranked.Term`;
  Tasks 3, 5, 8 consume `Ranked.induction`; Task 3 consumes
  `Ranked.Term.size`.

- [ ] **Step 1: Write the failing test**

Create `GebTests/Mathlib/Data/Tree/Ranked/Basic.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.Tree.Ranked.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# The ranked alphabet on a worked signature

`size` on the terms of a four-symbol alphabet of arities zero to three.

## Main definitions

* `sampleAlphabet` — the alphabet the assertions are stated at.
* `sampleNullary`, `sampleBinary` — the terms they are stated at.

## Main statements

The assertions below give `size` on a nullary term and on a binary term
over that alphabet.

## Tags

ranked alphabet, term algebra, W-type
-/

set_option linter.privateModule false

/-- Four symbols of arities zero to three, spelled by two bits each. -/
def sampleAlphabet : Ranked := ⟨4, 2, by decide, by decide, ![0, 1, 2, 3]⟩

/-- The nullary symbol's term. -/
def sampleNullary : sampleAlphabet.Term :=
  sampleAlphabet.mk' ⟨0, by decide⟩ (fun i ↦ absurd i.isLt (by decide))

/-- The binary symbol applied to two nullary terms. -/
def sampleBinary : sampleAlphabet.Term :=
  sampleAlphabet.mk' ⟨2, by decide⟩ (fun _ ↦ sampleNullary)

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

Create `Geb/Mathlib/Data/Tree/Ranked/Basic.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.W.Basic

/-!
# Ranked alphabets and their term algebras

A ranked alphabet names finitely many symbols, each with an arity and each
spelled by a block of bits of one common width. Its term algebra is the
W-type of the finitary polynomial functor whose shape type is `Fin card`
and whose direction family sends a symbol to `Fin` of its arity, so that
all recursion over terms is carried by `WType.elim` and `WType.rec`.

The unlabelled binary trees of `Data/Tree/Binary.lean` are the terms of the
alphabet of one symbol of arity zero and one of arity two.

## Main definitions

* `Ranked` — the alphabet.
* `Ranked.Term` — the term algebra.
* `Ranked.mk'` — the constructor, at the alphabet's own arities.
* `Ranked.Term.size` — the number of nodes.

## Main statements

* `Ranked.induction` — induction in the `mk'` presentation.

## Implementation notes

`width_pos` is not decoration. It is what makes one layer of the recursive
descent of `Data/Tree/Ranked/Preorder.lean` consume at least one bit before
delegating, which is the invariant that module's fuel argument rests on.

`Term` is `@[expose]`, as `BinTree` is: without it `WType.mk` applications
against `Fin (R.ar i)` do not elaborate across the module boundary.

`mk'` exists because `WType.mk` at a concrete alphabet presents a child
family at type `Fin (R.ar ⟨v, h⟩)`, which is not syntactically `Fin 0` at a
nullary symbol; `mk'` names the arity so that a caller writes it once.

## Tags

ranked alphabet, term algebra, W-type, polynomial functor, arity
-/

/-- A ranked alphabet: `card` symbols, each spelled by a block of `width`
bits and each carrying an arity. `card_le` admits an alphabet whose size is
not a power of two, at the price of blocks that spell no symbol. -/
public structure Ranked where
  /-- The number of symbols. -/
  card : ℕ
  /-- The number of bits spelling one symbol. -/
  width : ℕ
  /-- Every symbol's block is non-empty. -/
  width_pos : 0 < width
  /-- Every symbol has a block of the common width. -/
  card_le : card ≤ 2 ^ width
  /-- The arity of each symbol. -/
  ar : Fin card → ℕ

namespace Ranked

public section

/-- The term algebra of a ranked alphabet. -/
@[expose] def Term (R : Ranked) : Type := WType fun i : Fin R.card ↦ Fin (R.ar i)

/-- The term with head symbol `i` and children `ch`. -/
@[expose] def mk' (R : Ranked) (i : Fin R.card) (ch : Fin (R.ar i) → R.Term) : R.Term :=
  WType.mk i ch

/-- The number of nodes of a term. -/
@[expose] def Term.size {R : Ranked} : R.Term → ℕ :=
  WType.elim ℕ fun x ↦ (List.ofFn x.2).sum + 1

/-- Induction in the `mk'` presentation, so that a proof driven by it need
not mention the underlying shape and direction families. -/
theorem induction {R : Ranked} {motive : R.Term → Prop}
    (hmk : ∀ i ch, (∀ d, motive (ch d)) → motive (R.mk' i ch)) :
    ∀ t, motive t :=
  WType.rec (motive := motive) fun i ch ih ↦ hmk i ch ih

@[simp] theorem size_mk' {R : Ranked} (i : Fin R.card) (ch : Fin (R.ar i) → R.Term) :
    (R.mk' i ch).size = (List.ofFn fun d ↦ (ch d).size).sum + 1 := rfl

end

end Ranked
```

- [ ] **Step 4: Build and test**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Basic GebTests.Mathlib.Data.Tree.Ranked.Basic
```

Expected: PASS. If `size_mk'` does not close by `rfl`, the cause is
`WType.elim`'s reduction at a `Sigma` pattern; replace the body with
`by rfl` and, failing that, with `by simp [Term.size, mk']`.

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Basic.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Basic.lean \
  -m "feat(tree): add ranked alphabets and their term algebras"
```

### Task 2: Codes and their round trip

**Files:**

- Create: `Geb/Mathlib/Data/Tree/Ranked/Code.lean`
- Create: `GebTests/Mathlib/Data/Tree/Ranked/Code.lean`

**Interfaces:**

- Consumes: `Ranked` from Task 1.
- Produces: `Ranked.code`, `decodeBits`, `Ranked.arOf`,
  `Ranked.length_code`, `Ranked.decodeBits_code`,
  `Ranked.arOf_decodeBits_code`. Tasks 3, 4, 7, 8, 9 consume them.

- [ ] **Step 1: Write the failing test**

Create `GebTests/Mathlib/Data/Tree/Ranked/Code.lean` with the header and
module docstring of Task 1's test (title `# Codes on a worked signature`,
tags `ranked alphabet, code, binary representation`). It imports
`GebTests.Mathlib.Data.Tree.Ranked.Basic` for `sampleAlphabet` rather than
redeclaring it: the test index imports all four test modules together, so a
second top-level `sampleAlphabet` would clash. Then:

```lean
/-- The codes are the two-bit binary representations, least significant
bit first. -/
theorem code_zero : sampleAlphabet.code ⟨0, by decide⟩ = [false, false] := by decide

/-- The code of the symbol of arity one. -/
theorem code_one : sampleAlphabet.code ⟨1, by decide⟩ = [true, false] := by decide

/-- The code of the symbol of arity three. -/
theorem code_three : sampleAlphabet.code ⟨3, by decide⟩ = [true, true] := by decide

/-- The round trip on each of the alphabet's codes. -/
theorem decodeBits_code_all :
    ((List.finRange 4).all fun i ↦
      decodeBits (sampleAlphabet.code i) == i.val) = true := by decide

/-- A block outside the alphabet has no arity. -/
theorem arOf_out_of_range : sampleAlphabet.arOf 4 = none := by decide

/-- A block inside the alphabet has the arity the table gives. -/
theorem arOf_in_range : sampleAlphabet.arOf 2 = some 2 := by decide
```

Delete `codeRoundTripCheck` before committing; it is superseded by
`decodeBits_code_all`, which is the assertion that carries content.

- [ ] **Step 2: Run to verify it fails**

```bash
lake build GebTests.Mathlib.Data.Tree.Ranked.Code
```

Expected: FAIL, `unknown module Geb.Mathlib.Data.Tree.Ranked.Code`.

- [ ] **Step 3: Write the module**

Create `Geb/Mathlib/Data/Tree/Ranked/Code.lean` with the standard header,
`module`, and:

```lean
public import Geb.Mathlib.Data.Tree.Ranked.Basic
public import Mathlib.Data.Nat.Bitwise
```

Module docstring `# Symbol codes`, summary describing the least-significant
-bit-first block and its decoding, `## Main definitions` listing `code`,
`decodeBits`, `arOf`, `## Main statements` listing the three lemmas,
`## Implementation notes` recording finding 1 of this plan, and
`## Tags`: `ranked alphabet, code, binary representation, decoding`.

```lean
namespace Ranked

public section

/-- The block spelling a symbol: its index in binary, least significant bit
first, padded to the alphabet's width. -/
@[expose] def code (R : Ranked) (i : Fin R.card) : List Bool :=
  (List.range R.width).map fun j ↦ i.val.testBit j

/-- The value a block denotes, its head the least significant bit. -/
@[expose] def decodeBits : List Bool → ℕ :=
  List.rec 0 fun b _ ih ↦ 2 * ih + (if b then 1 else 0)

/-- The arity of the symbol a block denotes, absent at a block denoting
none. -/
@[expose] def arOf (R : Ranked) (v : ℕ) : Option ℕ :=
  if h : v < R.card then some (R.ar ⟨v, h⟩) else none

/-- Every block has the alphabet's width. -/
@[simp] theorem length_code (R : Ranked) (i : Fin R.card) :
    (R.code i).length = R.width := by
  simp [code]

/-- A block decodes to the symbol it spells. The bound `i.val < 2 ^ width`
comes from `card_le`, and is what makes the padding lossless. -/
theorem decodeBits_code (R : Ranked) (i : Fin R.card) :
    decodeBits (R.code i) = i.val := by
  have hlt : i.val < 2 ^ R.width := Nat.lt_of_lt_of_le i.isLt R.card_le
  -- `decodeBits ((List.range n).map (testBit v)) = v % 2 ^ n`, by `Nat.rec` on `n`
  have key : ∀ (n v : ℕ),
      decodeBits ((List.range n).map fun j ↦ v.testBit j) = v % 2 ^ n :=
    Nat.rec (fun v ↦ by simp [decodeBits])
      (fun n ih v ↦ by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map]
        simp only [decodeBits, Function.comp_def]
        rw [ih (v / 2)]
        rw [Nat.testBit_zero]
        omega) n
  rw [code, key, Nat.mod_eq_of_lt hlt]

/-- A block spelling a symbol has that symbol's arity. -/
theorem arOf_decodeBits_code (R : Ranked) (i : Fin R.card) :
    R.arOf (decodeBits (R.code i)) = some (R.ar i) := by
  rw [decodeBits_code, arOf, dif_pos i.isLt]

end

end Ranked
```

- [ ] **Step 4: Build and test**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Code GebTests.Mathlib.Data.Tree.Ranked.Code
```

Expected: PASS. `key`'s successor case is the only step likely to need
adjustment: it rests on `v % 2 ^ (n + 1) = 2 * ((v / 2) % 2 ^ n) + v % 2`,
which `omega` closes once `Nat.testBit_zero` has rewritten the head bit to
`v % 2 = 1`. If `omega` stalls, supply that identity as a `have` proved by
`Nat.div_add_mod` and `Nat.pow_succ`.

- [ ] **Step 5: Verify the axiom set**

```bash
lake lint
```

Expected: PASS. `Nat.Bitwise` is a mathlib module; if
`detectNonstandardAxiom` reports `Classical.choice` on `decodeBits_code`,
the cause is a `simp` lemma of the `Nat` order API, and the repair is
Global Constraint "bound `Fin` and `Nat` arithmetic by `omega` or by cases"
— replace the offending `simp` with `omega` over named hypotheses.

- [ ] **Step 6: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Code.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Code.lean \
  -m "feat(tree): add symbol codes and their round trip"
```

### Task 3: The spelling

**Files:**

- Create: `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean`
- Create: `GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean`

**Interfaces:**

- Consumes: `Ranked.mk'`, `Ranked.Term.size`, `Ranked.induction`,
  `Ranked.code`, `Ranked.length_code`.
- Produces: `Ranked.spell`, `Ranked.spell_mk'`, `Ranked.length_spell`,
  `Ranked.width_le_length_spell`. Tasks 5, 6, 8, 9, 10 consume them.

- [ ] **Step 1: Write the failing test**

Create `GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean` with the standard
header, `import Geb.Mathlib.Data.Tree.Ranked.Preorder`,
`import Mathlib.Data.Fin.VecNotation`, a module docstring titled
`# The ranked preorder encoding on worked terms`. It imports
`GebTests.Mathlib.Data.Tree.Ranked.Basic` for `sampleAlphabet`,
`sampleNullary` and `sampleBinary` rather than redeclaring them, for the
reason Task 2 gives. Then:

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

- [ ] **Step 3: Write the module's first section**

Create `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` with the standard
header, `module`, and:

```lean
public import Geb.Mathlib.Data.Tree.Ranked.Code
```

Module docstring `# The preorder encoding of ranked terms`, summarising
that a symbol is spelled by its block followed by its children's spellings,
that the encoding is a bijection onto the words satisfying `Valid`, and
that the processing order of a right-to-left scan is the reverse of the
list order so a symbol is applied after its children. Sections
`## Main definitions`, `## Main statements`, `## Implementation notes` and
`## Tags` are filled as the later tasks add their declarations; each task
below appends its own entries. Tags:
`ranked alphabet, preorder, prefix notation, encoding, retraction, scan`.

```lean
namespace Ranked

public section

/-- The preorder encoding: a symbol's block followed by its children's
spellings, in index order. -/
@[expose] def spell (R : Ranked) : R.Term → List Bool :=
  WType.elim (List Bool) fun x ↦ R.code x.1 ++ (List.ofFn x.2).flatten

@[simp] theorem spell_mk' (R : Ranked) (i : Fin R.card) (ch : Fin (R.ar i) → R.Term) :
    R.spell (R.mk' i ch) = R.code i ++ (List.ofFn fun d ↦ R.spell (ch d)).flatten := rfl

/-- A spelling's length is the alphabet's width times the term's node
count, so the input length is fuel enough for the descent to read anything
`spell` emits. -/
theorem length_spell (R : Ranked) (t : R.Term) :
    (R.spell t).length = R.width * t.size :=
  Ranked.induction (motive := fun t ↦ (R.spell t).length = R.width * t.size)
    (fun i ch ih ↦ by
      rw [spell_mk', List.length_append, length_code, size_mk', Nat.mul_add, Nat.mul_one]
      congr 1
      -- the flattened children contribute the width times the sum of their sizes
      rw [List.length_flatten, List.map_ofFn]
      simp only [Function.comp_def, ih]
      rw [← List.sum_ofFn_mul_left]) t

/-- A spelling is at least one block long. -/
theorem width_le_length_spell (R : Ranked) (t : R.Term) :
    R.width ≤ (R.spell t).length := by
  rw [length_spell]
  refine Nat.le_mul_of_pos_right _ ?_
  refine Ranked.induction (motive := fun t ↦ 0 < t.size) (fun i ch _ ↦ ?_) t
  rw [size_mk']
  omega
```

- [ ] **Step 4: Build and test**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Preorder \
  GebTests.Mathlib.Data.Tree.Ranked.Preorder
```

Expected: PASS. `length_spell`'s node case is the one to watch: it needs
`(List.ofFn fun d ↦ (R.spell (ch d)).length).sum = R.width * (List.ofFn fun d ↦
(ch d).size).sum`. If `List.sum_ofFn_mul_left` is not the mathlib name, find
it with `lean_loogle` on `List.sum (List.map (fun _ => ?c * _) ?l)`; the
fallback is a `List.rec` over `List.ofFn` distributing multiplication over
the sum.

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Preorder.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean \
  -m "feat(tree): add the preorder spelling of ranked terms"
```

### Task 4: The recursive descent

**Files:**

- Modify: `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` — after
  `width_le_length_spell`, and the module docstring
- Modify: `GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean`

**Interfaces:**

- Consumes: `Ranked.arOf`, `Ranked.mk'`, `decodeBits`.
- Produces: `Ranked.decodeBlock`, `Ranked.parseChildren`,
  `Ranked.parseStep`, `Ranked.parseAux`, `Ranked.parseAux_succ`,
  `Ranked.parse`. Tasks 5, 6, 9 consume them.

- [ ] **Step 1: Write the failing test**

Append to `GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean`:

```lean
/-- The descent reads a nullary term. -/
theorem parse_spell_sampleNullary :
    sampleAlphabet.parse [false, false] = some sampleNullary := by decide

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

Expected: FAIL, `unknown identifier 'Ranked.parse'`.

- [ ] **Step 3: Write the descent**

Append to `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean`, inside the
`public section`:

```lean
/-- Read one block: the symbol it spells and the unconsumed remainder,
absent when the word is short of a block or the block spells no symbol. -/
@[expose] def decodeBlock (R : Ranked) (w : List Bool) :
    Option (Fin R.card × List Bool) :=
  if h : decodeBits (w.take R.width) < R.card ∧ R.width ≤ w.length then
    some (⟨decodeBits (w.take R.width), h.1⟩, w.drop R.width)
  else none

/-- Read `n` children in index order, delegating each to `child`. -/
@[expose] def parseChildren {R : Ranked}
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

/-- One layer of the recursive descent: read one block, then as many
children as its symbol's arity. -/
@[expose] def parseStep (R : Ranked)
    (child : List Bool → Option (R.Term × List Bool)) (w : List Bool) :
    Option (R.Term × List Bool) :=
  match R.decodeBlock w with
  | none => none
  | some (i, rest) =>
    match parseChildren child (R.ar i) rest with
    | none => none
    | some (f, rest') => some (R.mk' i f, rest')

/-- Recursive descent bounded by an explicit `ℕ`. -/
@[expose] def parseAux (R : Ranked) : ℕ → List Bool → Option (R.Term × List Bool) :=
  Nat.rec (fun _ ↦ none) fun _ ih ↦ R.parseStep ih

theorem parseAux_succ (R : Ranked) (f : ℕ) :
    R.parseAux (f + 1) = R.parseStep (R.parseAux f) := rfl

/-- The decoding, rejecting trailing input. -/
@[expose] def parse (R : Ranked) (w : List Bool) : Option R.Term :=
  match R.parseAux w.length w with
  | some (t, []) => some t
  | _ => none
```

Add to the module docstring's `## Implementation notes`:

> `parseAux` recurses on an explicit `ℕ` bound rather than on its input:
> each child is parsed from a remainder the previous call computes, which
> is not a structural subterm. `parse` supplies the input's length, and
> `length_spell` shows that bound admits every word `spell` emits. Each
> `parseStep` layer consumes a whole block, of width at least one by
> `width_pos`, before delegating, so the invariant that the fuel dominates
> the remaining length holds from `parse`'s initial `w.length` down.

- [ ] **Step 4: Build and test**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Preorder \
  GebTests.Mathlib.Data.Tree.Ranked.Preorder
```

Expected: PASS. `decodeBlock`'s `if h : … ∧ …` is a `dite` on a decidable
conjunction, whose two components are `Nat.decLt` and `Nat.decLe`; both
reduce, so `decide` closes the three assertions. Should a `decide` stall,
finding 1 of this plan applies: replace the `dite` by a `match decide (…)`
pair and recover the `i.isLt` component from `of_decide_eq_true`.

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Preorder.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean \
  -m "feat(tree): add the recursive descent for ranked spellings"
```

### Task 5: The retraction

**Files:**

- Modify: `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` — after `parse`
- Modify: `GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean`

**Interfaces:**

- Consumes: `Ranked.parseAux`, `Ranked.parseAux_succ`,
  `Ranked.decodeBlock`, `Ranked.decodeBits_code`, `Ranked.length_code`,
  `Ranked.length_spell`, `Ranked.induction`.
- Produces: `Ranked.decodeBlock_code_append`, `Ranked.parseAux_spell`,
  `Ranked.parse_spell`. Tasks 6 and 9 consume them.

- [ ] **Step 1: Write the failing test**

Append to `GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean`:

```lean
/-- The descent inverts the spelling on the binary term. -/
theorem parse_spell_sampleBinary :
    sampleAlphabet.parse (sampleAlphabet.spell sampleBinary) = some sampleBinary := by
  decide
```

- [ ] **Step 2: Run to verify it builds**

```bash
lake build GebTests.Mathlib.Data.Tree.Ranked.Preorder
```

Expected: PASS. This is a sanity anchor on the definitions of Tasks 3 and
4, not a red test; the lemma's own failure mode is a build error at Step 4.

- [ ] **Step 3: Write the lemmas**

Append to `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean`:

```lean
/-- A block followed by anything is read as its own symbol, leaving what
follows. -/
theorem decodeBlock_code_append (R : Ranked) (i : Fin R.card) (rest : List Bool) :
    R.decodeBlock (R.code i ++ rest) = some (i, rest) := by
  have htake : (R.code i ++ rest).take R.width = R.code i := by
    rw [← length_code R i, List.take_left]
  have hdrop : (R.code i ++ rest).drop R.width = rest := by
    rw [← length_code R i, List.drop_left]
  have hlen : R.width ≤ (R.code i ++ rest).length := by
    rw [List.length_append, length_code]
    omega
  rw [decodeBlock, htake, hdrop, dif_pos ⟨by rw [decodeBits_code]; exact i.isLt, hlen⟩]
  congr 1
  exact Fin.ext (decodeBits_code R i)

/-- The descent inverts the spelling on spelled input, given fuel at least
the term's node count, and returns the unconsumed remainder. -/
theorem parseAux_spell (R : Ranked) (t : R.Term) :
    ∀ (f : ℕ) (rest : List Bool), t.size ≤ f →
      R.parseAux f (R.spell t ++ rest) = some (t, rest) :=
  Ranked.induction
    (motive := fun t ↦ ∀ (f : ℕ) (rest : List Bool), t.size ≤ f →
      R.parseAux f (R.spell t ++ rest) = some (t, rest))
    (fun i ch ih f rest hf ↦ by
      cases f with
      | zero => rw [size_mk'] at hf; omega
      | succ f =>
        rw [parseAux_succ, spell_mk', List.append_assoc, parseStep,
          decodeBlock_code_append]
        -- each child's size is at most `f`, so the hypothesis applies to it
        have hchild : ∀ d, (ch d).size ≤ f := by
          intro d
          rw [size_mk'] at hf
          have hmem : (ch d).size ∈ List.ofFn fun e ↦ (ch e).size :=
            List.mem_ofFn.mpr ⟨d, rfl⟩
          have := List.le_sum_of_mem hmem
          omega
        rw [parseChildren_flatten R ih f rest hchild]) t
```

The node case delegates to an auxiliary lemma over the children, stated and
proved immediately above `parseAux_spell`:

```lean
/-- Reading `n` children off the concatenation of their spellings returns
them and the remainder. Driven by `Nat.rec` on the number of children, with
`Fin.cons` matching the way `parseChildren` assembles the family. -/
theorem parseChildren_flatten (R : Ranked) {n : ℕ} (ch : Fin n → R.Term)
    (ih : ∀ d f rest, (ch d).size ≤ f →
      R.parseAux f (R.spell (ch d) ++ rest) = some (ch d, rest))
    (f : ℕ) (rest : List Bool) (hf : ∀ d, (ch d).size ≤ f) :
    parseChildren (R.parseAux f) n ((List.ofFn fun d ↦ R.spell (ch d)).flatten ++ rest)
      = some (ch, rest) := by
  refine Nat.rec (motive := fun n ↦ ∀ (ch : Fin n → R.Term),
    (∀ d f' rest', (ch d).size ≤ f' →
      R.parseAux f' (R.spell (ch d) ++ rest') = some (ch d, rest')) →
    (∀ d, (ch d).size ≤ f) →
    parseChildren (R.parseAux f) n
      ((List.ofFn fun d ↦ R.spell (ch d)).flatten ++ rest) = some (ch, rest))
    ?base ?step n ch ih hf
  · intro ch _ _
    simp [parseChildren, List.ofFn_zero]
    exact funext fun d ↦ d.elim0
  · intro n ihn ch ihch hch
    rw [List.ofFn_succ, List.flatten_cons, List.append_assoc]
    simp only [parseChildren]
    rw [ihch 0 f _ (hch 0), ihn (Fin.tail ch) (fun d ↦ ihch d.succ)
      (fun d ↦ hch d.succ)]
    simp [Fin.cons_self_tail]
```

Then:

```lean
/-- The retraction law: the descent recovers every term the encoding
spells. -/
theorem parse_spell (R : Ranked) (t : R.Term) : R.parse (R.spell t) = some t := by
  have hf : t.size ≤ (R.spell t).length := by
    rw [length_spell]
    exact Nat.le_mul_of_pos_left _ R.width_pos
  have h := parseAux_spell R t (R.spell t).length [] hf
  rw [List.append_nil] at h
  rw [parse, h]
```

- [ ] **Step 4: Build**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Preorder
```

Expected: PASS. `parseChildren_flatten` is the step most likely to need
adjustment; its shape is forced by `parseChildren` assembling with
`Fin.cons`, so the closing rewrite is `Fin.cons_self_tail`. If
`List.le_sum_of_mem` is not the mathlib name, `lean_loogle` on
`?a ∈ ?l → ?a ≤ List.sum ?l` finds it; the fallback is
`List.single_le_sum` with the non-negativity of `ℕ`.

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Preorder.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean \
  -m "feat(tree): prove the descent inverts the ranked spelling"
```

### Task 6: The descent reads only spellings

**Files:**

- Modify: `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` — after
  `parse_spell`
- Modify: `Geb/Mathlib/Data/Tree/Ranked/Code.lean` — `testBit_decodeBits`
  beside `decodeBits_code`, and the module docstring's
  `## Main statements`
- Modify: `GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean`

**Interfaces:**

- Consumes: `Ranked.parseAux`, `Ranked.parseAux_succ`,
  `Ranked.decodeBlock`, `Ranked.parse_spell`.
- Produces: `Ranked.decodeBlock_eq_some`, `Ranked.parseChildren_eq_some`,
  `Ranked.parseAux_eq_some`, `Ranked.parse_eq_some_iff`,
  `Ranked.spell_injective`. Task 9 consumes `parse_eq_some_iff`; Task 10
  consumes `spell_injective`.

- [ ] **Step 1: Write the failing test**

Append to `GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean`:

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

- [ ] **Step 3: Write the lemmas**

The model is `BinTree.parseAux_eq_some` and the two lemmas after it in
`Geb/Mathlib/Data/Tree/Preorder.lean` lines 210 to 265; the difference is
that the two nested child matches become one `parseChildren` induction.

```lean
/-- Whatever a block read returns, it reads that symbol's block. -/
theorem decodeBlock_eq_some (R : Ranked) {w rest : List Bool} {i : Fin R.card}
    (h : R.decodeBlock w = some (i, rest)) : R.code i ++ rest = w := by
  rw [decodeBlock] at h
  split at h
  · rename_i hcond
    have hi : (decodeBits (w.take R.width)) = i.val := by
      have := (Option.some.inj h)
      exact congrArg (fun p ↦ (Prod.fst p).val) this.symm ▸ rfl
    have hrest : w.drop R.width = rest := congrArg Prod.snd (Option.some.inj h)
    have hcode : R.code i = w.take R.width := by
      -- both are the `width`-bit block of the same value, so they agree pointwise
      refine List.ext_getElem (by rw [length_code, List.length_take]; omega) ?_
      intro n h₁ h₂
      -- the `n`th bit of the block is `testBit` of the decoded value
      exact (getElem_code_eq R i n h₁).trans (getElem_take_eq_testBit R w n h₂ hi).symm
    rw [hcode, hrest, List.take_append_drop]
  · contradiction

/-- Whatever `parseChildren` returns, it reads the concatenation of the
children's spellings. -/
theorem parseChildren_eq_some (R : Ranked) (f : ℕ)
    (ih : ∀ w t rest, R.parseAux f w = some (t, rest) → R.spell t ++ rest = w) :
    ∀ (n : ℕ) (w : List Bool) (g : Fin n → R.Term) (rest : List Bool),
      parseChildren (R.parseAux f) n w = some (g, rest) →
        (List.ofFn fun d ↦ R.spell (g d)).flatten ++ rest = w :=
  Nat.rec
    (fun w g rest h ↦ by
      simp only [parseChildren] at h
      have := Option.some.inj h
      rw [List.ofFn_zero, List.flatten_nil, List.nil_append,
        (congrArg Prod.snd this : w = rest)])
    (fun n ihn w g rest h ↦ by
      simp only [parseChildren] at h
      split at h
      · contradiction
      · rename_i t w₁ h₁
        split at h
        · contradiction
        · rename_i g' w₂ h₂
          have heq := Option.some.inj h
          have hg : Fin.cons t g' = g := congrArg Prod.fst heq
          have hrest : w₂ = rest := congrArg Prod.snd heq
          subst hg; subst hrest
          rw [List.ofFn_succ, List.flatten_cons, List.append_assoc,
            ihn w₁ g' rest h₂, ih w t w₁ h₁]
          simp)

/-- Whatever the descent reads, it reads a spelling: the term returned,
spelled and followed by the remainder, is the input. -/
theorem parseAux_eq_some (R : Ranked) : ∀ (f : ℕ) (w : List Bool) (t : R.Term)
    (rest : List Bool), R.parseAux f w = some (t, rest) → R.spell t ++ rest = w :=
  Nat.rec
    (fun _ _ _ h ↦ nomatch h)
    (fun f ih w t rest h ↦ by
      rw [parseAux_succ, parseStep] at h
      split at h
      · contradiction
      · rename_i i rest₁ hb
        split at h
        · contradiction
        · rename_i g rest₂ hc
          have heq := Option.some.inj h
          have ht : R.mk' i g = t := congrArg Prod.fst heq
          have hrest : rest₂ = rest := congrArg Prod.snd heq
          subst ht; subst hrest
          rw [spell_mk', List.append_assoc,
            parseChildren_eq_some R f ih (R.ar i) rest₁ g rest hc,
            decodeBlock_eq_some R hb])

/-- The descent succeeds exactly on the spellings, returning the term
spelled. -/
theorem parse_eq_some_iff (R : Ranked) {w : List Bool} {t : R.Term} :
    R.parse w = some t ↔ R.spell t = w := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ parse_spell R t⟩
  rw [parse] at h
  split at h
  · rename_i t' hp
    rw [← Option.some.inj h]
    simpa using parseAux_eq_some R w.length w t' [] hp
  · contradiction

/-- Distinct terms have distinct spellings. -/
theorem spell_injective (R : Ranked) : Function.Injective R.spell := by
  intro a b h
  have ha := parse_spell R a
  rw [h, parse_spell R b] at ha
  exact (Option.some.inj ha).symm
```

`decodeBlock_eq_some` names two helpers; state them immediately above it,
both proved from `code` and `decodeBits` by `Nat.testBit`:

```lean
/-- The `n`th bit of a block is the `n`th bit of the symbol's index. -/
theorem getElem_code_eq (R : Ranked) (i : Fin R.card) (n : ℕ)
    (h : n < (R.code i).length) : (R.code i)[n] = i.val.testBit n := by
  simp [code] at h ⊢

/-- The `n`th bit of a word's leading block is the `n`th bit of that
block's value. -/
theorem getElem_take_eq_testBit (R : Ranked) (w : List Bool) (n : ℕ)
    (h : n < (w.take R.width).length) {v : ℕ}
    (hv : decodeBits (w.take R.width) = v) : (w.take R.width)[n] = v.testBit n := by
  subst hv
  -- `decodeBits` is little-endian, so its `n`th bit is the list's `n`th entry
  exact (testBit_decodeBits (w.take R.width) n h).symm
```

and, in `Code.lean` beside `decodeBits_code`, the lemma both rest on:

```lean
/-- The `n`th bit of a block's value is the block's `n`th entry. -/
theorem testBit_decodeBits : ∀ (bs : List Bool) (n : ℕ) (h : n < bs.length),
    (decodeBits bs).testBit n = bs[n] :=
  List.rec (fun n h ↦ absurd h (by simp))
    (fun b bs ih n h ↦ by
      cases n with
      | zero => simp [decodeBits, Nat.testBit_zero]; cases b <;> omega
      | succ n =>
        rw [decodeBits]
        rw [Nat.testBit_succ]
        have : (2 * decodeBits bs + (if b then 1 else 0)) / 2 = decodeBits bs := by
          cases b <;> omega
        rw [this, ih n (by simpa using h)]
        simp)
```

- [ ] **Step 4: Build**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Preorder
```

Expected: PASS. `Nat.testBit_succ`'s exact form (whether it is stated as
`testBit (n+1)` in terms of `n / 2` or `n >>> 1`) decides the `succ` case's
middle rewrite; check it with `lean_hover_info` before adjusting.

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Preorder.lean \
  Geb/Mathlib/Data/Tree/Ranked/Code.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean \
  -m "feat(tree): prove the ranked descent reads only spellings"
```

### Task 7: The scanning validity predicate

**Files:**

- Modify: `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` — after
  `spell_injective`
- Modify: `GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean`

**Interfaces:**

- Consumes: `Ranked.arOf`, `decodeBits`.
- Produces: `Scan`, `Ranked.scanStep`, `Ranked.scanFrom`,
  `Ranked.scanFinal`, `Ranked.validBool`, `Ranked.Valid`, its
  `DecidablePred` instance, and `Ranked.scanFrom_append`. Tasks 8, 9, 10
  consume them; branch B2 consumes `scanStep` and `Valid`.

- [ ] **Step 1: Write the failing test**

Append to `GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean`:

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

Expected: FAIL, `unknown identifier 'Ranked.Valid'`.

- [ ] **Step 3: Write the scan**

Append to `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean`. Finding 1 of this
plan governs every branch here: match on `Bool`, never on a decidable
proposition.

```lean
/-- The state of the validity scan: the bits of an incomplete block, the
count of pending subterms, and whether the scan has failed. -/
public structure Scan where
  /-- The bits of an incomplete block, most recently read first. -/
  buf : List Bool
  /-- The count of pending subterms. -/
  depth : ℕ
  /-- Whether the scan has not yet failed. -/
  live : Bool
deriving DecidableEq, Repr

namespace Ranked

public section

/-- One step of the scan, reading one bit. A failed state absorbs. An
incomplete block takes the bit; a complete one is decoded, and its symbol
pops its arity and pushes one, failing when the block spells no symbol or
the pending count is short of the arity. -/
@[expose] def scanStep (R : Ranked) (b : Bool) (s : Scan) : Scan :=
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
@[expose] def scanFrom (R : Ranked) (w : List Bool) (s : Scan) : Scan :=
  w.foldr R.scanStep s

/-- The scan of a word from the initial state. -/
@[expose] def scanFinal (R : Ranked) (w : List Bool) : Scan :=
  R.scanFrom w ⟨[], 0, true⟩

/-- Whether a word spells a term: the scan ends live, with no incomplete
block and exactly one pending subterm. -/
@[expose] def validBool (R : Ranked) (w : List Bool) : Bool :=
  (R.scanFinal w).live && (R.scanFinal w).buf.isEmpty && (R.scanFinal w).depth == 1

/-- A word spells a term. -/
@[expose] def Valid (R : Ranked) (w : List Bool) : Prop := R.validBool w = true

/-- `Valid` is a `Bool` equation, so membership is decidable. Instance
search does not unfold the `def`, so the instance is supplied. -/
instance (R : Ranked) : DecidablePred R.Valid :=
  fun _ ↦ inferInstanceAs (Decidable (_ = true))

@[simp] theorem scanFrom_nil (R : Ranked) (s : Scan) : R.scanFrom [] s = s := rfl

@[simp] theorem scanFrom_cons (R : Ranked) (b : Bool) (w : List Bool) (s : Scan) :
    R.scanFrom (b :: w) s = R.scanStep b (R.scanFrom w s) := rfl

/-- The scan of a concatenation reads the later part first. -/
theorem scanFrom_append (R : Ranked) (u v : List Bool) (s : Scan) :
    R.scanFrom (u ++ v) s = R.scanFrom u (R.scanFrom v s) :=
  List.rec rfl (fun b w ih ↦ by rw [List.cons_append, scanFrom_cons, ih, scanFrom_cons]) u
```

Add `Scan`, `scanStep`, `scanFrom`, `scanFinal`, `validBool` and `Valid` to
the module docstring's `## Main definitions`, and to
`## Implementation notes`:

> `scanStep` matches on `Bool` values rather than testing decidable
> propositions, and `Valid` is a `Bool` equation rather than an equation of
> `Scan`. Both are forced by kernel reduction: an `if` at a decidable
> proposition, or a derived `DecidableEq` at a symbolic fold, leaves
> `decide` stuck on the `Decidable` instance rather than reducing it.

- [ ] **Step 4: Build and test**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Preorder \
  GebTests.Mathlib.Data.Tree.Ranked.Preorder
```

Expected: PASS, all five assertions closing by `decide`.

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Preorder.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean \
  -m "feat(tree): add the scanning validity predicate for ranked words"
```

### Task 8: Every spelling is valid

**Files:**

- Modify: `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` — after
  `scanFrom_append`
- Modify: `GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean`

**Interfaces:**

- Consumes: `Ranked.scanFrom`, `Ranked.scanFrom_append`,
  `Ranked.arOf_decodeBits_code`, `Ranked.length_code`,
  `Ranked.induction`, `Ranked.spell_mk'`.
- Produces: `Ranked.scanFrom_code`, `Ranked.scanFrom_flatten`,
  `Ranked.scanFrom_spell`, `Ranked.valid_spell`. Task 9 consumes
  `scanFrom_spell`; Task 10 consumes `valid_spell`.

- [ ] **Step 1: Write the failing test**

Append to `GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean`:

```lean
/-- Every spelling over the worked alphabet is valid, on the two sample
terms. -/
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
/-- Reading a symbol's block from a state with no incomplete block and at
least the symbol's arity pending pops that arity and pushes one. Driven by
`List.rec` over the block, whose length is `width` by `length_code`. -/
theorem scanFrom_code (R : Ranked) (i : Fin R.card) (d : ℕ) (h : R.ar i ≤ d) :
    R.scanFrom (R.code i) ⟨[], d, true⟩ = ⟨[], d - R.ar i + 1, true⟩ := by
  -- reading the block's bits accumulates them in order, completing at `width`
  have hacc : ∀ (pre suf : List Bool), pre ++ suf = R.code i → suf.length < R.width →
      R.scanFrom suf ⟨[], d, true⟩ = ⟨suf, d, true⟩ := by
    intro pre suf hsplit hlt
    refine List.rec (motive := fun u ↦ u.length < R.width →
      R.scanFrom u ⟨[], d, true⟩ = ⟨u, d, true⟩) (fun _ ↦ rfl) (fun b v ih hv ↦ ?_) suf hlt
    rw [scanFrom_cons, ih (by simpa using Nat.lt_of_succ_lt hv), scanStep]
    simp only []
    rw [decide_eq_false (by simpa using Nat.ne_of_lt hv)]
  have hfull := hacc [] (R.code i) (List.nil_append _)
  -- the last bit read completes the block
  match hcode : R.code i, hlen : (R.code i).length with
  | [], _ => exact absurd (length_code R i ▸ hcode ▸ rfl) (by omega)
  | b :: v, _ =>
    rw [hcode, scanFrom_cons, hacc [b] v (by rw [← hcode]) (by
      have := length_code R i
      rw [hcode] at this
      simp at this
      omega), scanStep]
    simp only []
    rw [decide_eq_true (by rw [← hcode] at *; simpa using length_code R i),
      ← hcode, arOf_decodeBits_code, decide_eq_true h]

/-- The scan of a list of spellings, each raising the pending count by one,
raises it by their number. -/
theorem scanFrom_flatten (R : Ranked) (ws : List (List Bool))
    (hw : ∀ u ∈ ws, ∀ d, R.scanFrom u ⟨[], d, true⟩ = ⟨[], d + 1, true⟩) (d : ℕ) :
    R.scanFrom ws.flatten ⟨[], d, true⟩ = ⟨[], d + ws.length, true⟩ :=
  List.rec (motive := fun l ↦ (∀ u ∈ l, ∀ d, R.scanFrom u ⟨[], d, true⟩ =
      ⟨[], d + 1, true⟩) → R.scanFrom l.flatten ⟨[], d, true⟩ = ⟨[], d + l.length, true⟩)
    (fun _ ↦ by simp)
    (fun u l ih hl ↦ by
      rw [List.flatten_cons, scanFrom_append,
        ih (fun x hx ↦ hl x (List.mem_cons_of_mem u hx)),
        hl u List.mem_cons_self (d + l.length), List.length_cons]
      congr 1
      omega)
    ws hw

/-- A spelling raises the pending count by one, whatever the count before
it. -/
theorem scanFrom_spell (R : Ranked) (t : R.Term) (d : ℕ) :
    R.scanFrom (R.spell t) ⟨[], d, true⟩ = ⟨[], d + 1, true⟩ :=
  Ranked.induction
    (motive := fun t ↦ ∀ d, R.scanFrom (R.spell t) ⟨[], d, true⟩ = ⟨[], d + 1, true⟩)
    (fun i ch ih d ↦ by
      rw [spell_mk', scanFrom_append,
        scanFrom_flatten R _ (fun u hu e ↦ by
          obtain ⟨n, hn⟩ := List.mem_ofFn.mp hu
          exact hn ▸ ih n e) d,
        List.length_ofFn, scanFrom_code R i (d + R.ar i) (Nat.le_add_left _ _)]
      congr 1
      omega)
    t d

/-- Every spelling is valid. -/
theorem valid_spell (R : Ranked) (t : R.Term) : R.Valid (R.spell t) := by
  rw [Valid, validBool, scanFinal, scanFrom_spell R t 0]
  rfl
```

- [ ] **Step 4: Build**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Preorder
```

Expected: PASS. `scanFrom_code` is the heaviest step; its content is that
the first `width - 1` bits read only accumulate and the last completes the
block. If the `match hcode` destructuring fights the rewrite, restate
`hacc` as a lemma over an arbitrary word of length below `width` and apply
it to `(R.code i).tail`, taking the head with `List.head_cons_tail` and
`length_code`.

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Preorder.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean \
  -m "feat(tree): prove every ranked spelling is valid"
```

### Task 9: Every valid word is a spelling

**Files:**

- Modify: `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` — after
  `valid_spell`
- Modify: `GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean`

**Interfaces:**

- Consumes: `Ranked.scanFrom_spell`, `Ranked.scanFrom_append`,
  `Ranked.valid_spell`, `Ranked.parse_eq_some_iff`, `Ranked.parse_spell`.
- Produces: `Ranked.exists_spell_append`, `Ranked.eq_nil_of_valid_zero`,
  `Ranked.exists_spell_of_valid`, `Ranked.valid_iff_exists_spell`,
  `Ranked.valid_iff_isSome_parse`. Task 10 and branch B2 consume the last
  two.

The model is `BinTree.exists_print_append_of_ok_of_one_le_depth` and the
three lemmas after it, `Geb/Mathlib/Data/Tree/Preorder.lean` lines 292 to
364. The transposition replaces "a leaf bit or a node bit" by "a complete
block", and the two recursive uses by `Nat.rec` over the arity.

- [ ] **Step 1: Write the failing test**

Append to `GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean`:

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

Expected: PASS. If `decide` exceeds its heartbeat budget at 127 words,
lower the bound from 7 to 5 rather than reaching for `native_decide`, which
adds a compiler-trust axiom the linter rejects.

- [ ] **Step 3: Write the lemmas**

```lean
/-- A word whose scan ends live with no incomplete block and a positive
pending count has a complete spelling as a suffix in processing order,
which is a prefix in list order. Bounded by an explicit `ℕ` and driven by
`Nat.rec`, as its `BinTree` model is: the arity's worth of recursive uses
sit at one bound. -/
theorem exists_spell_append (R : Ranked) :
    ∀ (n : ℕ) (w : List Bool), w.length ≤ n →
      (R.scanFinal w).live = true → (R.scanFinal w).buf = [] →
      1 ≤ (R.scanFinal w).depth →
        ∃ t rest, R.spell t ++ rest = w ∧
          (R.scanFinal rest).live = true ∧ (R.scanFinal rest).buf = [] ∧
          (R.scanFinal rest).depth + 1 = (R.scanFinal w).depth := _

/-- A word whose scan ends live with no incomplete block and nothing
pending is empty. -/
theorem eq_nil_of_valid_zero (R : Ranked) (w : List Bool)
    (hlive : (R.scanFinal w).live = true) (hbuf : (R.scanFinal w).buf = [])
    (hd : (R.scanFinal w).depth = 0) : w = [] := _

/-- Every valid word is a spelling. -/
theorem exists_spell_of_valid (R : Ranked) {w : List Bool} (h : R.Valid w) :
    ∃ t, R.spell t = w := by
  rw [Valid, validBool] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
  obtain ⟨⟨hlive, hbuf⟩, hd⟩ := h
  obtain ⟨t, rest, he, hlive', hbuf', hd'⟩ :=
    exists_spell_append R w.length w le_rfl hlive hbuf (by omega)
  have hz : (R.scanFinal rest).depth = 0 := by omega
  have hnil : rest = [] := eq_nil_of_valid_zero R rest hlive' hbuf' hz
  subst hnil
  exact ⟨t, by simpa using he⟩

/-- The encoding's image is exactly the valid words. -/
theorem valid_iff_exists_spell (R : Ranked) (w : List Bool) :
    R.Valid w ↔ ∃ t, R.spell t = w :=
  ⟨exists_spell_of_valid R, fun ⟨t, ht⟩ ↦ ht ▸ valid_spell R t⟩

/-- The descent decides validity. -/
theorem valid_iff_isSome_parse (R : Ranked) (w : List Bool) :
    R.Valid w ↔ (R.parse w).isSome := by
  rw [valid_iff_exists_spell]
  refine ⟨fun ⟨t, ht⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [← ht, parse_spell]; rfl
  · obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
    exact ⟨t, parse_eq_some_iff.mp ht⟩
```

The two underscores are the task's work. `exists_spell_append` proceeds by
`Nat.rec` on the bound; in the successor case, the word's last `width` bits
in processing order form the head symbol's block, which
`scanFrom_append` splits off, and the symbol's arity many applications of
the hypothesis, threaded by a `Nat.rec` over the arity, produce the
children. `eq_nil_of_valid_zero` is a `match` on `w`: a non-empty word ends
its scan either mid-block, contradicting `hbuf`, or having pushed a symbol,
contradicting `hd`.

- [ ] **Step 4: Build**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Preorder
```

Expected: PASS, with no underscore remaining. Underscores, not `sorry`, mark
the holes while the proofs are being written; the build reports each as an
unsolved goal with its type, which is the intended development loop.

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Preorder.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean \
  -m "feat(tree): characterise the ranked encoding's image"
```

### Task 10: The binary alphabet

**Files:**

- Create: `Geb/Mathlib/Data/Tree/Ranked/Binary.lean`
- Create: `GebTests/Mathlib/Data/Tree/Ranked/Binary.lean`

**Interfaces:**

- Consumes: everything above, plus `BinTree`, `BinTree.print`,
  `BinTree.Valid`, `BinTree.valid_iff_exists_print`,
  `BinTree.print_injective`.
- Produces: `binRanked`, `binLeaf`, `binNode`, `binRanked.termEquiv`,
  `binRanked.spell_termEquiv`, `binRanked.valid_iff`. Branch B2 consumes
  `binRanked.valid_iff`.

- [ ] **Step 1: Write the failing test**

Create `GebTests/Mathlib/Data/Tree/Ranked/Binary.lean` with the standard
header and:

```lean
/-- The width-one alphabet's validity agrees with the existing predicate on
every word of length at most eight. -/
def binValidAgrees : Bool :=
  ((List.range 9).flatMap fun n ↦
    (List.range (2 ^ n)).map fun m ↦ (List.range n).map fun j ↦ m.testBit j).all
    fun w ↦ binRanked.validBool w == decide (BinTree.Valid w)

/-- The agreement holds. -/
theorem binValidAgrees_eq : binValidAgrees = true := by decide

/-- The leaf's spelling is the existing one. -/
theorem spell_binLeaf : binRanked.spell binLeaf = BinTree.print BinTree.leaf := by decide

/-- The two-leaf node's spelling is the existing one. -/
theorem spell_binNode :
    binRanked.spell (binNode binLeaf binLeaf) =
      BinTree.print (BinTree.node BinTree.leaf BinTree.leaf) := by decide
```

- [ ] **Step 2: Run to verify it fails**

```bash
lake build GebTests.Mathlib.Data.Tree.Ranked.Binary
```

Expected: FAIL, `unknown module Geb.Mathlib.Data.Tree.Ranked.Binary`.

- [ ] **Step 3: Write the module**

Create `Geb/Mathlib/Data/Tree/Ranked/Binary.lean` with the standard header,
`module`, and:

```lean
public import Geb.Mathlib.Data.Tree.Ranked.Preorder
public import Geb.Mathlib.Data.Tree.Preorder
public import Mathlib.Data.Fin.VecNotation
```

Module docstring `# The binary alphabet`, stating that the unlabelled
binary trees are the terms of the alphabet of one symbol of arity zero and
one of arity two, that `spell` at that alphabet is `BinTree.print`, and
that `Valid` at that alphabet is `BinTree.Valid`. Tags:
`ranked alphabet, binary tree, preorder, encoding`.

```lean
/-- One symbol of arity zero and one of arity two, each spelled by one bit:
the alphabet whose terms are the unlabelled binary trees. -/
@[expose] def binRanked : Ranked := ⟨2, 1, Nat.one_pos, by decide, ![0, 2]⟩

/-- The leaf, at the binary alphabet. -/
@[expose] def binLeaf : binRanked.Term :=
  binRanked.mk' ⟨0, by decide⟩ (fun i ↦ absurd i.isLt (by decide))

/-- The node, at the binary alphabet. -/
@[expose] def binNode (l r : binRanked.Term) : binRanked.Term :=
  binRanked.mk' ⟨1, by decide⟩ (fun d ↦ Fin.cases l (fun _ ↦ r) (Fin.cast (by decide) d))

/-- The terms of the binary alphabet are the unlabelled binary trees. The
map is by `Ranked.induction` in one direction and `BinTree.induction` in
the other; both round trips are by the same recursors. -/
@[expose] def binRanked.termEquiv : binRanked.Term ≃ BinTree where
  toFun := WType.elim BinTree fun x ↦
    if h : x.1.val = 0 then BinTree.leaf
    else BinTree.node (x.2 ⟨0, by omega⟩) (x.2 ⟨1, by omega⟩)
  invFun := WType.elim binRanked.Term fun x ↦
    match x with
    | ⟨.leaf, _⟩ => binLeaf
    | ⟨.node, ch⟩ => binNode (ch (0 : Fin 2)) (ch (1 : Fin 2))
  left_inv := _
  right_inv := _

/-- The spelling at the binary alphabet is the existing encoding. -/
theorem binRanked.spell_termEquiv (t : binRanked.Term) :
    binRanked.spell t = BinTree.print (binRanked.termEquiv t) := _

/-- Validity at the binary alphabet is the existing predicate. -/
theorem binRanked.valid_iff (w : List Bool) : binRanked.Valid w ↔ BinTree.Valid w := by
  rw [Ranked.valid_iff_exists_spell, BinTree.valid_iff_exists_print]
  refine ⟨fun ⟨t, ht⟩ ↦ ⟨binRanked.termEquiv t, ?_⟩, fun ⟨u, hu⟩ ↦
    ⟨binRanked.termEquiv.symm u, ?_⟩⟩
  · rw [← ht, spell_termEquiv]
  · rw [spell_termEquiv, Equiv.apply_symm_apply, hu]
```

The three underscores are the task's work: the two round trips of
`termEquiv`, each by the corresponding recursor, and `spell_termEquiv` by
`Ranked.induction` with a case analysis on the head symbol's index.

- [ ] **Step 4: Build and test**

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Binary \
  GebTests.Mathlib.Data.Tree.Ranked.Binary
```

Expected: PASS. `binValidAgrees` at bound 8 covers 511 words; the same
check at bound 10 was run before this plan was written and returned `true`,
so a failure here is a defect in the transcription, not in the design.

Finding 5 of this plan bears on `binNode`: the child family's type is
`Fin (binRanked.ar ⟨1, _⟩)`, which is not syntactically `Fin 2`, hence the
`Fin.cast`. If `by decide` does not discharge `binRanked.ar ⟨1, _⟩ = 2`,
the cause is `binRanked` not reducing; add `@[simp]` unfolding lemmas
`binRanked_card`, `binRanked_width` and `binRanked_ar` and use them.

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Data/Tree/Ranked/Binary.lean \
  GebTests/Mathlib/Data/Tree/Ranked/Binary.lean \
  -m "feat(tree): exhibit the binary trees as a ranked alphabet's terms"
```

### Task 11: Indices, documentation and the full check

**Files:**

- Create: `Geb/Mathlib/Data/Tree/Ranked.lean`
- Create: `GebTests/Mathlib/Data/Tree/Ranked.lean`
- Modify: `Geb/Mathlib/Data/Tree.lean`
- Modify: `GebTests/Mathlib/Data/Tree.lean`
- Modify: `docs/index.md`

**Interfaces:**

- Consumes: every module above.
- Produces: no declaration; the package's index reaches the new modules.

- [ ] **Step 1: Write the indices**

Create `Geb/Mathlib/Data/Tree/Ranked.lean` with the standard header,
`module`, the four `public import`s in dependency order, and the docstring
`/-! # Ranked — index -/`, matching `Geb/Mathlib/Data/Tree.lean`.

Create `GebTests/Mathlib/Data/Tree/Ranked.lean` with the same shape over
the four test modules, using plain `import`.

Add to `Geb/Mathlib/Data/Tree.lean`:

```lean
public import Geb.Mathlib.Data.Tree.Ranked
```

Add the parallel plain `import` to `GebTests/Mathlib/Data/Tree.lean`.

- [ ] **Step 2: Document the modules**

Add one entry per new module to `docs/index.md`, beside the existing
`Data/Tree/Binary.lean` and `Data/Tree/Preorder.lean` entries, in
topological order, each naming what the module defines and states. Per
CONTRIBUTING § Each phase produces an artifact, this is not optional.

- [ ] **Step 3: Build everything**

```bash
lake build
```

Expected: PASS with no warnings.

- [ ] **Step 4: Run the full check**

```bash
lake test && lake lint && lake shake && bash scripts/lint-imports.sh
```

Expected: all PASS. `lake lint` covers `detectNonstandardAxiom`: every new
declaration must depend only on `propext` and `Quot.sound`. `lake shake`
may report an import used only inside an `example`; the sanctioned repair
is to name the `def` the assertion is built from, not `-- shake: keep`.

- [ ] **Step 5: Verify the axiom set explicitly**

```bash
lake env lean --run scripts/print-axioms.lean 2>/dev/null || true
```

If that script does not exist, check the four modules by hand: open each in
the editor and read `#print axioms` for `Ranked.valid_iff_exists_spell`,
`Ranked.spell_injective` and `binRanked.valid_iff` through
`lean_verify`, whose fully qualified names are those three. Expected:
`[propext, Quot.sound]` for each.

- [ ] **Step 6: Run the markdown checks**

```bash
doctoc --update-only docs/index.md && markdownlint-cli2 '**/*.md' &&
  bash scripts/check-md-links.sh
```

Expected: all PASS.

- [ ] **Step 7: Commit**

```bash
jj commit -m "doc(tree): index and document the ranked encoding modules"
```

- [ ] **Step 8: Pre-push checklist**

```bash
bash scripts/pre-push.sh
```

Expected: PASS. Do not push. The branch waits on the user's line-by-line
review, per CONTRIBUTING § Working and AGENTS.md § No `jj git push` without
user line-by-line review.
