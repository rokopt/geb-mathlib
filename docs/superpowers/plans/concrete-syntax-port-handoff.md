# Handoff: port the concrete-syntax prototype to W-types

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Lifespan](#lifespan)
- [Where the work stands](#where-the-work-stands)
- [Decisions already taken](#decisions-already-taken)
- [Facts established by experiment](#facts-established-by-experiment)
- [The validated encoding](#the-validated-encoding)
- [Findings to discharge](#findings-to-discharge)
  - [Round 1 on `Geb/Internal/ConcreteSyntax.lean`](#round-1-on-gebinternalconcretesyntaxlean)
  - [Round 1 on `docs/concrete-syntaxes.md`](#round-1-on-docsconcrete-syntaxesmd)
- [Suggested order](#suggested-order)
- [Environment notes](#environment-notes)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Lifespan

This file is a transient process artifact in the sense of
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape and
[docs/process.md](../../process.md) § Specs and plans are transient. It
records how the current state was reached and what to do next, not what
the code is. It is committed so that a long-running prototype branch can
be resumed across sessions, and it is deleted in the final commits of the
branch, alongside any spec and plan documents, before the branch is
pushed.

The same applies to any successor handoff written on this branch.

## Where the work stands

Four commits on `ws2@`, none pushed:

| Change | Subject |
| --- | --- |
| `skolzrlx` | `feat(internal): add concrete-syntax prototype for the Geb AST` |
| `zvxpwqmk` | `doc: add the concrete-syntax survey as received` |
| `wtzmxvsn` | `doc: revise the concrete-syntax survey against local results` |
| this one | the handoff |

`lake build` and `scripts/pre-push.sh` both pass on the stack as it
stands. That is not a statement that the work is correct: the first
commit's module is known to violate a binding rule, recorded as R1-B1
below, and the third commit's document contains two false statements,
recorded as D1-B1 and D1-B2.

`Geb/Internal/ConcreteSyntax.lean` implements the format-independent core
and one concrete syntax, the canonical S-expression form of RFC 9804
restricted to the bare tree. `docs/concrete-syntaxes.md` is the design
document; its sections Status, Local verification and Roadmap were
written here and are in scope for revision, and the rest is inherited
survey text whose prose-conformance pass is deferred in `TODO.md`.

## Decisions already taken

Both were put to the user and answered; do not reopen them.

1. **Full port to W-types, no exceptions.** Rebuild `Ast`, `Tree` and
   `Rose` on W-types and drive every fold through a recursor. Also remove
   the remaining self-recursive definitions — `digitsLE` and `uvarintAux`
   — by reformulating them as recursion on an explicit bound. The
   intended end state is zero violations of
   [docs/rules/lean-coding.md](../../rules/lean-coding.md) § Recursion
   and induction through recursors anywhere in the module.
2. **Delete the unused hashing layer**, restoring it at roadmap stage 3
   when there is a hash function to run it. Remove `uvarintAux`,
   `uvarint`, `HashFn`, `sha3256`, `Multihash`, `Multihash.encode`,
   `HashFn.mh`, the four tags, `tags_equal_length`, `Ast.subtreeMH`,
   `Ast.coreMH`, `Ast.validPath` and `Ast.subtreeAt`. The specification
   they implement stays in `docs/concrete-syntaxes.md`, so nothing is
   lost but code with no consumer.

Decision 2 shrinks decision 1: the deleted declarations do not need
porting.

## Facts established by experiment

Each was checked by compiling. Do not re-derive them, and do not trust a
reviewer who asserts the contrary without an experiment.

1. `decide` does not discharge `tagLeaf.size = 16` in a file carrying the
   `module` keyword: core's `String.toUTF8` is not exposed, so reduction
   gets stuck during elaboration. `simp [tagLeaf, ...]` first reduces the
   goal to one `decide` closes. The recipe works only inside the defining
   module; from a downstream module it fails with `Expected a definition
   with an exposed body`. (Moot once decision 2 deletes the tags, but the
   underlying `module`-system behaviour will recur.)
2. mathlib's `Nat.digits` depends on `Classical.choice`, which
   [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Constructive-only
   forbids. It **does** have a native implementation and **does** run;
   the earlier claim that it does not was a misdiagnosed
   `public import` versus `public meta import` error, which is the
   pitfall [docs/rules/lean-coding.md](../../rules/lean-coding.md)
   § Lean 4 module system already documents. The choice dependency alone
   justifies the hand-rolled decimal encoding.
3. `omega` reasons about `Nat.max` choice-free; `simp` on a hypothesis
   containing `Nat.max` does not, reaching choice-dependent order
   lemmas. So a `max`-based fuel measure is available provided the
   hypothesis is bounded by `omega`, per
   [docs/rules/lean-coding.md](../../rules/lean-coding.md)
   § Constructive-only. Witnesses:

   ```text
   (h : 1 + max a b ≤ f + 1) : a ≤ f  := by omega    -- [propext, Quot.sound]
   (h : 1 + max a b ≤ 0)     : False  := by simp at h -- + Classical.choice
   (h : 1 + max a b ≤ 0)     : False  := by omega     -- [propext, Quot.sound]
   ```

4. `FinEnum Bool` does not exist in mathlib; `FinEnum Empty`,
   `FinEnum PEmpty`, `FinEnum (Fin 0)` and `FinEnum (Fin 2)` all do. The
   fork arity is therefore `Fin 2`, not `Bool`.

## The validated encoding

This compiles as written, against
[Geb/Mathlib/Data/W/Basic.lean](../../../Geb/Mathlib/Data/W/Basic.lean).
Only the numeral ascriptions are delicate: `Arity Shape.fork` is not
syntactically `Fin 2`, so bare `0` and `1` fail to elaborate and every
index needs `(0 : Fin 2)`.

```lean
public inductive Shape (k : Nat) where
  | leaf : Fin k → Shape k
  | fork : Shape k
  deriving DecidableEq

@[expose] public def Arity {k : Nat} : Shape k → Type
  | .leaf _ => Empty
  | .fork => Fin 2

public instance {k : Nat} (s : Shape k) : FinEnum (Arity s) := by
  cases s
  · exact (inferInstance : FinEnum Empty)
  · exact (inferInstance : FinEnum (Fin 2))

public abbrev Ast (k : Nat) : Type := WType (Arity (k := k))

@[expose] public def Ast.leaf {k : Nat} (i : Fin k) : Ast k :=
  WType.mk (.leaf i) Empty.elim

@[expose] public def Ast.fork {k : Nat} (l r : Ast k) : Ast k :=
  WType.mk .fork (fun b : Fin 2 => Fin.cases l (fun _ => r) b)

@[expose] public def Ast.size {k : Nat} : Ast k → Nat :=
  WType.elim Nat fun x =>
    match x with
    | ⟨.leaf _, _⟩ => 1
    | ⟨.fork, ch⟩ => 1 + ch (0 : Fin 2) + ch (1 : Fin 2)

public theorem Ast.ind {k : Nat} {motive : Ast k → Prop}
    (leaf : ∀ i, motive (Ast.leaf i))
    (fork : ∀ l r, motive l → motive r → motive (Ast.fork l r)) :
    ∀ t, motive t :=
  WType.rec (motive := motive) fun s f ih =>
    match s, f, ih with
    | .leaf i, f, _ => by
        have : f = Empty.elim := funext (fun e => e.elim)
        subst this; exact leaf i
    | .fork, f, ih => by
        have : (fun b : Fin 2 => Fin.cases (f (0 : Fin 2))
            (fun _ => f (1 : Fin 2)) b) = f :=
          funext fun b => match b with
            | ⟨0, _⟩ => rfl
            | ⟨1, _⟩ => rfl
        exact this ▸ fork (f (0 : Fin 2)) (f (1 : Fin 2))
          (ih (0 : Fin 2)) (ih (1 : Fin 2))
```

Verified against this: `DecidableEq (Ast k)` resolves through
`WType.instDecidableEq`; `Ast.size` reduces by `rfl` on closed terms, so
`(Ast.fork (Ast.leaf (0 : Fin 3)) (Ast.leaf 1)).size = 3 := rfl` closes.
`Ast.ind` must be a `theorem`, not a `def`, or `linter.defProp` fires.

`WType.para` is available and is the right tool wherever a step needs a
child as a subtree rather than only as its folded value.

Recursion over `Nat` and `List` — the parser's fuel, the digit
reformulation — is unaffected by the rule's third clause, which concerns
types declared here. `Nat.rec` and `List.rec` are auto-generated
recursors on core types and are explicitly permitted. What is banned is
a `def` that calls itself, so the fuel recursion must be written as a
`Nat.rec` application rather than by the equation compiler.

## Findings to discharge

Two fresh-context adversarial rounds were run, one per artifact. Neither
converged. Every finding below is outstanding unless marked. Findings are
categorised blocker, serious, minor, cosmetic-taste, per
[AGENTS.md](../../../AGENTS.md) § Adversarial review of specs and plans;
respond to each in writing — fix, defer with rationale, or reject as
cosmetic-taste — and run further rounds until no blocker and no serious
finding remains.

### Round 1 on `Geb/Internal/ConcreteSyntax.lean`

Blocker:

- **R1-B1** The module violates § Recursion and induction through
  recursors in all three clauses: four self-referential inductives, four
  `termination_by`, nine `induction` tactic uses, one `mutual` block. It
  is the sole violator in the repository. Verified: no `termination_by`
  and no `induction`-tactic use exists anywhere else under `Geb/` or
  `GebTests/`; the other `induction` occurrences are recursor
  applications. Dispositioned by decision 1.

Serious:

- **R1-S1** `Ast.depth` computes the node count, not the depth, against
  mathlib's rule that functions are named for their return value. Rename
  to `Ast.size`. The reviewer additionally claimed the documented reason
  for preferring an additive measure was false; that claim is correct,
  see established fact 3, and `docs/concrete-syntaxes.md` § Local
  verification fact 3 must be restated or dropped.
- **R1-S2** Sections 1 to 8 carry no `@[expose]`, so `Retraction`,
  `format`, and the tree folds cannot be unfolded or applied from a
  downstream module — the generic law layer, which the module docstring
  gives as the reason the module exists, is unusable outside this file.
  Section 9 is exposed, so the asymmetry is inverted. This blocks
  roadmap stages 1b, 1c and 2 if any lands in a new module. Use
  `@[expose] public section`, as
  `Geb/Mathlib/CategoryTheory/FinCat/Basic.lean` does.
- **R1-S3** `rosePathToBin_last` proves one inclusion; its own docstring,
  the `Path` docstring and `docs/concrete-syntaxes.md` all state a
  biconditional. Neither the converse nor strictness is proved, and
  nothing connects `rosePathToBin` to `Ast.subtreeAt` or `Ast.toRose`, so
  the whole occurrence-path claim is unverified. Prove the converse and a
  compatibility lemma, or weaken all three statements.
- **R1-S4** The module docstring omits `## Main definitions`,
  `## Main statements` and `## Tags`, all mandatory per
  [docs/rules/lean-coding.md](../../rules/lean-coding.md)
  § Documentation.
- **R1-S5** The `## References` section reprints bibliographic detail
  that must live only in `docs/references.bib`. Cite by key, as
  `Geb/Mathlib/CategoryTheory/FinCat/Basic.lean` does.
- **R1-S6** Dead code. Dispositioned by decision 2.
- **R1-S7** `docs/concrete-syntaxes.md` § Roadmap says the Merkle fold is
  "proved compositional"; no such theorem exists, and `Ast.subtreeMH`'s
  docstring appeals to a universal property the module never states.
  Decision 2 deletes the code; the document sentences must go too.
- **R1-S8** Format-specific names occupy the flat `Geb` root:
  `print`, `parse`, `printAst`, `parseAst`, `readNat`, `readDigits`,
  `readVerbatim`, `printVerbatim`, `digitsVal`, `decOf`, `digitsLE`,
  `ofLE`, `digitChar`, `charDigit`, `leafTok`, `forkTok`,
  `depth_le_length`. Stage 1b needs its own `print`, `parse`, `printAst`,
  `parseAst` and number layer and has no room. Put the syntax in
  `namespace Csexp` while there is one client; keep only `Retraction` and
  `format` at the root.
- **R1-S9** No test module. Every rejection path is unexercised, since
  `parse_print` constrains the parser only on printer output. Add
  `GebTests/Internal/ConcreteSyntax.lean` using the
  `public meta import` plus `#guard` pattern.

Minor: `digitsVal [] = some 0`, so `parse` accepts an empty label atom
and this is undocumented; `parseAst`'s docstring overstates
`depth_le_length`; `print`'s docstring claims canonical *bytes* while
returning `List Char`; `printAst`'s docstring gives the advanced
grammar's token rule as the reason for a verbatim atom, when the reason
is that canonical form admits nothing else; `HashFn`'s docstring promises
theorems that do not exist; `Multihash.encode` and `uvarint` docstrings
assert unproved injectivity; `Tree.map` has no functor laws, so the
comonad claim is short two obligations; `Ann`, `HashFn`, `Multihash` lack
`@[ext]` and `Ann` lacks `Inhabited`; universes are fixed at `Type 0`
where polymorphism would compile; theorem namespacing is inconsistent
(`ofRose_toRose`, `depth_le_length` at the root); `Rose.ofRose` repeats
its namespace, and the return-value-named form is `Ast.ofRose`; the
generic layer's binders are named `parseDoc`/`printDoc` but are
instantiated at `Ast`.

Cosmetic-taste: double blank lines; two bare `simp only []`; needless
`_root_.List.tail`; `readDigits_append`'s second hypothesis is a
roundabout encoding of "empty or non-digit head"; numbered section
headers that renumber when a syntax is inserted; `tags_equal_length`'s
docstring states a design requirement rather than the theorem.

Recorded as clean by that round: the axiom table in `docs/index.md` is
accurate for all 27 theorems; `parse_print` is the retraction it claims;
the fuel argument is sound; and the adversarial parser inputs tried
(over-long declared length, label at or beyond `k`, `k = 0`, missing
`)`, unknown token, three children, trailing input, `:` and parens
inside verbatim content) all behave.

Not a finding but worth not restating as fact: § Complexity note claims
printing is linear. It is not — `++` is left-associative, so each node's
output is copied once per ancestor.

### Round 1 on `docs/concrete-syntaxes.md`

Blockers:

- **D1-B1** § Local verification fact 2 asserts `Nat.digits` has no
  native implementation. False; see established fact 2. Rest the case on
  `Classical.choice` alone.
- **D1-B2** § Local verification fact 3 asserts the fuel measure must be
  additive. False as a general claim; see established fact 3. Restate as
  a `simp`-versus-`omega` observation, or drop it as already covered by
  the standing rule.
- **D1-B3** § Local verification calls `rosePathToBin_last` "the
  occurrence characterization"; it is one inclusion. Same defect as
  R1-S3, and the design consequences drawn from it rest on the unproved
  direction.
- **D1-B4** The stage-1b rationale describes CBOR's byte-level integer
  encoding. Stage 1b is the JSON core profile, whose integers are decimal
  ASCII — the encoding whose round trip is already proved. The sentence
  is a survivor of the superseded staging, and it is the only support
  offered for the "1 to 2 days" figure.
- **D1-B5** § Relation to existing repository content argues for the
  ordinary-inductive choice as a free trade-off without mentioning that
  a binding rule forbids it, while the table asserts stage 1a "done".
  Decision 1 resolves the code; the section must be restated as the plan
  to move to the W-encoding.
- **D1-B6** Two attribution errors: the OCaml `csexp` package is in
  RFC 9804 Appendix A, not § 1.1, and Appendix A lists no Python code.
  This is the evidence base for the csexp tooling assessment.

Serious:

- **D1-S1** Five dangling references to the removed inline Lean
  development ("the Lean below", "proved below", "mechanized below",
  "that is done below", "the development above").
- **D1-S2** EverCBOR is called "the single largest piece of reusable
  verification leverage" in one section and dismissed as unimportable in
  another, with neither acknowledging the other. The dismissal is also
  over-strong: what cannot cross into Lean is the proof, not the
  artifact, and the document elsewhere proposes `@[extern]` against C as
  the route for the hash. This claim is load-bearing for the syntax
  ordering.
- **D1-S3** § Evaluating the candidates concludes "therefore csexp
  first" from three findings, two of which argue against csexp; the one
  pro-csexp argument, data-model diversity, argues for inclusion rather
  than position. State the actual reason or reorder.
- **D1-S4** The "decisively against JSON" passage is unreconciled with
  JSON's promotion to second syntax, and the asymmetry is unargued: no
  verified canonical-csexp parser exists either.
- **D1-S5** Deterministic CBOR is made the normative binary syntax and
  never given a roadmap stage.
- **D1-S6** "Stage 1a is measured" reports no measurement, so the
  extrapolation base is invisible.
- **D1-S7** The stage-2 injectivity argument collapses a disjunction the
  document states correctly elsewhere, and is vacuous for
  `Doc k = Tree k Ann`, which is a plain product with no redundant
  spellings. The redundancy concern belongs to the side-table
  presentation, which stage 2 does not lift. Keep the string-escaping
  half.
- **D1-S8** Six violations of CONTRIBUTING § Document only the
  persistent, all in in-scope sections: "the survey's original staging",
  "it is where the survey understates the cost", "compiling it in this
  repository established", "all found by compiling rather than by
  reading", and two provenance notes in § Status. State the facts, not
  the activity.
- **D1-S9** Stale staging language: "the bootstrap *pair*"; and a switch
  threshold offering to replace "the first syntax" that is already
  implemented, still cited as live.
- **D1-S10** The axiom table's column header says "Declarations" while
  its rows say "theorems". Under the header reading, row 2 is false.
  Retitle the column.

Minor: `erase_trivialDoc` is said to make a bare-level law a corollary,
but no bare-level law is stated; `annCanon` is listed as a proof
obligation but is defined nowhere; `tagDoc` is dead because `docMH` is
unimplemented; "genuinely four ABNF productions" is a framing error, the
canonical block has two and pulls in two by reference; the "exhaustive
random testing" and "about 78%" statistics are unverifiable and
unnecessary, the underlying claim having a two-line proof already given;
the DAG-CBOR key-ordering exception is sourced to the legacy IPLD
specification, not the one cited; three works have entries both here and
in `docs/references.bib`, against "lives once", and roughly forty have no
`.bib` entry; several references carry no searchable identifier; the
document is reachable only from `TODO.md`.

Recorded as clean by that round: markdownlint, doctoc currency, every
anchor and relative link, the axiom table's three rows against `#print
axioms`, the byte counts in § One tree, and the RFC 9804 ABNF quotations,
RFC 8785 § 3.2.3, RFC 8949 § 4.2, the DAG-JSON and DAG-CBOR constraints,
the protobuf non-canonicality claims and the Unison hash description
against their sources.

## Suggested order

1. Port the module per decisions 1 and 2, keeping the retraction law and
   its two corollaries proved throughout. Take R1-S2 and R1-S8 in the
   same pass, since both are cheapest while there is one client.
2. Add `GebTests/Internal/ConcreteSyntax.lean` (R1-S9), covering the
   rejection paths.
3. Discharge the remaining module findings and re-run `lake lint`, which
   catches missing docstrings and naming violations that `lake build`
   does not.
4. Revise `docs/concrete-syntaxes.md` for the document findings, and
   bring § Local verification into line with whatever the port makes
   true.
5. Update the `docs/index.md` entry and the `TODO.md` entries.
6. Re-run both adversarial cycles to convergence, one fresh
   general-purpose agent per round, per
   [AGENTS.md](../../../AGENTS.md).
7. Delete this handoff, with any spec and plan documents, before the
   branch is pushed.

## Environment notes

- Use `jj`, never a mutating `git` subcommand; a hook blocks them.
- `scripts/pre-push.sh` is the gate. `lake build` passing is not
  sufficient — `lake lint` runs only there and in `lake lint`.
- Evaluating against the module from a scratch file needs `module`, then
  `public import Geb.Internal.ConcreteSyntax`, and additionally
  `public meta import` of the same module for `#eval` or `#guard`. Run
  `lake env lean <path>` from the repository root; a `cd` in a compound
  command resets `LEAN_PATH`.
- `#` commands are banned in the `Geb` library and available in
  `GebTests`.
