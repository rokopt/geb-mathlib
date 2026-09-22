# Handoff: Oitavem-coded bitstreams, follow-up sessions

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Session A: merged as PR #235, three commits](#session-a-merged-as-pr-235-three-commits)
- [Session B: `head` on codes, landed](#session-b-head-on-codes-landed)
- [Session C: bitstreams as elements of arbitrary finitary M-types, landed](#session-c-bitstreams-as-elements-of-arbitrary-finitary-m-types-landed)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

State of the repository. PR #232
(`feat(bitstream): recognize Oitavem-coded bitstreams in logspace`) is merged on
`main`; sessions A and B below extend it. PR #232 adds
`Geb/Prototypes/BitStream/Oitavem/` (index
`Geb/Prototypes/BitStream/Oitavem.lean`):

- `Sig.lean`: the bundle signature
  `sig : SlicePFunctor (Option (ℕ × ℕ)) (Option (ℕ × ℕ))` with shapes
  `Option Shape` (root, or a shape of `Geb.Oitavem.sig`); `Kind` (17
  constructors), `tag`/`readTag`, `fields : Option Shape → Fin 8 → ℕ` (rn, rs,
  hn, hs, tn, ts, card, x), `Atom`, `atoms : Kind → List Atom`, `check`, `mk`,
  `build`; `code a = true :: tag (kind a) ++ codes (List.ofFn (fields a))`,
  `decode`; `finitary` with explicit direction enumerations;
  `coded : CodedSig (Option (ℕ × ℕ))`; `card_eq`, `q_eq`, `rCurried_dir_eq`.
- `Bundle.lean`: `embed`/`unembed` between `Geb.Oitavem.sig.toPFunctor.W` and
  `sig.toPFunctor.W`; `Bundle := {t : sig.W // sig.wIndex t = none}`; `wrap`,
  `unwrap`, `bundleEquiv : Bundle ≃ Expr 1 0`; `rootPrefix` (31 bits),
  `spell_wrap`.
- `Stream.lean`: `depthWord n = List.replicate n false`,
  `valueAt e n = e.eval ![depthWord n] Fin.elim0`, `step`,
  `toStream e = WConstruction.corec (step e) 0`, `get?_seq_toStream`.
- `Fields.lean` (namespace `FieldExpr`): `dropC`, `fieldPtr W p i`, `fpos`,
  parse lemmas (`sem_fieldPtr`, `ok_fieldPtr`, `field_split`, `fields_of_ok`),
  `constAt`, `atomBounded : Atom → Bool`, `atomExpr`, `atomsExpr`, `sem_atom`,
  `sem_atomsExpr`.
- `Label.lean` (`LabelExpr`): `onBits`, `oksExpr`, `kindOk`, `labelOk : LOf 4`,
  `of_label_code`, `form_or`, `labelOk_eq`, `computesLabel`.
- `Edge.lean` (`EdgeExpr`): `pfield`/`cfield` (abbrevs), `headCase`, `tailCase`,
  `someChild`, `edgeOk : LOf 6`, `computesEdge`. Kind-independent thanks to the
  redundant numerals.
- `Recognize.lean`: `startsWithExpr`,
  `recognize w = coded.recognize w && decide (rootPrefix <+: w)`,
  `recognizer : LOf 1`, `spellExpr e = coded.spell (wrap e).1.1`,
  `encode_spine`, `spell_mk_none`, `head_none_of_prefix`, `recognize_iff`,
  `recognize_iff_spellExpr`, `recognizerSem_eq`,
  `recognizerSem_eq_singleton_iff`, `decodeStream`, `decodeStream_spellExpr`.
- `Machine.lean` (in `GebMeta.classicalAllowedModules`):
  `computableInTimeAndSpace_recognizer`, `computableInTimeAndSpace_recognize`.
- Tests: `GebTests/Prototypes/BitStream/Oitavem.lean`. Docs: `docs/index.md`
  entry; `docs/presheaf-recognizer-complexity.md` § Observing coded bitstreams.

Settled semantics (user decision): a code is read as a bit oracle. `valueAt e n`
is the entry at depth `n`; the stream terminates at the first empty value;
consistency comes from the corecursion, not from a check. The map code → stream
is neither injective nor surjective.

Conventions and pitfalls that cost time last session:

- VCS is `jj` (workspace has `.jj`, no `.git`). Commit with
  `jj describe`/`jj new`, bookmark `jj bookmark create <name> -r @`. Never push.
  Commit messages: `<type>(<scope>): <subject>`, subject ≤ 72 chars,
  `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>` footer.
- Run `scripts/pre-push.sh` before declaring done (build, `lake test`,
  `lake lint` on Geb and GebTests with the axiom linter, literate site, manual,
  `lake shake`, import lints, doctoc, markdownlint, md-links). It takes about 12
  minutes. `lake shake` wants a `-- shake: keep; #guard needs it` comment on a
  test's `public import`, and `public meta import` of the module under test.
- Every new module is literate: `set_option doc.verso true in` before the module
  docstring, `set_option doc.verso true` after, roles `{name}` (must resolve, so
  only imported or earlier names), `{lit}`, `{cite}`;
  `meta import GebMeta -- shake: keep`; docstring on every def and theorem;
  `# Main definitions` / `# Main statements` / `# Tags` sections.
- Axiom linter: `by_cases` on a non-decidable proposition, and `omega` on an `↔`
  goal, both introduce `Classical.choice` and fail `lake lint`. Use constructive
  splits (`form_or` in `Label.lean`),
  `Decidable.byCases (p := …) (dec := Nat.decidableBallLT 8 fun i _ ↦ …)`, and
  `constructor <;> intro h <;> omega`. Check with `#print axioms` in a scratch
  file via `lake env lean`.
- `rw` fails with "motive is not type correct" or "did not find pattern"
  whenever the goal mixes `sig.A`/`sig.toPFunctor.W` with
  `Option Shape`/`WType Dir` (semireducible `sig`). Use term mode (`exact`,
  `Iff.trans`, `Eq.trans`), `have h := lemma args; rw [h]` with no
  metavariables, or `change` to the unfolded form. `coded.P.q`, `coded.card`
  likewise: `change` to `sig.q`.
- `Fin 8` literals `6` versus `⟨6, _⟩` are defeq but not syntactically equal:
  `rw` leaves goals that `exact rfl` or `(congrFun (ofList_ofFn _) _).trans rfl`
  close; omega treats them as different atoms, so normalize first
  (`rw [show (⟨i.1, i.2⟩ : Fin 8) = i from rfl]`).
- `fin_cases` is not imported in this part of the tree; `Fields.ext8` does the
  eight cases. The flexible linter forbids a non-terminal `simp`; use
  `simp only [...]` with the `Matrix.cons_val` simproc for `![…] i`.
  `if_pos`/`if_neg` are `ite_eq_left`/`ite_eq_right` here; `List.take_succ` is
  `List.take_add_one`; `Bool.true_ne_false` does not exist (use `cases`).
- Evaluating `recognizer.1.semVec ![w]` with the sharing evaluator on the
  smallest code (58 bits) did not finish in 15 minutes; do not add such a
  `#guard`.

## Session A: merged as PR #235, three commits

1. `tail` on codes (`feat` or `refactor` scope `bitstream`). Define

   ```lean
   tailExpr (e : Expr 1 0) : Expr 1 0 := Expr.comp (safe := false) e ![Expr.initial (.succ false)]
   ```

   so that `valueAt (tailExpr e) n = valueAt e (n + 1)` (by `Expr.eval_comp`,
   `eval_initial`, `depthWord`). Prove the generator law

   ```lean
   WConstruction.dest (toStream e) = match valueAt e 0 with | [] => none | b :: _ => some (b, toStream (tailExpr e))
   ```

   via `corec_eq`/`stream_ext` and a lemma
   `corec (step e) (k + 1) = corec (step (tailExpr e)) k`. Note
   `toStream (tailExpr e) = tail (toStream e)` holds only when
   `valueAt e 0 ≠ []` (the bit-oracle reading truncates at the first empty
   value; `proj` is a counterexample). Prove

   ```lean
   spellExpr (tailExpr e) = rootPrefix ++ compHeader ++ coded.spell (embed e.1.1) ++ succLeaf
   ```

   with `compHeader`, `succLeaf` constant words (the spine of the
   `comp 1 1 false` node has two forks: use `encode_spine`, `List.ofFn_succ`,
   `Sig.compEquiv`), i.e. tail on words is a constant prefix/suffix rewrite. The
   successor-free subalgebra cannot produce longer words, so state the
   word-level tail as a Lean function, not an `LOf` expression; a remark
   suffices for its constant-space computability.
2. All-arities recognizer. Define `codedPlain : CodedSig (ℕ × ℕ)` for
   `Geb.Oitavem.sig`: `code a := code (some a)`,
   `decode w := match decode w with | some (some a) => some a | _ => none`, with
   `decode_code`/`code_of_decode` from `Sig.lean`'s and an explicit `finitary`
   (reuse the `some` cases of `Sig.finitary`). Label check:
   `onBitAt (tailAppL L4) (constL 4 []) (constL 4 []) LabelExpr.labelOk` (reject
   the root tag's set first bit), proved from `labelOk_eq`; edge check:
   `EdgeExpr.edgeOk` unchanged (`ComputesEdge` only constrains decoding labels,
   and a root child is already rejected). Theorems:

   ```lean
   recognizePlain_iff : … ↔ ∃ t, Geb.Oitavem.sig.WValid t ∧ codedPlain.spell t = w
   ```

   (every arity), the expression's agreement, and the machine bound (another
   `classicalAllowedModules` entry). The recognizer lives in the size-bounded
   subalgebra, so no self-recognition statement applies.
3. `PresheafCounterexample.lean` refactor: replace `initialFields`,
   `readInitial`, `shapeFields`, `readShape`, `fieldsTree`,
   `lengths_fieldsTree`, `syntaxShapeCode`, `readSyntaxShape`,
   `readSyntaxShape_code` and `syntaxCode` by `codedPlain`; keep `readExpr` and
   `readExpr_spell` (proof via `codedPlain.readW_toTree`) so
   `no_oitavem_recognizer` and `no_oitavem_nativeCheck` are untouched. Update
   `docs/index.md` and any mention of `syntaxCode` in `docs/`. Import direction:
   the counterexample then imports `Geb.Prototypes.BitStream.Oitavem.Sig` (check
   `scripts/lint-imports.sh` and `check-transitive-imports.sh`; both are under
   `Prototypes`).

Each commit: `lake build`, the relevant `GebTests` module, `docs/index.md`; run
`scripts/pre-push.sh` once at the end.

## Session B: `head` on codes, landed

Branch `feat/bitstream-head`. The evaluator is a Lean function; the machine
bound is the follow-up below, with a corrected target.

- `Geb/Prototypes/Computability/Oitavem/Size.lean`: `size`, the node count
  of a syntax tree; `lengthPoly_le_pow`; `Expr.length_le_pow`, the output
  length at normal arguments of length at most `m` is at most
  `(m + 2) ^ 2 ^ size`.
- `Recognize.lean`: `decodeExpr : List Bool → Option (Expr 1 0)`, and
  `decodeStream w = (decodeExpr w).map toStream`.
- `Head.lean`: `headCode w = (decodeExpr w).map fun e ↦ (valueAt e 0).head?`
  with `headCode_eq_decodeStream`; the coalgebra
  `stepCode w = (headCode w).bind fun h ↦ h.map (·, tailWord w)` with
  `toStream_eq_corec : toStream e = corec stepCode (spellExpr e)` and
  `decodeStream_eq_corec` for recognized words; `length_valueAt_le`,
  `(valueAt e n).length ≤ (n + 2) ^ 2 ^ size e.1.1`; `size_tailExpr`.
- Tests: heads and steps of the three expressions, and `squaresE`, the
  iterated unary square of a two-bit constant, with value lengths
  `[2, 4, 16, 256, 65536]` at sizes `[5, 10, 15, 20, 25]`.

Correction. The target stated for this session, and
`docs/presheaf-recognizer-complexity.md` § Observing coded bitstreams before
this session, put the observation in `PSPACE` on the ground that the largest
intermediate word is at most exponential in the code's size. It is doubly
exponential: `squaresE k` has `5 * k + 5` nodes and value length `2 ^ 2 ^ k`
at the empty word, and `Expr.length_le_pow` is the matching upper bound;
every intermediate word is the value of a subexpression at intermediate
words, so the bound covers it with the size doubled. The recomputing
evaluator holds one counter per node of a position in an intermediate word,
so its workspace is the code's size times the logarithm of the largest
intermediate word, exponential in the code's size. The machine statement the
argument supports is

```lean
∃ c d, ComputableInTimeAndSpaceOfLength (fun w ↦ …) … (fun n ↦ c * 2 ^ 2 ^ ((n + 1) ^ d)) (fun n ↦ c * 2 ^ ((n + 1) ^ d))
```

exponential space and doubly exponential time on one machine, the
observation in `EXPSPACE`; `EXPSPACE` is closed under composition of
decisions, and `ELEMENTARY` still bounds the word-valued evaluator. No
step-counting cost model was written: the evaluator's space is set by the
lengths of intermediate words, which `Expr.length_le_pow` bounds without an
instrumented evaluator, and a machine's time follows from its space by
counting configurations, so an evaluator-level time account would not enter
the machine proof.

Follow-up, the evaluator machine. Time from space is proved:
`Machine.computes_of_space` (`Machine/SpaceTime.lean`) bounds a halting
transducer's time by `(n + 2) * a * 2 ^ (b * s n)` under any work space
bound `s`, by the configuration count, and `Machine.computes_expspace`
instantiates it at `c * 2 ^ ((n + 1) ^ d)`, which is the statement above
with `D = d + 1`; `computes_polytime_logspace` is its instance at
logarithmic space. What remains is the machine, one machine for every code,
whose space bound the theorem converts.

The fixed-expression construction does not transfer directly. It mirrors the
syntax in the machine, one machine and one tape layout per expression, and
its contract `Expr.Realized` quantifies over generators for the arguments,
which are machines. A uniform evaluator holds the code on the input tape and
its call structure on work tapes. Design, from the semantics the generators
implement:

- Frames. A frame holds a node of the code (a position, of size `log n`),
  the depth of the frame binding its variables, a query (a position in the
  node's value, or its length) and the register receiving the answer, and,
  at a safe-recursion node, the recursion counter and the saved prefix of
  the safe value, of length at most `Expr.recursionCutoff`. Every counter
  is at most the logarithm of `(n + 2) ^ 2 ^ n`, and every saved prefix at
  most a constant times `2 ^ n`.
- Binding. The variables of a subtree are bound by the nearest ancestor of
  which it is in function position: the function of a normal composition
  by that composition, the base and steps of a recursion by that recursion,
  and the arguments of a composition and the argument of a log-transition
  by the binder of their parent. The frame evaluating a subtree refers to
  the frame evaluating its binder, below it on the stack; resolving a
  variable walks that chain, accumulating the offsets by which recursions
  drop their recursion argument, and ends at a composition's argument
  subtree, a saved prefix, or the physical argument, empty at depth zero.
- Depth. The claim to prove: the nodes of the frames on the stack are
  pairwise distinct, since a frame waits on one query at a time and the
  closures a frame resolves lie in argument subtrees disjoint from the
  function subtree containing it. Then the stack has at most `size` frames
  and the space is `size` times the counter size, within
  `c * 2 ^ ((n + 1) ^ d)`.
- Machine. The stack is a word in one register and the current frame is in
  dedicated registers; a call saves the current frame onto the stack word
  and a return restores it; a driver loop dispatches on the node's kind and
  the frame's phase. Code navigation, the kind at a position and the
  positions of a node's children, is a logspace function of the input, so
  it is written as expressions of the successor-free subalgebra, as
  `Fields.lean` and the W-tree child scan `WTree/Children.lean` are, and
  compiled by `LOf.correct` into subroutines under `TransformsIn`
  contracts, whose bounds are parameters; the counter and loop routines of
  `Machine/Counter.lean` and `Machine/While.lean` likewise serve at the
  exponential bound.
- Proof. The driver loop's contract needs an invariant over the whole
  stack, which the compositional contracts of the fixed construction do not
  supply: either an abstract stack machine in Lean, with `headCode w` its
  result and the frame bounds its measure, which the machine's body refines
  one step at a time; or a contract per frame, from a push to the matching
  pop, proved by induction on the subtree with the stack below it as the
  environment, which states the same invariant frame by frame. The
  semantic lemmas of the fixed construction (`prefixLoop`,
  `evalRec_cons_prefixLoop`, `Expr.eval_safeRec_cons_prefixCutoff`) apply
  unchanged.

Scale. The fixed construction is the modules under `Oitavem/Machine/` and
`docs/oitavem-logspace-soundness.md`; the uniform evaluator replaces its
tape-per-level layout by the stack register, adds code navigation and the
global invariant, and reuses its semantic lemmas, so it is a development of
the same order, over several sessions. A strict evaluator storing complete
words in frames would need no closures, no binding chain and no cutoffs, and
would relate to `Expr.eval` directly, but its words have length up to
`2 ^ 2 ^ n`, so its space is doubly exponential and its class is not the one
stated. The choice between the two, and whether Aristotle is to be used on
the machine proofs, is the user's before the next session.

## Session C: bitstreams as elements of arbitrary finitary M-types, landed

Branch `feat/bitstream-tree`, one commit.
`Geb/Prototypes/BitStream/Oitavem/Tree.lean`, over a coded signature
`C : CodedSig I` with `[Inhabited C.P.A]`:

- `dirWord i = List.replicate i true ++ [false]`, the unary code of a
  direction's position, and `pathWord C ps`, the concatenation over a path
  `ps : List C.P.toPFunctor.Idx` (mathlib's `PFunctor.Approx.Path`); the path
  of positions zero to a depth is `depthWord`.
- `shapeAt C e p = (C.decode (e.eval ![p] Fin.elim0)).getD default`,
  `stepM C e p = ⟨shapeAt C e p, fun b ↦ p ++ dirWord (C.idx _ b)⟩`, and
  `toM C e = PFunctor.M.corec (stepM C e) []`, the coded element of
  `C.P.toPFunctor.M`.
- `corec_stepM`, `toM_eq_mk` (the generator law, `PFunctor.M.corec_def`),
  `isubtree_corec_stepM` and `iselect_toM`: for `IsPath ps (toM C e)`,
  `iselect ps (toM C e) = shapeAt C e (pathWord C ps)`. The hypothesis in the
  handoff's statement, that every prefix decoded, is not needed: mathlib's
  `IsPath` types each direction by the shape at its node, and the fallback
  reads as a node like any other.
- Tests in `GebTests/Prototypes/BitStream/Oitavem.lean` instantiate `C` at
  the bundle signature `coded` itself, with the root as the default shape,
  and read a conditional expression's tree at the root and at both children.

Design decisions taken: the fallback is the signature's `Inhabited` shape,
so the option "designated nullary shape" is the instance with a nullary
`default`, and the option "add a shape" is the same construction at the
signature with the shape added; positions are coded in unary rather than by
`Numeral.natCode`, so the bitstream depth word is a path word. Mathlib's
`PFunctor.M.dest`, `isubtree` and `iselect` depend on `Classical.choice`
(through the cast in `PFunctor.M.children`), `PFunctor.M.corec` and
`corec_def` do not; the definitions are choice-free, the path theorems are
not, and the module is listed in `GebMeta.classicalAllowedModules`, as is
the test module, whose `iselect` helper inherits the same dependence.
Instance search does not see through `coded.P.A` to `Option Shape`: the
tests declare `Inhabited coded.P.A` and `DecidableEq coded.P.A` locally
and read shapes through helpers typed at `Option Shape`, since a `#guard`
on an equation at `coded.P.toPFunctor.A` finds no `Decidable` instance.

Then slice and presheaf M-types (sessions D and E): the slice and presheaf
M-types are not yet defined in the repository; `TODO.md` § Polynomial functors
item 2 ("M-types and their categorical wrappers as terminal coalgebras") is the
prerequisite, and admissibility on infinite trees is a coinductive predicate.
The fallback shape must lie over the required index, so it is a fallback per
index, again by adding shapes (one root-like shape per index). For presheaf PRA
functors the hereditary-naturality condition becomes coinductive; the
counterexample (`PresheafCounterexample.lean`) shows finiteness alone does not
bound restriction cost even for finite trees, so expect an additional complexity
assumption on the signature's operations.
