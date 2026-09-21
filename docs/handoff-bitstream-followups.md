# Handoff: Oitavem-coded bitstreams, follow-up sessions

State of the repository. PR #232 (`feat(bitstream): recognize
Oitavem-coded bitstreams in logspace`) is merged on `main`. It adds
`Geb/Prototypes/BitStream/Oitavem/` (index `Geb/Prototypes/BitStream/Oitavem.lean`):

- `Sig.lean`: the bundle signature `sig : SlicePFunctor (Option (ℕ × ℕ)) (Option (ℕ × ℕ))`
  with shapes `Option Shape` (root, or a shape of `Geb.Oitavem.sig`);
  `Kind` (17 constructors), `tag`/`readTag`, `fields : Option Shape → Fin 8 → ℕ`
  (rn, rs, hn, hs, tn, ts, card, x), `Atom`, `atoms : Kind → List Atom`,
  `check`, `mk`, `build`; `code a = true :: tag (kind a) ++ codes (List.ofFn (fields a))`,
  `decode`; `finitary` with explicit direction enumerations; `coded : CodedSig (Option (ℕ × ℕ))`;
  `card_eq`, `q_eq`, `rCurried_dir_eq`.
- `Bundle.lean`: `embed`/`unembed` between `Geb.Oitavem.sig.toPFunctor.W` and `sig.toPFunctor.W`;
  `Bundle := {t : sig.W // sig.wIndex t = none}`; `wrap`, `unwrap`, `bundleEquiv : Bundle ≃ Expr 1 0`;
  `rootPrefix` (31 bits), `spell_wrap`.
- `Stream.lean`: `depthWord n = List.replicate n false`, `valueAt e n = e.eval ![depthWord n] Fin.elim0`,
  `step`, `toStream e = WConstruction.corec (step e) 0`, `get?_seq_toStream`.
- `Fields.lean` (namespace `FieldExpr`): `dropC`, `fieldPtr W p i`, `fpos`, parse lemmas
  (`sem_fieldPtr`, `ok_fieldPtr`, `field_split`, `fields_of_ok`), `constAt`, `atomBounded : Atom → Bool`,
  `atomExpr`, `atomsExpr`, `sem_atom`, `sem_atomsExpr`.
- `Label.lean` (`LabelExpr`): `onBits`, `oksExpr`, `kindOk`, `labelOk : LOf 4`, `of_label_code`,
  `form_or`, `labelOk_eq`, `computesLabel`.
- `Edge.lean` (`EdgeExpr`): `pfield`/`cfield` (abbrevs), `headCase`, `tailCase`, `someChild`,
  `edgeOk : LOf 6`, `computesEdge`. Kind-independent thanks to the redundant numerals.
- `Recognize.lean`: `startsWithExpr`, `recognize w = coded.recognize w && decide (rootPrefix <+: w)`,
  `recognizer : LOf 1`, `spellExpr e = coded.spell (wrap e).1.1`, `encode_spine`, `spell_mk_none`,
  `head_none_of_prefix`, `recognize_iff`, `recognize_iff_spellExpr`, `recognizerSem_eq`,
  `recognizerSem_eq_singleton_iff`, `decodeStream`, `decodeStream_spellExpr`.
- `Machine.lean` (in `GebMeta.classicalAllowedModules`): `computableInTimeAndSpace_recognizer`,
  `computableInTimeAndSpace_recognize`.
- Tests: `GebTests/Prototypes/BitStream/Oitavem.lean`. Docs: `docs/index.md` entry;
  `docs/presheaf-recognizer-complexity.md` § Observing coded bitstreams.

Settled semantics (user decision): a code is read as a bit oracle. `valueAt e n` is the entry
at depth `n`; the stream terminates at the first empty value; consistency comes from the
corecursion, not from a check. The map code → stream is neither injective nor surjective.

Conventions and pitfalls that cost time last session:

- VCS is `jj` (workspace has `.jj`, no `.git`). Commit with `jj describe`/`jj new`, bookmark
  `jj bookmark create <name> -r @`. Never push. Commit messages: `<type>(<scope>): <subject>`,
  subject ≤ 72 chars, `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>` footer.
- Run `scripts/pre-push.sh` before declaring done (build, `lake test`, `lake lint` on Geb and
  GebTests with the axiom linter, literate site, manual, `lake shake`, import lints, doctoc,
  markdownlint, md-links). It takes about 12 minutes. `lake shake` wants a
  `-- shake: keep; #guard needs it` comment on a test's `public import`, and
  `public meta import` of the module under test.
- Every new module is literate: `set_option doc.verso true in` before the module docstring,
  `set_option doc.verso true` after, roles `{name}` (must resolve, so only imported or earlier
  names), `{lit}`, `{cite}`; `meta import GebMeta -- shake: keep`; docstring on every def and
  theorem; `# Main definitions` / `# Main statements` / `# Tags` sections.
- Axiom linter: `by_cases` on a non-decidable proposition, and `omega` on an `↔` goal, both
  introduce `Classical.choice` and fail `lake lint`. Use constructive splits (`form_or` in
  `Label.lean`), `Decidable.byCases (p := …) (dec := Nat.decidableBallLT 8 fun i _ ↦ …)`, and
  `constructor <;> intro h <;> omega`. Check with `#print axioms` in a scratch file via
  `lake env lean`.
- `rw` fails with "motive is not type correct" or "did not find pattern" whenever the goal mixes
  `sig.A`/`sig.toPFunctor.W` with `Option Shape`/`WType Dir` (semireducible `sig`). Use term
  mode (`exact`, `Iff.trans`, `Eq.trans`), `have h := lemma args; rw [h]` with no metavariables,
  or `change` to the unfolded form. `coded.P.q`, `coded.card` likewise: `change` to `sig.q`.
- `Fin 8` literals `6` versus `⟨6, _⟩` are defeq but not syntactically equal: `rw` leaves
  goals that `exact rfl` or `(congrFun (ofList_ofFn _) _).trans rfl` close; omega treats them as
  different atoms, so normalize first (`rw [show (⟨i.1, i.2⟩ : Fin 8) = i from rfl]`).
- `fin_cases` is not imported in this part of the tree; `Fields.ext8` does the eight cases.
  The flexible linter forbids a non-terminal `simp`; use `simp only [...]` with the `Matrix.cons_val`
  simproc for `![…] i`. `if_pos`/`if_neg` are `ite_eq_left`/`ite_eq_right` here;
  `List.take_succ` is `List.take_add_one`; `Bool.true_ne_false` does not exist (use `cases`).
- Evaluating `recognizer.1.semVec ![w]` with the sharing evaluator on the smallest code (58 bits)
  did not finish in 15 minutes; do not add such a `#guard`.

## Session A: branch `refactor/bitstream`, three commits

1. `tail` on codes (`feat` or `refactor` scope `bitstream`). Define
   `tailExpr (e : Expr 1 0) : Expr 1 0 := Expr.comp (safe := false) e ![Expr.initial (.succ false)]`
   so that `valueAt (tailExpr e) n = valueAt e (n + 1)` (by `Expr.eval_comp`, `eval_initial`,
   `depthWord`). Prove the generator law
   `WConstruction.dest (toStream e) = match valueAt e 0 with | [] => none | b :: _ => some (b, toStream (tailExpr e))`
   via `corec_eq`/`stream_ext` and a lemma `corec (step e) (k + 1) = corec (step (tailExpr e)) k`.
   Note `toStream (tailExpr e) = tail (toStream e)` holds only when `valueAt e 0 ≠ []`
   (the bit-oracle reading truncates at the first empty value; `proj` is a counterexample).
   Prove `spellExpr (tailExpr e) = rootPrefix ++ compHeader ++ coded.spell (embed e.1.1) ++ succLeaf`
   with `compHeader`, `succLeaf` constant words (the spine of the `comp 1 1 false` node has two
   forks: use `encode_spine`, `List.ofFn_succ`, `Sig.compEquiv`), i.e. tail on words is a
   constant prefix/suffix rewrite. The successor-free subalgebra cannot produce longer words, so
   state the word-level tail as a Lean function, not an `LOf` expression; a remark suffices for
   its constant-space computability.
2. All-arities recognizer. Define `codedPlain : CodedSig (ℕ × ℕ)` for `Geb.Oitavem.sig`:
   `code a := code (some a)`, `decode w := match decode w with | some (some a) => some a | _ => none`,
   with `decode_code`/`code_of_decode` from `Sig.lean`'s and an explicit `finitary` (reuse the
   `some` cases of `Sig.finitary`). Label check: `onBitAt (tailAppL L4) (constL 4 []) (constL 4 []) LabelExpr.labelOk`
   (reject the root tag's set first bit), proved from `labelOk_eq`; edge check: `EdgeExpr.edgeOk`
   unchanged (`ComputesEdge` only constrains decoding labels, and a root child is already rejected).
   Theorems: `recognizePlain_iff : … ↔ ∃ t, Geb.Oitavem.sig.WValid t ∧ codedPlain.spell t = w`
   (every arity), the expression's agreement, and the machine bound (another
   `classicalAllowedModules` entry). The recognizer lives in the size-bounded subalgebra, so no
   self-recognition statement applies.
3. `PresheafCounterexample.lean` refactor: replace `initialFields`, `readInitial`, `shapeFields`,
   `readShape`, `fieldsTree`, `lengths_fieldsTree`, `syntaxShapeCode`, `readSyntaxShape`,
   `readSyntaxShape_code` and `syntaxCode` by `codedPlain`; keep `readExpr` and `readExpr_spell`
   (proof via `codedPlain.readW_toTree`) so `no_oitavem_recognizer` and `no_oitavem_nativeCheck`
   are untouched. Update `docs/index.md` and any mention of `syntaxCode` in `docs/`.
   Import direction: the counterexample then imports `Geb.Prototypes.BitStream.Oitavem.Sig`
   (check `scripts/lint-imports.sh` and `check-transitive-imports.sh`; both are under `Prototypes`).

Each commit: `lake build`, the relevant `GebTests` module, `docs/index.md`; run `scripts/pre-push.sh`
once at the end.

## Session B: the evaluator (`head` on codes)

Target: a Lean function `headCode : List Bool → Option (Option Bool)` (none when the word is not
a code; `some none` for termination; `some (some b)` for the first bit), agreeing with
`decodeStream` (`(decodeStream w).map fun s ↦ (seqEquiv s).get? 0`), and the machine statement
`∃ c d, ComputableInTimeAndSpaceOfLength (fun w ↦ …) … (fun n ↦ c * 2 ^ ((n + 1) ^ d)) (fun n ↦ c * (n + 1) ^ d)`
(polynomial space, exponential time, simultaneously on one machine). The class facts: the
bit query is in PSPACE (workspace linear in the code size times the logarithm of the largest
intermediate word), hence in EXPTIME by the configuration count, hence elementary; a machine
halting in polynomial space runs in exponential time on the same machine, which is the form
`Geb.Oitavem.Machine.computes_polytime_logspace` already proves for the logspace case (time from
space), so the space bound is the real work. `PSPACE` is closed under composition of decisions;
`ELEMENTARY` only enters for the word-valued universal function. The generator view is right:
with `tailExpr` from session A, codes carry a coalgebra `List Bool → Option (Bool × List Bool)`,
`w ↦ (headCode w).bind fun h ↦ h.map (·, tailWord w)`, and `toStream` is its corecursion; the
k-th head costs polynomial space in `|e| + k` because `tailExpr` grows the code by a constant.

Proof routes, in order of preference:

- Reuse the Oitavem machine work (`Geb/Prototypes/Computability/Oitavem/Machine/*`,
  `docs/oitavem-logspace-soundness.md`): it builds Cslib multi-tape transducers for fixed
  expressions by recomputation; the uniform evaluator is the same construction with the code on
  an input tape and the recursion stack of counters bounded by the code's size. Read that
  document's status before choosing; the fixed-expression soundness is still in progress and the
  evaluator would subsume it.
- If a machine proof is out of reach in one session, first land the Lean-level evaluator with a
  step-counting cost model (compare `SizeBounded/Cost.lean`'s `SemC` accounts) and the
  coalgebra laws, and state the machine bound as the follow-up.

## Session C: bitstreams as elements of arbitrary finitary M-types

Observation to start from: the recognized language does not depend on the target M-type. Any
`Expr 1 0` codes an element of the M-type of any finitary polynomial functor `P` with a coded
signature `C : CodedSig`: take `PFunctor.M.corec` (mathlib `Mathlib/Data/PFunctor/Univariate/M.lean`,
`corec_def`, `dest`) with state a path word, at each node evaluating `e` at the path and
decoding the value as a shape; the child at direction `i` extends the path by a code of `i`
(unary or `Numeral.natCode`, a design choice). Consistency is automatic as for bitstreams. What
is not automatic is totality: when the value fails to decode the corecursion needs a fallback
shape (for bitstreams, `[]` reads as the nullary shape). Options: require a designated nullary
shape of `P`; or add one, as the bundle signature added the root, and target the M-type of
`P + 1`. The theorem analogous to `get?_seq_toStream`: the shape of `toM e` at path `p` is the
decoding of `valueAt e p` when every prefix of `p` decoded. The recognizer is reused unchanged;
only the interpretation and the `decodeStream` analogue are new. Compare the finite case:
`CodedSig.recognize` recognizes W-trees of every finitary signature.

Then slice and presheaf M-types (sessions D and E): the slice and presheaf M-types are not yet
defined in the repository; `TODO.md` § Polynomial functors item 2 ("M-types and their categorical
wrappers as terminal coalgebras") is the prerequisite, and admissibility on infinite trees is a
coinductive predicate. The fallback shape must lie over the required index, so it is a fallback
per index, again by adding shapes (one root-like shape per index). For presheaf PRA functors the
hereditary-naturality condition becomes coinductive; the counterexample
(`PresheafCounterexample.lean`) shows finiteness alone does not bound restriction cost even for
finite trees, so expect an additional complexity assumption on the signature's operations.
