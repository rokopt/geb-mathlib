/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Computability.Cobham.Cases
public import Geb.Mathlib.Computability.Cobham.Tree
public import Geb.Mathlib.Data.Tree.Ranked.Binary
public import Geb.Mathlib.Data.Tree.Ranked.Preorder

/-!
# Prototype of the generic ranked recognizer

Compiles the pieces the design's segment 2 rests on, at a symbolic ranked
alphabet, before that segment's plan is written. Deleted once
`Cobham/RankedTree.lean` lands.

## Tags

ranked alphabet, Cobham, scan, prototype
-/

namespace RankedAlphabet

public section

/-- The largest arity of a symbol of the alphabet. -/
@[expose] def maxArity (R : RankedAlphabet) : ℕ :=
  (List.ofFn R.arity).foldr max 0

/-- Every symbol's arity is at most the largest. -/
theorem arity_le_maxArity (R : RankedAlphabet) (i : Fin R.card) :
    R.arity i ≤ R.maxArity := by
  have hmem : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldr max 0 := fun l ↦
    List.rec (fun x hx ↦ absurd hx (by simp))
      (fun a t iht x hx ↦ by
        rcases List.mem_cons.mp hx with h | h
        · subst h
          exact Nat.le_max_left _ _
        · exact Nat.le_trans (iht x h) (Nat.le_max_right _ _)) l
  exact hmem _ _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

/-- Every arity a block yields is at most the largest, every such arity lying
in the image of `arity`. -/
theorem le_maxArity_of_arOf_eq_some (R : RankedAlphabet) {v r : ℕ}
    (h : R.arOf v = some r) : r ≤ R.maxArity := by
  rw [arOf] at h
  split at h
  · rename_i hlt
    rw [← Option.some.inj h]
    exact arity_le_maxArity R ⟨v, hlt⟩
  · exact absurd h (by nofun)

/-- The scan's incomplete block never fills: a live scan's block holds the
word's length modulo the width, and a failed scan carries no block. -/
theorem length_buf_scanFinal_lt (R : RankedAlphabet) (w : List Bool) :
    (R.scanFinal w).buf.length < R.width :=
  List.rec R.width_pos
    (fun b v ih ↦ by
      rw [scanFinal_cons, scanStep]
      cases (R.scanFinal v).live
      · exact ih
      · simp only []
        cases hc : decide ((b :: (R.scanFinal v).buf).length = R.width)
        · simp only [List.length_cons] at hc ⊢
          have := of_decide_eq_false hc
          omega
        · simp only []
          cases R.arOf (decodeBits (b :: (R.scanFinal v).buf))
          · exact R.width_pos
          · simp only []
            cases decide (_ ≤ (R.scanFinal v).depth) <;> exact R.width_pos) w

/-- The pending count is at most the word's length: every clause but the pop
leaves it alone, and the pop raises it by at most one. -/
theorem depth_scanFinal_le_length (R : RankedAlphabet) (w : List Bool) :
    (R.scanFinal w).depth ≤ w.length :=
  List.rec (Nat.le_refl 0)
    (fun b v ih ↦ by
      have hlen : (b :: v).length = v.length + 1 := rfl
      rw [scanFinal_cons, scanStep]
      cases (R.scanFinal v).live
      · simp only []
        omega
      · simp only []
        cases decide ((b :: (R.scanFinal v).buf).length = R.width)
        · simp only []
          omega
        · simp only []
          cases R.arOf (decodeBits (b :: (R.scanFinal v).buf))
          · simp only []
            omega
          · simp only []
            cases decide (_ ≤ (R.scanFinal v).depth)
            · simp only []
              omega
            · simp only []
              omega) w

/-- Validity as the three conditions on the final state, in the form a
statement about the state word consumes. Proved from its two implications,
`omega` on an `Iff` goal depending on `Classical.choice`. -/
theorem valid_iff_scanFinal (R : RankedAlphabet) (w : List Bool) :
    R.Valid w ↔ ((R.scanFinal w).live = true ∧ (R.scanFinal w).buf = [] ∧
      (R.scanFinal w).depth = 1) := by
  constructor
  · intro hv
    have hb : ((R.scanFinal w).live && (R.scanFinal w).buf.isEmpty &&
        ((R.scanFinal w).depth == 1)) = true := hv
    rw [Bool.and_eq_true, Bool.and_eq_true] at hb
    exact ⟨hb.1.1, List.isEmpty_iff.mp hb.1.2, of_decide_eq_true hb.2⟩
  · intro hf
    change ((R.scanFinal w).live && (R.scanFinal w).buf.isEmpty &&
      ((R.scanFinal w).depth == 1)) = true
    rw [hf.1, hf.2.1, hf.2.2]
    rfl

end

end RankedAlphabet

namespace Cobham

open RankedAlphabet

public section

/-- The incomplete block in a slot of the alphabet's width: `false` padding,
a `true` sentinel, then the block. -/
@[expose] def bufBits (R : RankedAlphabet) (buf : List Bool) : List Bool :=
  List.replicate (R.width - 1 - buf.length) false ++ true :: buf

/-- The scan state as a bitstring: the liveness flag, the block slot, then the
pending count in unary. -/
@[expose] def stateWord (R : RankedAlphabet) (s : Scan) : List Bool :=
  s.live :: bufBits R s.buf ++ List.replicate s.depth true

/-- The number of state bits the step dispatches on. -/
@[expose] def dispatchWidth (R : RankedAlphabet) : ℕ := R.width + R.maxArity + 2

/-- The slot holds the alphabet's width, the padding shrinking as the block
grows. `Nat` subtraction being truncated, the hypothesis is consumed. -/
theorem length_bufBits_of_lt (R : RankedAlphabet) (buf : List Bool)
    (h : buf.length < R.width) : (bufBits R buf).length = R.width := by
  rw [bufBits, List.length_append, List.length_replicate, List.length_cons]
  omega

/-- The state word's length: the flag, the slot, and the pending count. -/
theorem length_stateWord_of_lt (R : RankedAlphabet) (s : Scan)
    (h : s.buf.length < R.width) :
    (stateWord R s).length = 1 + R.width + s.depth := by
  rw [stateWord, List.cons_append, List.length_cons, List.length_append,
    length_bufBits_of_lt R s.buf h, List.length_replicate]
  omega

/-- The slot past its padding is the sentinel followed by the block. -/
theorem dropWhile_bufBits (R : RankedAlphabet) (buf : List Bool) :
    (bufBits R buf).dropWhile (fun b ↦ !b) = true :: buf := by
  rw [bufBits, List.dropWhile_append_of_pos
    (fun a ha ↦ by rw [List.eq_of_mem_replicate ha]; rfl)]
  rfl

/-- The state word truncated to a window past the slot and zero-padded: the
flag, the slot, and the pending count capped at the window. Stated at an
arbitrary window, the dispatch and the verdict reading different ones. -/
theorem ofFn_bits_stateWord (R : RankedAlphabet) (s : Scan) (p m : ℕ)
    (hp : p = 1 + R.width + m) (h : s.buf.length < R.width) :
    List.ofFn (bits p (stateWord R s)) =
      s.live :: (bufBits R s.buf ++
        (List.replicate (min m s.depth) true ++
          List.replicate (m - s.depth) false)) := by
  subst hp
  have hbuf : (bufBits R s.buf).length = R.width := length_bufBits_of_lt R s.buf h
  have hdw : 1 + R.width + m = (bufBits R s.buf).length + m + 1 := by
    rw [hbuf]
    omega
  have hpad : 1 + R.width + m - (stateWord R s).length = m - s.depth := by
    rw [length_stateWord_of_lt R s h]
    omega
  rw [ofFn_bits, hpad, stateWord, List.cons_append, hdw, List.take_succ_cons,
    List.take_length_add_append, List.take_replicate, List.cons_append,
    List.append_assoc]

/-- The inverse of the state layout, read off `List.ofFn` of the bit family:
the flag is the head, the block is the slot past its padding and sentinel, and
the pending count is the run of `true` that follows the slot. -/
@[expose] def decodeState (R : RankedAlphabet)
    (v : Fin (dispatchWidth R) → Bool) : Scan :=
  ⟨(((List.ofFn v).tail.take R.width).dropWhile (fun b ↦ !b)).tail,
    (((List.ofFn v).tail.drop R.width).takeWhile id).length,
    (List.ofFn v).headD false⟩

/-- The decoder inverts the layout, up to capping the pending count at the
dispatch window. -/
theorem decodeState_stateWord_of_lt (R : RankedAlphabet) (s : Scan)
    (h : s.buf.length < R.width) :
    decodeState R (bits (dispatchWidth R) (stateWord R s)) =
      { s with depth := min s.depth (R.maxArity + 1) } := by
  have hbuf : (bufBits R s.buf).length = R.width := length_bufBits_of_lt R s.buf h
  have hword := ofFn_bits_stateWord R s (dispatchWidth R) (R.maxArity + 1)
    (by rw [dispatchWidth]; omega) h
  have hslot : ((List.ofFn (bits (dispatchWidth R) (stateWord R s))).tail.take
      R.width) = bufBits R s.buf := by
    rw [hword, List.tail_cons, List.take_left' hbuf]
  have htail : ((List.ofFn (bits (dispatchWidth R) (stateWord R s))).tail.drop
      R.width) = List.replicate (min (R.maxArity + 1) s.depth) true ++
        List.replicate (R.maxArity + 1 - s.depth) false := by
    rw [hword, List.tail_cons, List.drop_left' hbuf]
  refine Scan.ext ?_ ?_ ?_
  · rw [decodeState, hslot, dropWhile_bufBits]
    rfl
  · have hfalse : ∀ j : ℕ, (List.replicate j false).takeWhile id = [] := fun j ↦
      match j with
      | 0 => rfl
      | _ + 1 => rfl
    rw [decodeState, htail,
      List.takeWhile_append_of_pos (fun a ha ↦ by rw [List.eq_of_mem_replicate ha]; rfl),
      hfalse, List.append_nil, List.length_replicate]
    exact Nat.min_comm _ _
  · rw [decodeState, hword, List.headD_cons]

/-- The bits a step drops from the state word: the flag and the slot, together
with the popped subterms where a completed block's symbol pops. -/
@[expose] def dropCount (R : RankedAlphabet) (b : Bool) (s : Scan) : ℕ :=
  match s.live with
  | false => 1 + R.width
  | true =>
    match decide ((b :: s.buf).length = R.width) with
    | false => 1 + R.width
    | true =>
      match R.arOf (decodeBits (b :: s.buf)) with
      | none => 1 + R.width
      | some r =>
        match decide (r ≤ s.depth) with
        | false => 1 + R.width
        | true => 1 + R.width + r

/-- The bits a step prepends to the state word: the rebuilt flag and slot,
together with the pushed subterm where a completed block's symbol pops. -/
@[expose] def nextPrefix (R : RankedAlphabet) (b : Bool) (s : Scan) :
    List Bool :=
  match s.live with
  | false => false :: bufBits R s.buf
  | true =>
    match decide ((b :: s.buf).length = R.width) with
    | false => true :: bufBits R (b :: s.buf)
    | true =>
      match R.arOf (decodeBits (b :: s.buf)) with
      | none => false :: bufBits R []
      | some r =>
        match decide (r ≤ s.depth) with
        | false => false :: bufBits R []
        | true => true :: bufBits R [] ++ [true]

/-- Capping the pending count at the dispatch window leaves the bits dropped
unchanged: the only test reading the count compares it with an arity, which is
at most the largest. -/
theorem dropCount_min_depth (R : RankedAlphabet) (b : Bool) (s : Scan) :
    dropCount R b { s with depth := min s.depth (R.maxArity + 1) } =
      dropCount R b s := by
  obtain ⟨buf, depth, live⟩ := s
  rw [dropCount, dropCount]
  dsimp only
  cases live
  · rfl
  · cases har : R.arOf (decodeBits (b :: buf))
    · rfl
    · rename_i r
      have hr : r ≤ R.maxArity := le_maxArity_of_arOf_eq_some R har
      dsimp only
      rcases Nat.le_total depth (R.maxArity + 1) with hle | hle
      · rw [Nat.min_eq_left hle]
      · rw [decide_eq_true (by omega : r ≤ min depth (R.maxArity + 1)),
          decide_eq_true (by omega : r ≤ depth)]

/-- Capping the pending count leaves the bits prepended unchanged, as
`dropCount_min_depth`. -/
theorem nextPrefix_min_depth (R : RankedAlphabet) (b : Bool) (s : Scan) :
    nextPrefix R b { s with depth := min s.depth (R.maxArity + 1) } =
      nextPrefix R b s := by
  obtain ⟨buf, depth, live⟩ := s
  rw [nextPrefix, nextPrefix]
  dsimp only
  cases live
  · rfl
  · cases har : R.arOf (decodeBits (b :: buf))
    · rfl
    · rename_i r
      have hr : r ≤ R.maxArity := le_maxArity_of_arOf_eq_some R har
      dsimp only
      rcases Nat.le_total depth (R.maxArity + 1) with hle | hle
      · rw [Nat.min_eq_left hle]
      · rw [decide_eq_true (by omega : r ≤ min depth (R.maxArity + 1)),
          decide_eq_true (by omega : r ≤ depth)]

/-- A step of the scan rewrites a bounded prefix of the state word and drops a
bounded number of its bits: the flag and the slot are rebuilt, and the pending
count in the tail is popped by the arity of a completed block's symbol. -/
theorem stateWord_scanStep_of_lt (R : RankedAlphabet) (b : Bool) (s : Scan)
    (h : s.buf.length < R.width) :
    stateWord R (R.scanStep b s) =
      nextPrefix R b s ++ (stateWord R s).drop (dropCount R b s) := by
  have hpre : (s.live :: bufBits R s.buf).length = 1 + R.width := by
    rw [List.length_cons, length_bufBits_of_lt R s.buf h]
    omega
  have hdrop : (stateWord R s).drop (1 + R.width) =
      List.replicate s.depth true := List.drop_left' hpre
  have hdropr : ∀ r : ℕ, (stateWord R s).drop (1 + R.width + r) =
      List.replicate (s.depth - r) true := fun r ↦ by
    rw [← List.drop_drop, hdrop, List.drop_replicate]
  obtain ⟨buf, depth, live⟩ := s
  rw [scanStep, dropCount, nextPrefix]
  dsimp only
  cases live
  · dsimp only
    rw [hdrop]
    rfl
  · cases hc : decide ((b :: buf).length = R.width)
    · dsimp only
      rw [hdrop]
      rfl
    · dsimp only
      cases har : R.arOf (decodeBits (b :: buf))
      · dsimp only
        rw [hdrop]
        rfl
      · rename_i r
        dsimp only
        cases hle : decide (r ≤ depth)
        · dsimp only
          rw [hdrop]
          rfl
        · dsimp only
          rw [hdropr r, stateWord, List.replicate_succ, List.append_assoc]
          rfl

/-- One step of the recognizer: dispatch on the state's leading bits, prepend
the rebuilt prefix and drop the consumed bits. -/
@[expose] def rankedStep (R : RankedAlphabet) (b : Bool) : COf 1 :=
  diagOf (casesOf (dispatchWidth R) fun v ↦
    prependOf (nextPrefix R b (decodeState R v))
      (predIterOf (dropCount R b (decodeState R v))))

/-- The recognizer's scan, at the two steps and the growth the state layout
allows. -/
@[expose] def rankedSem (R : RankedAlphabet) : Sem 1 :=
  scanSem (constAtOf 0 (stateWord R ⟨[], 0, true⟩)) (rankedStep R false)
    (rankedStep R true) (R.width + 1)

/-- A step of the expression computes a step of the scan, on a state whose
incomplete block is short of the width. -/
theorem stepWord_rankedStep_of_lt (R : RankedAlphabet) (b : Bool) (s : Scan)
    (h : s.buf.length < R.width) :
    stepWord (rankedStep R b) (stateWord R s) = stateWord R (R.scanStep b s) := by
  rw [rankedStep, stepWord_diagOf]
  change casesSem (dispatchWidth R) _ ![stateWord R s, stateWord R s] = _
  rw [casesSem_eq, stepWord_prependOf, stepWord_predIterOf,
    decodeState_stateWord_of_lt R s h, nextPrefix_min_depth, dropCount_min_depth,
    stateWord_scanStep_of_lt R b s h]

/-- The expression computes the scan's state word on every input. -/
theorem rankedSem_eq (R : RankedAlphabet) (w : List Bool) :
    rankedSem R ![w] = stateWord R (R.scanFinal w) := by
  rw [rankedSem, scanSem_eq]
  refine List.rec ?_ ?_ w
  · rw [List.foldr_nil, baseWord_constAtOf, scanFinal_nil]
  · intro b v ih
    rw [List.foldr_cons, ih, scanFinal_cons]
    cases b
    · exact stepWord_rankedStep_of_lt R false _ (length_buf_scanFinal_lt R v)
    · exact stepWord_rankedStep_of_lt R true _ (length_buf_scanFinal_lt R v)

/-- The value never exceeds the input by more than the state's fixed part, so
the scanner's recursion bound holds at growth `R.width + 1`. -/
theorem length_rankedSem_le (R : RankedAlphabet) (w : List Bool) :
    (scanSem (constAtOf 0 (stateWord R ⟨[], 0, true⟩)) (rankedStep R false)
      (rankedStep R true) (R.width + 1) ![w]).length ≤ w.length + (R.width + 1) := by
  have hlen := length_stateWord_of_lt R (R.scanFinal w) (length_buf_scanFinal_lt R w)
  have hdepth := depth_scanFinal_le_length R w
  rw [← rankedSem, rankedSem_eq, hlen]
  omega

/-- The accepting state's word: live, no incomplete block, one pending
subterm. -/
@[expose] def acceptWord (R : RankedAlphabet) : List Bool :=
  stateWord R ⟨[], 1, true⟩

/-- The verdict window separates the accepting state from every other state
whose block is short of the width. It reads one bit past the accepting word,
so a pending count above one is rejected. -/
theorem ofFn_bits_stateWord_eq_iff (R : RankedAlphabet) (s : Scan)
    (h : s.buf.length < R.width) :
    List.ofFn (bits (R.width + 3) (stateWord R s)) = acceptWord R ++ [false] ↔
      (s.live = true ∧ s.buf = [] ∧ s.depth = 1) := by
  have hbuf : (bufBits R s.buf).length = R.width := length_bufBits_of_lt R s.buf h
  have hnil : (bufBits R ([] : List Bool)).length = R.width :=
    length_bufBits_of_lt R [] R.width_pos
  have hleft := ofFn_bits_stateWord R s (R.width + 3) 2 (by omega) h
  have hright : acceptWord R ++ [false] =
      true :: (bufBits R [] ++ ([true] ++ [false])) := by
    rw [acceptWord, stateWord, List.cons_append, List.cons_append,
      List.append_assoc]
    rfl
  rw [hleft, hright]
  constructor
  · intro heq
    injection heq with hhead htail
    have hlen : (bufBits R s.buf).length = (bufBits R []).length := by
      rw [hbuf, hnil]
    obtain ⟨hslot, hrest⟩ := List.append_inj htail hlen
    have hbufnil : s.buf = [] := by
      have hd := congrArg (List.dropWhile (fun b ↦ !b)) hslot
      rw [dropWhile_bufBits, dropWhile_bufBits] at hd
      injection hd with _ hd'
    refine ⟨hhead, hbufnil, ?_⟩
    match hdep : s.depth with
    | 0 =>
      rw [hdep] at hrest
      exact absurd hrest (by decide)
    | 1 => rfl
    | (n + 2) =>
      rw [hdep, Nat.min_eq_left (by omega), (by omega : 2 - (n + 2) = 0)] at hrest
      exact absurd hrest (by decide)
  · intro hs
    rw [hs.1, hs.2.1, hs.2.2]
    rfl

/-- The verdict test: the branch at the accepting window returns `[true]`, and
every other branch the empty bitstring. The decision is taken on `List Bool`,
whose `DecidableEq` depends on no axiom. -/
@[expose] def acceptTest (R : RankedAlphabet) : COf 1 :=
  diagOf (casesOf (R.width + 3) fun v ↦
    if List.ofFn v = acceptWord R ++ [false] then constAtOf 1 [true]
    else constAtOf 1 [])

/-- The verdict test's value at the state it reads. -/
theorem stepWord_acceptTest (R : RankedAlphabet) (u : List Bool) :
    stepWord (acceptTest R) u =
      if List.ofFn (bits (R.width + 3) u) = acceptWord R ++ [false] then [true]
      else [] := by
  rw [acceptTest, stepWord_diagOf]
  change casesSem (R.width + 3) _ ![u, u] = _
  rw [casesSem_eq]
  by_cases hb : List.ofFn (bits (R.width + 3) u) = acceptWord R ++ [false]
  · rw [if_pos hb, if_pos hb, stepWord_constAtOf]
  · rw [if_neg hb, if_neg hb, stepWord_constAtOf]

/-- The scan as an expression of the class, its recursion bound discharged by
`length_rankedSem_le`. -/
@[expose] def ranked (R : RankedAlphabet) : C :=
  scan (constAtOf 0 (stateWord R ⟨[], 0, true⟩)) (rankedStep R false)
    (rankedStep R true) (R.width + 1) (length_rankedSem_le R)

/-- `ranked` at its declared arity. -/
@[expose] def rankedOf (R : RankedAlphabet) : COf 1 :=
  scanOf (constAtOf 0 (stateWord R ⟨[], 0, true⟩)) (rankedStep R false)
    (rankedStep R true) (R.width + 1) (length_rankedSem_le R)

/-- The raw tree of the recognizer: the verdict test on the scan. -/
@[expose] def isRankedRaw (R : RankedAlphabet) : sig.toPFunctor.W :=
  WType.mk (.comp 1 1) fun d ↦
    match d with
    | .inl () => (acceptTest R).1.1.1
    | .inr _ => (rankedOf R).1.1.1

/-- The recognizer's tree is admissible, from its two components'. `decide`
does not apply: at a symbolic alphabet nothing reduces. -/
theorem wValid_isRankedRaw (R : RankedAlphabet) : sig.WValid (isRankedRaw R) :=
  ⟨fun d ↦ match d with
    | .inl () => (acceptTest R).1.1.2
    | .inr _ => (rankedOf R).1.1.2,
  funext fun d ↦ match d with
    | .inl () => (sig.wIndexValid_index_eq_wIndexRoot _).trans (acceptTest R).2
    | .inr _ => (sig.wIndexValid_index_eq_wIndexRoot _).trans (rankedOf R).2⟩

/-- The recognizer as an expression of the class. -/
@[expose] def isRanked (R : RankedAlphabet) : C :=
  ⟨⟨isRankedRaw R, wValid_isRankedRaw R⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => (acceptTest R).1.2
      | .inr _ => (rankedOf R).1.2⟩⟩

/-- `isRanked` at its declared arity. -/
@[expose] def isRankedOf (R : RankedAlphabet) : COf 1 := ⟨isRanked R, rfl⟩

/-- The recognizer's meaning at its arity, read at the raw tree. -/
@[expose] def isRankedSem (R : RankedAlphabet) : Sem 1 :=
  semAt 1 ⟨isRankedRaw R, wValid_isRankedRaw R⟩ rfl

/-- One step of the recognizer: the verdict test on the scan's value. -/
theorem isRankedSem_apply (R : RankedAlphabet) (w : List Bool) :
    isRankedSem R ![w] = stepWord (acceptTest R) (rankedSem R ![w]) :=
  congrArg (semAt 1 (acceptTest R).1.1 (acceptTest R).2)
    (funext fun i ↦ match i with | ⟨0, _⟩ => rfl)

/-- The recognizer's value on both branches: a rejected word receives the empty
bitstring, not merely something other than `[true]`. -/
theorem isRankedSem_eq_ite (R : RankedAlphabet) (w : List Bool) :
    isRankedSem R ![w] = if R.Valid w then [true] else [] := by
  have hsep := ofFn_bits_stateWord_eq_iff R (R.scanFinal w)
    (length_buf_scanFinal_lt R w)
  rw [isRankedSem_apply, rankedSem_eq, stepWord_acceptTest]
  by_cases hv : R.Valid w
  · rw [if_pos hv, if_pos (hsep.mpr ((valid_iff_scanFinal R w).mp hv))]
  · rw [if_neg hv, if_neg fun hw ↦ hv ((valid_iff_scanFinal R w).mpr (hsep.mp hw))]

/-- The recognizer accepts exactly the words spelling a term. -/
theorem isRankedSem_eq_singleton_iff_valid (R : RankedAlphabet) (w : List Bool) :
    isRankedSem R ![w] = [true] ↔ R.Valid w := by
  rw [isRankedSem_eq_ite]
  by_cases hv : R.Valid w
  · rw [if_pos hv]
    exact ⟨fun _ ↦ hv, fun _ ↦ rfl⟩
  · rw [if_neg hv]
    exact ⟨fun hw ↦ absurd hw (by nofun), fun h ↦ absurd h hv⟩

/-- The scan's meaning read at the raw tree is the meaning the expression
carries, as the scan combinator's counterpart. -/
theorem rankedSem_eq_eval (R : RankedAlphabet) :
    transport (rankedOf R).2 (rankedOf R).1.eval = rankedSem R :=
  scanSem_eq_eval (constAtOf 0 (stateWord R ⟨[], 0, true⟩)) (rankedStep R false)
    (rankedStep R true) (R.width + 1) (length_rankedSem_le R)

/-- The recognizer's meaning read at the raw tree is the meaning the expression
carries. -/
theorem isRankedSem_eq_eval (R : RankedAlphabet) :
    transport (isRankedOf R).2 (isRankedOf R).1.eval = isRankedSem R := rfl

/-- At the two-symbol alphabet the generic recognizer accepts the language the
recognizer of `Cobham/Tree.lean` accepts. Every link relates semantic
predicates on `List Bool`, so the two recognizers' differing failure
conventions need no reconciling. -/
theorem isRankedSem_binRanked_eq_singleton_iff_isTreeSem (w : List Bool) :
    isRankedSem RankedAlphabet.Binary.binRanked ![w] = [true] ↔
      isTreeSem ![w] = [true] :=
  (isRankedSem_eq_singleton_iff_valid _ w).trans
    ((RankedAlphabet.Binary.valid_iff w).trans
      (isTreeSem_eq_singleton_iff_valid w).symm)

/-- Whether the recognizer reduces in the kernel at a concrete alphabet, which
is what the test mirror's sweep costs. A leaf's spelling is accepted. -/
theorem isRankedSem_binRanked_leaf :
    isRankedSem RankedAlphabet.Binary.binRanked ![[false]] = [true] := by decide

/-- A bare node symbol has no children pending, and is rejected. -/
theorem isRankedSem_binRanked_bare_node :
    isRankedSem RankedAlphabet.Binary.binRanked ![[true]] = [] := by decide

/-- A node over two leaves is accepted. -/
theorem isRankedSem_binRanked_node :
    isRankedSem RankedAlphabet.Binary.binRanked ![[true, false, false]] =
      [true] := by decide

/-- An alphabet whose `card` is below `2 ^ width`, so the block `[true, true]`
spells no symbol. Its dispatch is six bits wide, which is what the mirror's
sweep costs. -/
@[expose] def narrowAlphabet : RankedAlphabet := ⟨3, 2, by decide, by decide, ![0, 1, 2]⟩

/-- A nullary symbol's block alone is accepted. -/
theorem isRankedSem_narrow_nullary :
    isRankedSem narrowAlphabet ![[false, false]] = [true] := by decide

/-- A block spelling no symbol is rejected. -/
theorem isRankedSem_narrow_no_symbol :
    isRankedSem narrowAlphabet ![[true, true]] = [] := by decide

/-- A unary symbol over a nullary one is accepted. -/
theorem isRankedSem_narrow_unary :
    isRankedSem narrowAlphabet ![[true, false, false, false]] = [true] := by decide

/-- A binary symbol with nothing pending is rejected. -/
theorem isRankedSem_narrow_underflow :
    isRankedSem narrowAlphabet ![[false, true]] = [] := by decide

/-- An alphabet every one of whose blocks spells a symbol. -/
@[expose] def sampleAlphabet : RankedAlphabet := ⟨4, 2, by decide, by decide, ![0, 1, 2, 3]⟩

/-- Whether the decoder's inversion is assertable as one equation. `Scan`
derives no `DecidableEq`, so it is not, and the mirror sweeps the fields. -/
theorem decodeState_initial_buf :
    (decodeState narrowAlphabet
      (bits (dispatchWidth narrowAlphabet)
        (stateWord narrowAlphabet ⟨[], 0, true⟩))).buf = [] := by decide

/-- The initial state's pending count. -/
theorem decodeState_initial_depth :
    (decodeState narrowAlphabet
      (bits (dispatchWidth narrowAlphabet)
        (stateWord narrowAlphabet ⟨[], 0, true⟩))).depth = 0 := by decide

/-- The initial state's flag. -/
theorem decodeState_initial_live :
    (decodeState narrowAlphabet
      (bits (dispatchWidth narrowAlphabet)
        (stateWord narrowAlphabet ⟨[], 0, true⟩))).live = true := by decide

/-- A state carrying one bit of an incomplete block. -/
theorem decodeState_partial_buf :
    (decodeState narrowAlphabet
      (bits (dispatchWidth narrowAlphabet)
        (stateWord narrowAlphabet ⟨[true], 1, true⟩))).buf = [true] := by decide

/-- A failed state's flag, which the decoder recovers as `false`. -/
theorem decodeState_dead_live :
    (decodeState narrowAlphabet
      (bits (dispatchWidth narrowAlphabet)
        (stateWord narrowAlphabet ⟨[], 2, false⟩))).live = false := by decide

/-- A pending count above the dispatch window is recovered capped, which is
what `decodeState_stateWord_of_lt`'s `min` states. At `narrowAlphabet` the
window is three. -/
theorem decodeState_capped_depth :
    (decodeState narrowAlphabet
      (bits (dispatchWidth narrowAlphabet)
        (stateWord narrowAlphabet ⟨[], 5, true⟩))).depth = 3 := by decide

/-- A block of the alphabet's own width overflows the slot, so
`length_bufBits_of_lt`'s hypothesis is consumed rather than decorative. -/
theorem length_bufBits_overflow :
    (bufBits narrowAlphabet [false, true]).length = 3 := by decide

/-- The recognizer at its declared arity, named so that a mirror references a
constant of the module under test. -/
def isRankedArity : COf 1 := isRankedOf narrowAlphabet

/-- A word ending mid-block leaves that block incomplete. -/
theorem scanFinal_narrow_partial_buf :
    (narrowAlphabet.scanFinal [false]).buf = [false] := by decide

/-- And leaves nothing pending, no block having completed. -/
theorem scanFinal_narrow_partial_depth :
    (narrowAlphabet.scanFinal [false]).depth = 0 := by decide

/-- And leaves the scan live. -/
theorem scanFinal_narrow_partial_live :
    (narrowAlphabet.scanFinal [false]).live = true := by decide

/-- A block spelling no symbol fails the scan and clears the block. -/
theorem scanFinal_narrow_dead_buf :
    (narrowAlphabet.scanFinal [true, true]).buf = [] := by decide

/-- And leaves it failed. -/
theorem scanFinal_narrow_dead_live :
    (narrowAlphabet.scanFinal [true, true]).live = false := by decide

/-- The narrow alphabet's binary symbol's block yields its arity, and that
arity is the alphabet's largest. -/
theorem arOf_narrow_two_eq_maxArity :
    narrowAlphabet.arOf 2 = some narrowAlphabet.maxArity := by decide

/-- A block spelling no symbol yields no arity. -/
theorem arOf_narrow_three : narrowAlphabet.arOf 3 = none := by decide

/-- The largest arity at an alphabet whose arities run up to three. -/
theorem maxArity_sampleAlphabet : sampleAlphabet.maxArity = 3 := by decide

/-- And at the narrow alphabet, whose arities stop at two. -/
theorem maxArity_narrowAlphabet : narrowAlphabet.maxArity = 2 := by decide

/-- The words over `Bool` of at most a given length, each once. -/
@[expose] def wordsUpTo : ℕ → List (List Bool) :=
  Nat.rec [[]] fun _ ih ↦ [] :: ih.flatMap fun w ↦ [false :: w, true :: w]

/-- The recognizer and the validity scan accept the same words, at the
alphabet reaching the block that spells no symbol. -/
theorem isRankedSem_eq_validBool_narrow :
    (wordsUpTo 6).all (fun w ↦
      (isRankedSem narrowAlphabet ![w] == [true]) ==
        narrowAlphabet.validBool w) = true := by
  set_option maxRecDepth 100000 in decide

/-- And at an alphabet every one of whose blocks spells a symbol. Its largest
arity is one above the narrow alphabet's, so its dispatch is one bit wider and
its case tree three times the size; the sweep is correspondingly shorter. -/
theorem isRankedSem_eq_validBool_sample :
    (wordsUpTo 5).all (fun w ↦
      (isRankedSem sampleAlphabet ![w] == [true]) ==
        sampleAlphabet.validBool w) = true := by
  set_option maxRecDepth 100000 in decide

/-- And at the two-symbol alphabet, whose width is one, so the block slot is
the bare sentinel and the bridge's own alphabet is exercised. -/
theorem isRankedSem_eq_validBool_binRanked :
    (wordsUpTo 6).all (fun w ↦
      (isRankedSem RankedAlphabet.Binary.binRanked ![w] == [true]) ==
        RankedAlphabet.Binary.binRanked.validBool w) = true := by
  set_option maxRecDepth 100000 in decide

end

end Cobham
