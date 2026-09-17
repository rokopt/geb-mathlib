/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Rep
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Branch
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.Inc
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.Dec
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Primitives.Pop
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Primitives.ReadInput
public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Basic
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Compiling the subalgebra into logarithmic-space programs

{lit}`compile` folds an expression of the successor-free subalgebra into a
program of the calculus whose registers hold the representation of
{lit}`Geb.Prototypes.Computability.SizeBounded.Logspace.Rep`: a logical
register is a pair of work tapes, the word tape holding the word part and
the counter tape holding the end segment length in binary. The fold has the
shape of {name}`Geb.SizeBounded.Logspace.evalRep`: a constant writes its word
and empties the counter; a projection copies both tapes; a substitution runs
its arguments into fresh registers and then its head; a recursion runs its
bases into the value registers, then the two phases of
{name}`Geb.SizeBounded.Logspace.evalSRNRep` as two loops, the first over the
end segment lengths, reading the bit at each length off the input and
counting the length up, the second over the word part, popping its bits off a
reversed copy and pushing each onto the cursor's word; and the successor,
which the subalgebra excludes, compiles to the idle program.

A compiled expression carries the number of tapes it needs above a first
free one and a bound on its step count as a function of the word bound and
the input's length, both read off the syntax as the program is assembled, so
that the resource bounds are the compiler's own arithmetic.

# Main definitions

* {lit}`Reg`, {lit}`readRep`, {lit}`writeRep`, {lit}`WF` — a logical register
  as a pair of tapes, the representation it holds, writing one into it, and
  its well-formedness at a word bound and an input length.
* {lit}`bound` — the length bound of every tape at a word bound and an input
  length.
* {lit}`Compiled`, {lit}`transportP` — the carrier of a compiled expression
  and its transport along an equality of arities.
* {lit}`Prog.seq`, {lit}`Prog.seqFin`, {lit}`Prog.whileReg`, {lit}`Prog.caseReg`
  — programs with their enumerations under the combinators.
* {lit}`regsValue`, {lit}`timeValue` — the tapes and the step bound one node
  needs from its children's.
* {lit}`srnV`, {lit}`srnVals`, {lit}`srnScr`, {lit}`srnEnv` — the register
  layout of a recursion node and the environment its steps read.
* {lit}`srnMiddle`, {lit}`srnBody1`, {lit}`srnBody2`, {lit}`srnProg` — the
  middle the two loop bodies share, the bodies, and the whole program of a
  recursion node.
* {lit}`compileValue`, {lit}`compileStep`, {lit}`compile`, {lit}`compileAt`,
  {lit}`LOf.compile` — the program of one node, the algebra, the fold, and
  the compiled program of an expression of the subalgebra.

# Main statements

* {lit}`readRep_writeRep`, {lit}`writeRep_of_ne` — reading back a written
  representation, and the tapes a write leaves alone.
* {lit}`fst_compile` — the index component of a tree's compilation is its
  arity.

# Tags

Turing machine, compilation, register, logspace, recursion on notation
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Turing MultiTapeTM
open scoped FinEnum
open Geb.SizeBounded (Shape Direction rc q sig finMax le_finMax stepDir S arity SOf)
open Geb.SizeBounded.Machine (Prog seq seqFin seqFinEnum idle copy const copyRev)

public section

/-- A logical register: its word tape at {lit}`0` and its counter tape at
{lit}`1`. -/
abbrev Reg (k : ℕ) : Type := Fin 2 → Fin k

/-- The representation a valuation holds in a register. -/
@[expose] def readRep {k : ℕ} (σ : Fin k → List Bool) (r : Reg k) : Rep :=
  ⟨σ (r 0), counterValue (σ (r 1))⟩

/-- The valuation with a representation written into a register. -/
@[expose] def writeRep {k : ℕ} (σ : Fin k → List Bool) (r : Reg k) (x : Rep) :
    Fin k → List Bool :=
  Function.update (Function.update σ (r 0) x.word) (r 1) (counterWord x.suffix)

/-- Reading back a written representation. -/
theorem readRep_writeRep {k : ℕ} (σ : Fin k → List Bool) (r : Reg k) (hr : r 0 ≠ r 1) (x : Rep) :
    readRep (writeRep σ r x) r = x := by
  unfold readRep writeRep
  rw [Function.update_of_ne hr, Function.update_self, Function.update_self,
    counterValue_counterWord]

/-- A write leaves every other tape alone. -/
theorem writeRep_of_ne {k : ℕ} (σ : Fin k → List Bool) (r : Reg k) (x : Rep) (t : Fin k)
    (h0 : t ≠ r 0) (h1 : t ≠ r 1) : writeRep σ r x t = σ t := by
  unfold writeRep
  rw [Function.update_of_ne h1, Function.update_of_ne h0]

/-- A register is well-formed at a word bound {lit}`M` and an input length
{lit}`n` when its word tape is within {lit}`M` and its counter tape holds a
counter within {lit}`n`. -/
@[expose] def WF {k : ℕ} (M n : ℕ) (σ : Fin k → List Bool) (r : Reg k) : Prop :=
  (σ (r 0)).length ≤ M ∧ ∃ l ≤ n, σ (r 1) = counterWord l

/-- The length bound of every tape: the word bound, the binary size of the
input's length, and one more for a flag. -/
@[expose] def bound (M n : ℕ) : ℕ := M + Nat.size n + 1

/-- A compiled expression of arity {lit}`n`: the number of tapes it needs above
its first free one, its step bound at a word bound and an input length, and,
for an environment of registers, an output register and a first free tape
above which its need fits, its program. -/
structure Compiled (k n : ℕ) : Type 1 where
  /-- The number of tapes the program uses above its first free one. -/
  regs : ℕ
  /-- The step bound, at a word bound and an input length. -/
  time : ℕ → ℕ → ℕ
  /-- The program, given the argument registers, the output register and the
  first free tape, with the proof that the need fits below {lit}`k`. -/
  prog : (env : Fin n → Reg k) → (out : Reg k) → (free : ℕ) → free + regs ≤ k → Prog k

/-- Transport of a compiled expression along an equality of arities. -/
@[expose] def transportP {k i j : ℕ} (h : i = j) (v : Compiled k i) : Compiled k j := h ▸ v

/-- Transport preserves the tape need. -/
theorem regs_transportP {k i j : ℕ} (h : i = j) (v : Compiled k i) :
    (transportP h v).regs = v.regs := by
  subst h
  rfl

/-- Transport preserves the step bound. -/
theorem time_transportP {k i j : ℕ} (h : i = j) (v : Compiled k i) :
    (transportP h v).time = v.time := by
  subst h
  rfl

/-- Transport composes. -/
theorem transportP_transportP {k i j l : ℕ} (h : i = j) (g : j = l) (v : Compiled k i) :
    transportP g (transportP h v) = transportP (h.trans g) v := by
  subst h
  subst g
  rfl

/-- A machine with a choice-free enumeration of its state type as a program. -/
@[expose] def Prog.ofTM {k : ℕ} {S : Type} (e : FinEnum S) (tm : MultiTapeTM k Bool S) : Prog k :=
  ⟨S, e, tm⟩

/-- The sequencing of two programs. -/
@[expose] def Prog.seq {k : ℕ} (P Q : Prog k) : Prog k :=
  ⟨P.State ⊕ Q.State, @FinEnum.finSum _ _ P.enum Q.enum, Geb.SizeBounded.Machine.seq P.tm Q.tm⟩

/-- The sequencing of a family of programs. -/
@[expose] def Prog.seqFin {k : ℕ} (m : ℕ) (P : Fin m → Prog k) : Prog k :=
  ⟨(Geb.SizeBounded.Machine.seqFin m (fun i ↦ (P i).State) (fun i ↦ (P i).tm)).1,
    seqFinEnum m _ _ fun i ↦ (P i).enum,
    (Geb.SizeBounded.Machine.seqFin m (fun i ↦ (P i).State) (fun i ↦ (P i).tm)).2⟩

/-- The loop of a program while a register is nonempty. -/
@[expose] def Prog.whileReg {k : ℕ} (R : Fin k) (P : Prog k) : Prog k :=
  ⟨Unit ⊕ P.State, @FinEnum.finSum _ _ FinEnum.unit P.enum, whileNonblank (some R) P.tm⟩

/-- The branch on a register's last bit. -/
@[expose] def Prog.caseReg {k : ℕ} (R : Fin k) (P Q : Prog k) : Prog k :=
  ⟨Unit ⊕ (P.State ⊕ Q.State),
    @FinEnum.finSum _ _ FinEnum.unit (@FinEnum.finSum _ _ P.enum Q.enum),
    caseProbe (some R) P.tm Q.tm⟩

/-- The tapes one node needs above its children's: a substitution two per
argument, a recursion two per value register and per scratch register, two for
the cursor, and one each for the counter of the first loop, the seek scratch,
the flag and the reversed word. -/
@[expose] def regsValue : (a : Shape) → (Direction a → ℕ) → ℕ
  | .const _ _, _ => 0
  | .proj _ _, _ => 0
  | .sbs _, _ => 0
  | .comp _ m, r => 2 * m + max (r (.inl ())) (finMax m fun i ↦ r (.inr i))
  | .srn _ b _, r =>
      4 * b + 6 + max (finMax b fun l ↦ r (.inl l))
        (max (finMax b fun l ↦ r (.inr (.inl l))) (finMax b fun l ↦ r (.inr (.inr l))))

/-- The tape need of a substitution node. -/
theorem regsValue_comp (n m : ℕ) (r : Direction (.comp n m) → ℕ) :
    regsValue (.comp n m) r = 2 * m + max (r (.inl ())) (finMax m fun i ↦ r (.inr i)) := rfl

/-- The tape need of a recursion node. -/
theorem regsValue_srn (a b : ℕ) (j : Fin b) (r : Direction (.srn a b j) → ℕ) :
    regsValue (.srn a b j) r = 4 * b + 6 + max (finMax b fun l ↦ r (.inl l))
      (max (finMax b fun l ↦ r (.inr (.inl l))) (finMax b fun l ↦ r (.inr (.inr l)))) := rfl

/-- The step bound of a copy of a register: two tape copies. -/
@[expose] def copyRegTime (B : ℕ) : ℕ := 2 * (5 * B + 12)

/-- The step bound of the first loop's body less its steps: the read of the
input bit, the dispatch, the copies of the scratch registers into the value
registers, the increment and the decrement. -/
@[expose] def body1Time (b B n : ℕ) : ℕ :=
  readInputTime B n + 1 + (b * copyRegTime B + 1) + (2 * B + 4) + (2 * B + 6)

/-- The step bound of the second loop's body less its steps: the pop, the
dispatch, the copies, and the dispatch of the push. -/
@[expose] def body2Time (b B : ℕ) : ℕ :=
  (4 * B + 12) + 1 + (b * copyRegTime B + 1) + (1 + (2 * B + 6))

/-- The step bound of one node from its children's, as a function of the word
bound {lit}`M` and the input length {lit}`n`; the tapes are bounded by
{name}`bound`. A recursion node runs its bases, initializes, loops at most
{lit}`n` times in the first phase and at most {lit}`M` times in the second,
and copies the selected value out. -/
@[expose] def timeValue : (a : Shape) → (Direction a → ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ
  | .const _ _, _ => fun M n ↦ 2 * (4 * bound M n + 9)
  | .proj _ _, _ => fun M n ↦ copyRegTime (bound M n)
  | .sbs _, _ => fun _ _ ↦ 1
  | .comp _ m, t => fun M n ↦ m * finMax m (fun i ↦ t (.inr i) M n) + 1 + t (.inl ()) M n
  | .srn _ b _, t => fun M n ↦
      let B := bound M n
      let steps := max (finMax b fun l ↦ t (.inr (.inl l)) M n)
        (finMax b fun l ↦ t (.inr (.inr l)) M n)
      (b * finMax b (fun l ↦ t (.inl l) M n) + 1) + 2 * (4 * B + 9) + (5 * B + 12)
        + (n * (b * steps + 1 + body1Time b B n + 1) + 1) + (5 * B + 12)
        + (M * (b * steps + 1 + body2Time b B + 1) + 1) + copyRegTime B

/-- The cursor register of a recursion node: the two tapes at the first free
one. -/
@[expose] def srnV {k : ℕ} (free : ℕ) (hk : free + 2 ≤ k) : Reg k :=
  fun t ↦ ⟨free + t, by have := t.isLt; omega⟩

/-- The value registers of a recursion node, above its six single tapes. -/
@[expose] def srnVals {k : ℕ} (b free : ℕ) (hk : free + 6 + 2 * b ≤ k) : Fin b → Reg k :=
  fun l t ↦ ⟨free + 6 + 2 * l + t, by have := l.isLt; have := t.isLt; omega⟩

/-- The scratch registers of a recursion node, above its value registers. -/
@[expose] def srnScr {k : ℕ} (b free : ℕ) (hk : free + 6 + 4 * b ≤ k) : Fin b → Reg k :=
  fun l t ↦ ⟨free + 6 + 2 * b + 2 * l + t, by have := l.isLt; have := t.isLt; omega⟩

/-- The environment a step of a recursion node reads: the cursor, the value
registers and the parameters. -/
@[expose] def srnEnv {k a b : ℕ} (free : ℕ) (hk : free + 6 + 2 * b ≤ k) (params : Fin a → Reg k) :
    Fin (b + a + 1) → Reg k :=
  Fin.cons (srnV free (by omega)) (Fin.append (srnVals b free hk) params)

/-- The copy of a logical register: its word tape, then its counter tape. -/
@[expose] def copyReg {k : ℕ} (src dst : Reg k) : Prog k :=
  Prog.seq (Prog.ofTM inferInstance (copy (src 0) (dst 0)))
    (Prog.ofTM inferInstance (copy (src 1) (dst 1)))

/-- The copies of the scratch registers into the value registers. -/
@[expose] def copyRegs {k b : ℕ} (scr vals : Fin b → Reg k) : Prog k :=
  Prog.seqFin b fun l ↦ copyReg (scr l) (vals l)

/-- The middle of both loop bodies: the dispatch on the flag to the steps for
that bit, into the scratch registers, then the copies into the value
registers. -/
@[expose] def srnMiddle {k b : ℕ} (F : Fin k) (vals scr : Fin b → Reg k)
    (steps0 steps1 : Prog k) : Prog k :=
  Prog.seq (Prog.caseReg F steps0 steps1) (copyRegs scr vals)

/-- The body of the first loop: read the input bit at the cursor's length into
the flag, the middle, then count the cursor's length up and the loop's counter
down. -/
@[expose] def srnBody1 {k b : ℕ} (V : Reg k) (CR S F : Fin k) (vals scr : Fin b → Reg k)
    (steps0 steps1 : Prog k) : Prog k :=
  Prog.seq (Prog.ofTM inferInstance (readInput (V 1) S F))
    (Prog.seq (srnMiddle F vals scr steps0 steps1)
      (Prog.seq (Prog.ofTM inferInstance (inc (V 1))) (Prog.ofTM inferInstance (dec CR))))

/-- The body of the second loop: pop the next bit of the reversed word into the
flag, the middle, then push the bit onto the cursor's word. -/
@[expose] def srnBody2 {k b : ℕ} (V : Reg k) (R F : Fin k) (vals scr : Fin b → Reg k)
    (steps0 steps1 : Prog k) : Prog k :=
  Prog.seq (Prog.ofTM inferInstance (pop R F))
    (Prog.seq (srnMiddle F vals scr steps0 steps1)
      (Prog.caseReg F (Prog.ofTM inferInstance (push false (V 0)))
        (Prog.ofTM inferInstance (push true (V 0)))))

/-- The program of a recursion node: the bases into the value registers, the
empty cursor, the argument's counter copied into the loop counter, the first
loop, the argument's word reversed into the reversed-word register, the second
loop, and the selected value register copied into the output. -/
@[expose] def srnProg {k b : ℕ} (Y V : Reg k) (CR R : Fin k) (vals : Fin b → Reg k)
    (out : Reg k) (j : Fin b) (bases : Fin b → Prog k) (body1 body2 : Prog k) : Prog k :=
  Prog.seq (Prog.seqFin b bases)
    (Prog.seq (Prog.ofTM inferInstance (const [] (V 0)))
      (Prog.seq (Prog.ofTM inferInstance (const [] (V 1)))
        (Prog.seq (Prog.ofTM inferInstance (copy (Y 1) CR))
          (Prog.seq (Prog.whileReg CR body1)
            (Prog.seq (Prog.ofTM inferInstance (copyRev (Y 0) R))
              (Prog.seq (Prog.whileReg R body2) (copyReg (vals j) out)))))))

/-- The program of one node from its children's. -/
@[expose] def compileValue {k : ℕ} : (a : Shape) → (c : Direction a → Σ i, Compiled k i) →
    (∀ b, (c b).1 = rc a b) → Compiled k (q a)
  | .const n w, _, _ =>
    ⟨0, timeValue (.const n w) fun _ ↦ fun _ _ ↦ 0, fun _ out _ _ ↦
      Prog.seq (Prog.ofTM inferInstance (const w (out 0)))
        (Prog.ofTM inferInstance (const [] (out 1)))⟩
  | .proj n i, _, _ =>
    ⟨0, timeValue (.proj n i) fun _ ↦ fun _ _ ↦ 0, fun env out _ _ ↦ copyReg (env i) out⟩
  | .sbs b, _, _ =>
    ⟨0, timeValue (.sbs b) fun _ ↦ fun _ _ ↦ 0, fun _ _ _ _ ↦ Prog.ofTM inferInstance idle⟩
  | .comp n m, c, h =>
    ⟨regsValue (.comp n m) fun d ↦ (c d).2.regs,
      timeValue (.comp n m) fun d ↦ (c d).2.time,
      fun env out free hfree ↦
        let r : Fin m → Reg k := fun i b ↦ ⟨free + 2 * i + b, by
          have := i.isLt
          have := b.isLt
          rw [regsValue_comp] at hfree
          omega⟩
        let args := fun i ↦ (transportP (h (.inr i)) (c (.inr i)).2).prog env (r i) (free + 2 * m)
          (by
            rw [regs_transportP]
            have := le_finMax m (fun i ↦ (c (.inr i)).2.regs) i
            rw [regsValue_comp] at hfree
            omega)
        let head := (transportP (h (.inl ())) (c (.inl ())).2).prog r out (free + 2 * m) (by
          rw [regs_transportP]
          rw [regsValue_comp] at hfree
          omega)
        Prog.seq (Prog.seqFin m args) head⟩
  | .srn a b j, c, h =>
    ⟨regsValue (.srn a b j) fun d ↦ (c d).2.regs,
      timeValue (.srn a b j) fun d ↦ (c d).2.time,
      fun env out free hfree ↦
        have hk : free + (4 * b + 6) ≤ k := by
          rw [regsValue_srn] at hfree
          omega
        let V : Reg k := srnV free (by omega)
        let CR : Fin k := ⟨free + 2, by omega⟩
        let S : Fin k := ⟨free + 3, by omega⟩
        let F : Fin k := ⟨free + 4, by omega⟩
        let R : Fin k := ⟨free + 5, by omega⟩
        let vals : Fin b → Reg k := srnVals b free (by omega)
        let scr : Fin b → Reg k := srnScr b free (by omega)
        let free' := free + (4 * b + 6)
        let params := Fin.tail env
        let Y := env 0
        let bases := fun l ↦ (transportP (h (.inl l)) (c (.inl l)).2).prog params (vals l) free'
          (by
            rw [regs_transportP]
            have := le_finMax b (fun l ↦ (c (.inl l)).2.regs) l
            rw [regsValue_srn] at hfree
            omega)
        let steps := fun (i : Bool) (l : Fin b) ↦
          (transportP (h (stepDir i l)) (c (stepDir i l)).2).prog
            (srnEnv free (by omega) params) (scr l) free' (by
              rw [regs_transportP]
              rw [regsValue_srn] at hfree
              cases i
              · have h1 : (c (stepDir false l)).2.regs ≤
                    finMax b fun l ↦ (c (.inr (.inl l))).2.regs :=
                  le_finMax b (fun l ↦ (c (.inr (.inl l))).2.regs) l
                omega
              · have h1 : (c (stepDir true l)).2.regs ≤
                    finMax b fun l ↦ (c (.inr (.inr l))).2.regs :=
                  le_finMax b (fun l ↦ (c (.inr (.inr l))).2.regs) l
                omega)
        srnProg Y V CR R vals out j bases
          (srnBody1 V CR S F vals scr (Prog.seqFin b (steps false)) (Prog.seqFin b (steps true)))
          (srnBody2 V R F vals scr (Prog.seqFin b (steps false)) (Prog.seqFin b (steps true)))⟩

/-- {name}`compileValue` as an algebra for {name}`Geb.SizeBounded.sig` in the
slice over {lit}`ℕ`. -/
@[expose] def compileStep {k : ℕ} :
    sig.toSliceDomPFunctor.Obj (Sigma.fst (β := Compiled k)) → Σ i, Compiled k i :=
  fun z ↦ ⟨sig.q z.1.1,
    compileValue z.1.1 z.1.2
      ((sig.toSliceDomPFunctor.compatible_iff _ z.1.1 z.1.2).mp z.2)⟩

/-- The compilation of a tree: its arity together with its compiled program at
that arity, by the slice W-type's eliminator. -/
@[expose] def compile (k : ℕ) : sig.W → Σ n, Compiled k n :=
  SlicePFunctor.W.elim sig (Σ n, Compiled k n) (Sigma.fst (β := Compiled k)) compileStep rfl

/-- The index component of a tree's compilation is its arity. -/
theorem fst_compile (k : ℕ) (z : S) : (compile k z).1 = arity z :=
  congrFun (SlicePFunctor.W.comp_elim sig (Σ n, Compiled k n) (Sigma.fst (β := Compiled k))
    compileStep rfl) z

/-- The compiled program of an expression at a given arity. -/
@[expose] def compileAt (k n : ℕ) (e : S) (he : arity e = n) : Compiled k n :=
  transportP ((fst_compile k e).trans he) (compile k e).2

/-- The compiled program of an expression of the subalgebra. -/
@[expose] def LOf.compile (k : ℕ) {n : ℕ} (e : LOf n) : Compiled k n :=
  compileAt k n e.1.1 e.1.2

end

end Geb.SizeBounded.Logspace.Machine
