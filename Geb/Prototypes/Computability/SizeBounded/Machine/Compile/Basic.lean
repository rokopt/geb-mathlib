/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.SeqFin
public import Geb.Prototypes.Computability.SizeBounded.Machine.Primitives.Copy
public import Geb.Prototypes.Computability.SizeBounded.Machine.Primitives.Const
public import Geb.Prototypes.Computability.SizeBounded.Machine.Primitives.Sbs
public import Geb.Prototypes.Computability.SizeBounded.Machine.Primitives.CopyRev
public import Geb.Prototypes.Computability.SizeBounded.Machine.Loop.Basic
public import Geb.Prototypes.Computability.SizeBounded.Basic
public import Geb.Mathlib.Data.FinEnum

set_option doc.verso true in
/-!
# Compiling the algebra into programs

{lit}`compile` is the fold of the signature {name}`Geb.SizeBounded.sig` that
carries an expression of the size-bounded algebra to a program of the machine
calculus, by the slice W-type's eliminator, in the same shape as the model fold
{name}`Geb.SizeBounded.eval`. A node's program is assembled from its children's
by {lit}`compileValue`: the three base forms are the primitives
{name}`Geb.SizeBounded.Machine.const`, {name}`Geb.SizeBounded.Machine.copy` and
{name}`Geb.SizeBounded.Machine.sbs`; a substitution node sequences its arguments
into consecutive registers and then its head; a recursion node reverses the
recursion argument into a register, clears the processed suffix, runs the bases
into the value registers, and loops with
{name}`Geb.SizeBounded.Machine.caseLoop` over the reversed argument.

A compiled expression carries the number of registers it needs above a first
free one, {lit}`regsValue` at the node, and its program is a function of the
argument registers, the output register, the first free register and the proof
that the need fits below the register count. A program carries a choice-free
enumeration of its state type, its initial state and its transition function,
and its machine is the machine built from that function by
{name}`Turing.MultiTapeTM.ofTr`. The combinators assemble programs from the
transition-level combinators {name}`Geb.SizeBounded.Machine.seqTr`,
{name}`Geb.SizeBounded.Machine.seqFinTr` and
{name}`Geb.SizeBounded.Machine.caseLoopTr`, so the compiled programs, their
transitions and their machines are computable and choice-free.

# Main definitions

* {lit}`Prog` — a state type with a choice-free enumeration, an initial state
  and a transition function on it.
* {lit}`Prog.tm` — the machine of a program, built from its transition
  function.
* {lit}`seqProg`, {lit}`seqFinProg`, {lit}`caseLoopProg` — sequencing two
  programs, sequencing a family, and the loop, on programs.
* {lit}`constProg`, {lit}`copyProg`, {lit}`copyRevProg`, {lit}`sbsProg` — the
  programs of the primitives.
* {lit}`Compiled` — a register need together with a program of it.
* {lit}`transportP` — transport of a compiled expression along an equality of
  arities.
* {lit}`regsValue` — the registers one node needs above its children's.
* {lit}`srnBody`, {lit}`srnProg` — the loop body and the whole program of a
  recursion node.
* {lit}`compileValue`, {lit}`compileStep`, {lit}`compile` — the program of one
  node, the algebra, and the fold.
* {lit}`compileAt`, {lit}`SOf.compile` — the compiled program of an expression
  at a given arity, and of an expression of a given arity.

# Main statements

* {lit}`regs_transportP`, {lit}`transportP_transportP` — transport preserves
  the register need, and composes.
* {lit}`regsValue_comp`, {lit}`regsValue_srn` — the equations of
  {lit}`regsValue` at a substitution and at a recursion node.
* {lit}`fst_compile` — the index component of a tree's compilation is its
  arity.

# Tags

Turing machine, compilation, register, recursion, size-bounded
-/

set_option doc.verso true

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM
open scoped FinEnum
open Geb.SizeBounded (Shape Direction rc q sig finMax le_finMax stepDir sbsSem evalSRN S arity SOf)

public section

/-- A program: a state type with a choice-free enumeration, an initial state and
a transition function on it. -/
structure Prog (k : ℕ) : Type 1 where
  /-- The state type. -/
  State : Type
  /-- Its enumeration, built from the choice-free scoped instances. -/
  enum : FinEnum State
  /-- The initial state. -/
  q₀ : State
  /-- The transition function. -/
  tr : State → Option Bool → (Fin k → Option Bool) → Action k Bool State

/-- The machine of a program: the machine built from its transition function. -/
@[expose] def Prog.tm {k : ℕ} (p : Prog k) : MultiTapeTM k Bool p.State := ofTr p.q₀ p.tr

/-- Sequencing two programs: the sum of their states, {name}`seqTr` of their
transitions. -/
@[expose] def seqProg {k : ℕ} (p q : Prog k) : Prog k :=
  ⟨p.State ⊕ q.State, @FinEnum.finSum _ _ p.enum q.enum, .inl p.q₀, seqTr p.tr q.tr q.q₀⟩

/-- Sequencing a family of programs indexed by {lit}`Fin m`, by
{name}`seqFinTr`. -/
@[expose] def seqFinProg {k : ℕ} (m : ℕ) (ps : Fin m → Prog k) : Prog k :=
  let t := seqFinTr m (fun i ↦ (ps i).State) fun i ↦ ((ps i).q₀, (ps i).tr)
  ⟨seqFinState m fun i ↦ (ps i).State, seqFinEnum m _ fun i ↦ (ps i).enum, t.1, t.2⟩

/-- The loop over register {lit}`R` with two body programs, by
{name}`caseLoopTr`. -/
@[expose] def caseLoopProg {k : ℕ} (R : Fin k) (pF pT : Prog k) : Prog k :=
  ⟨Fin 4 ⊕ (pF.State ⊕ pT.State),
    @FinEnum.finSum _ _ (FinEnum.finFin 4) (@FinEnum.finSum _ _ pF.enum pT.enum), .inl 0,
    caseLoopTr R pF.tr pT.tr pF.q₀ pT.q₀⟩

/-- The program of {name}`const`. -/
@[expose] def constProg {k : ℕ} (w : List Bool) (j : Fin k) : Prog k :=
  ⟨_, inferInstance, .inl (.inl ()), constTr w j⟩

/-- The program of {name}`copy`. -/
@[expose] def copyProg {k : ℕ} (i j : Fin k) : Prog k :=
  ⟨_, inferInstance, .inl (.inl ()), copyTr i j⟩

/-- The program of {name}`copyRev`. -/
@[expose] def copyRevProg {k : ℕ} (i j : Fin k) : Prog k :=
  ⟨_, inferInstance, .inl (.inl ()), copyRevTr i j⟩

/-- The program of {name}`sbs`. -/
@[expose] def sbsProg {k : ℕ} (b : Bool) (x y j : Fin k) : Prog k :=
  ⟨_, inferInstance, .inl (.inl ()), sbsTr b x y j⟩

/-- A compiled expression of arity {lit}`n`: its register need and, for an
environment, an output register and a first free register above which its need
fits, its program. -/
structure Compiled (k n : ℕ) : Type 1 where
  /-- The number of registers the program uses above its first free one. -/
  regs : ℕ
  /-- The program, given the argument registers, the output register and the
  first free register, with the proof that the need fits below {lit}`k`. -/
  prog : (env : Fin n → Fin k) → (out : Fin k) → (free : ℕ) → free + regs ≤ k → Prog k

/-- Transport of a compiled expression along an equality of arities. -/
@[expose] def transportP {k i j : ℕ} (h : i = j) (v : Compiled k i) : Compiled k j := h ▸ v

/-- Transport preserves the register need. -/
theorem regs_transportP {k i j : ℕ} (h : i = j) (v : Compiled k i) :
    (transportP h v).regs = v.regs := by
  subst h
  rfl

/-- Transport composes. -/
theorem transportP_transportP {k i j l : ℕ} (h : i = j) (g : j = l) (v : Compiled k i) :
    transportP g (transportP h v) = transportP (h.trans g) v := by
  subst h
  subst g
  rfl

/-- The registers one node needs above its children's. -/
@[expose] def regsValue : (a : Shape) → (Direction a → ℕ) → ℕ
  | .const _ _, _ => 0
  | .proj _ _, _ => 0
  | .sbs _, _ => 0
  | .comp _ m, r => m + max (r (.inl ())) (finMax m fun i ↦ r (.inr i))
  | .srn _ b _, r =>
      2 * b + 3 + max (finMax b fun l ↦ r (.inl l))
        (max (finMax b fun l ↦ r (.inr (.inl l))) (finMax b fun l ↦ r (.inr (.inr l))))

/-- The register need of a substitution node. -/
theorem regsValue_comp (n m : ℕ) (r : Direction (.comp n m) → ℕ) :
    regsValue (.comp n m) r = m + max (r (.inl ())) (finMax m fun i ↦ r (.inr i)) := rfl

/-- The register need of a recursion node. -/
theorem regsValue_srn (a b : ℕ) (j : Fin b) (r : Direction (.srn a b j) → ℕ) :
    regsValue (.srn a b j) r = 2 * b + 3 + max (finMax b fun l ↦ r (.inl l))
      (max (finMax b fun l ↦ r (.inr (.inl l))) (finMax b fun l ↦ r (.inr (.inr l)))) := rfl

/-- The body of the recursion loop for the bit {lit}`i`: the step programs into the
scratch registers, the copies of the scratch registers into the value registers,
and the bounded successor of the processed suffix by the recursion argument
into a scratch register copied back into the suffix. -/
@[expose] def srnBody {k b : ℕ} (i : Bool) (V X Tmp : Fin k) (vals scr : Fin b → Fin k)
    (steps : Fin b → Prog k) : Prog k :=
  seqProg (seqFinProg b steps)
    (seqProg (seqFinProg b fun l ↦ copyProg (scr l) (vals l))
      (seqProg (sbsProg i V X Tmp) (copyProg Tmp V)))

/-- The program of a recursion node: the reversed copy of the recursion argument,
the empty processed suffix, the bases into the value registers, the loop, and
the selected value into the output register. -/
@[expose] def srnProg {k b : ℕ} (R V X : Fin k) (vals : Fin b → Fin k) (out : Fin k)
    (j : Fin b) (bases : Fin b → Prog k) (bodyF bodyT : Prog k) : Prog k :=
  seqProg (copyRevProg X R) (seqProg (constProg [] V) (seqProg (seqFinProg b bases)
    (seqProg (caseLoopProg R bodyF bodyT) (copyProg (vals j) out))))

/-- The program of one node from its children's. -/
@[expose] def compileValue {k : ℕ} : (a : Shape) → (c : Direction a → Σ i, Compiled k i) →
    (∀ b, (c b).1 = rc a b) → Compiled k (q a)
  | .const _ w, _, _ =>
    ⟨0, fun _ out _ _ ↦ constProg w out⟩
  | .proj _ i, _, _ =>
    ⟨0, fun env out _ _ ↦ copyProg (env i) out⟩
  | .sbs b, _, _ =>
    ⟨0, fun env out _ _ ↦ sbsProg b (env 0) (env 1) out⟩
  | .comp n m, c, h =>
    ⟨regsValue (.comp n m) fun d ↦ (c d).2.regs, fun env out free hfree ↦
      let r : Fin m → Fin k := fun i ↦ ⟨free + i, by
        have := i.isLt
        rw [regsValue_comp] at hfree
        omega⟩
      let args := fun i ↦ (transportP (h (.inr i)) (c (.inr i)).2).prog env (r i) (free + m) (by
        rw [regs_transportP]
        have := le_finMax m (fun i ↦ (c (.inr i)).2.regs) i
        rw [regsValue_comp] at hfree
        omega)
      let head := (transportP (h (.inl ())) (c (.inl ())).2).prog r out (free + m) (by
        rw [regs_transportP]
        rw [regsValue_comp] at hfree
        omega)
      seqProg (seqFinProg m args) head⟩
  | .srn a b j, c, h =>
    ⟨regsValue (.srn a b j) fun d ↦ (c d).2.regs, fun env out free hfree ↦
      have hk : free + (2 * b + 3) ≤ k := by
        rw [regsValue_srn] at hfree
        omega
      let R : Fin k := ⟨free, by omega⟩
      let V : Fin k := ⟨free + 1, by omega⟩
      let Tmp : Fin k := ⟨free + 2, by omega⟩
      let vals : Fin b → Fin k := fun l ↦ ⟨free + 3 + l, by have := l.isLt; omega⟩
      let scr : Fin b → Fin k := fun l ↦ ⟨free + 3 + b + l, by have := l.isLt; omega⟩
      let free' := free + (2 * b + 3)
      let params := Fin.tail env
      let X := env 0
      let bases := fun l ↦ (transportP (h (.inl l)) (c (.inl l)).2).prog params (vals l) free' (by
        rw [regs_transportP]
        have := le_finMax b (fun l ↦ (c (.inl l)).2.regs) l
        rw [regsValue_srn] at hfree
        omega)
      let steps := fun (i : Bool) (l : Fin b) ↦
        (transportP (h (stepDir i l)) (c (stepDir i l)).2).prog
          (Fin.cons V (Fin.append vals params)) (scr l) free' (by
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
      srnProg R V X vals out j bases (srnBody false V X Tmp vals scr (steps false))
        (srnBody true V X Tmp vals scr (steps true))⟩

/-- {name}`compileValue` as an algebra for {name}`Geb.SizeBounded.sig` in the slice
over {lit}`ℕ`. -/
@[expose] def compileStep {k : ℕ} :
    sig.toSliceDomPFunctor.Obj (Sigma.fst (β := Compiled k)) → Σ i, Compiled k i :=
  fun z ↦ ⟨sig.q z.1.1,
    compileValue z.1.1 z.1.2
      ((sig.toSliceDomPFunctor.compatible_iff _ z.1.1 z.1.2).mp z.2)⟩

/-- The compilation of a tree: its arity together with its compiled program at that
arity, by the slice W-type's eliminator. -/
@[expose] def compile (k : ℕ) : sig.W → Σ n, Compiled k n :=
  SlicePFunctor.W.elim sig (Σ n, Compiled k n) (Sigma.fst (β := Compiled k)) compileStep rfl

/-- The index component of a tree's compilation is its arity. -/
theorem fst_compile (k : ℕ) (z : S) : (compile k z).1 = arity z :=
  congrFun (SlicePFunctor.W.comp_elim sig (Σ n, Compiled k n) (Sigma.fst (β := Compiled k))
    compileStep rfl) z

/-- The compiled program of an expression at a given arity. -/
@[expose] def compileAt (k n : ℕ) (e : S) (he : arity e = n) : Compiled k n :=
  transportP ((fst_compile k e).trans he) (compile k e).2

/-- The compiled program of an expression of a given arity. -/
@[expose] def SOf.compile (k : ℕ) {n : ℕ} (e : SOf n) : Compiled k n := compileAt k n e.1 e.2

end

end Geb.SizeBounded.Machine
