/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile.Correct
public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Bound
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Correctness of a substitution node's compilation

The compiled program of a substitution node runs its arguments into the
consecutive fresh registers above the first free tape, in index order, and
then its head with those registers as its environment. {lit}`correct_comp`
derives the node's contract from its children's: every argument program reads
only the environment, which lies below the first free tape and which every
argument leaves as it is, so
{name}`Geb.SizeBounded.Logspace.Machine.composeFin_fresh2` reads the head's
environment off the composite valuation and
{name}`Geb.SizeBounded.Machine.composeFin_of_lt` leaves the tapes below the
first free one to the head. The node's step bound is
{name}`Geb.SizeBounded.Logspace.Machine.TransformsIn.seqFin`'s for the
arguments, each weakened to the maximum of their bounds, followed by the
head's, which is the bound {name}`Geb.SizeBounded.Logspace.Machine.timeValue`
assigns the node.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's {name}`Turing.Cfg.inputSymbol`.

# Main statements

* {lit}`envWF_of_frame` — an environment stays well-formed under a transformer
  leaving its tapes alone.
* {lit}`correct_comp` — a substitution node meets the contract when its
  children do.

# Tags

Turing machine, compilation, correctness, substitution, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Geb.SizeBounded (Direction rc nsiValue finMax le_finMax)
open Geb.SizeBounded.Machine (composeFin composeFin_of_lt le_nsiValue seqFin)

public section

/-- An environment stays well-formed under a transformer that leaves every tape
of the environment alone. -/
theorem envWF_of_frame {k n : ℕ} {M : ℕ} {input : List Bool} {σ σ' : Fin k → List Bool}
    {env : Fin n → Reg k} (hwf : EnvWF M input σ env) (hframe : ∀ i b, σ' (env i b) = σ (env i b)) :
    EnvWF M input σ' env := by
  intro i
  obtain ⟨hw, l, hl, hc⟩ := hwf i
  refine ⟨?_, l, hl, ?_⟩
  · rw [hframe i 0]
    exact hw
  · rw [hframe i 1]
    exact hc

/-- A substitution node is correct when its children are: the arguments run into
fresh registers in sequence, then the head reads them. -/
theorem correct_comp {k n m : ℕ} (c : Direction (.comp n m) → Σ i, Compiled k i)
    (h : ∀ b, (c b).1 = rc (.comp n m) b) (s : Direction (.comp n m) → List Bool → Σ i, RepSem i)
    (hs : ∀ b x, (s b x).1 = rc (.comp n m) b) (K : Direction (.comp n m) → ℕ)
    (hk : ∀ b, CorrectSigma (c b) (s b) (K b)) :
    Correct (compileValue (.comp n m) c h)
      (fun x ↦ evalRepValue x (.comp n m) (fun b ↦ s b x) (hs · x)) (nsiValue (.comp n m) K) := by
  intro env out free hfree hadm M hK
  obtain ⟨hinj, henv, hout, hout01, houtenv⟩ := hadm
  have hregs : free + (2 * m + max (c (.inl ())).2.regs
      (finMax m fun i ↦ (c (.inr i)).2.regs)) ≤ k := hfree
  -- every child is correct at the arity the signature prescribes
  have hchild : ∀ d, Correct (transportP (h d) (c d).2)
      (fun x ↦ repTransport (hs d x) (s d x).2) (K d) := fun d ↦ (hk d).atArity (h d) (hs d)
  -- the fresh registers the arguments write
  have hrlt : ∀ (i : Fin m) (b : Fin 2), free + 2 * i + b < k := fun i b ↦ by
    have := i.isLt
    have := b.isLt
    omega
  set r : Fin m → Reg k := fun i b ↦ ⟨free + 2 * i + b, hrlt i b⟩ with hr
  have hrval : ∀ i b, (r i b : ℕ) = free + 2 * i + b := fun _ _ ↦ rfl
  have harg : ∀ i : Fin m, free + 2 * m + (transportP (h (.inr i)) (c (.inr i)).2).regs ≤ k := by
    intro i
    rw [regs_transportP]
    have := le_finMax m (fun i ↦ (c (.inr i)).2.regs) i
    omega
  have hhead : free + 2 * m + (transportP (h (.inl ())) (c (.inl ())).2).regs ≤ k := by
    rw [regs_transportP]
    omega
  have hrinj : Function.Injective (fun x : Fin m × Fin 2 ↦ r x.1 x.2) := fun x y hxy ↦ by
    have hval := congrArg Fin.val hxy
    change free + 2 * (x.1 : ℕ) + (x.2 : ℕ) = free + 2 * (y.1 : ℕ) + (y.2 : ℕ) at hval
    have hx2 := x.2.isLt
    have hy2 := y.2.isLt
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  have hr01 : ∀ i : Fin m, r i 0 ≠ r i 1 := fun i ↦ Fin.ne_of_val_ne (by
    change free + 2 * (i : ℕ) + 0 ≠ free + 2 * (i : ℕ) + 1
    omega)
  have henvr : ∀ (j : Fin n) (b : Fin 2) (i : Fin m) (b' : Fin 2), env j b ≠ r i b' :=
    fun j b i b' ↦ Fin.ne_of_val_ne (by
      have := henv j b
      change (env j b : ℕ) ≠ free + 2 * (i : ℕ) + (b' : ℕ)
      omega)
  have hrlt' : ∀ (i : Fin m) (b : Fin 2), (r i b : ℕ) < free + 2 * m := fun i b ↦ by
    have := i.isLt
    have := b.isLt
    rw [hrval]
    omega
  -- the arguments, each into its own fresh register
  have hargs := fun i : Fin m ↦ hchild (.inr i) env (r i) (free + 2 * m) (harg i)
    ⟨hinj, fun j b ↦ by have := henv j b; omega, hrlt' i, hr01 i, fun j b b' ↦ henvr j b i b'⟩ M
    (Nat.le_trans (le_nsiValue _ K (.inr i)) hK)
  choose F hFT hFout hFframe hFB using hargs
  -- the head, reading the fresh registers
  obtain ⟨G, hGT, hGout, hGframe, hGB⟩ := hchild (.inl ()) r out (free + 2 * m) hhead
    ⟨hrinj, hrlt', fun b ↦ by have := hout b; omega, hout01,
      fun i b b' ↦ Fin.ne_of_val_ne (by have := hout b'; rw [hrval]; omega)⟩ M
    (Nat.le_trans (le_nsiValue _ K (.inl ())) hK)
  -- the environment survives every argument
  have hpres : ∀ (l : Fin m) input σ, EnvWF M input σ env → EnvWF M input (F l input σ) env :=
    fun l input σ hwf ↦ envWF_of_frame hwf fun j b ↦
      hFframe l input σ (env j b) (by have := henv j b; omega) (henvr j b l 0) (henvr j b l 1)
  have hseq := TransformsIn.seqFin (bound M) (fun n ↦ finMax m fun i ↦ (c (.inr i)).2.time M n) m
    (fun i ↦ ((transportP (h (.inr i)) (c (.inr i)).2).prog env (r i) (free + 2 * m)
      (harg i)).State)
    (fun i ↦ ((transportP (h (.inr i)) (c (.inr i)).2).prog env (r i) (free + 2 * m)
      (harg i)).tm)
    (fun _ input σ ↦ EnvWF M input σ env) F
    (fun i ↦ TransformsIn.mono_time (hFT i) fun n ↦ by
      rw [time_transportP]
      exact le_finMax m (fun i ↦ (c (.inr i)).2.time M n) i)
  -- the head's environment after the arguments have run
  have hfresh : ∀ input σ, EnvWF M input σ env → ∀ i : Fin m,
      composeFin m (fun l ↦ F l input) σ (r i 0) =
        (repTransport (hs (.inr i) input) (s (.inr i) input).2 fun j ↦ readRep σ (env j)).word ∧
      composeFin m (fun l ↦ F l input) σ (r i 1) =
        counterWord (repTransport (hs (.inr i) input) (s (.inr i) input).2
          fun j ↦ readRep σ (env j)).suffix := by
    intro input σ hσ i
    refine composeFin_fresh2 free (fun σ ↦ EnvWF M input σ env) m (by omega)
      (fun l ↦ F l input)
      (fun l σ ↦ (repTransport (hs (.inr l) input) (s (.inr l) input).2
        fun j ↦ readRep σ (env j)).word)
      (fun l σ ↦ counterWord (repTransport (hs (.inr l) input) (s (.inr l) input).2
        fun j ↦ readRep σ (env j)).suffix)
      (fun l σ ↦ hpres l input σ) ?_ ?_ ?_ ?_ ?_ σ hσ i
    · intro l τ τ' hτ
      exact congrArg (fun x ↦ (repTransport (hs (.inr l) input) (s (.inr l) input).2 x).word)
        (funext fun j ↦ by
          unfold readRep
          rw [hτ _ (henv j 0), hτ _ (henv j 1)])
    · intro l τ τ' hτ
      exact congrArg (fun x ↦ counterWord (repTransport (hs (.inr l) input)
        (s (.inr l) input).2 x).suffix)
        (funext fun j ↦ by
          unfold readRep
          rw [hτ _ (henv j 0), hτ _ (henv j 1)])
    · intro l τ hτ
      exact congrArg Rep.word (hFout l input τ hτ)
    · intro l τ hτ
      obtain ⟨_, l', _, hc⟩ := hFB l input τ hτ
      have hsuf := congrArg Rep.suffix (hFout l input τ hτ)
      change counterValue (F l input τ (r l 1)) = _ at hsuf
      rw [← hsuf, hc, counterValue_counterWord]
      exact hc
    · intro l τ i hi h0 h1
      exact hFframe l input τ i hi h0 h1
  have hheadwf : ∀ input σ, EnvWF M input σ env →
      EnvWF M input (composeFin m (fun l ↦ F l input) σ) r := by
    intro input σ hσ i
    obtain ⟨h0, h1⟩ := hfresh input σ hσ i
    obtain ⟨hw, l, hl, hc⟩ := hFB i input σ hσ
    have hsuf := congrArg Rep.suffix (hFout i input σ hσ)
    change counterValue (F i input σ (r i 1)) = _ at hsuf
    refine ⟨?_, l, hl, ?_⟩
    · rw [h0, ← congrArg Rep.word (hFout i input σ hσ)]
      exact hw
    · rw [h1, ← hsuf, hc, counterValue_counterWord]
  refine ⟨fun input σ ↦ G input (composeFin m (fun l ↦ F l input) σ), ?_, ?_, ?_, ?_⟩
  · refine TransformsIn.mono_pre (TransformsIn.mono_time (TransformsIn.seq hseq hGT) ?_) ?_
    · intro n
      change (m * finMax m (fun i ↦ (c (.inr i)).2.time M n) + 1) +
        (transportP (h (.inl ())) (c (.inl ())).2).time M n ≤
        m * finMax m (fun i ↦ (c (.inr i)).2.time M n) + 1 + (c (.inl ())).2.time M n
      rw [time_transportP]
    · intro input σ _ hσ
      exact ⟨preFin_of_invariant (fun input σ ↦ EnvWF M input σ env) m F hpres input σ hσ,
        hheadwf input σ hσ⟩
  · intro input σ hσ
    rw [hGout input _ (hheadwf input σ hσ)]
    change _ = repTransport (hs (.inl ()) input) (s (.inl ()) input).2
      fun i ↦ repTransport (hs (.inr i) input) (s (.inr i) input).2 fun j ↦ readRep σ (env j)
    refine congrArg _ (funext fun i ↦ ?_)
    obtain ⟨h0, h1⟩ := hfresh input σ hσ i
    unfold readRep
    rw [h0, h1, counterValue_counterWord]
    rfl
  · intro input σ t ht h0 h1
    change G input (composeFin m (fun l ↦ F l input) σ) t = σ t
    rw [hGframe input _ t (by omega) h0 h1]
    exact composeFin_of_lt free m (fun l ↦ F l input)
      (fun l τ j hj ↦ hFframe l input τ j (by omega)
        (Fin.ne_of_val_ne (by rw [hrval]; omega)) (Fin.ne_of_val_ne (by rw [hrval]; omega))) σ t ht
  · intro input σ hσ
    exact hGB input _ (hheadwf input σ hσ)

end

end Geb.SizeBounded.Logspace.Machine
