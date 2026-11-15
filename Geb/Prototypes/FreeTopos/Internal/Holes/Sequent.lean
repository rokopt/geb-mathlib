/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Derivation
public import Geb.Prototypes.FreeTopos.Prover.Library

set_option doc.verso true in
/-!
# Transporting embedded sequent certificates

Adding hypotheses restricts the subobject on which a theorem's conclusion holds. A certificate
of the original sequent is composed with the inclusion of the smaller subobject. Intermediate
equations are cut into the resulting certificate, without extending the theorem environment.

## Main definitions

* {lit}`State` — the intermediate equations, their proofs, and the prover's typing cache.

## Tags

internal language, partial Horn logic, proof certificate, weakening
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal.ProofHoles.Sequent

open PartialHorn
open Sorts

open scoped FinEnum

/-- The intermediate equations, their proofs in order, and the prover's typing cache. -/
structure State where
  /-- Equations established by the preceding cuts. -/
  hyps : List Eqn := []
  /-- Certificates of those equations, each in the scope of its predecessors. -/
  cuts : List Tree := []
  /-- Typings and normal forms whose proofs refer only to preceding hypotheses. -/
  prover : Prover.St

/-- Certificate construction in the scope extended by the intermediate equations. -/
abbrev Build (α : Type) := StateT State Option α

/-- Run the prover with its cache, in the scope of the equations established so far. -/
def run {α : Type} (n : ℕ) (p : Prover.PM α) : Build α := fun s ↦ do
  let (x, st) ← (p.run ⟨List.replicate n obj, s.hyps⟩).run s.prover
  pure (x, {
    hyps := s.hyps ++ st.localLemmas.map Prod.fst
    cuts := s.cuts ++ st.localLemmas.map Prod.snd
    prover := { st with localLemmas := [] } })

/-- Record an equation and its certificate, returning its citation as a hypothesis. -/
def record (q : Eqn) (c : Tree) : Build Tree := do
  let s ← get
  set { s with hyps := s.hyps ++ [q], cuts := s.cuts ++ [c] }
  pure (Cert.hyp s.hyps.length)

/-- The characteristic map of a diagonal is defined: postcomposing the kernel pair's equation
with the first projection cancels the diagonal. -/
def diagonalClassifierDfd (m : Prover.Ty) : Prover.PM Tree := do
  let A ← (m.term.children[0]?).bind fun t ↦ t.children[0]?
  guard (m.term == diag A)
  let d := dom m.term
  let l := comp m.term (fst d d)
  let r := comp m.term (snd d d)
  let (q, c) ← Prover.inst
    (.ax (Prover.axIdx (Prover.beforeProduct ++ [productAxioms]) 7)) [l, r]
  let f := fst A A
  let tf ← Prover.typeTerm f
  let tq ← Prover.typeTerm (comp f q.lhs)
  let c := Cert.cong tq.dfd [tf.dfd, c]
  let p := monoCond m.term
  let cl ← Prover.byNorm Prover.baseRules ⟨p.lhs, comp f q.lhs⟩
  let cr ← Prover.byNorm Prover.baseRules ⟨comp f q.rhs, p.rhs⟩
  pure (Cert.ax (Prover.axIdx (Prover.beforeExponential ++ [exponentialAxioms]) 4)
    [m.term] [m.dfd] [Cert.trans cl (Cert.trans c cr)])

/-- Type an operation, constructing the diagonal's monomorphism certificate where compilation
of equality needs its characteristic map. -/
def typeOp (patTy : List Prover.Ty → Tree → Prover.PM Prover.Ty) (k : ℕ)
    (tys : List Prover.Ty) : Prover.PM Prover.Ty := do
  match k, tys with
  | 27, [m] =>
    let d ← diagonalClassifierDfd m
    let t := chi m.term
    let ty ← Prover.typeOpTy patTy k arr t d tys
    Prover.memoize ty
    pure ty
  | _, _ => Prover.typeOp patTy k tys

/-- A step of typing with the additional case for the characteristic map of a diagonal. -/
def typeStep (patTy : List Prover.Ty → Tree → Prover.PM Prover.Ty)
    (leaf : ℕ → Prover.PM Prover.Ty) (term : Tree → Tree) :
    ℕ → List (Tree × Prover.PM Prover.Ty) → Prover.PM Prover.Ty
  | 0, [(i, _)] => leaf i.label
  | k + 1, cs => do
    if let some ty ← Prover.lookup (term (RoseTree.node (k + 1) (cs.map Prod.fst))) then
      return ty
    typeOp patTy k (← cs.mapM Prod.snd)
  | _, _ => failure

/-- The typing procedures, including equality's characteristic maps inside defined operations. -/
def typers : ℕ → (List Prover.Ty → Tree → Prover.PM Prover.Ty) ×
    (Tree → Prover.PM Prover.Ty) :=
  Nat.rec (fun _ _ ↦ failure, fun _ ↦ failure) fun _ rec ↦
    (fun env ↦ RoseTree.para (typeStep rec.1 (fun i ↦ match env[i]? with
      | some ty => pure ty
      | none => failure) (PartialHorn.subst (env.map Prover.Ty.term))),
      RoseTree.para (typeStep rec.1 (Prover.typeVar rec.2) id))

/-- Type a term and record its subterms' typings for the categorical normalizer. -/
def typed (n : ℕ) (t : Tree) : Build Prover.Ty := run n ((typers Prover.typingFuel).2 t)

/-- Normalize composites while keeping the arrows defining equalizers in place. Rewriting
inside an inclusion would change its domain's syntax, whereas the typing prover's canonical
objects retain those defining arrows. Object arguments of atomic arrows are canonicalized. -/
def compositionStep (rec : Tree → Prover.PM (Tree × Tree)) :
    ℕ → List (Tree × Prover.PM (Tree × Tree)) → Prover.PM (Tree × Tree) := fun l cs ↦ do
  let t := RoseTree.node l (cs.map Prod.fst)
  let ty ← (typers Prover.typingFuel).2 t
  if ty.sort == obj then return (ty.lo, ty.loCert)
  if l == 0 then return (t, ty.dfd)
  let rs ← if l == 4 then cs.mapM Prod.snd else cs.mapM fun c ↦ do
    let tc ← (typers Prover.typingFuel).2 c.1
    return if tc.sort == obj then (tc.lo, tc.loCert) else (c.1, tc.dfd)
  let t' := RoseTree.node l (rs.map Prod.fst)
  let c := if t' == t then ty.dfd else Cert.cong ty.dfd (rs.map Prod.snd)
  if l != 4 then return (t', c)
  let _ ← (typers Prover.typingFuel).2 t'
  match ← (some <$> Prover.rewriteRoot Prover.baseRules t') <|> pure none with
  | none => pure (t', c)
  | some (u, cu) =>
    let (v, cv) ← rec u
    pure (v, Cert.trans c (Cert.trans cu cv))

/-- The composition normalizers at a bound on rewritings at one position. -/
def compositionNormalizers : ℕ → Tree → Prover.PM (Tree × Tree) :=
  Nat.rec (fun _ ↦ failure) fun _ rec ↦ RoseTree.para (compositionStep rec)

/-- Prove an equation by composition normalization, preserving subobject domains. -/
def normalize (n : ℕ) (q : Eqn) : Build Tree := do
  let (l, cl) ← run n (compositionNormalizers Prover.normFuel q.lhs)
  let (r, cr) ← run n (compositionNormalizers Prover.normFuel q.rhs)
  guard (l == r)
  pure (Cert.trans cl (Cert.symm cr))

/-- Transport a proved equation along normalization of its two sides. -/
def transport (n : ℕ) (q : Eqn) (c : Tree) (q' : Eqn) : Build Tree := do
  let l ← normalize n ⟨q'.lhs, q.lhs⟩
  let r ← normalize n ⟨q.rhs, q'.rhs⟩
  pure (Cert.trans l (Cert.trans c r))

/-- Compose two equations, one for each argument of composition. -/
def compCong (n : ℕ) (f g : Eqn) (cf cg : Tree) : Build Tree := do
  let ty ← typed n (comp f.lhs g.lhs)
  pure (Cert.cong ty.dfd [cf, cg])

/-- Postcompose an equation with an arrow. -/
def postcompose (n : ℕ) (f : Tree) (q : Eqn) (c : Tree) : Build Tree := do
  let ty ← typed n f
  compCong n (dfd f) q ty.dfd c

/-- Precompose an equation with an arrow. -/
def precompose (n : ℕ) (q : Eqn) (c : Tree) (g : Tree) : Build Tree := do
  let ty ← typed n g
  compCong n q (dfd g) c ty.dfd

/-- The index of an equalizer axiom. -/
def equalizerAxiom (i : ℕ) : ℕ :=
  Prover.axIdx (Prover.beforeProduct ++ [productAxioms]) i

/-- The equation imposed by a truth subobject's inclusion. -/
def truthEquation (n : ℕ) (p : Tree) : Build (Eqn × Tree) := do
  let _ ← typed n (eqz p (comp tru (bang (dom p))))
  run n (Prover.inst (.ax (equalizerAxiom 7)) [p, comp tru (bang (dom p))])

/-- Construct the factorization through a truth subobject, given its equalizing equation.
Its typing is recorded explicitly because the equation is an arrow equation, beyond the
typing prover's inference from canonical objects. -/
def truthFactor (n : ℕ) (p k : Tree) (c : Tree) : Build (Tree × Tree) := do
  let q := comp tru (bang (dom p))
  let tp ← typed n p
  let tq ← typed n q
  let tk ← typed n k
  let te ← typed n (eqz p q)
  let args := [p, q, k]
  let ds := [tp.dfd, tq.dfd, tk.dfd]
  let l := truthLift p k
  let dl ← record (dfd l) (Cert.ax (equalizerAxiom 10) args ds [te.dfd, c])
  let ld ← record ⟨dom l, tk.lo⟩
    (Cert.trans (Cert.ax (equalizerAxiom 11) args ds [dl]) tk.loCert)
  let lc ← record ⟨cod l, te.lo⟩
    (Cert.trans (Cert.ax (equalizerAxiom 12) args ds [dl]) te.loCert)
  run n (Prover.memoize ⟨l, arr, dl, tk.lo, ld, te.lo, lc⟩)
  let e ← record ⟨comp (truthIncl p) l, k⟩ (Cert.ax (equalizerAxiom 13) args ds [dl])
  pure (l, e)

/-- A truth subobject and the equations that its defining predicates hold on it. -/
structure Subobject where
  /-- The subobject's domain. -/
  domain : Tree
  /-- Its inclusion in the context object. -/
  inclusion : Tree
  /-- Each defining predicate, with its equation to truth after the inclusion. -/
  facts : List (Tree × Tree)

/-- Intersect with one predicate's truth subobject, transporting the preceding equations. -/
def intersect (n : ℕ) (s : Subobject) (H : Tree) : Build Subobject := do
  let p := comp H s.inclusion
  let i := truthIncl p
  let S := truthEq p
  let m := comp s.inclusion i
  let facts ← s.facts.mapM fun (h, c) ↦ do
    let q : Eqn := ⟨comp h s.inclusion, comp tru (bang s.domain)⟩
    let c ← precompose n q c i
    let q' : Eqn := ⟨comp h m, comp tru (bang S)⟩
    let c ← transport n ⟨comp q.lhs i, comp q.rhs i⟩ c q'
    return (h, ← record q' c)
  let (q, c) ← truthEquation n p
  let q' : Eqn := ⟨comp H m, comp tru (bang S)⟩
  let c ← transport n q c q'
  let c ← record q' c
  pure ⟨S, m, facts ++ [(H, c)]⟩

/-- Construct a truth subobject, with certificates for all of its defining predicates. -/
def subobject (n : ℕ) (X : Tree) (Hs : List Tree) : Build Subobject :=
  Hs.foldlM (intersect n) ⟨X, idt X, []⟩

/-- A factorization of an inclusion through the subobject constructed so far. -/
structure Factor where
  /-- The intermediate inclusion. -/
  inclusion : Tree
  /-- The factor from the new subobject into the intermediate one. -/
  lift : Tree
  /-- The equation of the inclusion after the factor with the new inclusion. -/
  equation : Tree

/-- Factor through one more predicate, whose truth on the new subobject has been proved. -/
def factorStep (n : ℕ) (s : Subobject) (f : Factor) (H : Tree) : Build Factor := do
  let some (_, hc) := s.facts.find? (fun e ↦ e.1 == H) | failure
  let p := comp H f.inclusion
  let q := comp tru (bang (dom p))
  let he ← postcompose n H ⟨comp f.inclusion f.lift, s.inclusion⟩ f.equation
  let he := Cert.trans he hc
  let he ← transport n
    ⟨comp H (comp f.inclusion f.lift), comp tru (bang s.domain)⟩ he
    ⟨comp p f.lift, comp q f.lift⟩
  let (k, hk) ← truthFactor n p f.lift he
  let h ← postcompose n f.inclusion ⟨comp (truthIncl p) k, f.lift⟩ hk
  let m := comp f.inclusion (truthIncl p)
  let q' : Eqn := ⟨comp m k, s.inclusion⟩
  let h ← transport n ⟨comp f.inclusion (comp (truthIncl p) k), s.inclusion⟩
    (Cert.trans h f.equation) q'
  pure ⟨m, k, ← record q' h⟩

/-- Factor the new inclusion through the original hypotheses' truth subobject. -/
def factor (n : ℕ) (X : Tree) (s : Subobject) (Hs : List Tree) : Build Factor := do
  let h ← normalize n ⟨comp (idt X) s.inclusion, s.inclusion⟩
  Hs.foldlM (factorStep n s) ⟨idt X, s.inclusion, h⟩

/-- Transport one side of the original sequent along the factorization. -/
def sideEquation (n : ℕ) (s : Subobject) (f : Factor) (arrow oldSide newSide : Tree) :
    Build Tree := do
  let c ← postcompose n arrow ⟨comp f.inclusion f.lift, s.inclusion⟩ f.equation
  transport n ⟨comp arrow (comp f.inclusion f.lift), comp arrow s.inclusion⟩ c
    ⟨comp oldSide f.lift, newSide⟩

/-- Compose the original equation with the factor from the enlarged list of hypotheses. -/
def weakenProof (G : Globals) (a : Thm) (Φ : List Term) : Build Tree := do
  let n := a.arity
  let X := ctxObj a.ctx
  let s ← subobject n X (Φ.map (a.arrow G))
  let f ← factor n X s (a.hyps.map (a.arrow G))
  let old := (a.seq G).concl
  let target := ({ a with hyps := Φ }.seq G).concl
  let arrows := ({ a with hyps := [] }.seq G).concl
  let l ← sideEquation n s f arrows.lhs old.lhs target.lhs
  let r ← sideEquation n s f arrows.rhs old.rhs target.rhs
  let c ← precompose n old (Cert.hyp 0) f.lift
  pure (Cert.trans (Cert.symm l) (Cert.trans c r))

/-- Reindex certificate hypotheses, leaving the terms of axiom and theorem instances intact.
The second premise of a cut has its own new hypothesis at index zero. -/
def reindex (T : Theory) (E : Array Seq) : Tree → (ℕ → ℕ) → Tree :=
  RoseTree.para fun l cs ρ ↦
    let original := RoseTree.node l (cs.map Prod.fst)
    match l, cs with
    | PartialHorn.Rule.hyp, [(i, _)] => Cert.hyp (ρ i.label)
    | PartialHorn.Rule.refl, _ => original
    | PartialHorn.Rule.strict, [(i, _), (_, p)] => Cert.strict i.label (p ρ)
    | PartialHorn.Rule.cut, [(_, p), (_, q)] =>
      Cert.cut (p ρ) (q (fun i ↦ match i with | 0 => 0 | k + 1 => ρ k + 1))
    | PartialHorn.Rule.ax, (i, _) :: ps | PartialHorn.Rule.thm, (i, _) :: ps =>
      let a := if l == PartialHorn.Rule.ax then T.axioms[i.label]? else E[i.label]?
      let n := (a.map fun a ↦ a.ctx.length).getD 0
      RoseTree.node l (i :: (ps.take n).map Prod.fst ++ (ps.drop n).map fun c ↦ c.2 ρ)
    | _, _ => RoseTree.node l (cs.map fun c ↦ c.2 ρ)

/-- Assemble equations numbered in insertion order as cuts, whose hypotheses are prepended. -/
def assemble (T : Theory) (E : Array Seq) (cs : List Tree) (p : Tree) : Tree :=
  (cs.zipIdx).foldr (fun (c, n) p ↦ Cert.cut (reindex T E c (fun i ↦ n - 1 - i)) p)
    (reindex T E p (fun i ↦ cs.length - 1 - i))

/-- Weaken an embedded certificate to additional hypotheses in the same context. The returned
certificate is checked against the resulting sequent in the original environment. -/
def weaken (G : Globals) (E : Array Entry) (a : Thm) (Φ : List Term) (c : Tree) : Option Tree := do
  if !Internal.certifies G E c (a.seq G) then none else do
    let cds ← compileDefs G
    let s : State := ⟨[(a.seq G).concl], [c], {
      dev := #[], defs := cds, sig := sig ++ cds.map (fun d ↦ (d.ctx, d.sort)),
      localProofs := true }⟩
    let (p, s) ← (weakenProof G a Φ).run s
    let p := assemble (ext cds) (E.map (Entry.seq G)) s.cuts p
    if Internal.certifies G E p ({ a with hyps := Φ }.seq G) then some p else none

end Geb.FreeTopos.Internal.ProofHoles.Sequent

end
