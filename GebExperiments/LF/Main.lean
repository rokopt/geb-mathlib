/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebExperiments.LF.Bridge
public import Geb.Prototypes.LF.Topos
public import Geb.Prototypes.FreeTopos.Internal.Prove

/-!
# Canonical on the internal language of a topos

Goals of the fragment of the internal language represented by `Geb.LF.Topos.sig`, each given to
Canonical in two regimes: pure LF, the computation rules derivation rules among the constants; and
modulo the rewrite rules `Geb.LF.Topos.rules`, the derivation rules they make redundant withheld.
Each regime is run with every constant offered and with only those relevant to the goal
(`GebExperiments.LF.relevant`), from the core of the types, terms, formulas and proofs.
Each term Canonical returns is translated back to canonical LF and checked by the checker of the
regime, `Geb.LF.Checks` or `Geb.LF.ChecksMod`, and then decoded to a certificate of the internal
language and checked: a term of pure LF to a derivation (`Geb.LF.Topos.decPf`), checked by the
base checker (`Geb.FreeTopos.Internal.Thm.checks`), and a term found modulo the rules to a
certificate with steps of conversion (`Geb.LF.Topos.decPfMod`), checked by the conversion checker
(`Geb.FreeTopos.Internal.Thm.convChecks`). The decoding applies to a goal whose outermost
parameters are of `tp`, the object variables, and whose others are term variables and
hypotheses; a hypothesis's formula is weakened past the parameters after it. Further goals are
posed in the signatures of developments (`Geb.LF.Topos.devSig`): that of the theorems of lemmas
(`GebExperiments.LF.lemmas`) on a definition of addition (`GebExperiments.LF.addDefn`), whose
constants past the signature are the definition, its unfolding and the lemmas' theorems, each
applied as the language applies it; and that of the quotient of the pairs of natural numbers by
the relation of equal sums, with the descents of the sum and of the sum with zero added
(`GebExperiments.LF.quotDecls`), whose goals are the declarations of theorems of the internal
language. The program
prints, for each goal and regime, whether a term was found, the time taken, the term, and both
checkers' verdicts.
Its first argument is the timeout in seconds of each search, and a second, if given, restricts
the goals to those whose names contain it.

## Tags

logical framework, LF, Canonical, Mitchell–Bénabou language, experiment
-/

@[expose] public section

namespace GebExperiments.LF

open Geb Geb.LF Geb.LF.Topos
open Expr (arrow pi)

/-- The names of the constants of `Geb.LF.Topos.sig`. -/
def toposNames : List String :=
  ["tp", "one", "prod", "exp", "omega", "nat", "tm", "star", "pair", "fst", "snd", "lam", "app",
    "zero", "succ", "natRec", "eq", "pf", "refl", "leib", "beta", "fstPair", "sndPair", "pairEta",
    "unitEta", "natZero", "natSucc", "funExt", "propExt", "natInd", "list", "nilAt", "cons",
    "listRec", "listNil", "listCons", "listInd", "rose", "node", "roseRec", "roseNode", "roseInd",
    "lrose", "lnode", "lroseRec", "lroseNode", "lroseInd", "cong", "coprod", "initial", "inl",
    "inr", "case", "caseInl", "caseInr", "coprodInd", "exfalso"]

/-- The constants the rewrite rules make redundant: `beta`, `fstPair`, `sndPair`, `natZero`,
`natSucc`, `listNil`, `listCons`, `roseNode`, `lroseNode`, `caseInl` and `caseInr`. -/
def redundantModRules : List ℕ := [20, 21, 22, 25, 26, 34, 35, 40, 45, 53, 54]

/-- The core of the constants relevant to every goal: the kind of types, the families of terms
and of proofs, equality, the subobject classifier and the terminal object with its element. -/
def coreConsts : List ℕ := [0, 1, 4, 6, 7, 16, 17]

/-- A goal: a name and a closed type to inhabit. -/
structure Goal where
  /-- The goal's name. -/
  name : String
  /-- The type to inhabit, in the empty context. -/
  type : Expr

/-- The addition of `n` to `m`, the fold of `n` from `m` by the successor. -/
def add (m n : Expr) : Expr := natRec nat m (Expr.lam (succ (v 0))) n

/-- The construction of a list of natural numbers as a step of a fold:
`λ h r. cons nat (pair h r)`. -/
def consLam : Expr := Expr.lam (Expr.lam (cons nat (pair nat (list nat) (v 1) (v 0))))

/-- The concatenation of the lists of natural numbers `xs` and `ys`, the right fold of `xs` by
construction from `ys`. -/
def append (xs ys : Expr) : Expr := listRec nat (list nat) ys consLam xs

/-- The right fold of the list of natural numbers `xs` by construction from the empty list. -/
def foldrId (xs : Expr) : Expr := listRec nat (list nat) (nil nat) consLam xs

/-- The type of the pairs of an element and a list of natural numbers. -/
def natCell : Expr := prod nat (list nat)

/-- The goals. -/
def goals : List Goal :=
  [ ⟨"symmetry", pi tp (pi (tm (v 0)) (pi (tm (v 1))
      (arrow (pf (eq (v 2) (v 1) (v 0))) (pf (eq (v 2) (v 0) (v 1))))))⟩,
    ⟨"transitivity", pi tp (pi (tm (v 0)) (pi (tm (v 1)) (pi (tm (v 2))
      (arrow (pf (eq (v 3) (v 2) (v 1)))
        (arrow (pf (eq (v 3) (v 1) (v 0))) (pf (eq (v 3) (v 2) (v 0))))))))⟩,
    ⟨"congruence of succ", pi (tm nat) (pi (tm nat)
      (arrow (pf (eq nat (v 1) (v 0))) (pf (eq nat (succ (v 1)) (succ (v 0))))))⟩,
    ⟨"fold at one", pi tp (pi (tm (v 0)) (pi (arrow (tm (v 1)) (tm (v 1)))
      (pf (eq (v 2) (natRec (v 2) (v 1) (Expr.lam (Expr.var 1 [v 0])) (succ zero))
        (Expr.var 0 [v 1])))))⟩,
    ⟨"n + 0 = n", pi (tm nat) (pf (eq nat (add (v 0) zero) (v 0)))⟩,
    ⟨"m + succ n = succ (m + n)", pi (tm nat) (pi (tm nat)
      (pf (eq nat (add (v 1) (succ (v 0))) (succ (add (v 1) (v 0))))))⟩,
    ⟨"0 + n = n", pi (tm nat) (pf (eq nat (add zero (v 0)) (v 0)))⟩,
    ⟨"succ m + n = succ (m + n)", pi (tm nat) (pi (tm nat)
      (pf (eq nat (add (succ (v 1)) (v 0)) (succ (add (v 1) (v 0))))))⟩,
    ⟨"η of the identity's application", pf (eq (exp nat nat)
      (lam nat nat (Expr.lam (v 0)))
      (lam nat nat (Expr.lam (app nat nat (lam nat nat (Expr.lam (v 0))) (v 0)))))⟩,
    ⟨"foldr cons nil xs = xs", pi (tm (list nat)) (pf (eq (list nat) (foldrId (v 0)) (v 0)))⟩,
    ⟨"foldr cons nil xs = xs, for every element type", pi tp (pi (tm (list (v 0)))
      (pf (eq (list (v 1)) (listRec (v 1) (list (v 1)) (nil (v 1))
        (Expr.lam (Expr.lam (cons (v 3) (pair (v 3) (list (v 3)) (v 1) (v 0))))) (v 0)) (v 0))))⟩,
    -- the uniqueness of the right fold, its hypothesis at a construction an equation of functions
    ⟨"uniqueness of the right fold", pi (tm nat) (pi (tm (exp nat (exp nat nat)))
      (pi (tm (exp (list nat) nat))
        (arrow (pf (eq nat (app (list nat) nat (v 0) (nil nat)) (v 2)))
          (arrow (pf (eq (exp natCell nat)
              (lam natCell nat (Expr.lam (app (list nat) nat (v 1) (cons nat (v 0)))))
              (lam natCell nat (Expr.lam (app nat nat
                (app nat (exp nat nat) (v 2) (fst nat (list nat) (v 0)))
                (app (list nat) nat (v 1) (snd nat (list nat) (v 0))))))))
            (pi (tm (list nat)) (pf (eq nat (app (list nat) nat (v 1) (v 0))
              (listRec nat nat (v 3)
                (Expr.lam (Expr.lam (app nat nat (app nat (exp nat nat) (v 4) (v 1)) (v 0))))
                (v 0)))))))))⟩,
    ⟨"associativity of appending", pi (tm (list nat)) (pi (tm (list nat)) (pi (tm (list nat))
      (pf (eq (list nat) (append (append (v 2) (v 1)) (v 0))
        (append (v 2) (append (v 1) (v 0)))))))⟩ ]

/-- The primitive arrows of the internal language that the signature's constants stand for. -/
def toposGlobals : FreeTopos.Internal.Globals :=
  ⟨[FreeTopos.Internal.zeroPrim, FreeTopos.Internal.succPrim, FreeTopos.Internal.nilPrim,
    FreeTopos.Internal.consPrim, FreeTopos.Internal.nodePrim, FreeTopos.Internal.lnodePrim,
    FreeTopos.Internal.inlPrim, FreeTopos.Internal.inrPrim, FreeTopos.Internal.casePrim], [], 0⟩

/-- The indices of the primitive arrows of `toposGlobals`. -/
def toposIdx : PrimIdx := ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, []⟩

/-- The right fold of a list of elements of the type of the LF variable one outside it by
construction from the empty list. -/
def foldrIdPoly (xs : Expr) : Expr :=
  listRec (v 1) (list (v 1)) (nil (v 1))
    (Expr.lam (Expr.lam (cons (v 3) (pair (v 3) (list (v 3)) (v 1) (v 0))))) xs

/-- The lemmas, goals whose theorems the goals posed in the extended signature may apply, each a
constant past `Geb.LF.Topos.sig` (`Geb.LF.Topos.thmTy`). -/
def lemmas : List Goal :=
  [⟨"foldr cons nil xs = xs, for every element type", pi tp (pi (tm (list (v 0)))
    (pf (eq (list (v 1)) (foldrIdPoly (v 0)) (v 0))))⟩]

/-- The goals posed in the signature extended by the lemmas' theorems. -/
def devGoals : List Goal :=
  [⟨"foldr cons nil applied twice, by the lemma", pi (tm (list nat))
      (pf (eq (list nat) (foldrId (foldrId (v 0))) (v 0)))⟩,
    ⟨"foldr cons nil applied twice, for every element type, by the lemma", pi tp
      (pi (tm (list (v 0))) (pf (eq (list (v 1)) (foldrIdPoly (foldrIdPoly (v 0))) (v 0))))⟩]

/-- One step of the parameters of a type and its body, the parameters the outermost first. -/
def telescopeStep (l : Label) (cs : List (Expr × (List Expr × Expr))) : List Expr × Expr :=
  match l, cs with
    | .pi, [(a, _), (_, (as, body))] => (a :: as, body)
    | l, cs => ([], RoseTree.node l (cs.map (·.1)))

/-- The parameters of a type, the outermost first, and its body. -/
def telescope : Expr → List Expr × Expr := RoseTree.para telescopeStep

/-- The body of an LF abstraction. -/
def lfBody (e : Expr) : Option Expr := match e.label, e.children with
  | .lam, [b] => some b
  | _, _ => none

/-- Whether a parameter is of `tp`, an object variable. -/
def isTpParam (p : Expr) : Bool := match p.label, p.children with
  | .app (.const 0), [] => true
  | _, _ => false

/-- The theorem of the internal language that a goal states, with the environment of its
parameters: its outermost parameters of `tp` are the theorem's object variables, a parameter of
`tm A` inside them is a variable of the type `A` decodes to, at the offset of the parameters
of terms and proofs before it, and one of `pf F` a hypothesis, `F` decoded after its weakening
past the parameters after it. A goal with a parameter of another type, or of `tp` inside one of
`tm` or `pf`, or whose body is not a family of proofs, states none. The goal's constants are
those of the indices `k`. -/
def internalThm (k : PrimIdx) (goal : Expr) :
    Option (List (Option ℕ) × FreeTopos.Internal.Thm) := do
  let (ps, body) := telescope goal
  let F ← match body.label, body.children with
    | .app (.const 17), [F] => some F
    | _, _ => none
  let nObj := (ps.takeWhile isTpParam).length
  let ps := ps.drop nObj
  let n := ps.length
  let (env, Γ, Φ) ← ps.zipIdx.foldlM (init := (([] : List (Option ℕ)), ([] : List _),
      ([] : List (Expr × ℕ)))) fun (env, Γ, Φ) (p, j) ↦
    match p.label, p.children with
      | .app (.const 6), [A] => do pure (none :: env, (← decTy k env.length A) :: Γ, Φ)
      | .app (.const 17), [P] => some (some Φ.length :: env, Γ, (P, n - 1 - j) :: Φ)
      | _, _ => none
  let hyps ← Φ.reverse.mapM fun (P, i) ↦ termOf k env (Expr.rename P (· + (i + 1)))
  pure (env, ⟨nObj, Γ, hyps, ← termOf k env F⟩)

/-- The theorems the lemmas state. -/
def lemmaThms : List FreeTopos.Internal.Thm :=
  lemmas.filterMap fun g ↦ (internalThm toposIdx g.type).map (·.2)

/-- The entries of the lemmas' theorems, in order. -/
def lemmaEntries : Array FreeTopos.Internal.Entry := (lemmaThms.map .language).toArray

/-- The addition of the second parameter to the first, the fold of the second from the first by
the successor. -/
def addDefn : FreeTopos.Internal.Defn :=
  ⟨0, [FreeTopos.nat, FreeTopos.nat], FreeTopos.nat,
    FreeTopos.Internal.Term.natRec (FreeTopos.Internal.Term.var 1)
      (FreeTopos.Internal.Term.arr toposIdx.succ [] (FreeTopos.Internal.Term.var 0))
      (FreeTopos.Internal.Term.var 0)⟩

/-- The constants of `toposGlobals` with the definition `addDefn`, the object definitions
numbered past the signature of the combinators. -/
def devGlobals : FreeTopos.Internal.Globals :=
  { toposGlobals with defs := [.language addDefn], base := FreeTopos.sig.length }

/-- The name of a constant of the table of a development. -/
def extName : ExtConst → String
  | .obj op _ => s!"obj{op}"
  | .tm (.defn k) _ _ => s!"defn{k}"
  | .tm (.arr k) _ _ => s!"arr{k}"
  | .delta k _ _ => s!"delta{k}"
  | .quotInd k _ _ => s!"quotInd{k}"
  | .thm j _ _ => s!"thm{j}"

/-- A development: the constants and the environment after it. -/
structure Dev where
  /-- The constants after the development. -/
  G : FreeTopos.Internal.Globals
  /-- The environment after the development. -/
  E : Array FreeTopos.Internal.Entry

/-- The table of a development (`Geb.LF.Topos.devIdx`), from the indices `toposIdx`. -/
def Dev.idx (d : Dev) : PrimIdx := devIdx toposIdx d.G d.E

/-- The signature of a development (`Geb.LF.Topos.devSig`), where it is formed. -/
def Dev.sig? (d : Dev) : Option Sig := devSig toposIdx d.G d.E

/-- The names of the constants of the signature of a development. -/
def Dev.names (d : Dev) : List String := toposNames ++ d.idx.ext.map extName

/-- The application of a constant of the table of a development, in its signature. -/
def Dev.const (d : Dev) (c : ExtConst) (args : List Expr) : Expr :=
  Expr.const (sig.length + (c.find? d.idx.ext).getD d.idx.ext.length) args

/-- The goal of inhabiting the declaration of a theorem of the internal language in the
signature of a development. -/
def Dev.thmGoal (d : Dev) (name : String) (a : FreeTopos.Internal.Thm) : Option Goal :=
  (thmTy d.G d.idx a).map (⟨name, ·⟩)

/-- The development of no declarations on `toposGlobals`, whose signature is
`Geb.LF.Topos.sig`. -/
def baseDev : Dev := ⟨toposGlobals, #[]⟩

/-- The development of the lemmas' theorems on `devGlobals`. -/
def lemmaDev : Dev := ⟨devGlobals, lemmaEntries⟩

/-- The application of the definition `addDefn` in the signature of `lemmaDev`. -/
def addC (m n : Expr) : Expr := lemmaDev.const (.tm (.defn 0) 0 2) [m, n]

/-- The goals posed in the extended signature that apply the definition `addDefn`. -/
def defGoals : List Goal :=
  [⟨"add m n unfolds, by the definition", pi (tm nat) (pi (tm nat)
      (pf (eq nat (addC (v 1) (v 0)) (add (v 1) (v 0)))))⟩,
    ⟨"add m 0 = m, by the definition", pi (tm nat) (pf (eq nat (addC (v 0) zero) (v 0)))⟩]

section Quotient

open FreeTopos.Internal (Term Decl)

/-- The pairs of natural numbers. -/
def natPair : PartialHorn.Tree := FreeTopos.prod FreeTopos.nat FreeTopos.nat

/-- The sum of two terms of the natural numbers, by the definition `addDefn`. -/
def addT (m n : Term) : Term := Term.defn 0 [] [n, m]

/-- The sum of the components of the pair that is the variable of an index. -/
def sumT (i : ℕ) : Term := addT (Term.fst (Term.var i)) (Term.snd (Term.var i))

/-- The sum of the components of the pair that is the variable of an index, with zero added. -/
def sum0T (i : ℕ) : Term := addT (sumT i) (Term.arr toposIdx.zero [] Term.star)

/-- The relation of equal sums, between the pairs that are the innermost two variables. -/
def sameSum : Term := Term.eq (sumT 1) (sumT 0)

/-- The development of the quotient of the pairs of natural numbers by the relation of equal
sums on `devGlobals`: the quotient, with the theorem that related pairs have equal images; the
respect of the relation by the sum, the relation itself, and the sum's descent; and the respect
of the relation by the sum with zero added, by normalization under the relation, and its
descent. -/
def quotDecls : Option (List Decl) := do
  let ds : List Decl := [.quotient 0 natPair sameSum,
    .language ⟨0, [natPair, natPair], [sameSum], sameSum⟩ (RoseTree.node (.hyp 0) []),
    .descent 9 FreeTopos.nat (sumT 0) 1]
  let (G, E) ← FreeTopos.Internal.checkDev devGlobals #[] ds
  let d ← FreeTopos.Internal.byNorm G E 0 [.hyp 0] 16 [natPair, natPair] [sameSum] (sum0T 1)
    (sum0T 0)
  pure (ds ++ [.language ⟨0, [natPair, natPair], [sameSum], Term.eq (sum0T 1) (sum0T 0)⟩ d,
    .descent 9 FreeTopos.nat (sum0T 0) 3])

/-- The development `quotDecls`, where it checks. -/
def quotDev? : Option Dev :=
  quotDecls.bind fun ds ↦ (FreeTopos.Internal.checkDev devGlobals #[] ds).map fun (G, E) ↦ ⟨G, E⟩

/-- The development `quotDecls`, or `lemmaDev` where it does not check. -/
def quotDev : Dev := quotDev?.getD lemmaDev

/-- The quotient, the object definition after the definition `addDefn`. -/
def quotT : PartialHorn.Tree := PartialHorn.op (FreeTopos.sig.length + 1) []

/-- The projection to the quotient, the primitive arrow after those of `toposGlobals`. -/
def qT (t : Term) : Term := Term.arr 9 [] t

/-- The descent of the sum. -/
def descT (t : Term) : Term := Term.arr 10 [] t

/-- The descent of the sum with zero added. -/
def desc0T (t : Term) : Term := Term.arr 11 [] t

/-- The goals posed in the signature of the quotient's development, each the declaration of a
theorem of the internal language. -/
def quotGoals : List Goal := List.filterMap (fun (name, a) ↦ quotDev.thmGoal name a)
  [("the descent of the sum computes at an image",
      ⟨0, [natPair], [], Term.eq (descT (qT (Term.var 0))) (sumT 0)⟩),
    ("the descent of the sum at the image of (m, 0) is m",
      ⟨0, [FreeTopos.nat], [], Term.eq (descT (qT (Term.pair (Term.var 0)
        (Term.arr toposIdx.zero [] Term.star)))) (Term.var 0)⟩),
    ("a pair and the pair with zero added have one image",
      ⟨0, [FreeTopos.nat, FreeTopos.nat], [], Term.eq
        (qT (Term.pair (Term.var 1) (addT (Term.var 0) (Term.arr toposIdx.zero [] Term.star))))
        (qT (Term.pair (Term.var 1) (Term.var 0)))⟩),
    ("the descents agree on the quotient",
      ⟨0, [quotT], [], Term.eq (desc0T (Term.var 0)) (descT (Term.var 0))⟩)]

end Quotient

/-- The verdict of the internal language's checkers on a term found for a goal: the term's
abstractions over the goal's parameters removed, its body decoded in their environment and the
certificate checked against the goal's theorem, by the base checker for a term of pure LF and by
the conversion checker for one found modulo the rules. -/
def internalVerdict (G : FreeTopos.Internal.Globals) (k : PrimIdx)
    (E : Array FreeTopos.Internal.Entry) (modulo : Bool) (goal term : Expr) : String :=
  match internalThm k goal with
    | none => "outside the internal fragment"
    | some (env, thm) =>
      let body := (List.range (thm.arity + env.length)).foldlM (fun e _ ↦ lfBody e) term
      let verdict := if modulo then
          (body >>= fun b ↦ decPfMod k b env thm.hyps.length).map
            (thm.convChecks G E)
        else (body >>= fun b ↦ decPf k b env thm.hyps.length).map
            (thm.checks G E)
      match verdict with
        | none => "undecodable"
        | some true => "internal checks"
        | some false => "internal DOES NOT CHECK"

/-- The bound on the steps of normalization modulo the rules. -/
def fuel : ℕ := 64

/-- Run one goal in one regime, in the signature `S` of a development, printing the outcome. -/
def runGoal (timeout : UInt64) (d : Dev) (S : Sig) (g : Goal) (modulo select : Bool) :
    IO Unit := do
  let (names, G, k, E) := (d.names, d.G, d.idx, d.E)
  let rs := if modulo then rules else []
  let rel := relevant S 0 coreConsts g.type
  let usable := fun c ↦ !(modulo && redundantModRules.contains c) && (!select || rel c)
  let decl := problem g.name names S rs usable [] g.type
  let t₀ ← IO.monoMsNow
  let r ← Canonical.canonical decl timeout 1
  let t₁ ← IO.monoMsNow
  let regime := (if modulo then "modulo rules" else "pure LF") ++
    (if select then ", relevant constants" else "")
  match r.terms[0]? with
    | none => IO.println s!"{g.name} [{regime}]: not found in {t₁ - t₀} ms"
    | some t =>
      let verdict := match fromTerm names [] t with
        | none => "untranslatable"
        | some e =>
          let ok := if modulo then ChecksMod rules fuel S [] e g.type else Checks S [] e g.type
          (if ok then "checks" else "DOES NOT CHECK") ++ ", " ++
            internalVerdict G k E modulo g.type e
      IO.println s!"{g.name} [{regime}]: found in {t₁ - t₀} ms, {verdict}: {
        {t with lets := #[]}}"
  (← IO.getStdout).flush

/-- Run every goal in both regimes. -/
def main (args : List String) : IO UInt32 := do
  if toposNames.length != sig.length then
    IO.eprintln s!"{toposNames.length} names for {sig.length} constants"
    return 1
  if quotDev?.isNone then
    IO.eprintln "the quotient's development does not check"
    return 1
  if quotGoals.length != 4 then
    IO.eprintln "a goal of the quotient's development is not declared"
    return 1
  let timeout := (args.head? >>= String.toNat?).getD 10
  let chosen := fun gs : List Goal ↦ match args with
    | [_, part] => gs.filter fun (g : Goal) ↦ (g.name.splitOn part).length > 1
    | _ => gs
  for (d, gs) in [(baseDev, goals), (lemmaDev, devGoals ++ defGoals), (quotDev, quotGoals)] do
    let some S := d.sig?
      | IO.eprintln s!"the signature of a development is not formed"
        return 1
    for g in chosen gs do
      for modulo in [false, true] do
        for select in [false, true] do
          runGoal timeout.toUInt64 d S g modulo select
  return 0

end GebExperiments.LF

/-- The program's entry point. -/
def main (args : List String) : IO UInt32 := GebExperiments.LF.main args

end
