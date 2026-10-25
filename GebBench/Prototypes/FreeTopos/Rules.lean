/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebBench.Prototypes.FreeTopos.TranslationProofs
public import GebTests.Prototypes.FreeTopos.Stored

set_option doc.verso true in
/-!
# The stored derivations' nodes by rule

For each certificate of {lit}`bootstrap/certificates/`, the nodes of the derivations of the
theorems its development declares, counted by rule, and the rewritings among them: the
derivations a rule proving a formula takes as premises that rewrite a term, the two of
{lit}`join` and the first of {lit}`conv` and of {lit}`convFrom`. A rewriting is built of the
identity, composition, congruence and the rewriting rules at a term's root, and is a derivation
that a checker with a step of conversion
({lit}`Geb.FreeTopos.Internal.convCheck`) can replace by one step where the conversion it
computes reaches the rewriting's result. The measurement decides which rules that step carries
(the bootstrap chapter's section on the next phase).

A derivation is counted as a tree, a node once for each path to it from the root, which is the
number of steps the checker's fold takes; the certificate stores the table of its distinct nodes,
whose length is counted beside it. The terms the rules name are counted apart, as
{name}`GebBench.Prototypes.FreeTopos.TranslationProofs.derivSize` counts them.

## Main definitions

* {lit}`ruleName` — a rule's name.
* {lit}`Counts`, {lit}`visit` — the counts of a derivation's nodes by rule, within rewritings and
  in all, and their accumulation over a derivation.
* {lit}`measure` — the counts of a development's derivations.
* {lit}`run` — the measurements of the certificates.

## Tags

internal language, derivation, conversion, certificate, measurement
-/

set_option doc.verso true

@[expose] public section

namespace GebBench.Prototypes.FreeTopos.Rules

open Geb Geb.FreeTopos
open GebTests.Prototypes.FreeTopos
open GebTests.Prototypes.FreeTopos.Translation (sizeM)
open GebBench.Prototypes.FreeTopos.TranslationProofs (ruleTerms)
open Internal (Rule Deriv Decl)

/-- A rule's name, its constructor's. -/
def ruleName : Rule → String
  | .refl => "refl" | .trans => "trans" | .cong => "cong" | .beta => "beta"
  | .fstPair => "fstPair" | .sndPair => "sndPair" | .pairEta => "pairEta"
  | .unitEta => "unitEta" | .delta => "delta" | .natZero _ => "natZero"
  | .natSucc _ => "natSucc" | .listNil _ => "listNil" | .listCons _ => "listCons"
  | .roseNode _ _ _ => "roseNode" | .caseInl _ _ => "caseInl" | .caseInr _ _ => "caseInr"
  | .thm _ _ _ _ => "thm" | .rwHyp _ _ => "rwHyp" | .join => "join"
  | .natInd _ _ _ => "natInd" | .listInd _ _ _ => "listInd" | .hyp _ => "hyp"
  | .cut _ => "cut" | .conv => "conv" | .convFrom _ => "convFrom" | .propExt => "propExt"
  | .funExt => "funExt" | .apply _ _ _ => "apply" | .natIndHyp _ _ => "natIndHyp"
  | .listIndHyp _ _ => "listIndHyp" | .cert _ => "cert" | .certSeq _ => "certSeq"
  | .roseInd _ _ _ _ => "roseInd" | .roseIndHyp _ _ _ => "roseIndHyp"
  | .coprodInd _ _ => "coprodInd" | .zeroInd _ => "zeroInd" | .quotInd _ _ => "quotInd"

/-- The positions of the premises of a rule that are rewritings: both of {lit}`join`'s, and the
first of {lit}`conv`'s and of {lit}`convFrom`'s. -/
def rewritingPremises : Rule → List ℕ
  | .join => [0, 1]
  | .conv | .convFrom _ => [0]
  | _ => []

/-- An array with its entry at an index increased by {lit}`k`, extended by zeros to reach it. -/
def bump (a : Array ℕ) (i k : ℕ) : Array ℕ :=
  (if i < a.size then a else a ++ Array.replicate (i + 1 - a.size) 0).modify i (· + k)

/-- The counts of derivations' nodes. -/
structure Counts where
  /-- The nodes of each rule, by the rule's position among the rules. -/
  nodes : Array ℕ := #[]
  /-- The nodes of each rule within rewritings, by the rule's position. -/
  inRewritings : Array ℕ := #[]
  /-- The name of the rule of each position counted. -/
  names : Array String := #[]
  /-- The nodes of the terms the rules of each position name. -/
  terms : Array ℕ := #[]
  /-- The rewritings. -/
  rewritings : ℕ := 0
  /-- The nodes of the largest rewriting. -/
  largest : ℕ := 0

/-- The counts with a node of a rule added, within a rewriting when {lit}`inside`. -/
def Counts.node (s : Counts) (l : Rule) (inside : Bool) : Counts :=
  let k := (Stored.ruleData l).1
  let names := if k < s.names.size then s.names else
    s.names ++ Array.replicate (k + 1 - s.names.size) ""
  { s with
    nodes := bump s.nodes k 1
    inRewritings := if inside then bump s.inRewritings k 1 else s.inRewritings
    names := if names[k]!.isEmpty then names.set! k (ruleName l) else names
    terms := bump s.terms k ((ruleTerms l).map sizeM).sum }

/-- The counts with a rewriting of {lit}`n` nodes added. -/
def Counts.rewriting (s : Counts) (n : ℕ) : Counts :=
  { s with rewritings := s.rewritings + 1, largest := max s.largest n }

/-- The accumulation of a derivation's counts, within a rewriting when the argument holds: the
derivation's nodes, each premise of a rule that is a rewriting, outside one, counted as one. The
result is the derivation's number of nodes. -/
def visit : Deriv → Bool → StateM Counts ℕ :=
  RoseTree.elim fun l cs inside ↦ do
    modify (·.node l inside)
    let ns ← cs.zipIdx.mapM fun (c, i) ↦ do
      let starts := !inside && (rewritingPremises l).contains i
      let n ← c (inside || starts)
      if starts then modify (·.rewriting n)
      pure n
    pure (1 + ns.sum)

/-- The counts of a development's derivations, those of its declarations of theorems. -/
def measure (ds : List Decl) : Counts :=
  ((ds.filterMap fun | .language _ d => some d | _ => none).mapM (visit · false)).run {} |>.2

/-- The number of distinct nodes the table a certificate's text stores has, its first number. -/
def tableNodes (text : String) : ℕ := ((Stored.natsOfText text).bind List.head?).getD 0

/-- The rows of a certificate: its summary, and its nodes of each rule counted. -/
def rows (name : String) (tab : ℕ) (decls : ℕ) (s : Counts) : String × List String :=
  let total := s.nodes.foldl (· + ·) 0
  let within := s.inRewritings.foldl (· + ·) 0
  let terms := s.terms.foldl (· + ·) 0
  let row (xs : List String) : String := ",".intercalate xs
  (row ([name] ++ [tab, decls, total, terms, s.rewritings, within, s.largest].map toString),
    (List.range s.nodes.size).filterMap fun k ↦
      if s.nodes[k]! = 0 then none else
        some (row ([name, s.names[k]!] ++
          [s.nodes[k]!, s.inRewritings.getD k 0, s.terms.getD k 0].map toString)))

/-- The counts of all the certificates together. -/
def Counts.add (s t : Counts) : Counts where
  nodes := (List.range (max s.nodes.size t.nodes.size)).foldl
    (fun a k ↦ bump a k (t.nodes.getD k 0)) s.nodes
  inRewritings := (List.range (max s.inRewritings.size t.inRewritings.size)).foldl
    (fun a k ↦ bump a k (t.inRewritings.getD k 0)) s.inRewritings
  names := (List.range (max s.names.size t.names.size)).toArray.map fun k ↦
    let n := s.names.getD k ""
    if n.isEmpty then t.names.getD k "" else n
  terms := (List.range (max s.terms.size t.terms.size)).foldl
    (fun a k ↦ bump a k (t.terms.getD k 0)) s.terms
  rewritings := s.rewritings + t.rewritings
  largest := max s.largest t.largest

/-- The measurements of the certificates of a directory, printed: a row for each certificate, of
its table's distinct nodes, its declarations, its derivations' nodes, the nodes of the terms their
rules name, its rewritings, their nodes and the nodes of the largest; then a row for each
certificate and rule, of the rule's nodes, those within rewritings and the nodes of the terms the
rule's nodes name; each table ending in the row of all the certificates together. An error when a
certificate does not read. -/
def report (dir : System.FilePath) : IO Unit := do
  let entries ← dir.readDir
  let files := (entries.filter (·.path.extension == some "cert")).qsort (·.fileName < ·.fileName)
  let mut summaries : Array String := #[]
  let mut byRule : Array String := #[]
  let mut all : Counts := {}
  let mut tabs := 0
  let mut decls := 0
  for e in files do
    let text ← IO.FS.readFile e.path
    let some ds := Stored.declsOfText text
      | throw (IO.userError s!"{e.fileName}: the certificate does not read")
    let s := measure ds
    let name := e.path.fileStem.getD e.fileName
    let (summary, rs) := rows name (tableNodes text) ds.length s
    summaries := summaries.push summary
    byRule := byRule ++ rs.toArray
    all := all.add s
    tabs := tabs + tableNodes text
    decls := decls + ds.length
  let (summary, rs) := rows "all" tabs decls all
  IO.println ("certificate,table_nodes,declarations,derivation_nodes,term_nodes,rewritings," ++
    "rewriting_nodes,largest_rewriting")
  for r in summaries.push summary do IO.println r
  IO.println "certificate,rule,nodes,in_rewritings,term_nodes"
  for r in byRule ++ rs.toArray do IO.println r

/-- The measurements of the certificates of {lit}`bootstrap/certificates/`, read from the working
directory. -/
def run : IO Unit := report ("bootstrap" / "certificates")

end GebBench.Prototypes.FreeTopos.Rules

end
