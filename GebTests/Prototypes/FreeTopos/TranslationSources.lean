/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.TranslationProofs -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.TranslationProofs -- shake: keep
public import GebTests.Prototypes.Stage0 -- shake: keep
public meta import GebTests.Prototypes.Stage0 -- shake: keep

set_option doc.verso true in
/-!
# The translation at programs compiled from their sources

The tests of the translation of kernel programs and of the proofs about them that read a
program's source: the programs the proofs in Gödel's T are about, the prelude, the reader and the
kernel's type checker written in the kernel's syntax, translate, each definition's translation
having, in the internal language, the translation of its kernel type, and the literals' cost of
that program is printed; and the development of each file of theorems
({lit}`GebTests.Prototypes.FreeTopos.TranslationProofs`) checks at the file's program, which the
stage-0 compiler's front end reads and expands. The module imports the stage-0 tests, whose
library depends on the sources read; the definitions the developments of the internal language
share are in the modules it imports, which read no source.

## Main definitions

* {lit}`Translation.kernelText` — the text of the prelude, the reader and the type checker.
* {lit}`Translation.translated` — a program's translation, from its text.
* {lit}`Translation.literalCost` — the sizes of the program and of its translation.
* {lit}`TranslationProofs.files` — the texts of the files, each the programs and the theorems'
  statements.
* {lit}`TranslationProofs.results` — the programs and theorems of the files.

## Tags

internal language, Gödel's T, translation, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Translation

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation
open scoped FinEnum
open Internal (Term NormRule)

/-- The text of the prelude, the reader and the kernel's type checker. -/
def kernelText : String := include_manifest "bootstrap/checker.manifest"

/-- A program's translation, from its text read by the seed: the kernel types of its globals and
the definitions of the internal language. -/
def translated (text : List Char) : Option (List Tree × List Internal.Defn) :=
  (Kernel.readProgram text).bind fun ds ↦ program (ds.map Prod.snd)

-- the program translates
#guard (translated kernelText.toList).isSome

-- each translated definition compiles, to the translation of its kernel type
#guard (translated kernelText.toList).any fun (gt, defs) ↦
  (Internal.compileDefs (globals defs)).isSome &&
    (gt.zip defs).all fun (A, d) ↦ ty A == some d.type

/-- The number of nodes of a tree. -/
def sizeK : Tree → ℕ := RoseTree.elim fun _ rs ↦ 1 + rs.sum

/-- The number of the nodes of a term's numerals: the applications of the definitions of the
empty bitstring and of a bit before a bitstring. -/
def numeralNodes : Internal.Term → ℕ := RoseTree.elim fun l rs ↦
  (match l with
    | .defn k [] => if k = D.bnil ∨ k = D.b0 ∨ k = D.b1 then 1 else 0
    | _ => 0) + rs.sum

/-- The number of quoted trees in a kernel term, and their nodes. -/
def quotes : Tree → ℕ × ℕ := RoseTree.para fun l cs ↦
  if l = Kernel.Label.quote then (1, (cs.head?.map fun c ↦ sizeK c.1).getD 0)
  else ((cs.map (·.2.1)).sum, (cs.map (·.2.2)).sum)

/-- The literals' cost of a program, from its text, printed: the program's definitions, nodes,
quoted trees and their nodes, and its translation's nodes, the numerals' nodes among them, and
the library's nodes. -/
def literalCost (text : List Char) : IO Unit := do
  match Kernel.readProgram text, translated text with
  | some ds, some (_, defs) =>
    IO.println ("definitions,kernel_nodes,quoted_trees,quoted_nodes,translation_nodes," ++
      "numeral_nodes,library_nodes")
    let row := [ds.length, (ds.map fun d ↦ sizeK d.2).sum, (ds.map fun d ↦ (quotes d.2).1).sum,
      (ds.map fun d ↦ (quotes d.2).2).sum, (defs.map fun d ↦ sizeM d.body).sum,
      (defs.map fun d ↦ numeralNodes d.body).sum, (lib.map fun d ↦ sizeM d.body).sum]
    IO.println (",".intercalate (row.map toString))
  | _, _ => throw (IO.userError "the program does not translate")

#eval literalCost kernelText.toList

end GebTests.Prototypes.FreeTopos.Translation

namespace GebTests.Prototypes.FreeTopos.TranslationProofs

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation
open scoped FinEnum

/-- The statements of the prelude's theorems: appending the empty list on either side, the
associativity of appending, and appending the empty list twice. -/
def preludeStatements : String := "
(import Prelude)
(def appendNilLeftL (lam ((ys Ts)) (append (nil T) ys)))
(def appendNilLeftR (lam ((ys Ts)) ys))
(def appendNilL (lam ((xs Ts)) (append xs (nil T))))
(def appendNilR (lam ((xs Ts)) xs))
(def appendAssocL (lam ((ys Ts) (zs Ts) (xs Ts)) (append (append xs ys) zs)))
(def appendAssocR (lam ((ys Ts) (zs Ts) (xs Ts)) (append xs (append ys zs))))
(def appendNilTwiceL (lam ((xs Ts)) (append (append xs (nil T)) (nil T))))
(def appendNilTwiceR (lam ((xs Ts)) xs))"

/-- The statements of the labels' addition: zero on the right, the successor on the right, and
zero on the left. -/
def natStatements : String := "
(import Prelude)
(def addZeroL (lam ((m T)) (add m 0)))
(def addZeroR (lam ((m T)) (label m)))
(def addSuccL (lam ((m T) (n T)) (add m (add n 1))))
(def addSuccR (lam ((m T) (n T)) (add (add m n) 1)))
(def addZeroLeftL (lam ((n T)) (add 0 n)))
(def addZeroLeftR (lam ((n T)) (label n)))"

/-- The statement of the type checker's type of a quoted tree. -/
def checkStatements : String := "
(import Prelude) (import Reader) (import Check)
(def typeQuoteL (lam ((G Ts) (ctx Ts) (x T)) (typeIn G ctx (node Label.quote (single x)))))
(def typeQuoteR (lam ((G Ts) (ctx Ts) (x T)) (some Label.tyTree)))"

/-- A program by structural recursion over a datatype, and the statements of its recursion
equations. -/
def datatypeStatements : String := "
(import Prelude) (import Reader) (import Check)
(data Nat (zero) (succ Nat))
(defn plus ((m Nat) (n Nat)) Nat (cata Nat Nat m ((zero) n) ((succ r) (succ r))))
(def plusZeroL (lam ((n Nat)) (plus zero n)))
(def plusZeroR (lam ((n Nat)) n))
(def plusSuccL (lam ((m Nat) (n Nat)) (plus (succ m) n)))
(def plusSuccR (lam ((m Nat) (n Nat)) (succ (plus m n))))"

/-- The texts of the files, each the programs its theorems are about and their statements, with
the number of its theorems: the prelude, the labels, the kernel's type checker and a program by
structural recursion. -/
def files : List (String × ℕ) :=
  let pr := Kernel.Stage0Tests.prelude
  let prc := include_manifest "bootstrap/checker.manifest"
  [(pr ++ "\n" ++ preludeStatements, 4), (pr ++ "\n" ++ natStatements, 3),
    (prc ++ checkStatements, 1), (prc ++ datatypeStatements, 2)]

/-- The programs and theorems of the files, each read and expanded by the stage-0 compiler's front
end. -/
def results (files : List (List Char × ℕ)) : Option (List (List Tree × List GoedelT.Thm)) :=
  files.mapM fun (text, k) ↦ do pure (theoremsOf (← Kernel.Stage0Tests.bundled text) k)

-- each file's development checks, the prelude's both by innermost normalization and through weak
-- head normal forms
#guard match results (files.map fun (t, k) ↦ (t.toList, k)) with
  | some [(D₀, t₀), (D₁, t₁), (D₂, t₂), (D₃, t₃)] =>
    checks D₀ t₀ preludeDev && checks D₀ t₀ preludeDevW && checks D₁ t₁ natDev &&
      checks D₂ t₂ checkDev && checks D₃ t₃ treeDev
  | _ => false

end GebTests.Prototypes.FreeTopos.TranslationProofs

end
