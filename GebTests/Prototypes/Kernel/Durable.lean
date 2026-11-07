/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Durable -- shake: keep
public meta import Geb.Prototypes.Kernel.Durable -- shake: keep
public import GebTests.Prototypes.Kernel.Document -- shake: keep
public meta import GebTests.Prototypes.Kernel.Document -- shake: keep

set_option doc.verso true in
/-!
# Durable document examples

The profile this host reads is read back from its form and accepted; a profile of another version
of the syntax, schema or prose, one requiring a field this host does not read, and one whose
fields are malformed are rejected, and an optional field is kept. A document with notes before a
definition and inside a module is read with each note's path and fields, and its names, prose,
examples, links and unknown fields survive the authoring profile's printer and formatter and the
canonical, advanced and basic encodings. A malformed note, or one documenting no declaration, is
rejected; a source without notes is compiled as it is written, and one with notes as the same
declarations without them.

The texts are string constants, converted to lists of characters inside each {lit}`#guard`,
as in the kernel's examples.

## Main definitions

* {lit}`generated` is a profile with an optional field.
* {lit}`noted` is a text with notes, and {lit}`unnoted` the same declarations without them.

## Tags

document, profile, note, retraction, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Document.DurableTests

open Geb.Kernel.Stage0Tests Geb.Kernel.Document.Tests

/-- The profile a text writes, when this host reads it, or what rejects it. -/
def profileOf (s : String) : Except String Profile :=
  match readSExps s.toList with
  | some [t] => Profile.parse t
  | _ => .error "the text is not one form"

-- the current profile is the form a manifest writes, read back and accepted
#guard readSExps "(document (syntax authoring 0) (schema 0) (prose verso 0))".toList =
  some [Profile.current.toSExp]
#guard (Profile.ofSExp? Profile.current.toSExp).map Profile.toSExp = some Profile.current.toSExp
#guard (Profile.parse Profile.current.toSExp).toOption.isSome

-- another version of the syntax, the schema or the prose is rejected
#guard (profileOf "(document (syntax authoring 1) (schema 0) (prose verso 0))") matches .error _
#guard (profileOf "(document (syntax other 0) (schema 0) (prose verso 0))") matches .error _
#guard (profileOf "(document (syntax authoring 0) (schema 1) (prose verso 0))") matches .error _
#guard (profileOf "(document (syntax authoring 0) (schema 0) (prose markdown 0))") matches .error _

-- a field the document requires and this host does not read is rejected; one it reads is not
#guard (profileOf
  "(document (syntax authoring 0) (schema 0) (prose verso 0) (crit signature) (signature x))")
  matches .error _
#guard (profileOf "(document (syntax authoring 0) (schema 0) (prose verso 0) (crit schema))")
  matches .ok _

/-- A profile with an optional field. -/
def generated : String :=
  "(document (syntax authoring 0) (schema 0) (prose verso 0) (generator geb-fmt (0 1)))"

-- an optional field is kept as it is read, and written back
#guard ((profileOf generated).toOption.map Profile.toSExp) =
  (readSExps generated.toList).bind List.head?

-- the fields stand in order, the field of the required ones before the optional ones, and an
-- optional field is a list headed by an atom
#guard (profileOf "(document (schema 0) (syntax authoring 0) (prose verso 0))") matches .error _
#guard (profileOf "(document (syntax authoring 0) (schema 0) (prose verso 0) (g) (crit schema))")
  matches .error _
#guard (profileOf "(document (syntax authoring 0) (schema 0) (prose verso 0) x)") matches .error _
#guard (profileOf "(document (syntax authoring 0) (schema 0))") matches .error _

/-- A text with notes: one before a definition, with an example, a link and an unknown field, and
one inside a module, with comments around them. -/
def noted : String := "; a durable document
(note (example (f 1) 1) (link lean Geb.Kernel.Tree) (author someone))
; the identity
(def f (lam ((x T)) x))

(module M (export g)
  ; g applies f
  (note (link geb f) (example (g 2) 2))
  (def g (lam ((x T)) (f x))))
"

/-- The declarations of {name}`noted` without its notes. -/
def unnoted : String := "(def f (lam ((x T)) x)) (module M (export g) (def g (lam ((x T)) (f x))))"

-- each note is read with the path of the declaration it documents and its fields
#guard ((readDoc noted.toList).map fun d ↦ (notesOf d).toOption.map (·.map (·.1))) =
  some (some [[['f']], [['M'], ['g']]])
#guard ((readDoc noted.toList).bind fun d ↦ (notesOf d).toOption).map
    (·.map fun (_, n) ↦ n.map fun
      | .example _ _ => 0
      | .link _ _ => 1
      | .other _ => 2) =
  some [[0, 1, 2], [1, 0]]
#guard ((readDoc noted.toList).bind fun d ↦ (notesOf d).toOption).map
    (·.flatMap fun (_, n) ↦ n.filterMap fun
      | .link k x => some (String.ofList k, String.ofList x)
      | _ => none) =
  some [("lean", "Geb.Kernel.Tree"), ("geb", "f")]

-- a note's fields are written back as they are read
#guard ((readDoc noted.toList).bind fun d ↦ (notesOf d).toOption).map
    (·.map fun (_, n) ↦ noteSExp n) =
  some ((readSExps "(note (example (f 1) 1) (link lean Geb.Kernel.Tree) (author someone))
    (note (link geb f) (example (g 2) 2))".toList).getD [])

-- the document with its notes survives the authoring profile's printer and its formatter
#guard (readDoc noted.toList).all fun d ↦
  (readDoc (printAt (defaultLayout .profile 100 d) d)).map Doc.tokens == some d.tokens
#guard ((format 100 noted.toList).bind fun t ↦ format 100 t) = format 100 noted.toList

-- the durable document, its profile and its notes survive the canonical, advanced and basic
-- encodings
#guard (readDoc noted.toList).all fun d ↦
  let D : Durable := ⟨Profile.current, d⟩
  D.wf &&
    (readStrictDurable (printCanonDurable D)).map (fun E ↦ (E.profile.toSExp, E.doc.tokens)) ==
      some (Profile.current.toSExp, d.tokens) &&
    (readStrictDurable (printAdvancedDurable 100 D)).map (fun E ↦ (E.profile.toSExp, E.doc.tokens))
      == some (Profile.current.toSExp, d.tokens) &&
    (readBasicDurable (printCanonDurable D)).map (fun E ↦ E.doc.tokens) == some d.tokens &&
    (printAdvancedDurable 100 D).all (·.toNat < 128)

-- an optional field of the profile survives them
#guard ((profileOf
    "(document (syntax authoring 0) (schema 0) (prose verso 0) (crit schema) (g x))").toOption).all
  fun p ↦ (readStrictDurable (printCanonDurable ⟨p, ⟨[], []⟩⟩)).map (·.profile.toSExp) ==
    some p.toSExp

-- a strict document whose header is not a profile is not a durable document
#guard (readStrictDurable "(4:*doc(1:h)())".toList).isNone

-- a source without notes is compiled as it is written
#guard (erasedText compiler.toList) matches .ok none
#guard (erasedText unnoted.toList) matches .ok none

-- a source with notes is compiled as the same declarations without them
#guard (match erasedText noted.toList with
  | .ok (some t) => readSExps t
  | _ => none) = readSExps unnoted.toList

-- a malformed note, a note that no declaration follows, and a note of a declaration without a
-- name are rejected
#guard (erasedText "(note (link url x)) (def f (lam ((x T)) x))".toList) matches .error _
#guard (erasedText "(note (link geb (f))) (def f (lam ((x T)) x))".toList) matches .error _
#guard (erasedText "(note (example 1)) (def f (lam ((x T)) x))".toList) matches .error _
#guard (erasedText "(note x) (def f (lam ((x T)) x))".toList) matches .error _
#guard (erasedText "(def f (lam ((x T)) x)) (note (link geb f))".toList) matches .error _
#guard (erasedText "(note) (note) (def f (lam ((x T)) x))".toList) matches .error _
#guard (erasedText "(note) (quote x)".toList) matches .error _
#guard (erasedText "(note) (def (f) x)".toList) matches .error _
#guard (erasedText "(module M (export g) (note) (import N) (def g 0))".toList) matches .error _

end Geb.Kernel.Document.DurableTests

end
