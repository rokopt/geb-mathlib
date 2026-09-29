/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.Base

set_option doc.verso true in
/-!
# The theory of an elementary topos in the checker written in Geb

The signature and the axioms of {lit}`bootstrap/free-topos/theory.geb`, in the Lean the
bootstrap compiler emits ({lit}`GebMirror.Metalogic`), are the encodings of the theory of an
elementary topos with the data objects, {name}`Geb.FreeTopos.theory`, block by block.

## Main statements

* {lit}`toposTheory_eq` — the mirror's theory is the encoding of the theory.

## Tags

elementary topos, partial Horn theory, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Agreement.Theory

open Geb Geb.Kernel Geb.FreeTopos GebTests.Prototypes.FreeTopos.Agreement.Encode
  GebTests.Prototypes.FreeTopos.Agreement.Base

/-- The mirror's the object variable of an index. -/
@[simp] theorem mirror_x (i : ℕ) : GebMirror.Metalogic.x (leaf i) = x i := rfl

/-- The mirror's domain. -/
@[simp] theorem mirror_dom (f : Tree) : GebMirror.Metalogic.dom f = dom f := rfl

/-- The mirror's codomain. -/
@[simp] theorem mirror_cod (f : Tree) : GebMirror.Metalogic.cod f = cod f := rfl

/-- The mirror's identity. -/
@[simp] theorem mirror_idt (a : Tree) : GebMirror.Metalogic.idt a = idt a := rfl

/-- The mirror's composite. -/
@[simp] theorem mirror_comp (g f : Tree) : GebMirror.Metalogic.comp g f = comp g f := rfl

/-- The mirror's terminal object. -/
@[simp] theorem mirror_one : GebMirror.Metalogic.one = one := rfl

/-- The mirror's arrow to the terminal object. -/
@[simp] theorem mirror_bang (a : Tree) : GebMirror.Metalogic.bang a = bang a := rfl

/-- The mirror's product. -/
@[simp] theorem mirror_prod (a b : Tree) : GebMirror.Metalogic.prod a b = prod a b := rfl

/-- The mirror's first projection. -/
@[simp] theorem mirror_cFst (a b : Tree) : GebMirror.Metalogic.cFst a b = fst a b := rfl

/-- The mirror's second projection. -/
@[simp] theorem mirror_cSnd (a b : Tree) : GebMirror.Metalogic.cSnd a b = snd a b := rfl

/-- The mirror's pairing. -/
@[simp] theorem mirror_cPair (f g : Tree) : GebMirror.Metalogic.cPair f g = pair f g := rfl

/-- The mirror's equalizer. -/
@[simp] theorem mirror_eqz (f g : Tree) : GebMirror.Metalogic.eqz f g = eqz f g := rfl

/-- The mirror's equalizer's inclusion. -/
@[simp] theorem mirror_eqIncl (f g : Tree) : GebMirror.Metalogic.eqIncl f g = eqIncl f g := rfl

/-- The mirror's lifting through an equalizer. -/
@[simp] theorem mirror_eqLift (f g h :
    Tree) : GebMirror.Metalogic.eqLift f g h = eqLift f g h := rfl

/-- The mirror's initial object. -/
@[simp] theorem mirror_cZero : GebMirror.Metalogic.cZero = zero := rfl

/-- The mirror's arrow from the initial object. -/
@[simp] theorem mirror_absurd (a : Tree) : GebMirror.Metalogic.absurd a = absurd a := rfl

/-- The mirror's coproduct. -/
@[simp] theorem mirror_coprod (a b : Tree) : GebMirror.Metalogic.coprod a b = coprod a b := rfl

/-- The mirror's left injection. -/
@[simp] theorem mirror_inl (a b : Tree) : GebMirror.Metalogic.inl a b = inl a b := rfl

/-- The mirror's right injection. -/
@[simp] theorem mirror_inr (a b : Tree) : GebMirror.Metalogic.inr a b = inr a b := rfl

/-- The mirror's copairing. -/
@[simp] theorem mirror_copair (f g : Tree) : GebMirror.Metalogic.copair f g = copair f g := rfl

/-- The mirror's coequalizer. -/
@[simp] theorem mirror_coeqz (f g : Tree) : GebMirror.Metalogic.coeqz f g = coeqz f g := rfl

/-- The mirror's coequalizer's projection. -/
@[simp] theorem mirror_coeqProj (f g :
    Tree) : GebMirror.Metalogic.coeqProj f g = coeqProj f g := rfl

/-- The mirror's descent through a coequalizer. -/
@[simp] theorem mirror_coeqDesc (f g h :
    Tree) : GebMirror.Metalogic.coeqDesc f g h = coeqDesc f g h := rfl

/-- The mirror's exponential. -/
@[simp] theorem mirror_exp (a b : Tree) : GebMirror.Metalogic.exp a b = exp a b := rfl

/-- The mirror's evaluation. -/
@[simp] theorem mirror_ev (a b : Tree) : GebMirror.Metalogic.ev a b = ev a b := rfl

/-- The mirror's currying. -/
@[simp] theorem mirror_curry (c a f : Tree) : GebMirror.Metalogic.curry c a f = curry c a f := rfl

/-- The mirror's subobject classifier. -/
@[simp] theorem mirror_omega : GebMirror.Metalogic.omega = omega := rfl

/-- The mirror's truth. -/
@[simp] theorem mirror_tru : GebMirror.Metalogic.tru = tru := rfl

/-- The mirror's characteristic map. -/
@[simp] theorem mirror_chi (m : Tree) : GebMirror.Metalogic.chi m = chi m := rfl

/-- The mirror's inverse of a characteristic map. -/
@[simp] theorem mirror_chiInv (m : Tree) : GebMirror.Metalogic.chiInv m = chiInv m := rfl

/-- The mirror's natural numbers object. -/
@[simp] theorem mirror_nat : GebMirror.Metalogic.nat = nat := rfl

/-- The mirror's zero. -/
@[simp] theorem mirror_zeroN : GebMirror.Metalogic.zeroN = zeroN := rfl

/-- The mirror's successor. -/
@[simp] theorem mirror_succ : GebMirror.Metalogic.succ = succ := rfl

/-- The mirror's fold of the natural numbers. -/
@[simp] theorem mirror_natRec (z s : Tree) : GebMirror.Metalogic.natRec z s = natRec z s := rfl

/-- The mirror's list object. -/
@[simp] theorem mirror_list (a : Tree) : GebMirror.Metalogic.list a = list a := rfl

/-- The mirror's empty list. -/
@[simp] theorem mirror_cNil (a : Tree) : GebMirror.Metalogic.cNil a = nil a := rfl

/-- The mirror's construction of a list. -/
@[simp] theorem mirror_cCons (a : Tree) : GebMirror.Metalogic.cCons a = cons a := rfl

/-- The mirror's fold of lists. -/
@[simp] theorem mirror_listRec (a z s :
    Tree) : GebMirror.Metalogic.listRec a z s = listRec a z s := rfl

/-- The mirror's rose-tree object. -/
@[simp] theorem mirror_rose : GebMirror.Metalogic.rose = rose := rfl

/-- The mirror's construction of a rose tree. -/
@[simp] theorem mirror_cNode : GebMirror.Metalogic.cNode = node := rfl

/-- The mirror's fold of rose trees. -/
@[simp] theorem mirror_roseRec (f : Tree) : GebMirror.Metalogic.roseRec f = roseRec f := rfl

/-- The mirror's rose-tree object over a type of labels. -/
@[simp] theorem mirror_lrose (a : Tree) : GebMirror.Metalogic.lrose a = lrose a := rfl

/-- The mirror's construction of a rose tree over labels. -/
@[simp] theorem mirror_lnode (a : Tree) : GebMirror.Metalogic.lnode a = lnode a := rfl

/-- The mirror's fold of rose trees over labels. -/
@[simp] theorem mirror_lroseRec (a f :
    Tree) : GebMirror.Metalogic.lroseRec a f = lroseRec a f := rfl

/-- The mirror's diagonal. -/
@[simp] theorem mirror_diag (a : Tree) : GebMirror.Metalogic.diag a = diag a := rfl

/-- The mirror's subobject on which an arrow is truth. -/
@[simp] theorem mirror_truthEq (p : Tree) : GebMirror.Metalogic.truthEq p = truthEq p := rfl

/-- The mirror's inclusion of the subobject on which an arrow is truth. -/
@[simp] theorem mirror_truthIncl (p : Tree) : GebMirror.Metalogic.truthIncl p = truthIncl p := rfl

/-- The mirror's lifting into the subobject on which an arrow is truth. -/
@[simp] theorem mirror_truthLift (p m :
    Tree) : GebMirror.Metalogic.truthLift p m = truthLift p m := rfl

/-- The mirror's signature. -/
theorem sig_eq : GebMirror.Metalogic.sig = sig.map encOpSig := by rfl

/-- The mirror's axioms of a category. -/
theorem categoryAxioms_eq :
    GebMirror.Metalogic.categoryAxioms = categoryAxioms.map encSeq := by rfl

/-- The mirror's axioms of the terminal object. -/
theorem terminalAxioms_eq :
    GebMirror.Metalogic.terminalAxioms = terminalAxioms.map encSeq := by rfl

/-- The mirror's axioms of products. -/
theorem productAxioms_eq :
    GebMirror.Metalogic.productAxioms = productAxioms.map encSeq := by rfl

/-- The mirror's axioms of equalizers. -/
theorem equalizerAxioms_eq :
    GebMirror.Metalogic.equalizerAxioms = equalizerAxioms.map encSeq := by rfl

/-- The mirror's axioms of the initial object. -/
theorem initialAxioms_eq :
    GebMirror.Metalogic.initialAxioms = initialAxioms.map encSeq := by rfl

/-- The mirror's axioms of coproducts. -/
theorem coproductAxioms_eq :
    GebMirror.Metalogic.coproductAxioms = coproductAxioms.map encSeq := by rfl

/-- The mirror's axioms of coequalizers. -/
theorem coequalizerAxioms_eq :
    GebMirror.Metalogic.coequalizerAxioms = coequalizerAxioms.map encSeq := by rfl

/-- The mirror's axioms of exponentials. -/
theorem exponentialAxioms_eq :
    GebMirror.Metalogic.exponentialAxioms = exponentialAxioms.map encSeq := by rfl

/-- The mirror's axioms of the subobject classifier. -/
theorem classifierAxioms_eq :
    GebMirror.Metalogic.classifierAxioms = classifierAxioms.map encSeq := by rfl

/-- The mirror's axioms of the natural numbers object. -/
theorem natAxioms_eq :
    GebMirror.Metalogic.natAxioms = natAxioms.map encSeq := by rfl

/-- The mirror's axioms of list objects. -/
theorem listAxioms_eq :
    GebMirror.Metalogic.listAxioms = listAxioms.map encSeq := by rfl

/-- The mirror's axioms of the rose-tree object. -/
theorem roseAxioms_eq :
    GebMirror.Metalogic.roseAxioms = roseAxioms.map encSeq := by rfl

/-- The mirror's axioms of rose-tree objects over types of labels. -/
theorem lroseAxioms_eq :
    GebMirror.Metalogic.lroseAxioms = lroseAxioms.map encSeq := by rfl

/-- The mirror's axioms. -/
theorem axioms_eq : GebMirror.Metalogic.axioms = axioms.map encSeq := by
  simp only [GebMirror.Metalogic.axioms, append_eq, categoryAxioms_eq, terminalAxioms_eq,
    productAxioms_eq, equalizerAxioms_eq, initialAxioms_eq, coproductAxioms_eq,
    coequalizerAxioms_eq, exponentialAxioms_eq, classifierAxioms_eq, natAxioms_eq, listAxioms_eq,
    roseAxioms_eq, lroseAxioms_eq, axioms, List.map_append, List.append_assoc]

/-- The mirror's theory of an elementary topos with the data objects is the encoding of the
theory. -/
theorem toposTheory_eq : GebMirror.Metalogic.toposTheory = encTheory theory := by
  simp only [GebMirror.Metalogic.toposTheory, sig_eq, axioms_eq]
  rfl

end GebTests.Prototypes.FreeTopos.Agreement.Theory

end
