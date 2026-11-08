module

public import GebMirror.Metalogic.Tactics

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «Authoring/LD.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Authoring/LD.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/LD.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/LD.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Authoring/LD.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Authoring/LD.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List T := Const.iter (α := List T) «Authoring/LD.tail» x1 x0;
    x2

def «Authoring/LD.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Authoring/LD.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Authoring/OS.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Authoring/OS.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/OS.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/OS.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Authoring/OS.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Authoring/OS.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List T := Const.iter (α := List T) «Authoring/OS.tail» x1 x0;
    x2

def «Authoring/OS.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Authoring/OS.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Authoring/PF.l2» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List T := (x0 :: (x1 :: ([] : List T))); x2

def «Authoring/PF.l3» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : List T := (x0 :: («Authoring/PF.l2» x1 x2)); x3

def «Authoring/PF.l4» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : List T := (x0 :: («Authoring/PF.l3» x1 x2 x3)); x4

def «Authoring/PF.l5» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : List T := (x0 :: («Authoring/PF.l4» x1 x2 x3 x4)); x5

def «Authoring/PF.l6» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : List T := (x0 :: («Authoring/PF.l5» x1 x2 x3 x4 x5)); x6

def «Authoring/DL.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Authoring/Decls.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Authoring/Decls.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/Decls.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/Decls.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Authoring/Decls.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Authoring/Decls.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Authoring/Decls.tail» x1 x0;
    x2

def «Authoring/Decls.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Authoring/Decls.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Authoring/Rules.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Authoring/Rules.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/Rules.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/Rules.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Authoring/Rules.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Authoring/Rules.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Authoring/Rules.tail» x1 x0;
    x2

def «Authoring/Rules.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Authoring/Rules.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Authoring.word» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prelude.and»
      («Reader.isAtom» x0)
      (Const.equal («Reader.nameOf» x0) x1);
    x2

def «Authoring.form» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Prelude.and»
      («Reader.isList» x0)
      («Prelude.and»
        (Const.eq («Prelude.length» (Const.children x0)) x2)
        («Authoring.word» (Const.child x0 (leaf 0)) x1));
    x3

def «Authoring.headed» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prelude.and»
      («Reader.isList» x0)
      («Prelude.and»
        (Const.lt (leaf 0) («Prelude.length» (Const.children x0)))
        («Authoring.word» (Const.child x0 (leaf 0)) x1));
    x2

def «Authoring.number» :=
  fun (x0 : T) =>
    let x1 : T := (if («Reader.isAtom» x0).label ≠ 0 then
      «Reader.numeral» (Const.children x0)
    else
      «Prelude.none»);
    x1

def «Authoring.has» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := «Prelude.isSome» («Reader.indexOf» x0 x1); x2

def «Authoring.declared» :=
  fun (x0 : T) =>
    let x1 : T := «Prelude.and»
      («Reader.isAtom» x0)
      («Prelude.and»
        («Base.not» («Base.isEmpty» (Const.children x0)))
        («Prelude.and»
          («Base.not» («Prelude.isSome» («Authoring.number» x0)))
          («Base.not»
            («Authoring.has» («Reader.nameOf» x0) «Reader.reservedNames»))));
    x1

def «Authoring.distinctFrom» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := List T → T)
      (fun (x2 : T) (x3 : List T → T) (x4 : List T) =>
        «Prelude.and» («Base.not» («Authoring.has» x2 x4)) (x3 (x2 :: x4)))
      (fun (_ : List T) => leaf 1)
      x1
      x0;
    x2

def «Authoring.globalsOf» :=
  fun (x0 : List T) =>
    let x1 : T := «Language.globals»
      («Language.prims»
        («Authoring/PF.l6»
          «Derivation.nilPrim»
          «Derivation.consPrim»
          «Derivation.lnodePrim»
          «Derivation.inlPrim»
          «Derivation.inrPrim»
          «Derivation.casePrim»))
      («Language.defs»
        («Authoring/DL.map»
          «Language.defLang»
          («Authoring/LD.append» «Translation.lib» x0)))
      («Authoring/OS.length» «Theory.sig»);
    x1

def «Authoring.rulesOf» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List
      T := (let x2 : List
              T := «Authoring/Rules.single»
              («Prover.nrBelow» x1 («Derivation.terms» ([] : List T)));
            ((«Prover.nrRule» (leaf 3) («Derivation.terms» ([] : List T))) ::
              ((«Prover.nrRule» (leaf 4) («Derivation.terms» ([] : List T))) ::
                ((«Prover.nrRule» (leaf 5) («Derivation.terms» ([] : List T))) ::
                  (if (Const.eq x0 (leaf 0)).label ≠ 0 then
                    x2
                  else
                    ((«Prover.nrRule»
                      (leaf 11)
                      («Derivation.terms» («Prelude.single» (leaf 0)))) ::
                      ((«Prover.nrRule»
                        (leaf 12)
                        («Derivation.terms» («Prelude.single» (leaf 1)))) ::
                        ((«Prover.nrRule»
                          (leaf 13)
                          («Derivation.terms» («Theory.l3» (leaf 2) (leaf 0) (leaf 1)))) ::
                          ((«Prover.nrRule»
                            (leaf 14)
                            («Derivation.terms» («Theory.l2» (leaf 5) (leaf 3)))) ::
                            ((«Prover.nrRule»
                              (leaf 15)
                              («Derivation.terms» («Theory.l2» (leaf 5) (leaf 4)))) ::
                              («Prover.nrUnit» :: x2)))))))))));
    x2

def «Authoring.kernelType» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (let x2 : T := «Reader.resolve»
                     ([] : List T)
                     x0
                     (Const.node
                       (leaf 2)
                       («Theory.l2»
                         (Const.node (leaf 1) (Const.children «Reader.kwNil»))
                         x1))
                     ([] : List T);
                   if («Prelude.isSome» x2).label ≠ 0 then
                     «Prelude.some» (Const.child («Prelude.get» x2) (leaf 0))
                   else
                     «Prelude.none»);
    x2

def «Authoring.sourceEqn» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: (x3 :: ([] : List T)))))

def «Authoring/OE.nothing» := Const.node (leaf 0) ([] : List T)

def «Authoring/OE.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Authoring/OE.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let x2 : List T := Const.children x1;
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x2
                       (leaf 0)
                       (fun (x3 : T) (_ : List T) => x3);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x2
                       ([] : List T)
                       (fun (_ : T) (x5 : List T) => x5);
                     leaf 1
                   else
                     let _ : List T := Const.children x1; leaf 0);
    x1

def «Authoring/OE.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x4
                   else
                     let _ : List T := Const.children x2; x0);
    x2

def «Authoring/OE.nthOf» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.lcase
      (α := T)
      (β := T)
      (Const.iter
        (α := List T)
        (fun (x2 : List T) =>
          Const.lcase
            (α := T)
            (β := List T)
            x2
            ([] : List T)
            (fun (_ : T) (x4 : List T) => x4))
        x0
        x1)
      «Authoring/OE.nothing»
      (fun (x2 : T) (_ : List T) => «Authoring/OE.just» x2);
    x2

def «Authoring/OE.allJust» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x4 : List T := Const.children x3;
          let x5 : T := Const.lcase
            (α := T)
            (β := T)
            x4
            (leaf 0)
            (fun (x5 : T) (_ : List T) => x5);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x4
            ([] : List T)
            (fun (_ : T) (x7 : List T) => x7);
          ((x2).1, (x5 :: (x2).2))
        else
          let _ : List T := Const.children x3; (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Authoring.eqnFormula» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : List T := Const.children x1;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x2
                     (leaf 0)
                     (fun (x3 : T) (_ : List T) => x3);
                   let x4 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x2
                     ([] : List T)
                     (fun (_ : T) (x5 : List T) => x5);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let x6 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x6
                     (leaf 0)
                     (fun (x7 : T) (_ : List T) => x7);
                   let x8 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x6
                     ([] : List T)
                     (fun (_ : T) (x9 : List T) => x9);
                   let x9 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x8
                     (leaf 0)
                     (fun (x9 : T) (_ : List T) => x9);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x8
                     ([] : List T)
                     (fun (_ : T) (x11 : List T) => x11);
                   x9);
    x1

def «Authoring.readEqn» :=
  fun (x0 : List T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : T) =>
    let x5 : T := (if («Authoring.form»
      x4
      (mk 0 [leaf 101, leaf 113, leaf 117, leaf 97, leaf 108])
      (leaf 3)).label ≠ 0 then
      let x5 : T := «Reader.resolve»
        ([] : List T)
        x1
        (Const.child x4 (leaf 1))
        x2;
      let x6 : T := «Reader.resolve»
        ([] : List T)
        x1
        (Const.child x4 (leaf 2))
        x2;
      if («Prelude.and»
        («Prelude.isSome» x5)
        («Prelude.isSome» x6)).label ≠ 0 then
        let x7 : T := «Translation.term» x0 x3 («Prelude.get» x5);
        if (Const.eq (Const.label x7) (leaf 0)).label ≠ 0 then
          let _ : List T := Const.children x7; «Authoring/OE.nothing»
        else
          let x8 : List T := Const.children x7;
          let x9 : T := Const.lcase
            (α := T)
            (β := T)
            x8
            (leaf 0)
            (fun (x9 : T) (_ : List T) => x9);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x8
            ([] : List T)
            (fun (_ : T) (x11 : List T) => x11);
          let x11 : T := «Translation.term» x0 x3 («Prelude.get» x6);
          if (Const.eq (Const.label x11) (leaf 0)).label ≠ 0 then
            let _ : List T := Const.children x11; «Authoring/OE.nothing»
          else
            let x12 : List T := Const.children x11;
            let x13 : T := Const.lcase
              (α := T)
              (β := T)
              x12
              (leaf 0)
              (fun (x13 : T) (_ : List T) => x13);
            let _ : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x12
              ([] : List T)
              (fun (_ : T) (x15 : List T) => x15);
            if (Const.equal («Language.p1» x9) («Language.p1» x13)).label ≠ 0 then
              «Authoring/OE.just»
                («Authoring.sourceEqn»
                  («Language.p1» x9)
                  («Prelude.get» x5)
                  («Prelude.get» x6)
                  («Language.mEq» («Language.p2» x9) («Language.p2» x13)))
            else
              «Authoring/OE.nothing»
      else
        «Authoring/OE.nothing»
    else
      «Authoring/OE.nothing»);
    x5

def «Authoring.statement» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «Authoring/OSt.nothing» := Const.node (leaf 0) ([] : List T)

def «Authoring/OSt.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Authoring/OSt.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let x2 : List T := Const.children x1;
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x2
                       (leaf 0)
                       (fun (x3 : T) (_ : List T) => x3);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x2
                       ([] : List T)
                       (fun (_ : T) (x5 : List T) => x5);
                     leaf 1
                   else
                     let _ : List T := Const.children x1; leaf 0);
    x1

def «Authoring/OSt.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x4
                   else
                     let _ : List T := Const.children x2; x0);
    x2

def «Authoring/OSt.nthOf» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.lcase
      (α := T)
      (β := T)
      (Const.iter
        (α := List T)
        (fun (x2 : List T) =>
          Const.lcase
            (α := T)
            (β := List T)
            x2
            ([] : List T)
            (fun (_ : T) (x4 : List T) => x4))
        x0
        x1)
      «Authoring/OSt.nothing»
      (fun (x2 : T) (_ : List T) => «Authoring/OSt.just» x2);
    x2

def «Authoring/OSt.allJust» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x4 : List T := Const.children x3;
          let x5 : T := Const.lcase
            (α := T)
            (β := T)
            x4
            (leaf 0)
            (fun (x5 : T) (_ : List T) => x5);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x4
            ([] : List T)
            (fun (_ : T) (x7 : List T) => x7);
          ((x2).1, (x5 :: (x2).2))
        else
          let _ : List T := Const.children x3; (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Authoring/EF.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Authoring.sourceEqns» :=
  fun (x0 : List T) => Const.node (leaf 0) x0

def «Authoring/OSourceEqns.nothing» :=
  Const.node (leaf 0) ([] : List T)

def «Authoring/OSourceEqns.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Authoring/OSourceEqns.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let x2 : List T := Const.children x1;
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x2
                       (leaf 0)
                       (fun (x3 : T) (_ : List T) => x3);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x2
                       ([] : List T)
                       (fun (_ : T) (x5 : List T) => x5);
                     leaf 1
                   else
                     let _ : List T := Const.children x1; leaf 0);
    x1

def «Authoring/OSourceEqns.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x4
                   else
                     let _ : List T := Const.children x2; x0);
    x2

def «Authoring/OSourceEqns.nthOf» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.lcase
      (α := T)
      (β := T)
      (Const.iter
        (α := List T)
        (fun (x2 : List T) =>
          Const.lcase
            (α := T)
            (β := List T)
            x2
            ([] : List T)
            (fun (_ : T) (x4 : List T) => x4))
        x0
        x1)
      «Authoring/OSourceEqns.nothing»
      (fun (x2 : T) (_ : List T) => «Authoring/OSourceEqns.just» x2);
    x2

def «Authoring/OSourceEqns.allJust» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x4 : List T := Const.children x3;
          let x5 : T := Const.lcase
            (α := T)
            (β := T)
            x4
            (leaf 0)
            (fun (x5 : T) (_ : List T) => x5);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x4
            ([] : List T)
            (fun (_ : T) (x7 : List T) => x7);
          ((x2).1, (x5 :: (x2).2))
        else
          let _ : List T := Const.children x3; (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Authoring.readHyps» :=
  fun (x0 : List T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T) =>
    let x5 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x5 : T) (x6 : T) =>
        let x7 : T := x6;
        if (Const.eq (Const.label x7) (leaf 0)).label ≠ 0 then
          let _ : List T := Const.children x7; «Authoring/OSourceEqns.nothing»
        else
          let x8 : List T := Const.children x7;
          let x9 : T := Const.lcase
            (α := T)
            (β := T)
            x8
            (leaf 0)
            (fun (x9 : T) (_ : List T) => x9);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x8
            ([] : List T)
            (fun (_ : T) (x11 : List T) => x11);
          let x11 : T := x9;
          let x12 : List T := Const.children x11;
          let x13 : List T := x12;
          if («Prelude.and»
            («Reader.isList» x5)
            («Prelude.and»
              (Const.eq («Prelude.length» (Const.children x5)) (leaf 2))
              («Authoring.declared» (Const.child x5 (leaf 0))))).label ≠ 0 then
            let x14 : T := «Authoring.readEqn»
              x0
              x1
              x2
              x3
              (Const.child x5 (leaf 1));
            if (Const.eq (Const.label x14) (leaf 0)).label ≠ 0 then
              let _ : List T := Const.children x14; «Authoring/OSourceEqns.nothing»
            else
              let x15 : List T := Const.children x14;
              let x16 : T := Const.lcase
                (α := T)
                (β := T)
                x15
                (leaf 0)
                (fun (x16 : T) (_ : List T) => x16);
              let _ : List
                T := Const.lcase
                (α := T)
                (β := List T)
                x15
                ([] : List T)
                (fun (_ : T) (x18 : List T) => x18);
              «Authoring/OSourceEqns.just» («Authoring.sourceEqns» (x16 :: x13))
          else
            «Authoring/OSourceEqns.nothing»)
      («Authoring/OSourceEqns.just» («Authoring.sourceEqns» ([] : List T)))
      x4;
    x5

def «Authoring.binderOk» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := «Prelude.and»
      («Reader.isList» x1)
      («Prelude.and»
        (Const.eq («Prelude.length» (Const.children x1)) (leaf 2))
        («Prelude.and»
          («Authoring.declared» (Const.child x1 (leaf 0)))
          («Prelude.isSome»
            («Authoring.kernelType» x0 (Const.child x1 (leaf 1))))));
    x2

def «Authoring.readStatement» :=
  fun (x0 : List T) (x1 : List T) (x2 : List T) (x3 : T) =>
    let x4 : T := (let x4 : T := «Authoring.form»
                     x3
                     (mk 0 [leaf 102, leaf 111, leaf 114, leaf 97, leaf 108, leaf 108])
                     (leaf 3);
                   let x5 : List
                     T := (if (x4).label ≠ 0 then
                     Const.children (Const.child x3 (leaf 1))
                   else
                     ([] : List T));
                   let x6 : T := (if (x4).label ≠ 0 then
                     Const.child x3 (leaf 2)
                   else
                     x3);
                   let x7 : T := «Prelude.length» (Const.children x6);
                   let x8 : T := «Prelude.and»
                     («Authoring.headed»
                       x6
                       (mk 0 [leaf 105,
                         leaf 109,
                         leaf 112,
                         leaf 108,
                         leaf 105,
                         leaf 101,
                         leaf 115]))
                     (Const.lt (leaf 2) x7);
                   let x9 : List
                     T := (if (x8).label ≠ 0 then
                     «Base.take»
                       (Const.sub x7 (leaf 2))
                       («Prelude.drop» (leaf 1) (Const.children x6))
                   else
                     ([] : List T));
                   let x10 : T := (if (x8).label ≠ 0 then
                     «Prelude.at» (Const.children x6) (Const.sub x7 (leaf 1))
                   else
                     x6);
                   let x11 : List
                     T := «Prelude.reverse»
                     («Base.mapT»
                       (fun (x11 : T) => «Reader.nameOf» (Const.child x11 (leaf 0)))
                       x5);
                   let x12 : List
                     T := «Prelude.reverse»
                     («Base.mapT»
                       (fun (x12 : T) =>
                         «Prelude.get» («Authoring.kernelType» x1 (Const.child x12 (leaf 1))))
                       x5);
                   let x13 : List
                     T := «Base.mapT»
                     (fun (x13 : T) => «Reader.nameOf» (Const.child x13 (leaf 0)))
                     x9;
                   if («Prelude.and»
                     («Prelude.or»
                       («Base.not» x4)
                       («Prelude.and»
                         («Reader.isList» (Const.child x3 (leaf 1)))
                         («Base.not» («Base.isEmpty» x5))))
                     («Prelude.and»
                       («Base.allT» («Authoring.binderOk» x1) x5)
                       («Authoring.distinctFrom»
                         x2
                         («Prelude.append» x11 x13)))).label ≠ 0 then
                     let x14 : T := «Authoring.readHyps» x0 x1 x11 x12 x9;
                     if (Const.eq (Const.label x14) (leaf 0)).label ≠ 0 then
                       let _ : List T := Const.children x14; «Authoring/OSt.nothing»
                     else
                       let x15 : List T := Const.children x14;
                       let x16 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x15
                         (leaf 0)
                         (fun (x16 : T) (_ : List T) => x16);
                       let _ : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x15
                         ([] : List T)
                         (fun (_ : T) (x18 : List T) => x18);
                       let x18 : T := x16;
                       let x19 : List T := Const.children x18;
                       let x20 : List T := x19;
                       let x21 : T := «Authoring.readEqn» x0 x1 x11 x12 x10;
                       if (Const.eq (Const.label x21) (leaf 0)).label ≠ 0 then
                         let _ : List T := Const.children x21; «Authoring/OSt.nothing»
                       else
                         let x22 : List T := Const.children x21;
                         let x23 : T := Const.lcase
                           (α := T)
                           (β := T)
                           x22
                           (leaf 0)
                           (fun (x23 : T) (_ : List T) => x23);
                         let _ : List
                           T := Const.lcase
                           (α := T)
                           (β := List T)
                           x22
                           ([] : List T)
                           (fun (_ : T) (x25 : List T) => x25);
                         let x25 : T := x23;
                         let x26 : List T := Const.children x25;
                         let x27 : T := Const.lcase
                           (α := T)
                           (β := T)
                           x26
                           (leaf 0)
                           (fun (x27 : T) (_ : List T) => x27);
                         let x28 : List
                           T := Const.lcase
                           (α := T)
                           (β := List T)
                           x26
                           ([] : List T)
                           (fun (_ : T) (x29 : List T) => x29);
                         let x29 : T := Const.lcase
                           (α := T)
                           (β := T)
                           x28
                           (leaf 0)
                           (fun (x29 : T) (_ : List T) => x29);
                         let x30 : List
                           T := Const.lcase
                           (α := T)
                           (β := List T)
                           x28
                           ([] : List T)
                           (fun (_ : T) (x31 : List T) => x31);
                         let x31 : T := Const.lcase
                           (α := T)
                           (β := T)
                           x30
                           (leaf 0)
                           (fun (x31 : T) (_ : List T) => x31);
                         let x32 : List
                           T := Const.lcase
                           (α := T)
                           (β := List T)
                           x30
                           ([] : List T)
                           (fun (_ : T) (x33 : List T) => x33);
                         let _ : T := Const.lcase
                           (α := T)
                           (β := T)
                           x32
                           (leaf 0)
                           (fun (x33 : T) (_ : List T) => x33);
                         let _ : List
                           T := Const.lcase
                           (α := T)
                           (β := List T)
                           x32
                           ([] : List T)
                           (fun (_ : T) (x35 : List T) => x35);
                         let x35 : T := «Translation.thm»
                           x0
                           («Translation.gthm»
                             («Translation.ktys» x12)
                             («Translation.geqn» x27 x29 x31));
                         if (Const.eq (Const.label x35) (leaf 0)).label ≠ 0 then
                           let _ : List T := Const.children x35; «Authoring/OSt.nothing»
                         else
                           let x36 : List T := Const.children x35;
                           let x37 : T := Const.lcase
                             (α := T)
                             (β := T)
                             x36
                             (leaf 0)
                             (fun (x37 : T) (_ : List T) => x37);
                           let _ : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x36
                             ([] : List T)
                             (fun (_ : T) (x39 : List T) => x39);
                           let x39 : T := x37;
                           let x40 : List T := Const.children x39;
                           let x41 : T := Const.lcase
                             (α := T)
                             (β := T)
                             x40
                             (leaf 0)
                             (fun (x41 : T) (_ : List T) => x41);
                           let x42 : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x40
                             ([] : List T)
                             (fun (_ : T) (x43 : List T) => x43);
                           let x43 : T := Const.lcase
                             (α := T)
                             (β := T)
                             x42
                             (leaf 0)
                             (fun (x43 : T) (_ : List T) => x43);
                           let x44 : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x42
                             ([] : List T)
                             (fun (_ : T) (x45 : List T) => x45);
                           let _ : T := Const.lcase
                             (α := T)
                             (β := T)
                             x44
                             (leaf 0)
                             (fun (x45 : T) (_ : List T) => x45);
                           let x46 : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x44
                             ([] : List T)
                             (fun (_ : T) (x47 : List T) => x47);
                           let x47 : T := Const.lcase
                             (α := T)
                             (β := T)
                             x46
                             (leaf 0)
                             (fun (x47 : T) (_ : List T) => x47);
                           let _ : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x46
                             ([] : List T)
                             (fun (_ : T) (x49 : List T) => x49);
                           «Authoring/OSt.just»
                             («Authoring.statement»
                               (Const.node (leaf 0) x11)
                               (Const.node (leaf 0) x13)
                               («Derivation.mkThm»
                                 x41
                                 x43
                                 («Derivation.terms»
                                   («Authoring/EF.map» «Authoring.eqnFormula» x20))
                                 x47))
                   else
                     «Authoring/OSt.nothing»);
    x4

def «Authoring/SRs.single» :=
  fun (x0 : List T →
      List T → T × (T → List T → List T → List T → List T → T → T → T)) =>
    let x1 : List
      (List T →
        List T →
          T ×
            (T →
              List T →
                List T →
                  List T →
                    List T →
                      T →
                        T →
                          T)) := (x0 ::
      ([] : List (List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T))));
    x1

def «Authoring/SRs.length» :=
  fun (x0 : List
      (List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x1 : T := Const.foldr
      (α := List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T))
      (β := T)
      (fun (_ : List T →
           List T → T × (T → List T → List T → List T → List T → T → T → T))
         (x2 : T) =>
        Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/SRs.append» :=
  fun (x0 : List
      (List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T)))
    (x1 : List
      (List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x2 : List
      (List T →
        List T →
          T ×
            (T →
              List T →
                List T →
                  List T →
                    List T →
                      T →
                        T →
                          T)) := Const.foldr
      (α := List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T))
      (β := List
        (List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T)))
      (fun (x2 : List T →
           List T → T × (T → List T → List T → List T → List T → T → T → T))
         (x3 : List
           (List T →
             List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/SRs.reverse» :=
  fun (x0 : List
      (List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x1 : List
      (List T →
        List T →
          T ×
            (T →
              List T →
                List T →
                  List T →
                    List T →
                      T →
                        T →
                          T)) := Const.foldr
      (α := List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T))
      (β := List
        (List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T)) →
        List
          (List T →
            List T → T × (T → List T → List T → List T → List T → T → T → T)))
      (fun (x1 : List T →
           List T → T × (T → List T → List T → List T → List T → T → T → T))
         (x2 : List
           (List T →
             List T → T × (T → List T → List T → List T → List T → T → T → T)) →
           List
             (List T →
               List T → T × (T → List T → List T → List T → List T → T → T → T)))
         (x3 : List
           (List T →
             List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
        x2 (x1 :: x3))
      (fun (x1 : List
           (List T →
             List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
        x1)
      x0
      ([] : List (List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T)));
    x1

def «Authoring/SRs.tail» :=
  fun (x0 : List
      (List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x1 : List
      (List T →
        List T →
          T ×
            (T →
              List T →
                List T →
                  List T →
                    List T →
                      T →
                        T →
                          T)) := Const.lcase
      (α := List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T))
      (β := List
        (List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T)))
      x0
      ([] : List (List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T)))
      (fun (_ : List T →
           List T → T × (T → List T → List T → List T → List T → T → T → T))
         (x2 : List
           (List T →
             List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
        x2);
    x1

def «Authoring/SRs.drop» :=
  fun (x0 : T)
    (x1 : List
      (List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x2 : List
      (List T →
        List T →
          T ×
            (T →
              List T →
                List T →
                  List T →
                    List T →
                      T →
                        T →
                          T)) := Const.iter
      (α := List
        (List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T)))
      «Authoring/SRs.tail»
      x1
      x0;
    x2

def «Authoring/SRs.atOr» :=
  fun (x0 : List T →
      List T → T × (T → List T → List T → List T → List T → T → T → T))
    (x1 : List
      (List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T)))
    (x2 : T) =>
    let x3 : List T →
      List T →
        T ×
          (T →
            List T →
              List T →
                List T →
                  List T →
                    T →
                      T →
                        T) := Const.lcase
      (α := List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T))
      (β := List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T))
      («Authoring/SRs.drop» x2 x1)
      x0
      (fun (x3 : List T →
           List T → T × (T → List T → List T → List T → List T → T → T → T))
         (_ : List
           (List T →
             List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
        x3);
    x3

def «Authoring.failTac» :=
  fun (_ : T)
    (_ : List T)
    (_ : List T)
    (_ : List T)
    (_ : List T)
    (_ : T)
    (_ : T) =>
    «Prelude.none»

def «Authoring.failSR» :=
  fun (_ : List T) (_ : List T) => (leaf 0, «Authoring.failTac»)

def «Authoring.ruleOk» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : T := «Prelude.and»
      («Reader.isAtom» x2)
      («Prelude.or»
        («Authoring.has» («Reader.nameOf» x2) x0)
        («Authoring.has» («Reader.nameOf» x2) x1));
    x3

def «Authoring.rulesFrom» :=
  fun (x0 : List T) (x1 : List T) (x2 : List T) =>
    let x3 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x3 : T) (x4 : List T) =>
        let x5 : T := «Reader.indexOf» («Reader.nameOf» x3) x0;
        ((if («Prelude.isSome» x5).label ≠ 0 then
          «Prover.nrHyp» («Prelude.get» x5)
        else
          «Prover.nrThm»
            (Const.add
              (Const.mul
                (leaf 2)
                («Base.getD» («Reader.indexOf» («Reader.nameOf» x3) x1) (leaf 0)))
              (leaf 1))
            («Language.objs» ([] : List T))) ::
          x4))
      ([] : List T)
      x2;
    x3

def «Authoring.depthOf» :=
  fun (x0 : T) =>
    let x1 : T := (if («Authoring.word»
      x0
      (mk 0 [leaf 104, leaf 101, leaf 97, leaf 100])).label ≠ 0 then
      «Prelude.some» (leaf 0)
    else
      if («Authoring.word»
        x0
        (mk 0 [leaf 119, leaf 101, leaf 97, leaf 107])).label ≠ 0 then
        «Prelude.some» (leaf 1)
      else
        if («Authoring.word»
          x0
          (mk 0 [leaf 111, leaf 112, leaf 101, leaf 110])).label ≠ 0 then
          «Prelude.some» (leaf 2)
        else
          if («Authoring.word»
            x0
            (mk 0 [leaf 102, leaf 117, leaf 108, leaf 108])).label ≠ 0 then
            «Prelude.some» (leaf 3)
          else
            «Prelude.none»);
    x1

def «Authoring.scriptStep» :=
  fun (x0 : List T)
    (x1 : T)
    (x2 : List
      (List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x3 : List T →
      List T →
        T ×
          (T →
            List T →
              List T →
                List T →
                  List T →
                    T →
                      T →
                        T) := (let x3 : List T := Const.children x1;
                               let x4 : T := «Prelude.length» x3;
                               let x5 : T := «Prelude.at» x3 (leaf 1);
                               let x6 : T →
                                 List T →
                                   List T →
                                     T ×
                                       (T →
                                         List T →
                                           List T →
                                             List T →
                                               List T →
                                                 T →
                                                   T →
                                                     T) := (fun (x6 : T) =>
                                 «Authoring/SRs.atOr» «Authoring.failSR» x2 x6);
                               fun (x7 : List T) (x8 : List T) =>
                                 let x9 : T →
                                   List
                                     T := (fun (x9 : T) =>
                                   «Authoring.rulesFrom» x8 x0 («Prelude.drop» x9 x3));
                                 let x10 : T →
                                   T := (fun (x10 : T) =>
                                   «Base.allT» («Authoring.ruleOk» x8 x0) («Prelude.drop» x10 x3));
                                 let x11 : List T →
                                   List T →
                                     T := (fun (x11 : List T) (x12 : List T) =>
                                   «Prelude.and»
                                     («Base.allT» «Authoring.declared» x12)
                                     («Authoring.distinctFrom»
                                       («Prelude.append» x11 («Prelude.append» x8 x0))
                                       («Base.mapT» «Reader.nameOf» x12)));
                                 if («Base.not» («Reader.isList» x1)).label ≠ 0 then
                                   (leaf 0, «Authoring.failTac»)
                                 else
                                   if («Authoring.headed»
                                     x1
                                     (mk 0 [leaf 110,
                                       leaf 111,
                                       leaf 114,
                                       leaf 109,
                                       leaf 97,
                                       leaf 108,
                                       leaf 105,
                                       leaf 122,
                                       leaf 101])).label ≠ 0 then
                                     («Prelude.and»
                                       (Const.lt (leaf 1) x4)
                                       («Prelude.and»
                                         («Prelude.isSome» («Authoring.number» x5))
                                         (x10 (leaf 2))),
                                       fun (x12 : T)
                                         (x13 : List T)
                                         (x14 : List T)
                                         (x15 : List T)
                                         (x16 : List T)
                                         (x17 : T)
                                         (x18 : T) =>
                                         «Prover.byNormW»
                                           x12
                                           x13
                                           (leaf 0)
                                           («Authoring/Rules.append» (x9 (leaf 2)) x14)
                                           («Base.getD» («Authoring.number» x5) (leaf 0))
                                           x15
                                           x16
                                           x17
                                           x18)
                                   else
                                     if («Authoring.headed»
                                       x1
                                       (mk 0 [leaf 114,
                                         leaf 101,
                                         leaf 100,
                                         leaf 117,
                                         leaf 99,
                                         leaf 101])).label ≠ 0 then
                                       («Prelude.and»
                                         (Const.lt (leaf 1) x4)
                                         («Prelude.and»
                                           («Prelude.isSome» («Authoring.depthOf» x5))
                                           (x10 (leaf 2))),
                                         fun (x12 : T) (x13 : List T) (x14 : List T) =>
                                           «Tactics.byMode»
                                             («Base.getD» («Authoring.depthOf» x5) (leaf 0))
                                             x12
                                             x13
                                             (leaf 0)
                                             («Authoring/Rules.append» (x9 (leaf 2)) x14))
                                     else
                                       if («Authoring.headed»
                                         x1
                                         (mk 0 [leaf 97,
                                           leaf 117,
                                           leaf 116,
                                           leaf 111])).label ≠ 0 then
                                         («Prelude.and»
                                           (Const.lt (leaf 2) x4)
                                           («Prelude.and»
                                             («Prelude.isSome» («Authoring.depthOf» x5))
                                             («Prelude.and»
                                               («Prelude.isSome»
                                                 («Authoring.number» («Prelude.at» x3 (leaf 2))))
                                               (x10 (leaf 3)))),
                                           fun (x12 : T) (x13 : List T) (x14 : List T) =>
                                             «Tactics.byAuto»
                                               x12
                                               x13
                                               (leaf 0)
                                               («Authoring/Rules.append» (x9 (leaf 3)) x14)
                                               («Base.getD»
                                                 («Authoring.number» («Prelude.at» x3 (leaf 2)))
                                                 (leaf 0))
                                               («Base.getD» («Authoring.depthOf» x5) (leaf 0)))
                                       else
                                         if («Authoring.form»
                                           x1
                                           (mk 0 [leaf 101,
                                             leaf 120,
                                             leaf 116,
                                             leaf 101,
                                             leaf 110,
                                             leaf 115,
                                             leaf 105,
                                             leaf 111,
                                             leaf 110,
                                             leaf 97,
                                             leaf 108,
                                             leaf 105,
                                             leaf 116,
                                             leaf 121])
                                           (leaf 3)).label ≠ 0 then
                                           let x12 : T ×
                                             (T →
                                               List T →
                                                 List T →
                                                   List T →
                                                     List T →
                                                       T →
                                                         T →
                                                           T) := x6
                                             (leaf 2)
                                             ((«Reader.nameOf» x5) :: x7)
                                             x8;
                                           («Prelude.and» (x11 x7 («Prelude.single» x5)) (x12).1,
                                             fun (x13 : T) (x14 : List T) (x15 : List T) =>
                                               «Prover.byFunExt» x13 (leaf 0) ((x12).2 x13 x14 x15))
                                         else
                                           let x12 : List
                                             T := Const.children («Prelude.at» x3 (leaf 2));
                                           let x13 : T := «Reader.nameOf»
                                             («Prelude.at» x12 (leaf 0));
                                           let x14 : T := «Reader.nameOf»
                                             («Prelude.at» x12 (leaf 1));
                                           if («Authoring.form»
                                             x1
                                             (mk 0 [leaf 105,
                                               leaf 110,
                                               leaf 100,
                                               leaf 117,
                                               leaf 99,
                                               leaf 116,
                                               leaf 105,
                                               leaf 111,
                                               leaf 110])
                                             (leaf 5)).label ≠ 0 then
                                             let x15 : List T := «Prelude.drop» (leaf 1) x7;
                                             let x16 : T ×
                                               (T →
                                                 List T →
                                                   List T →
                                                     List T →
                                                       List T → T → T → T) := x6 (leaf 3) x15 x8;
                                             let x17 : T ×
                                               (T →
                                                 List T →
                                                   List T →
                                                     List T →
                                                       List T →
                                                         T →
                                                           T →
                                                             T) := x6
                                               (leaf 4)
                                               (x14 :: (x13 :: x15))
                                               («Prelude.append»
                                                 x8
                                                 («Prelude.single»
                                                   («Reader.nameOf» («Prelude.at» x12 (leaf 2)))));
                                             («Prelude.and»
                                               («Prelude.and»
                                                 («Base.not» («Base.isEmpty» x7))
                                                 («Authoring.word» x5 («Prelude.at» x7 (leaf 0))))
                                               («Prelude.and»
                                                 («Reader.isList» («Prelude.at» x3 (leaf 2)))
                                                 («Prelude.and»
                                                   (Const.eq («Prelude.length» x12) (leaf 3))
                                                   («Prelude.and»
                                                     (x11 x15 x12)
                                                     («Prelude.and» (x16).1 (x17).1)))),
                                               fun (x18 : T) (x19 : List T) (x20 : List T) =>
                                                 «Prover.byListIndWith»
                                                   x18
                                                   (leaf 0)
                                                   (leaf 0)
                                                   (leaf 1)
                                                   ((x16).2 x18 x19 x20)
                                                   ((x17).2 x18 x19 x20))
                                           else
                                             if («Authoring.form»
                                               x1
                                               (mk 0 [leaf 99,
                                                 leaf 97,
                                                 leaf 115,
                                                 leaf 101,
                                                 leaf 115])
                                               (leaf 5)).label ≠ 0 then
                                               let x15 : T := «Reader.indexOf»
                                                 («Reader.nameOf» x5)
                                                 x7;
                                               let x16 : T ×
                                                 (T →
                                                   List T →
                                                     List T →
                                                       List T →
                                                         List T → T → T → T) := x6 (leaf 3) x7 x8;
                                               let x17 : T ×
                                                 (T →
                                                   List T →
                                                     List T →
                                                       List T →
                                                         List T →
                                                           T →
                                                             T →
                                                               T) := x6
                                                 (leaf 4)
                                                 (x14 :: (x13 :: x7))
                                                 («Prelude.append»
                                                   x8
                                                   («Prelude.single»
                                                     (Const.node (leaf 0) ([] : List T))));
                                               («Prelude.and»
                                                 («Reader.isAtom» x5)
                                                 («Prelude.and»
                                                   («Prelude.isSome» x15)
                                                   («Prelude.and»
                                                     («Reader.isList» («Prelude.at» x3 (leaf 2)))
                                                     («Prelude.and»
                                                       (Const.eq («Prelude.length» x12) (leaf 2))
                                                       («Prelude.and»
                                                         (x11 x7 x12)
                                                         («Prelude.and» (x16).1 (x17).1))))),
                                                 fun (x18 : T) (x19 : List T) (x20 : List T) =>
                                                   «Tactics.byListSplit»
                                                     x18
                                                     (leaf 0)
                                                     («Base.getD» x15 (leaf 0))
                                                     ((x16).2 x18 x19 x20)
                                                     ((x17).2 x18 x19 x20))
                                             else
                                               if («Authoring.form»
                                                 x1
                                                 (mk 0 [leaf 114,
                                                   leaf 101,
                                                   leaf 100,
                                                   leaf 117,
                                                   leaf 99,
                                                   leaf 101,
                                                   leaf 45,
                                                   leaf 104,
                                                   leaf 121,
                                                   leaf 112,
                                                   leaf 111,
                                                   leaf 116,
                                                   leaf 104,
                                                   leaf 101,
                                                   leaf 115,
                                                   leaf 101,
                                                   leaf 115])
                                                 (leaf 4)).label ≠ 0 then
                                                 let x15 : List
                                                   T := «Base.mapT»
                                                   «Reader.nameOf»
                                                   (Const.children («Prelude.at» x3 (leaf 2)));
                                                 let x16 : T ×
                                                   (T →
                                                     List T →
                                                       List T →
                                                         List T →
                                                           List T →
                                                             T →
                                                               T →
                                                                 T) := x6
                                                   (leaf 3)
                                                   x7
                                                   («Prelude.append»
                                                     («Base.mapT»
                                                       (fun (x16 : T) =>
                                                         if («Authoring.has» x16 x15).label ≠ 0 then
                                                           Const.node (leaf 0) ([] : List T)
                                                         else
                                                           x16)
                                                       x8)
                                                     x15);
                                                 («Prelude.and»
                                                   («Prelude.isSome» («Authoring.depthOf» x5))
                                                   («Prelude.and»
                                                     («Reader.isList» («Prelude.at» x3 (leaf 2)))
                                                     («Prelude.and»
                                                       («Base.not» («Base.isEmpty» x15))
                                                       («Prelude.and»
                                                         («Base.allT»
                                                           (fun (x17 : T) =>
                                                             «Prelude.and»
                                                               («Reader.isAtom» x17)
                                                               («Authoring.has»
                                                                 («Reader.nameOf» x17)
                                                                 x8))
                                                           (Const.children
                                                             («Prelude.at» x3 (leaf 2))))
                                                         («Prelude.and»
                                                           («Authoring.distinctFrom»
                                                             ([] : List T)
                                                             x15)
                                                           (x16).1)))),
                                                   fun (x17 : T) (x18 : List T) (x19 : List T) =>
                                                     «Tactics.withWeakHyps»
                                                       x17
                                                       x18
                                                       (leaf 0)
                                                       x19
                                                       («Base.mapT»
                                                         (fun (x20 : T) =>
                                                           «Base.getD»
                                                             («Reader.indexOf» x20 x8)
                                                             (leaf 0))
                                                         x15)
                                                       (fun (_ : List T) => (x16).2 x17 x18 x19)
                                                       («Base.getD»
                                                         («Authoring.depthOf» x5)
                                                         (leaf 0)))
                                               else
                                                 (leaf 0, «Authoring.failTac»));
    x3

def «Authoring.readScript» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : List T →
      List T →
        T ×
          (T →
            List T →
              List T →
                List T →
                  List T →
                    T →
                      T →
                        T) := Const.para
      (α := List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T))
      («Authoring.scriptStep» x0)
      x1;
    x2

def «Authoring.request» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «Authoring/OR.nothing» := Const.node (leaf 0) ([] : List T)

def «Authoring/OR.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Authoring/OR.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let x2 : List T := Const.children x1;
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x2
                       (leaf 0)
                       (fun (x3 : T) (_ : List T) => x3);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x2
                       ([] : List T)
                       (fun (_ : T) (x5 : List T) => x5);
                     leaf 1
                   else
                     let _ : List T := Const.children x1; leaf 0);
    x1

def «Authoring/OR.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x4
                   else
                     let _ : List T := Const.children x2; x0);
    x2

def «Authoring/OR.nthOf» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.lcase
      (α := T)
      (β := T)
      (Const.iter
        (α := List T)
        (fun (x2 : List T) =>
          Const.lcase
            (α := T)
            (β := List T)
            x2
            ([] : List T)
            (fun (_ : T) (x4 : List T) => x4))
        x0
        x1)
      «Authoring/OR.nothing»
      (fun (x2 : T) (_ : List T) => «Authoring/OR.just» x2);
    x2

def «Authoring/OR.allJust» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x4 : List T := Const.children x3;
          let x5 : T := Const.lcase
            (α := T)
            (β := T)
            x4
            (leaf 0)
            (fun (x5 : T) (_ : List T) => x5);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x4
            ([] : List T)
            (fun (_ : T) (x7 : List T) => x7);
          ((x2).1, (x5 :: (x2).2))
        else
          let _ : List T := Const.children x3; (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Authoring.requestName» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : List T := Const.children x1;
                   let x3 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x2
                     (leaf 0)
                     (fun (x3 : T) (_ : List T) => x3);
                   let x4 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x2
                     ([] : List T)
                     (fun (_ : T) (x5 : List T) => x5);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let x6 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x6
                     (leaf 0)
                     (fun (x7 : T) (_ : List T) => x7);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x6
                     ([] : List T)
                     (fun (_ : T) (x9 : List T) => x9);
                   x3);
    x1

def «Authoring.requestThm» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : List T := Const.children x1;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x2
                     (leaf 0)
                     (fun (x3 : T) (_ : List T) => x3);
                   let x4 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x2
                     ([] : List T)
                     (fun (_ : T) (x5 : List T) => x5);
                   let x5 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let x6 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x6
                     (leaf 0)
                     (fun (x7 : T) (_ : List T) => x7);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x6
                     ([] : List T)
                     (fun (_ : T) (x9 : List T) => x9);
                   let x9 : T := x5;
                   let x10 : List T := Const.children x9;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x10
                     (leaf 0)
                     (fun (x11 : T) (_ : List T) => x11);
                   let x12 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x10
                     ([] : List T)
                     (fun (_ : T) (x13 : List T) => x13);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x12
                     (leaf 0)
                     (fun (x13 : T) (_ : List T) => x13);
                   let x14 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x12
                     ([] : List T)
                     (fun (_ : T) (x15 : List T) => x15);
                   let x15 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x14
                     (leaf 0)
                     (fun (x15 : T) (_ : List T) => x15);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x14
                     ([] : List T)
                     (fun (_ : T) (x17 : List T) => x17);
                   x15);
    x1

def «Authoring.version0» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (let x2 : T := Const.child x1 (leaf 2);
                   let x3 : T := Const.child x1 (leaf 3);
                   «Prelude.and»
                     («Authoring.form»
                       x2
                       (mk 0 [leaf 101, leaf 113, leaf 117, leaf 97, leaf 108])
                       (leaf 3))
                     («Prelude.and»
                       («Prelude.and»
                         («Reader.isAtom» (Const.child x2 (leaf 1)))
                         («Authoring.has» («Reader.nameOf» (Const.child x2 (leaf 1))) x0))
                       («Prelude.and»
                         («Prelude.and»
                           («Reader.isAtom» (Const.child x2 (leaf 2)))
                           («Authoring.has» («Reader.nameOf» (Const.child x2 (leaf 2))) x0))
                         («Prelude.and»
                           («Authoring.form» x3 (mk 0 [leaf 98, leaf 121]) (leaf 2))
                           («Authoring.form»
                             (Const.child x3 (leaf 1))
                             (mk 0 [leaf 110,
                               leaf 111,
                               leaf 114,
                               leaf 109,
                               leaf 97,
                               leaf 108,
                               leaf 105,
                               leaf 122,
                               leaf 101])
                             (leaf 2))))));
    x2

def «Authoring.theoremName» :=
  fun (x0 : T) =>
    let x1 : T := (if («Prelude.and»
      («Reader.isList» x0)
      (Const.lt
        (leaf 1)
        («Prelude.length» (Const.children x0)))).label ≠ 0 then
      «Reader.nameOf» (Const.child x0 (leaf 1))
    else
      Const.node (leaf 0) ([] : List T));
    x1

def «Authoring.readRequest» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T) =>
    let x6 : T := (if («Prelude.and»
      («Authoring.form»
        x5
        (mk 0 [leaf 116,
          leaf 104,
          leaf 101,
          leaf 111,
          leaf 114,
          leaf 101,
          leaf 109])
        (leaf 4))
      («Prelude.and»
        («Reader.isAtom» (Const.child x5 (leaf 1)))
        («Prelude.and»
          («Base.not»
            («Base.isEmpty» (Const.children (Const.child x5 (leaf 1)))))
          («Prelude.and»
            («Authoring.form»
              (Const.child x5 (leaf 3))
              (mk 0 [leaf 98, leaf 121])
              (leaf 2))
            («Prelude.or»
              (Const.eq x0 (leaf 1))
              («Authoring.version0» x2 x5)))))).label ≠ 0 then
      let x6 : T := «Authoring.readStatement»
        x1
        x2
        («Prelude.append» x2 x3)
        (Const.child x5 (leaf 2));
      if (Const.eq (Const.label x6) (leaf 0)).label ≠ 0 then
        let _ : List T := Const.children x6; «Authoring/OR.nothing»
      else
        let x7 : List T := Const.children x6;
        let x8 : T := Const.lcase
          (α := T)
          (β := T)
          x7
          (leaf 0)
          (fun (x8 : T) (_ : List T) => x8);
        let _ : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x7
          ([] : List T)
          (fun (_ : T) (x10 : List T) => x10);
        let x10 : T := x8;
        let x11 : List T := Const.children x10;
        let x12 : T := Const.lcase
          (α := T)
          (β := T)
          x11
          (leaf 0)
          (fun (x12 : T) (_ : List T) => x12);
        let x13 : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x11
          ([] : List T)
          (fun (_ : T) (x14 : List T) => x14);
        let x14 : T := Const.lcase
          (α := T)
          (β := T)
          x13
          (leaf 0)
          (fun (x14 : T) (_ : List T) => x14);
        let x15 : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x13
          ([] : List T)
          (fun (_ : T) (x16 : List T) => x16);
        let _ : T := Const.lcase
          (α := T)
          (β := T)
          x15
          (leaf 0)
          (fun (x16 : T) (_ : List T) => x16);
        let _ : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x15
          ([] : List T)
          (fun (_ : T) (x18 : List T) => x18);
        let x18 : T := Const.child (Const.child x5 (leaf 3)) (leaf 1);
        if ((«Authoring.readScript»
          x4
          x18
          (Const.children x12)
          (Const.children x14)).1).label ≠ 0 then
          «Authoring/OR.just»
            («Authoring.request»
              («Reader.nameOf» (Const.child x5 (leaf 1)))
              x8
              x18)
        else
          «Authoring/OR.nothing»
    else
      «Authoring/OR.nothing»);
    x6

def «Authoring/Requests.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Authoring/Requests.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/Requests.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/Requests.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Authoring/Requests.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Authoring/Requests.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Authoring/Requests.tail» x1 x0;
    x2

def «Authoring/Requests.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Authoring/Requests.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Authoring.requests» :=
  fun (x0 : T) (x1 : List T) => Const.node (leaf 0) (x0 :: x1)

def «Authoring/ORequests.nothing» := Const.node (leaf 0) ([] : List T)

def «Authoring/ORequests.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Authoring/ORequests.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let x2 : List T := Const.children x1;
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x2
                       (leaf 0)
                       (fun (x3 : T) (_ : List T) => x3);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x2
                       ([] : List T)
                       (fun (_ : T) (x5 : List T) => x5);
                     leaf 1
                   else
                     let _ : List T := Const.children x1; leaf 0);
    x1

def «Authoring/ORequests.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x4
                   else
                     let _ : List T := Const.children x2; x0);
    x2

def «Authoring/ORequests.nthOf» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.lcase
      (α := T)
      (β := T)
      (Const.iter
        (α := List T)
        (fun (x2 : List T) =>
          Const.lcase
            (α := T)
            (β := List T)
            x2
            ([] : List T)
            (fun (_ : T) (x4 : List T) => x4))
        x0
        x1)
      «Authoring/ORequests.nothing»
      (fun (x2 : T) (_ : List T) => «Authoring/ORequests.just» x2);
    x2

def «Authoring/ORequests.allJust» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x4 : List T := Const.children x3;
          let x5 : T := Const.lcase
            (α := T)
            (β := T)
            x4
            (leaf 0)
            (fun (x5 : T) (_ : List T) => x5);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x4
            ([] : List T)
            (fun (_ : T) (x7 : List T) => x7);
          ((x2).1, (x5 :: (x2).2))
        else
          let _ : List T := Const.children x3; (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Authoring.readSource» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : T := (let x3 : T := «Reader.readSExps» (Const.children x2);
                   let x4 : T := Const.child («Prelude.get» x3) (leaf 0);
                   let x5 : T := «Authoring.number» (Const.child x4 (leaf 1));
                   if («Prelude.and»
                     («Prelude.isSome» x3)
                     («Prelude.and»
                       (Const.eq
                         («Prelude.length» (Const.children («Prelude.get» x3)))
                         (leaf 1))
                       («Prelude.and»
                         («Reader.isList» x4)
                         («Prelude.and»
                           («Authoring.word»
                             (Const.child x4 (leaf 0))
                             (mk 0 [leaf 112, leaf 114, leaf 111, leaf 111, leaf 102, leaf 115]))
                           («Prelude.and»
                             («Prelude.isSome» x5)
                             («Prelude.and»
                               (Const.lt («Prelude.get» x5) (leaf 2))
                               (Const.lt
                                 (leaf 2)
                                 («Prelude.length» (Const.children x4))))))))).label ≠ 0 then
                     let x6 : List T := «Prelude.drop» (leaf 2) (Const.children x4);
                     let x7 : List T := «Base.mapT» «Authoring.theoremName» x6;
                     if («Authoring.distinctFrom» ([] : List T) x7).label ≠ 0 then
                       Const.foldr
                         (α := T)
                         (β := T)
                         (fun (x8 : T) (x9 : T) =>
                           let x10 : T := x9;
                           if (Const.eq (Const.label x10) (leaf 0)).label ≠ 0 then
                             let _ : List T := Const.children x10; «Authoring/ORequests.nothing»
                           else
                             let x11 : List T := Const.children x10;
                             let x12 : T := Const.lcase
                               (α := T)
                               (β := T)
                               x11
                               (leaf 0)
                               (fun (x12 : T) (_ : List T) => x12);
                             let _ : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x11
                               ([] : List T)
                               (fun (_ : T) (x14 : List T) => x14);
                             let x14 : T := x12;
                             let x15 : List T := Const.children x14;
                             let x16 : T := Const.lcase
                               (α := T)
                               (β := T)
                               x15
                               (leaf 0)
                               (fun (x16 : T) (_ : List T) => x16);
                             let x17 : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x15
                               ([] : List T)
                               (fun (_ : T) (x18 : List T) => x18);
                             let x18 : List T := x17;
                             let x19 : T := «Authoring.readRequest»
                               x16
                               x0
                               x1
                               x7
                               («Base.take» x8 x7)
                               («Prelude.at» x6 x8);
                             if (Const.eq (Const.label x19) (leaf 0)).label ≠ 0 then
                               let _ : List T := Const.children x19; «Authoring/ORequests.nothing»
                             else
                               let x20 : List T := Const.children x19;
                               let x21 : T := Const.lcase
                                 (α := T)
                                 (β := T)
                                 x20
                                 (leaf 0)
                                 (fun (x21 : T) (_ : List T) => x21);
                               let _ : List
                                 T := Const.lcase
                                 (α := T)
                                 (β := List T)
                                 x20
                                 ([] : List T)
                                 (fun (_ : T) (x23 : List T) => x23);
                               «Authoring/ORequests.just» («Authoring.requests» x16 (x21 :: x18)))
                         («Authoring/ORequests.just»
                           («Authoring.requests» («Prelude.get» x5) ([] : List T)))
                         («Base.range» («Prelude.length» x6))
                     else
                       «Authoring/ORequests.nothing»
                   else
                     «Authoring/ORequests.nothing»);
    x3

def «Authoring.results» :=
  fun (x0 : T) (x1 : List T) => Const.node (leaf 0) (x0 :: x1)

def «Authoring.Results.member» :=
  fun (x0 : T) =>
    Const.mod
      (Const.div
        (Const.fold
          (α := T)
          (fun (x1 : T) (x2 : List T) =>
            let x3 : T := Const.node (leaf 0) x2;
            Const.add
              (if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                if (Const.lt
                  (leaf 1)
                  (Const.add (Const.arity x3) (leaf 1))).label ≠ 0 then
                  Const.foldr
                    (α := T)
                    (β := T)
                    (fun (x4 : T) (x5 : T) =>
                      if (Const.mod (Const.div x4 (leaf 2)) (leaf 2)).label ≠ 0 then
                        x5
                      else
                        leaf 0)
                    (leaf 1)
                    (Const.iter
                      (α := List T)
                      (fun (x4 : List T) =>
                        Const.lcase
                          (α := T)
                          (β := List T)
                          x4
                          ([] : List T)
                          (fun (_ : T) (x6 : List T) => x6))
                      x2
                      (leaf 1))
                else
                  leaf 0
              else
                leaf 0).label ≠ 0 then
                leaf 1
              else
                leaf 0)
              (Const.add
                (if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                  if (Const.eq (Const.arity x3) (leaf 2)).label ≠ 0 then
                    Const.mod (Const.div (Const.child x3 (leaf 0)) (leaf 4)) (leaf 2)
                  else
                    leaf 0
                else
                  if (Const.eq x1 (leaf 1)).label ≠ 0 then
                    if (Const.eq (Const.arity x3) (leaf 2)).label ≠ 0 then
                      Const.mod (Const.div (Const.child x3 (leaf 0)) (leaf 8)) (leaf 2)
                    else
                      leaf 0
                  else
                    if (Const.eq x1 (leaf 2)).label ≠ 0 then
                      if (Const.eq (Const.arity x3) (leaf 1)).label ≠ 0 then
                        Const.mod (Const.div (Const.child x3 (leaf 0)) (leaf 16)) (leaf 2)
                      else
                        leaf 0
                    else
                      if (Const.eq x1 (leaf 3)).label ≠ 0 then
                        if (Const.eq (Const.arity x3) (leaf 2)).label ≠ 0 then
                          Const.mod (Const.div (Const.child x3 (leaf 0)) (leaf 32)) (leaf 2)
                        else
                          leaf 0
                      else
                        if (Const.eq x1 (leaf 4)).label ≠ 0 then
                          Const.eq (Const.arity x3) (leaf 3)
                        else
                          if (Const.eq x1 (leaf 5)).label ≠ 0 then
                            Const.eq (Const.arity x3) (leaf 3)
                          else
                            if (Const.eq x1 (leaf 6)).label ≠ 0 then
                              Const.eq (Const.arity x3) (leaf 4)
                            else
                              leaf 0).label ≠ 0 then
                  leaf 2
                else
                  leaf 0)
                (Const.add
                  (if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                    if (Const.eq (Const.arity x3) (leaf 4)).label ≠ 0 then
                      if (Const.mod
                        (Const.div (Const.child x3 (leaf 1)) (leaf 64))
                        (leaf 2)).label ≠ 0 then
                        Const.mod (Const.div (Const.child x3 (leaf 2)) (leaf 1024)) (leaf 2)
                      else
                        leaf 0
                    else
                      leaf 0
                  else
                    leaf 0).label ≠ 0 then
                    leaf 4
                  else
                    leaf 0)
                  (Const.add
                    (if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                      if (Const.eq (Const.arity x3) (leaf 3)).label ≠ 0 then
                        if (Const.mod
                          (Const.div (Const.child x3 (leaf 0)) (leaf 128))
                          (leaf 2)).label ≠ 0 then
                          if (Const.mod
                            (Const.div (Const.child x3 (leaf 1)) (leaf 256))
                            (leaf 2)).label ≠ 0 then
                            Const.mod (Const.div (Const.child x3 (leaf 2)) (leaf 512)) (leaf 2)
                          else
                            leaf 0
                        else
                          leaf 0
                      else
                        leaf 0
                    else
                      leaf 0).label ≠ 0 then
                      leaf 8
                    else
                      leaf 0)
                    (Const.add
                      (if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                        if (Const.eq (Const.arity x3) (leaf 4)).label ≠ 0 then
                          Const.mod (Const.div (Const.child x3 (leaf 1)) (leaf 64)) (leaf 2)
                        else
                          leaf 0
                      else
                        leaf 0).label ≠ 0 then
                        leaf 16
                      else
                        leaf 0)
                      (Const.add
                        (if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                          Const.eq (Const.arity x3) (leaf 4)
                        else
                          leaf 0).label ≠ 0 then
                          leaf 32
                        else
                          leaf 0)
                        (Const.add
                          (if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                            Const.lt (leaf 0) (Const.add (Const.arity x3) (leaf 1))
                          else
                            leaf 0).label ≠ 0 then
                            leaf 64
                          else
                            leaf 0)
                          (Const.add
                            (if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                              Const.lt (leaf 0) (Const.add (Const.arity x3) (leaf 1))
                            else
                              leaf 0).label ≠ 0 then
                              leaf 128
                            else
                              leaf 0)
                            (Const.add
                              (if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                                if (Const.lt
                                  (leaf 0)
                                  (Const.add (Const.arity x3) (leaf 1))).label ≠ 0 then
                                  Const.foldr
                                    (α := T)
                                    (β := T)
                                    (fun (x4 : T) (x5 : T) =>
                                      if (Const.mod
                                        (Const.div x4 (leaf 512))
                                        (leaf 2)).label ≠ 0 then
                                        x5
                                      else
                                        leaf 0)
                                    (leaf 1)
                                    (Const.iter
                                      (α := List T)
                                      (fun (x4 : List T) =>
                                        Const.lcase
                                          (α := T)
                                          (β := List T)
                                          x4
                                          ([] : List T)
                                          (fun (_ : T) (x6 : List T) => x6))
                                      x2
                                      (leaf 0))
                                else
                                  leaf 0
                              else
                                leaf 0).label ≠ 0 then
                                leaf 256
                              else
                                leaf 0)
                              (Const.add
                                (if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                                  Const.eq (Const.arity x3) (leaf 2)
                                else
                                  leaf 0).label ≠ 0 then
                                  leaf 512
                                else
                                  leaf 0)
                                (Const.add
                                  (if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                                    Const.lt (leaf 0) (Const.add (Const.arity x3) (leaf 1))
                                  else
                                    leaf 0).label ≠ 0 then
                                    leaf 1024
                                  else
                                    leaf 0)
                                  (leaf 0))))))))))))
          x0)
        (leaf 1))
      (leaf 2)

def «Authoring/OResults.nothing» := Const.node (leaf 0) ([] : List T)

def «Authoring/OResults.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Authoring/OResults.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let x2 : List T := Const.children x1;
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x2
                       (leaf 0)
                       (fun (x3 : T) (_ : List T) => x3);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x2
                       ([] : List T)
                       (fun (_ : T) (x5 : List T) => x5);
                     leaf 1
                   else
                     let _ : List T := Const.children x1; leaf 0);
    x1

def «Authoring/OResults.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x4
                   else
                     let _ : List T := Const.children x2; x0);
    x2

def «Authoring/OResults.nthOf» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.lcase
      (α := T)
      (β := T)
      (Const.iter
        (α := List T)
        (fun (x2 : List T) =>
          Const.lcase
            (α := T)
            (β := List T)
            x2
            ([] : List T)
            (fun (_ : T) (x4 : List T) => x4))
        x0
        x1)
      «Authoring/OResults.nothing»
      (fun (x2 : T) (_ : List T) => «Authoring/OResults.just» x2);
    x2

def «Authoring/OResults.allJust» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x4 : List T := Const.children x3;
          let x5 : T := Const.lcase
            (α := T)
            (β := T)
            x4
            (leaf 0)
            (fun (x5 : T) (_ : List T) => x5);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x4
            ([] : List T)
            (fun (_ : T) (x7 : List T) => x7);
          ((x2).1, (x5 :: (x2).2))
        else
          let _ : List T := Const.children x3; (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Authoring.entriesOf» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x1 : T) (x2 : List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 0)).label ≠ 0 then
          let x4 : List T := Const.children x3;
          let x5 : T := Const.lcase
            (α := T)
            (β := T)
            x4
            (leaf 0)
            (fun (x5 : T) (_ : List T) => x5);
          let x6 : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x4
            ([] : List T)
            (fun (_ : T) (x7 : List T) => x7);
          let _ : T := Const.lcase
            (α := T)
            (β := T)
            x6
            (leaf 0)
            (fun (x7 : T) (_ : List T) => x7);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x6
            ([] : List T)
            (fun (_ : T) (x9 : List T) => x9);
          ((«Derivation.entLang» x5) :: x2)
        else
          x2)
      ([] : List T)
      x0;
    x1

def «Authoring.derive» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : List T) (x4 : T) =>
    let x5 : T := (let x5 : T := x4;
                   let x6 : List T := Const.children x5;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x6
                     (leaf 0)
                     (fun (x7 : T) (_ : List T) => x7);
                   let x8 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x6
                     ([] : List T)
                     (fun (_ : T) (x9 : List T) => x9);
                   let x9 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x8
                     (leaf 0)
                     (fun (x9 : T) (_ : List T) => x9);
                   let x10 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x8
                     ([] : List T)
                     (fun (_ : T) (x11 : List T) => x11);
                   let x11 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x10
                     (leaf 0)
                     (fun (x11 : T) (_ : List T) => x11);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x10
                     ([] : List T)
                     (fun (_ : T) (x13 : List T) => x13);
                   let x13 : T := x9;
                   let x14 : List T := Const.children x13;
                   let x15 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x14
                     (leaf 0)
                     (fun (x15 : T) (_ : List T) => x15);
                   let x16 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x14
                     ([] : List T)
                     (fun (_ : T) (x17 : List T) => x17);
                   let x17 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x16
                     (leaf 0)
                     (fun (x17 : T) (_ : List T) => x17);
                   let x18 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x16
                     ([] : List T)
                     (fun (_ : T) (x19 : List T) => x19);
                   let x19 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x18
                     (leaf 0)
                     (fun (x19 : T) (_ : List T) => x19);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x18
                     ([] : List T)
                     (fun (_ : T) (x21 : List T) => x21);
                   let x21 : T := x19;
                   let x22 : List T := Const.children x21;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x22
                     (leaf 0)
                     (fun (x23 : T) (_ : List T) => x23);
                   let x24 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x22
                     ([] : List T)
                     (fun (_ : T) (x25 : List T) => x25);
                   let x25 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x24
                     (leaf 0)
                     (fun (x25 : T) (_ : List T) => x25);
                   let x26 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x24
                     ([] : List T)
                     (fun (_ : T) (x27 : List T) => x27);
                   let x27 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x26
                     (leaf 0)
                     (fun (x27 : T) (_ : List T) => x27);
                   let x28 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x26
                     ([] : List T)
                     (fun (_ : T) (x29 : List T) => x29);
                   let x29 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x28
                     (leaf 0)
                     (fun (x29 : T) (_ : List T) => x29);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x28
                     ([] : List T)
                     (fun (_ : T) (x31 : List T) => x31);
                   let x31 : T := x25;
                   let x32 : List T := Const.children x31;
                   let x33 : List T := x32;
                   let x34 : T := x27;
                   let x35 : List T := Const.children x34;
                   let x36 : List T := x35;
                   let x37 : T := «Derivation.eqParts» x29;
                   if (Const.eq (Const.label x37) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x37; «Prelude.none»
                   else
                     let x38 : List T := Const.children x37;
                     let x39 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x38
                       (leaf 0)
                       (fun (x39 : T) (_ : List T) => x39);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x38
                       ([] : List T)
                       (fun (_ : T) (x41 : List T) => x41);
                     («Authoring.readScript»
                       x3
                       x11
                       (Const.children x15)
                       (Const.children x17)).2
                       x0
                       x1
                       x2
                       x33
                       x36
                       («Language.p1» x39)
                       («Language.p2» x39));
    x5

def «Authoring.companion» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : T) (x4 : T) =>
    let x5 : T := (let x5 : T := x4;
                   let x6 : List T := Const.children x5;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x6
                     (leaf 0)
                     (fun (x7 : T) (_ : List T) => x7);
                   let x8 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x6
                     ([] : List T)
                     (fun (_ : T) (x9 : List T) => x9);
                   let x9 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x8
                     (leaf 0)
                     (fun (x9 : T) (_ : List T) => x9);
                   let x10 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x8
                     ([] : List T)
                     (fun (_ : T) (x11 : List T) => x11);
                   let x11 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x10
                     (leaf 0)
                     (fun (x11 : T) (_ : List T) => x11);
                   let x12 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x10
                     ([] : List T)
                     (fun (_ : T) (x13 : List T) => x13);
                   let x13 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x12
                     (leaf 0)
                     (fun (x13 : T) (_ : List T) => x13);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x12
                     ([] : List T)
                     (fun (_ : T) (x15 : List T) => x15);
                   let x15 : T := x9;
                   let x16 : List T := Const.children x15;
                   let x17 : List T := x16;
                   let x18 : T := x11;
                   let x19 : List T := Const.children x18;
                   let x20 : List T := x19;
                   let x21 : T := «Derivation.eqParts» x13;
                   if (Const.eq (Const.label x21) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x21; «Prelude.none»
                   else
                     let x22 : List T := Const.children x21;
                     let x23 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x22
                       (leaf 0)
                       (fun (x23 : T) (_ : List T) => x23);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x22
                       ([] : List T)
                       (fun (_ : T) (x25 : List T) => x25);
                     «Prover.bindNT»
                       («Prover.eval»
                         x0
                         x1
                         (leaf 0)
                         x2
                         (leaf 4096)
                         (leaf 1)
                         x17
                         x20
                         («Language.p1» x23))
                       (fun (x25 : T) =>
                         «Prover.bindNT»
                           («Prover.eval»
                             x0
                             x1
                             (leaf 0)
                             x2
                             (leaf 4096)
                             (leaf 1)
                             x17
                             x20
                             («Language.p2» x23))
                           (fun (x26 : T) =>
                             «Prelude.some»
                               (Const.node
                                 (leaf 0)
                                 («Theory.l3»
                                   («Prover.nfTerm» x25)
                                   («Prover.nfTerm» x26)
                                   («Prover.dNode»
                                     (leaf 24)
                                     («Prelude.single» x13)
                                     («Theory.l2»
                                       («Prover.dNode»
                                         (leaf 2)
                                         ([] : List T)
                                         («Theory.l2»
                                           («Prover.mDeriv» («Prover.nfMarked» x25))
                                           («Prover.mDeriv» («Prover.nfMarked» x26))))
                                       («Prover.dNode»
                                         (leaf 27)
                                         («Theory.l3»
                                           x3
                                           (Const.node (leaf 0) ([] : List T))
                                           (Const.node
                                             (leaf 0)
                                             («Base.mapT»
                                               «Language.var»
                                               («Base.range» («Prelude.length» x17)))))
                                         («Base.mapT»
                                           (fun (x27 : T) =>
                                             «Prover.dNode»
                                               (leaf 21)
                                               («Prelude.single» x27)
                                               ([] : List T))
                                           («Base.range» («Prelude.length» x20)))))))))));
    x5

def «Authoring.withSides» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (let x3 : T := x0;
                   let x4 : List T := Const.children x3;
                   let x5 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let x6 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   let x7 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x6
                     (leaf 0)
                     (fun (x7 : T) (_ : List T) => x7);
                   let x8 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x6
                     ([] : List T)
                     (fun (_ : T) (x9 : List T) => x9);
                   let x9 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x8
                     (leaf 0)
                     (fun (x9 : T) (_ : List T) => x9);
                   let x10 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x8
                     ([] : List T)
                     (fun (_ : T) (x11 : List T) => x11);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x10
                     (leaf 0)
                     (fun (x11 : T) (_ : List T) => x11);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x10
                     ([] : List T)
                     (fun (_ : T) (x13 : List T) => x13);
                   «Derivation.mkThm» x5 x7 x9 («Language.mEq» x1 x2));
    x3

def «Authoring.sourceNames» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := (if (Const.eq x0 (leaf 0)).label ≠ 0 then
      x1
    else
      «Base.mapT»
        (fun (x2 : T) => «Prelude.at» x1 (Const.mul (leaf 2) x2))
        («Base.range» (Const.div («Prelude.length» x1) (leaf 2))));
    x2

def «Authoring.advance» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := (let x5 : T := x4;
                   if (Const.eq (Const.label x5) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x5; «Authoring/OResults.nothing»
                   else
                     let x6 : List T := Const.children x5;
                     let x7 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x6
                       (leaf 0)
                       (fun (x7 : T) (_ : List T) => x7);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x6
                       ([] : List T)
                       (fun (_ : T) (x9 : List T) => x9);
                     let x9 : T := x7;
                     let x10 : List T := Const.children x9;
                     let x11 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x10
                       (leaf 0)
                       (fun (x11 : T) (_ : List T) => x11);
                     let x12 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x10
                       ([] : List T)
                       (fun (_ : T) (x13 : List T) => x13);
                     let x13 : List T := x12;
                     let x14 : T := «Authoring.derive»
                       x0
                       («Authoring.entriesOf» x13)
                       x1
                       («Authoring.sourceNames» x2 (Const.children x11))
                       x3;
                     if («Prelude.isSome» x14).label ≠ 0 then
                       let x15 : List
                         T := «Authoring/Decls.append»
                         x13
                         («Authoring/Decls.single»
                           («Derivation.declLang»
                             («Authoring.requestThm» x3)
                             («Prelude.get» x14)));
                       if (Const.eq x2 (leaf 0)).label ≠ 0 then
                         «Authoring/OResults.just»
                           («Authoring.results»
                             (Const.node
                               (leaf 0)
                               («Prelude.append»
                                 (Const.children x11)
                                 («Prelude.single» («Authoring.requestName» x3))))
                             x15)
                       else
                         let x16 : T := «Authoring.companion»
                           x0
                           («Authoring.entriesOf» x15)
                           x1
                           («Authoring/Decls.length» x13)
                           («Authoring.requestThm» x3);
                         if («Prelude.isSome» x16).label ≠ 0 then
                           let x17 : List T := Const.children («Prelude.get» x16);
                           «Authoring/OResults.just»
                             («Authoring.results»
                               (Const.node
                                 (leaf 0)
                                 («Prelude.append»
                                   (Const.children x11)
                                   («Theory.l2»
                                     («Authoring.requestName» x3)
                                     («Authoring.requestName» x3))))
                               («Authoring/Decls.append»
                                 x15
                                 («Authoring/Decls.single»
                                   («Derivation.declLang»
                                     («Authoring.withSides»
                                       («Authoring.requestThm» x3)
                                       («Prelude.at» x17 (leaf 0))
                                       («Prelude.at» x17 (leaf 1)))
                                     («Prelude.at» x17 (leaf 2))))))
                         else
                           «Authoring/OResults.nothing»
                     else
                       «Authoring/OResults.nothing»);
    x5

def «Authoring.proveWith» :=
  fun (x0 : List T) (x1 : List T) (x2 : List T) (x3 : T) =>
    let x4 : T := (let x4 : T := «Authoring.readSource» x0 x1 x3;
                   if (Const.eq (Const.label x4) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x4; «Prelude.none»
                   else
                     let x5 : List T := Const.children x4;
                     let x6 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x5
                       (leaf 0)
                       (fun (x6 : T) (_ : List T) => x6);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x5
                       ([] : List T)
                       (fun (_ : T) (x8 : List T) => x8);
                     let x8 : T := x6;
                     let x9 : List T := Const.children x8;
                     let x10 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x9
                       (leaf 0)
                       (fun (x10 : T) (_ : List T) => x10);
                     let x11 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x9
                       ([] : List T)
                       (fun (_ : T) (x12 : List T) => x12);
                     let x12 : List T := x11;
                     let x13 : T := «Authoring.globalsOf» x2;
                     let x14 : List
                       T := «Authoring.rulesOf»
                       x10
                       (Const.add
                         («Authoring/LD.length» «Translation.lib»)
                         («Authoring/LD.length» x2));
                     let x15 : T := Const.foldr
                       (α := T)
                       (β := T → T)
                       (fun (x15 : T) (x16 : T → T) (x17 : T) =>
                         x16 («Authoring.advance» x13 x14 x10 x15 x17))
                       (fun (x15 : T) => x15)
                       x12
                       («Authoring/OResults.just»
                         («Authoring.results»
                           (Const.node (leaf 0) ([] : List T))
                           ([] : List T)));
                     if (Const.eq (Const.label x15) (leaf 0)).label ≠ 0 then
                       let _ : List T := Const.children x15; «Prelude.none»
                     else
                       let x16 : List T := Const.children x15;
                       let x17 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x16
                         (leaf 0)
                         (fun (x17 : T) (_ : List T) => x17);
                       let _ : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x16
                         ([] : List T)
                         (fun (_ : T) (x19 : List T) => x19);
                       let x19 : T := x17;
                       let x20 : List T := Const.children x19;
                       let _ : T := Const.lcase
                         (α := T)
                         (β := T)
                         x20
                         (leaf 0)
                         (fun (x21 : T) (_ : List T) => x21);
                       let x22 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x20
                         ([] : List T)
                         (fun (_ : T) (x23 : List T) => x23);
                       let x23 : List T := x22;
                       let x24 : T := «Derivation.checkDev» x13 ([] : List T) x23;
                       if (Const.eq (Const.label x24) (leaf 0)).label ≠ 0 then
                         let _ : List T := Const.children x24; «Prelude.none»
                       else
                         let x25 : List T := Const.children x24;
                         let _ : T := Const.lcase
                           (α := T)
                           (β := T)
                           x25
                           (leaf 0)
                           (fun (x26 : T) (_ : List T) => x26);
                         let _ : List
                           T := Const.lcase
                           (α := T)
                           (β := List T)
                           x25
                           ([] : List T)
                           (fun (_ : T) (x28 : List T) => x28);
                         «Prelude.some» x17);
    x4

def «Authoring.prove» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := «Translation.program»
                     (Const.children (Const.child x0 (leaf 0)));
                   if (Const.eq (Const.label x2) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x2; «Prelude.none»
                   else
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     let x6 : T := x4;
                     let x7 : List T := Const.children x6;
                     let x8 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x7
                       (leaf 0)
                       (fun (x8 : T) (_ : List T) => x8);
                     let x9 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x7
                       ([] : List T)
                       (fun (_ : T) (x10 : List T) => x10);
                     let x10 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x9
                       (leaf 0)
                       (fun (x10 : T) (_ : List T) => x10);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x9
                       ([] : List T)
                       (fun (_ : T) (x12 : List T) => x12);
                     let x12 : T := x8;
                     let x13 : List T := Const.children x12;
                     let x14 : List T := x13;
                     let x15 : T := x10;
                     let x16 : List T := Const.children x15;
                     let x17 : List T := x16;
                     «Authoring.proveWith»
                       x14
                       (Const.children (Const.child x0 (leaf 1)))
                       x17
                       x1);
    x2

def «Authoring.stated» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
                     let x2 : List T := Const.children x1;
                     let x3 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x2
                       (leaf 0)
                       (fun (x3 : T) (_ : List T) => x3);
                     let x4 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x2
                       ([] : List T)
                       (fun (_ : T) (x5 : List T) => x5);
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x4
                       (leaf 0)
                       (fun (x5 : T) (_ : List T) => x5);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x4
                       ([] : List T)
                       (fun (_ : T) (x7 : List T) => x7);
                     «Prelude.some» x3
                   else
                     «Prelude.none»);
    x1

def «Authoring.matches» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : List T) =>
    let x4 : T := «Prelude.and»
      (Const.eq
        (Const.mul
          (if (Const.eq x0 (leaf 0)).label ≠ 0 then leaf 1 else leaf 2)
          («Authoring/Requests.length» x1))
        («Authoring/Decls.length» x2))
      («Prelude.and»
        (Const.eq («Authoring/Decls.length» x2) («Prelude.length» x3))
        (Const.foldr
          (α := T)
          (β := List T → List T → T)
          (fun (x4 : T) (x5 : List T → List T → T) (x6 : List T) (x7 : List T) =>
            Const.lcase
              (α := T)
              (β := T)
              x6
              (leaf 0)
              (fun (x8 : T) (x9 : List T) =>
                «Prelude.and»
                  (Const.equal
                    («Authoring.stated» x8)
                    («Prelude.some» («Authoring.requestThm» x4)))
                  («Prelude.and»
                    (Const.equal («Authoring.requestName» x4) («Prelude.at» x7 (leaf 0)))
                    (if (Const.eq x0 (leaf 0)).label ≠ 0 then
                      x5 x9 («Prelude.drop» (leaf 1) x7)
                    else
                      Const.lcase
                        (α := T)
                        (β := T)
                        x9
                        (leaf 0)
                        (fun (x10 : T) (x11 : List T) =>
                          «Prelude.and»
                            («Prelude.isSome» («Authoring.stated» x10))
                            («Prelude.and»
                              (Const.equal («Authoring.requestName» x4) («Prelude.at» x7 (leaf 1)))
                              (x5 x11 («Prelude.drop» (leaf 2) x7))))))))
          (fun (_ : List T) (_ : List T) => leaf 1)
          x1
          x2
          x3));
    x4

def «Authoring.replayWith» :=
  fun (x0 : List T) (x1 : List T) (x2 : List T) (x3 : T) (x4 : T) =>
    let x5 : T := (let x5 : T := «Authoring.readSource» x0 x1 x3;
                   if (Const.eq (Const.label x5) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x5; leaf 0
                   else
                     let x6 : List T := Const.children x5;
                     let x7 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x6
                       (leaf 0)
                       (fun (x7 : T) (_ : List T) => x7);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x6
                       ([] : List T)
                       (fun (_ : T) (x9 : List T) => x9);
                     let x9 : T := x7;
                     let x10 : List T := Const.children x9;
                     let x11 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x10
                       (leaf 0)
                       (fun (x11 : T) (_ : List T) => x11);
                     let x12 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x10
                       ([] : List T)
                       (fun (_ : T) (x13 : List T) => x13);
                     let x13 : List T := x12;
                     let x14 : T := x4;
                     if («Authoring.Results.member» x14).label ≠ 0 then
                       let x15 : T := x14;
                       let x16 : T := x15;
                       let x17 : List T := Const.children x16;
                       let x18 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x17
                         (leaf 0)
                         (fun (x18 : T) (_ : List T) => x18);
                       let x19 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x17
                         ([] : List T)
                         (fun (_ : T) (x20 : List T) => x20);
                       let x20 : List T := x19;
                       if («Authoring.matches»
                         x11
                         x13
                         x20
                         (Const.children x18)).label ≠ 0 then
                         let x21 : T := «Derivation.checkDev»
                           («Authoring.globalsOf» x2)
                           ([] : List T)
                           x20;
                         if (Const.eq (Const.label x21) (leaf 0)).label ≠ 0 then
                           let _ : List T := Const.children x21; leaf 0
                         else
                           let x22 : List T := Const.children x21;
                           let _ : T := Const.lcase
                             (α := T)
                             (β := T)
                             x22
                             (leaf 0)
                             (fun (x23 : T) (_ : List T) => x23);
                           let _ : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x22
                             ([] : List T)
                             (fun (_ : T) (x25 : List T) => x25);
                           leaf 1
                       else
                         leaf 0
                     else
                       leaf 0);
    x5

def «Authoring.replay» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (let x3 : T := «Translation.program»
                     (Const.children (Const.child x0 (leaf 0)));
                   if (Const.eq (Const.label x3) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x3; leaf 0
                   else
                     let x4 : List T := Const.children x3;
                     let x5 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x4
                       (leaf 0)
                       (fun (x5 : T) (_ : List T) => x5);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x4
                       ([] : List T)
                       (fun (_ : T) (x7 : List T) => x7);
                     let x7 : T := x5;
                     let x8 : List T := Const.children x7;
                     let x9 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x8
                       (leaf 0)
                       (fun (x9 : T) (_ : List T) => x9);
                     let x10 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x8
                       ([] : List T)
                       (fun (_ : T) (x11 : List T) => x11);
                     let x11 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x10
                       (leaf 0)
                       (fun (x11 : T) (_ : List T) => x11);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x10
                       ([] : List T)
                       (fun (_ : T) (x13 : List T) => x13);
                     let x13 : T := x9;
                     let x14 : List T := Const.children x13;
                     let x15 : List T := x14;
                     let x16 : T := x11;
                     let x17 : List T := Const.children x16;
                     let x18 : List T := x17;
                     «Authoring.replayWith»
                       x15
                       (Const.children (Const.child x0 (leaf 1)))
                       x18
                       x1
                       x2);
    x3

def «Authoring.version» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := «Translation.program»
                     (Const.children (Const.child x0 (leaf 0)));
                   if (Const.eq (Const.label x2) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x2; «Prelude.none»
                   else
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     let x6 : T := x4;
                     let x7 : List T := Const.children x6;
                     let x8 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x7
                       (leaf 0)
                       (fun (x8 : T) (_ : List T) => x8);
                     let x9 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x7
                       ([] : List T)
                       (fun (_ : T) (x10 : List T) => x10);
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x9
                       (leaf 0)
                       (fun (x10 : T) (_ : List T) => x10);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x9
                       ([] : List T)
                       (fun (_ : T) (x12 : List T) => x12);
                     let x12 : T := x8;
                     let x13 : List T := Const.children x12;
                     let x14 : List T := x13;
                     let x15 : T := «Authoring.readSource»
                       x14
                       (Const.children (Const.child x0 (leaf 1)))
                       x1;
                     if (Const.eq (Const.label x15) (leaf 0)).label ≠ 0 then
                       let _ : List T := Const.children x15; «Prelude.none»
                     else
                       let x16 : List T := Const.children x15;
                       let x17 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x16
                         (leaf 0)
                         (fun (x17 : T) (_ : List T) => x17);
                       let _ : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x16
                         ([] : List T)
                         (fun (_ : T) (x19 : List T) => x19);
                       let x19 : T := x17;
                       let x20 : List T := Const.children x19;
                       let x21 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x20
                         (leaf 0)
                         (fun (x21 : T) (_ : List T) => x21);
                       let x22 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x20
                         ([] : List T)
                         (fun (_ : T) (x23 : List T) => x23);
                       let _ : List T := x22; «Prelude.some» x21);
    x2

end GebMirror.Metalogic

end
