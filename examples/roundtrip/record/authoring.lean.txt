module

public import GebMirror.Metalogic.Prover

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

def «Authoring.index» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (if («Reader.isAtom» x1).label ≠ 0 then
      «Reader.indexOf» («Reader.nameOf» x1) x0
    else
      «Prelude.none»);
    x2

def «Authoring.number» :=
  fun (x0 : T) =>
    let x1 : T := (if («Reader.isAtom» x0).label ≠ 0 then
      «Reader.numeral» (Const.children x0)
    else
      «Prelude.none»);
    x1

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
  fun (x0 : T) =>
    let x1 : List
      T := ((«Prover.nrRule»
      (leaf 3)
      («Derivation.terms» ([] : List T))) ::
      ((«Prover.nrRule» (leaf 4) («Derivation.terms» ([] : List T))) ::
        ((«Prover.nrRule» (leaf 5) («Derivation.terms» ([] : List T))) ::
          («Authoring/Rules.single»
            («Prover.nrBelow» x0 («Derivation.terms» ([] : List T)))))));
    x1

def «Authoring.request» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: (x3 :: ([] : List T)))))

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

def «Authoring.readRequest» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (let x2 : T := Const.child x1 (leaf 2);
                   let x3 : T := Const.child x1 (leaf 3);
                   let x4 : T := Const.child x3 (leaf 1);
                   if («Prelude.and»
                     («Authoring.form»
                       x1
                       (mk 0 [leaf 116,
                         leaf 104,
                         leaf 101,
                         leaf 111,
                         leaf 114,
                         leaf 101,
                         leaf 109])
                       (leaf 4))
                     («Prelude.and»
                       («Reader.isAtom» (Const.child x1 (leaf 1)))
                       («Prelude.and»
                         («Base.not»
                           («Base.isEmpty» (Const.children (Const.child x1 (leaf 1)))))
                         («Prelude.and»
                           («Authoring.form»
                             x2
                             (mk 0 [leaf 101, leaf 113, leaf 117, leaf 97, leaf 108])
                             (leaf 3))
                           («Prelude.and»
                             («Authoring.form» x3 (mk 0 [leaf 98, leaf 121]) (leaf 2))
                             («Authoring.form»
                               x4
                               (mk 0 [leaf 110,
                                 leaf 111,
                                 leaf 114,
                                 leaf 109,
                                 leaf 97,
                                 leaf 108,
                                 leaf 105,
                                 leaf 122,
                                 leaf 101])
                               (leaf 2))))))).label ≠ 0 then
                     let x5 : T := «Authoring.index» x0 (Const.child x2 (leaf 1));
                     let x6 : T := «Authoring.index» x0 (Const.child x2 (leaf 2));
                     let x7 : T := «Authoring.number» (Const.child x4 (leaf 1));
                     if («Prelude.and»
                       («Prelude.isSome» x5)
                       («Prelude.and»
                         («Prelude.isSome» x6)
                         («Prelude.isSome» x7))).label ≠ 0 then
                       «Authoring/OR.just»
                         («Authoring.request»
                           («Reader.nameOf» (Const.child x1 (leaf 1)))
                           («Prelude.get» x5)
                           («Prelude.get» x6)
                           («Prelude.get» x7))
                     else
                       «Authoring/OR.nothing»
                   else
                     «Authoring/OR.nothing»);
    x2

def «Authoring.statement» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   let x3 : List T := Const.children x2;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x3
                     (leaf 0)
                     (fun (x4 : T) (_ : List T) => x4);
                   let x5 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x3
                     ([] : List T)
                     (fun (_ : T) (x6 : List T) => x6);
                   let x6 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x5
                     (leaf 0)
                     (fun (x6 : T) (_ : List T) => x6);
                   let x7 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x5
                     ([] : List T)
                     (fun (_ : T) (x8 : List T) => x8);
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
                   «Derivation.mkThm»
                     (leaf 0)
                     («Language.objs» ([] : List T))
                     («Derivation.terms» ([] : List T))
                     («Language.mEq»
                       («Language.mDefn» (Const.add x0 x6) ([] : List T) ([] : List T))
                       («Language.mDefn» (Const.add x0 x8) ([] : List T) ([] : List T))));
    x2

def «Authoring.certificate» :=
  fun (x0 : T) (x1 : T) (x2 : List T) (x3 : T) =>
    let x4 : T := (let x4 : T := x3;
                   let x5 : List T := Const.children x4;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x5
                     (leaf 0)
                     (fun (x6 : T) (_ : List T) => x6);
                   let x7 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x5
                     ([] : List T)
                     (fun (_ : T) (x8 : List T) => x8);
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
                   let x11 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x9
                     ([] : List T)
                     (fun (_ : T) (x12 : List T) => x12);
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
                   «Prover.byNormW»
                     x0
                     ([] : List T)
                     (leaf 0)
                     x2
                     x12
                     ([] : List T)
                     ([] : List T)
                     («Language.mDefn» (Const.add x1 x8) ([] : List T) ([] : List T))
                     («Language.mDefn» (Const.add x1 x10) ([] : List T) ([] : List T)));
    x4

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
  fun (x0 : List T) => Const.node (leaf 0) x0

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
                   let x8 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x6
                     ([] : List T)
                     (fun (_ : T) (x9 : List T) => x9);
                   let _ : T := Const.lcase
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
                   x3);
    x1

def «Authoring.readSource» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (let x2 : T := «Reader.readSExps» (Const.children x1);
                   let x3 : T := Const.child («Prelude.get» x2) (leaf 0);
                   if («Prelude.and»
                     («Prelude.isSome» x2)
                     («Prelude.and»
                       (Const.eq
                         («Prelude.length» (Const.children («Prelude.get» x2)))
                         (leaf 1))
                       («Prelude.and»
                         («Reader.isList» x3)
                         («Prelude.and»
                           («Authoring.word»
                             (Const.child x3 (leaf 0))
                             (mk 0 [leaf 112, leaf 114, leaf 111, leaf 111, leaf 102, leaf 115]))
                           («Prelude.and»
                             (Const.equal
                               («Authoring.number» (Const.child x3 (leaf 1)))
                               («Prelude.some» (leaf 0)))
                             (Const.lt
                               (leaf 2)
                               («Prelude.length» (Const.children x3)))))))).label ≠ 0 then
                     Const.foldr
                       (α := T)
                       (β := T)
                       (fun (x4 : T) (x5 : T) =>
                         let x6 : T := x5;
                         if (Const.eq (Const.label x6) (leaf 0)).label ≠ 0 then
                           let _ : List T := Const.children x6; «Authoring/ORequests.nothing»
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
                           let x12 : List T := x11;
                           let x13 : T := «Authoring.readRequest» x0 x4;
                           if (Const.eq (Const.label x13) (leaf 0)).label ≠ 0 then
                             let _ : List T := Const.children x13; «Authoring/ORequests.nothing»
                           else
                             let x14 : List T := Const.children x13;
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
                             if (Const.foldr
                               (α := T)
                               (β := T)
                               (fun (x17 : T) (x18 : T) =>
                                 «Prelude.or»
                                   (Const.equal
                                     («Authoring.requestName» x15)
                                     («Authoring.requestName» x17))
                                   x18)
                               (leaf 0)
                               x12).label ≠ 0 then
                               «Authoring/ORequests.nothing»
                             else
                               «Authoring/ORequests.just» («Authoring.requests» (x15 :: x12)))
                       («Authoring/ORequests.just» («Authoring.requests» ([] : List T)))
                       («Prelude.drop» (leaf 2) (Const.children x3))
                   else
                     «Authoring/ORequests.nothing»);
    x2

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

def «Authoring.advance» :=
  fun (x0 : T) (x1 : T) (x2 : List T) (x3 : T) (x4 : T) =>
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
                     let x14 : T := «Authoring.certificate» x0 x1 x2 x3;
                     if («Prelude.isSome» x14).label ≠ 0 then
                       «Authoring/OResults.just»
                         («Authoring.results»
                           (Const.node
                             (leaf 0)
                             ((«Authoring.requestName» x3) :: (Const.children x11)))
                           ((«Derivation.declLang»
                             («Authoring.statement» x1 x3)
                             («Prelude.get» x14)) ::
                             x13))
                     else
                       «Authoring/OResults.nothing»);
    x5

def «Authoring.proveWith» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : T := (let x3 : T := «Authoring.readSource» x0 x2;
                   if (Const.eq (Const.label x3) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x3; «Prelude.none»
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
                     let x9 : List T := x8;
                     let x10 : T := «Authoring.globalsOf» x1;
                     let x11 : T := «Authoring/LD.length» «Translation.lib»;
                     let x12 : T := Const.foldr
                       (α := T)
                       (β := T)
                       («Authoring.advance»
                         x10
                         x11
                         («Authoring.rulesOf» (Const.add x11 («Authoring/LD.length» x1))))
                       («Authoring/OResults.just»
                         («Authoring.results»
                           (Const.node (leaf 0) ([] : List T))
                           ([] : List T)))
                       x9;
                     if (Const.eq (Const.label x12) (leaf 0)).label ≠ 0 then
                       let _ : List T := Const.children x12; «Prelude.none»
                     else
                       let x13 : List T := Const.children x12;
                       let x14 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x13
                         (leaf 0)
                         (fun (x14 : T) (_ : List T) => x14);
                       let _ : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x13
                         ([] : List T)
                         (fun (_ : T) (x16 : List T) => x16);
                       let x16 : T := x14;
                       let x17 : List T := Const.children x16;
                       let _ : T := Const.lcase
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
                       let x21 : T := «Derivation.checkDev» x10 ([] : List T) x20;
                       if (Const.eq (Const.label x21) (leaf 0)).label ≠ 0 then
                         let _ : List T := Const.children x21; «Prelude.none»
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
                         «Prelude.some» x14);
    x3

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
                     let _ : T := Const.lcase
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
                     let x12 : T := x10;
                     let x13 : List T := Const.children x12;
                     let x14 : List T := x13;
                     «Authoring.proveWith»
                       (Const.children (Const.child x0 (leaf 1)))
                       x14
                       x1);
    x2

def «Authoring.matches» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : List T) =>
    let x4 : T := «Prelude.and»
      (Const.eq
        («Authoring/Requests.length» x1)
        («Authoring/Decls.length» x2))
      («Prelude.and»
        (Const.eq («Authoring/Requests.length» x1) («Prelude.length» x3))
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
                let x10 : T := x8;
                if (Const.eq (Const.label x10) (leaf 0)).label ≠ 0 then
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
                  let _ : T := Const.lcase
                    (α := T)
                    (β := T)
                    x13
                    (leaf 0)
                    (fun (x14 : T) (_ : List T) => x14);
                  let _ : List
                    T := Const.lcase
                    (α := T)
                    (β := List T)
                    x13
                    ([] : List T)
                    (fun (_ : T) (x16 : List T) => x16);
                  «Prelude.and»
                    (Const.equal x12 («Authoring.statement» x0 x4))
                    («Prelude.and»
                      (Const.equal («Authoring.requestName» x4) («Prelude.at» x7 (leaf 0)))
                      (x5 x9 («Prelude.drop» (leaf 1) x7)))
                else
                  if (Const.eq (Const.label x10) (leaf 1)).label ≠ 0 then
                    let x11 : List T := Const.children x10;
                    let _ : T := Const.lcase
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
                    let _ : T := Const.lcase
                      (α := T)
                      (β := T)
                      x13
                      (leaf 0)
                      (fun (x14 : T) (_ : List T) => x14);
                    let _ : List
                      T := Const.lcase
                      (α := T)
                      (β := List T)
                      x13
                      ([] : List T)
                      (fun (_ : T) (x16 : List T) => x16);
                    leaf 0
                  else
                    if (Const.eq (Const.label x10) (leaf 2)).label ≠ 0 then
                      let x11 : List T := Const.children x10;
                      let _ : T := Const.lcase
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
                      leaf 0
                    else
                      if (Const.eq (Const.label x10) (leaf 3)).label ≠ 0 then
                        let x11 : List T := Const.children x10;
                        let _ : T := Const.lcase
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
                        let _ : T := Const.lcase
                          (α := T)
                          (β := T)
                          x13
                          (leaf 0)
                          (fun (x14 : T) (_ : List T) => x14);
                        let _ : List
                          T := Const.lcase
                          (α := T)
                          (β := List T)
                          x13
                          ([] : List T)
                          (fun (_ : T) (x16 : List T) => x16);
                        leaf 0
                      else
                        if (Const.eq (Const.label x10) (leaf 4)).label ≠ 0 then
                          let x11 : List T := Const.children x10;
                          let _ : T := Const.lcase
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
                          let _ : T := Const.lcase
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
                          leaf 0
                        else
                          if (Const.eq (Const.label x10) (leaf 5)).label ≠ 0 then
                            let x11 : List T := Const.children x10;
                            let _ : T := Const.lcase
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
                            let _ : T := Const.lcase
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
                            leaf 0
                          else
                            let x11 : List T := Const.children x10;
                            let _ : T := Const.lcase
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
                            let _ : T := Const.lcase
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
                            let x17 : List
                              T := Const.lcase
                              (α := T)
                              (β := List T)
                              x15
                              ([] : List T)
                              (fun (_ : T) (x18 : List T) => x18);
                            let _ : T := Const.lcase
                              (α := T)
                              (β := T)
                              x17
                              (leaf 0)
                              (fun (x18 : T) (_ : List T) => x18);
                            let _ : List
                              T := Const.lcase
                              (α := T)
                              (β := List T)
                              x17
                              ([] : List T)
                              (fun (_ : T) (x20 : List T) => x20);
                            leaf 0))
          (fun (_ : List T) (_ : List T) => leaf 1)
          x1
          x2
          x3));
    x4

def «Authoring.replayWith» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) (x3 : T) =>
    let x4 : T := (let x4 : T := «Authoring.readSource» x0 x2;
                   if (Const.eq (Const.label x4) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x4; leaf 0
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
                     let x10 : List T := x9;
                     let x11 : T := x3;
                     if («Authoring.Results.member» x11).label ≠ 0 then
                       let x12 : T := x11;
                       let x13 : T := x12;
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
                       let x17 : List T := x16;
                       if («Authoring.matches»
                         («Authoring/LD.length» «Translation.lib»)
                         x10
                         x17
                         (Const.children x15)).label ≠ 0 then
                         let x18 : T := «Derivation.checkDev»
                           («Authoring.globalsOf» x1)
                           ([] : List T)
                           x17;
                         if (Const.eq (Const.label x18) (leaf 0)).label ≠ 0 then
                           let _ : List T := Const.children x18; leaf 0
                         else
                           let x19 : List T := Const.children x18;
                           let _ : T := Const.lcase
                             (α := T)
                             (β := T)
                             x19
                             (leaf 0)
                             (fun (x20 : T) (_ : List T) => x20);
                           let _ : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x19
                             ([] : List T)
                             (fun (_ : T) (x22 : List T) => x22);
                           leaf 1
                       else
                         leaf 0
                     else
                       leaf 0);
    x4

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
                     let _ : T := Const.lcase
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
                     let x13 : T := x11;
                     let x14 : List T := Const.children x13;
                     let x15 : List T := x14;
                     «Authoring.replayWith»
                       (Const.children (Const.child x0 (leaf 1)))
                       x15
                       x1
                       x2);
    x3

end GebMirror.Metalogic

end
