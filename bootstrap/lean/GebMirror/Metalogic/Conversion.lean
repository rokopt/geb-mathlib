module

public import GebMirror.Metalogic.Affine

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «Literals.litBits» :=
  fun (x0 : T) => Const.node (leaf 0) (x0 :: ([] : List T))

def «Literals.litOrd» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Literals.litPair» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 2) (x0 :: (x1 :: ([] : List T)))

def «Literals/OLit.nothing» := Const.node (leaf 0) ([] : List T)

def «Literals/OLit.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Literals/OLit.isJust» :=
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

def «Literals/OLit.fromMaybe» :=
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

def «Literals/OLit.nthOf» :=
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
      «Literals/OLit.nothing»
      (fun (x2 : T) (_ : List T) => «Literals/OLit.just» x2);
    x2

def «Literals/OLit.allJust» :=
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

def «Literals/OLits.tail» :=
  fun (x0 : List T) =>
    Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2)

def «Literals/Lits.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Literals/Lits.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Literals/Lits.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Literals/Lits.reverse» :=
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

def «Literals/Lits.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Literals/Lits.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Literals/Lits.tail» x1 x0;
    x2

def «Literals/Lits.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Literals/Lits.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Literals/EachLit.all» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «Prelude.and» (x0 x2) x3)
      (leaf 1)
      x1;
    x2

def «Literals/EachLit.any» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «Prelude.or» (x0 x2) x3)
      (leaf 0)
      x1;
    x2

def «Literals/EachLit.isEmpty» :=
  fun (x0 : List T) =>
    let x1 : T := Const.eq
      (Const.foldr
        (α := T)
        (β := T)
        (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
        (leaf 0)
        x0)
      (leaf 0);
    x1

def «Literals/EachLit.take» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := (let x2 : T := Const.foldr
              (α := T)
              (β := T)
              (fun (_ : T) (x3 : T) => Const.add x3 (leaf 1))
              (leaf 0)
              x1;
            (Const.foldr
              (α := T)
              (β := T × List T)
              (fun (x3 : T) (x4 : T × List T) =>
                (Const.add (x4).1 (leaf 1),
                  if (Const.lt
                    (Const.sub (Const.sub x2 (x4).1) (leaf 1))
                    x0).label ≠ 0 then
                    (x3 :: (x4).2)
                  else
                    (x4).2))
              (leaf 0, ([] : List T))
              x1).2);
    x2

def «Literals.pairTy» :=
  «Theory.prod» «Translation.bitsTy» «Translation.bitsTy»

def «Literals.b1c» := «Prelude.single» «Translation.bitsTy»

def «Literals.b2c» :=
  «Theory.l2» «Translation.bitsTy» «Translation.bitsTy»

def «Literals.b3c» :=
  «Theory.l3»
    «Translation.bitsTy»
    «Translation.bitsTy»
    «Translation.bitsTy»

def «Literals.symRow» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : T) =>
    let x4 : T := Const.node
      (leaf 0)
      («Theory.l4» x0 (Const.node (leaf 0) x1) (Const.node (leaf 0) x2) x3);
    x4

def «Literals.syms» :=
  «Prelude.append»
    («Theory.l6»
      («Literals.symRow»
        (leaf 0)
        ([] : List T)
        ([] : List T)
        «Translation.bitsTy»)
      («Literals.symRow»
        (leaf 1)
        ([] : List T)
        «Literals.b1c»
        «Translation.bitsTy»)
      («Literals.symRow»
        (leaf 2)
        ([] : List T)
        «Literals.b1c»
        «Translation.bitsTy»)
      («Literals.symRow»
        (leaf 10)
        («Prelude.single» «Translation.bitTy»)
        «Literals.b1c»
        «Translation.bitsTy»)
      («Literals.symRow»
        (leaf 11)
        ([] : List T)
        «Literals.b1c»
        «Translation.bitsTy»)
      («Literals.symRow»
        (leaf 14)
        ([] : List T)
        «Literals.b1c»
        «Translation.bitsTy»))
    («Prelude.append»
      («Theory.l6»
        («Literals.symRow»
          (leaf 13)
          ([] : List T)
          «Literals.b1c»
          «Translation.bitsTy»)
        («Literals.symRow»
          (leaf 6)
          «Literals.b1c»
          «Literals.b3c»
          «Translation.bitsTy»)
        («Literals.symRow»
          (leaf 6)
          («Prelude.single» «Translation.ordTy»)
          («Theory.l3»
            «Translation.ordTy»
            «Translation.ordTy»
            «Translation.bitsTy»)
          «Translation.ordTy»)
        («Literals.symRow»
          (leaf 15)
          ([] : List T)
          «Literals.b2c»
          «Translation.bitsTy»)
        («Literals.symRow»
          (leaf 21)
          ([] : List T)
          «Literals.b2c»
          «Translation.bitsTy»)
        («Literals.symRow»
          (leaf 18)
          ([] : List T)
          «Literals.b2c»
          «Translation.bitsTy»))
      («Theory.l6»
        («Literals.symRow»
          (leaf 16)
          ([] : List T)
          «Literals.b2c»
          «Translation.ordTy»)
        («Literals.symRow»
          (leaf 17)
          ([] : List T)
          «Literals.b2c»
          «Translation.bitsTy»)
        («Literals.symRow»
          (leaf 19)
          ([] : List T)
          «Literals.b2c»
          «Translation.bitsTy»)
        («Literals.symRow»
          (leaf 20)
          ([] : List T)
          «Literals.b2c»
          «Translation.bitsTy»)
        («Literals.symRow»
          (leaf 22)
          ([] : List T)
          «Literals.b2c»
          «Literals.pairTy»)
        («Literals.symRow»
          (leaf 23)
          ([] : List T)
          «Literals.b1c»
          «Translation.bitsTy»)))

def «Literals.symOf» :=
  fun (x0 : T) =>
    let x1 : T := (if (Const.eq (Const.label x0) (leaf 11)).label ≠ 0 then
      let x1 : T := «Language.mD» x0 (leaf 0);
      let x2 : List T := Const.children («Language.mD» x0 (leaf 1));
      Const.foldr
        (α := T)
        (β := T → T)
        (fun (x3 : T) (x4 : T → T) (x5 : T) =>
          if («Prelude.and»
            (Const.eq (Const.child x3 (leaf 0)) x1)
            («Base.equalTs»
              (Const.children (Const.child x3 (leaf 1)))
              x2)).label ≠ 0 then
            «Prelude.some» x5
          else
            x4 (Const.add x5 (leaf 1)))
        (fun (_ : T) => «Prelude.none»)
        «Literals.syms»
        (leaf 0)
    else
      «Prelude.none»);
    x1

def «Literals.bits1» :=
  fun (x0 : List T) =>
    let x1 : T := Const.lcase
      (α := T)
      (β := T)
      x0
      «Prelude.none»
      (fun (x1 : T) (x2 : List T) =>
        if («Literals/EachLit.isEmpty» x2).label ≠ 0 then
          let x3 : T := x1;
          if (Const.eq (Const.label x3) (leaf 0)).label ≠ 0 then
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
            «Prelude.some» x5
          else
            «Prelude.none»
        else
          «Prelude.none»);
    x1

def «Literals.bits2» :=
  fun (x0 : List T) =>
    let x1 : T := Const.lcase
      (α := T)
      (β := T)
      x0
      «Language/OTPair.nothing»
      (fun (x1 : T) (x2 : List T) =>
        let x3 : T := «Literals.bits1» x2;
        if («Prelude.isSome» x3).label ≠ 0 then
          let x4 : T := x1;
          if (Const.eq (Const.label x4) (leaf 0)).label ≠ 0 then
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
            «Language/OTPair.just» («Language.pr» x6 («Prelude.get» x3))
          else
            «Language/OTPair.nothing»
        else
          «Language/OTPair.nothing»);
    x1

def «Literals.truth» :=
  fun (x0 : T) =>
    let x1 : T := (if (x0).label ≠ 0 then leaf 1 else leaf 0); x1

def «Literals.hostCond» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.lcase
      (α := T)
      (β := T)
      x1
      «Literals/OLit.nothing»
      (fun (x2 : T) (x3 : List T) =>
        Const.lcase
          (α := T)
          (β := T)
          x3
          «Literals/OLit.nothing»
          (fun (x4 : T) (x5 : List T) =>
            Const.lcase
              (α := T)
              (β := T)
              x5
              «Literals/OLit.nothing»
              (fun (x6 : T) (x7 : List T) =>
                if («Literals/EachLit.isEmpty» x7).label ≠ 0 then
                  let x8 : T := x2;
                  if (Const.eq (Const.label x8) (leaf 0)).label ≠ 0 then
                    let x9 : List T := Const.children x8;
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
                    let x12 : T := x4;
                    if (Const.eq (Const.label x12) (leaf 0)).label ≠ 0 then
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
                      let x16 : T := x6;
                      if (Const.eq (Const.label x16) (leaf 0)).label ≠ 0 then
                        let x17 : List T := Const.children x16;
                        let x18 : T := Const.lcase
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
                        if (Const.eq x0 (leaf 7)).label ≠ 0 then
                          «Literals/OLit.just»
                            («Literals.litBits»
                              (if (Const.eq x10 (leaf 0)).label ≠ 0 then x18 else x14))
                        else
                          «Literals/OLit.nothing»
                      else
                        «Literals/OLit.nothing»
                    else
                      if (Const.eq (Const.label x12) (leaf 1)).label ≠ 0 then
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
                        let x16 : T := x6;
                        if (Const.eq (Const.label x16) (leaf 1)).label ≠ 0 then
                          let x17 : List T := Const.children x16;
                          let x18 : T := Const.lcase
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
                          if (Const.eq x0 (leaf 8)).label ≠ 0 then
                            «Literals/OLit.just»
                              («Literals.litOrd»
                                (if (Const.eq x10 (leaf 0)).label ≠ 0 then x18 else x14))
                          else
                            «Literals/OLit.nothing»
                        else
                          «Literals/OLit.nothing»
                      else
                        «Literals/OLit.nothing»
                  else
                    «Literals/OLit.nothing»
                else
                  «Literals/OLit.nothing»)));
    x2

def «Literals.host» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := (if (Const.eq x0 (leaf 0)).label ≠ 0 then
      if («Literals/EachLit.isEmpty» x1).label ≠ 0 then
        «Literals/OLit.just» («Literals.litBits» (leaf 0))
      else
        «Literals/OLit.nothing»
    else
      if («Prelude.or»
        (Const.eq x0 (leaf 7))
        (Const.eq x0 (leaf 8))).label ≠ 0 then
        «Literals.hostCond» x0 x1
      else
        if («Prelude.or»
          (Const.lt x0 (leaf 7))
          (Const.eq x0 (leaf 17))).label ≠ 0 then
          let x2 : T := «Literals.bits1» x1;
          if («Prelude.isSome» x2).label ≠ 0 then
            let x3 : T := «Prelude.get» x2;
            «Literals/OLit.just»
              («Literals.litBits»
                (if (Const.eq x0 (leaf 1)).label ≠ 0 then
                  Const.add (Const.mul (leaf 2) x3) (leaf 1)
                else
                  if (Const.eq x0 (leaf 2)).label ≠ 0 then
                    Const.add (Const.mul (leaf 2) x3) (leaf 2)
                  else
                    if (Const.eq x0 (leaf 3)).label ≠ 0 then
                      «Literals.truth» (Const.eq x3 (leaf 0))
                    else
                      if (Const.eq x0 (leaf 4)).label ≠ 0 then
                        Const.add x3 (leaf 1)
                      else
                        if (Const.eq x0 (leaf 5)).label ≠ 0 then
                          Const.mul (leaf 2) x3
                        else
                          if (Const.eq x0 (leaf 6)).label ≠ 0 then
                            Const.sub x3 (leaf 1)
                          else
                            Const.log2 x3))
          else
            «Literals/OLit.nothing»
        else
          let x2 : T := «Literals.bits2» x1;
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
            let x6 : T := «Language.p1» x4;
            let x7 : T := «Language.p2» x4;
            if (Const.eq x0 (leaf 9)).label ≠ 0 then
              «Literals/OLit.just» («Literals.litBits» (Const.add x6 x7))
            else
              if (Const.eq x0 (leaf 10)).label ≠ 0 then
                «Literals/OLit.just» («Literals.litBits» (Const.mul x6 x7))
              else
                if (Const.eq x0 (leaf 11)).label ≠ 0 then
                  «Literals/OLit.just»
                    («Literals.litBits» («Literals.truth» (Const.eq x6 x7)))
                else
                  if (Const.eq x0 (leaf 12)).label ≠ 0 then
                    «Literals/OLit.just»
                      («Literals.litOrd»
                        (if (Const.lt x6 x7).label ≠ 0 then
                          leaf 0
                        else
                          if (Const.eq x6 x7).label ≠ 0 then leaf 1 else leaf 2))
                  else
                    if (Const.eq x0 (leaf 13)).label ≠ 0 then
                      «Literals/OLit.just»
                        («Literals.litBits» («Literals.truth» (Const.lt x6 x7)))
                    else
                      if (Const.eq x0 (leaf 14)).label ≠ 0 then
                        if (Const.lt x6 x7).label ≠ 0 then
                          «Literals/OLit.nothing»
                        else
                          «Literals/OLit.just» («Literals.litBits» (Const.sub x6 x7))
                      else
                        if (Const.eq x0 (leaf 15)).label ≠ 0 then
                          «Literals/OLit.just» («Literals.litBits» (Const.sub x6 x7))
                        else
                          if (Const.eq x0 (leaf 16)).label ≠ 0 then
                            «Literals/OLit.just»
                              («Literals.litPair» (Const.div x6 x7) (Const.mod x6 x7))
                          else
                            «Literals/OLit.nothing»
          else
            let _ : List T := Const.children x2; «Literals/OLit.nothing»);
    x2

def «Literals.pairStep» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := (if (Const.eq x0 (leaf 2)).label ≠ 0 then
      let x2 : T := «Literals.bits2» x1;
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
        «Literals/OLit.just»
          («Literals.litPair» («Language.p1» x4) («Language.p2» x4))
      else
        let _ : List T := Const.children x2; «Literals/OLit.nothing»
    else
      Const.lcase
        (α := T)
        (β := T)
        x1
        «Literals/OLit.nothing»
        (fun (x2 : T) (x3 : List T) =>
          if («Literals/EachLit.isEmpty» x3).label ≠ 0 then
            let x4 : T := x2;
            if (Const.eq (Const.label x4) (leaf 2)).label ≠ 0 then
              let x5 : List T := Const.children x4;
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
              let _ : List
                T := Const.lcase
                (α := T)
                (β := List T)
                x7
                ([] : List T)
                (fun (_ : T) (x10 : List T) => x10);
              if (Const.eq x0 (leaf 3)).label ≠ 0 then
                «Literals/OLit.just» («Literals.litBits» x6)
              else
                if (Const.eq x0 (leaf 4)).label ≠ 0 then
                  «Literals/OLit.just» («Literals.litBits» x8)
                else
                  «Literals/OLit.nothing»
            else
              «Literals/OLit.nothing»
          else
            «Literals/OLit.nothing»));
    x2

def «Literals.evalStep» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := (if (Const.equal x0 «Translation.ltO»).label ≠ 0 then
      «Literals/OLit.just» («Literals.litOrd» (leaf 0))
    else
      if (Const.equal x0 «Translation.eqO»).label ≠ 0 then
        «Literals/OLit.just» («Literals.litOrd» (leaf 1))
      else
        if (Const.equal x0 «Translation.gtO»).label ≠ 0 then
          «Literals/OLit.just» («Literals.litOrd» (leaf 2))
        else
          let x2 : T ×
            List T := «Literals/OLit.allJust» («Literals/OLits.tail» x1);
          if ((x2).1).label ≠ 0 then
            let x3 : T := «Literals.symOf» x0;
            if («Prelude.isSome» x3).label ≠ 0 then
              «Literals.host» («Prelude.get» x3) («Literals/Lits.reverse» (x2).2)
            else
              «Literals.pairStep» (Const.label x0) (x2).2
          else
            «Literals/OLit.nothing»);
    x2

def «Literals.valueOf» :=
  fun (x0 : T) =>
    let x1 : T := Const.para (α := T) «Literals.evalStep» x0; x1

def «Literals.litTerm» :=
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
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x2
                       ([] : List T)
                       (fun (_ : T) (x5 : List T) => x5);
                     «Translation.trNumeral» x3
                   else
                     if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                       let x2 : List T := Const.children x1;
                       let x3 : T := Const.lcase
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
                       if (Const.eq x3 (leaf 0)).label ≠ 0 then
                         «Translation.ltO»
                       else
                         if (Const.eq x3 (leaf 1)).label ≠ 0 then
                           «Translation.eqO»
                         else
                           «Translation.gtO»
                     else
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
                       «Language.mPair»
                         («Translation.trNumeral» x3)
                         («Translation.trNumeral» x5));
    x1

def «Literals.litEval» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «Literals.valueOf» x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let x2 : List T := Const.children x1;
                     let x3 : T := Const.lcase
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
                     «Prelude.some» («Literals.litTerm» x3)
                   else
                     let _ : List T := Const.children x1; «Prelude.none»);
    x1

def «Literals/ThmF.l2» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List T := (x0 :: (x1 :: ([] : List T))); x2

def «Literals/ThmF.l3» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : List T := (x0 :: («Literals/ThmF.l2» x1 x2)); x3

def «Literals/ThmF.l4» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : List T := (x0 :: («Literals/ThmF.l3» x1 x2 x3)); x4

def «Literals/ThmF.l5» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : List T := (x0 :: («Literals/ThmF.l4» x1 x2 x3 x4)); x5

def «Literals/ThmF.l6» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : List T := (x0 :: («Literals/ThmF.l5» x1 x2 x3 x4 x5)); x6

def «Literals/Thms.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Literals/Thms.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Literals/Thms.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Literals/Thms.reverse» :=
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

def «Literals/Thms.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Literals/Thms.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Literals/Thms.tail» x1 x0;
    x2

def «Literals/Thms.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Literals/Thms.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Literals.lemEqn» :=
  fun (x0 : List T) (x1 : T) (x2 : T) =>
    let x3 : T := «Derivation.mkThm»
      (leaf 0)
      («Language.objs» x0)
      («Derivation.terms» ([] : List T))
      («Language.mEq» x1 x2);
    x3

def «Literals.vy» := «Language.var» (leaf 0)

def «Literals.vx» := «Language.var» (leaf 1)

def «Literals.vz» := «Language.var» (leaf 2)

def «Literals.isNilT» :=
  fun (x0 : T) =>
    let x1 : T := «Translation.call»
      (leaf 10)
      («Prelude.single» «Translation.bitTy»)
      («Prelude.single» x0);
    x1

def «Literals.un» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Translation.call»
      x0
      ([] : List T)
      («Prelude.single» x1);
    x2

def «Literals.bin» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Translation.call» x0 ([] : List T) («Theory.l2» x1 x2);
    x3

def «Literals.condB» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Translation.call»
      (leaf 6)
      («Prelude.single» «Translation.bitsTy»)
      («Theory.l3» x0 x1 x2);
    x3

def «Literals.condO» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Translation.call»
      (leaf 6)
      («Prelude.single» «Translation.ordTy»)
      («Theory.l3» x0 x1 x2);
    x3

def «Literals.selIn» :=
  «Translation.ifOrd»
    «Literals.pairTy»
    («Language.var» (leaf 3))
    «Literals.vz»
    «Literals.vx»
    «Literals.vy»

def «Literals.selSel» :=
  fun (x0 : T) =>
    let x1 : T := «Translation.ifOrd»
      «Literals.pairTy»
      x0
      («Language.var» (leaf 5))
      («Language.var» (leaf 4))
      «Literals.selIn»;
    x1

def «Literals.divStep» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Language.subst»
      («Literals.selSel» («Language.var» (leaf 6)))
      («Language.substList»
        ((«Language.mPair» («Translation.b1T» x0) «Translation.bnilT») ::
          («Theory.l6»
            («Language.mPair» («Translation.b1T» x0) «Translation.bnilT»)
            («Language.mPair»
              («Translation.b0T» x0)
              («Literals.bin» (leaf 19) x1 x2))
            («Literals.bin» (leaf 16) x1 («Literals.un» (leaf 14) x2))
            («Language.mPair» («Translation.b0T» x0) «Translation.bnilT»)
            («Language.mPair» («Literals.un» (leaf 14) x0) x1)
            («Literals.bin» (leaf 16) x1 x2))));
    x3

def «Literals.bitT» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if (x0).label ≠ 0 then
      «Translation.b1T» x1
    else
      «Translation.b0T» x1);
    x2

def «Literals.divRhs» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := «Literals.bin»
                     (leaf 22)
                     «Literals.vx»
                     («Literals.bitT» x1 «Literals.vy»);
                   «Literals.divStep»
                     («Language.mFst» x2)
                     («Literals.bitT» x0 («Language.mSnd» x2))
                     («Literals.bitT» x1 «Literals.vy»));
    x2

def «Literals.lenOneT» :=
  fun (x0 : T) =>
    let x1 : T := «Language.mListRec»
      («Language.mPair» «Translation.bnilT» «Translation.bnilT»)
      («Language.app»
        («Language.mLam»
          «Literals.pairTy»
          («Language.mPair»
            («Literals.un» (leaf 11) («Language.mFst» «Literals.vy»))
            («Translation.ifBit»
              «Translation.bitsTy»
              «Literals.vz»
              («Language.mSnd» «Literals.vy»)
              «Translation.trueT»)))
        «Literals.vy»)
      x0;
    x1

def «Literals.lemSucc» :=
  «Literals/ThmF.l6»
    («Literals.lemEqn»
      ([] : List T)
      («Literals.isNilT» «Translation.bnilT»)
      «Translation.trueT»)
    («Literals.lemEqn»
      «Literals.b1c»
      («Literals.isNilT» («Translation.b0T» «Literals.vy»))
      «Translation.bnilT»)
    («Literals.lemEqn»
      «Literals.b1c»
      («Literals.isNilT» («Translation.b1T» «Literals.vy»))
      «Translation.bnilT»)
    («Literals.lemEqn»
      ([] : List T)
      («Literals.un» (leaf 11) «Translation.bnilT»)
      («Translation.b0T» «Translation.bnilT»))
    («Literals.lemEqn»
      «Literals.b1c»
      («Literals.un» (leaf 11) («Translation.b0T» «Literals.vy»))
      («Translation.b1T» «Literals.vy»))
    («Literals.lemEqn»
      «Literals.b1c»
      («Literals.un» (leaf 11) («Translation.b1T» «Literals.vy»))
      («Translation.b0T» («Literals.un» (leaf 11) «Literals.vy»)))

def «Literals.lemPred» :=
  «Literals/ThmF.l6»
    («Literals.lemEqn»
      ([] : List T)
      («Literals.un» (leaf 14) «Translation.bnilT»)
      «Translation.bnilT»)
    («Literals.lemEqn»
      «Literals.b1c»
      («Literals.un» (leaf 14) («Translation.b0T» «Literals.vy»))
      («Translation.b1T» («Literals.un» (leaf 14) «Literals.vy»)))
    («Literals.lemEqn»
      «Literals.b1c»
      («Literals.un» (leaf 14) («Translation.b1T» «Literals.vy»))
      («Translation.b1T» («Translation.b0T» «Literals.vy»)))
    («Literals.lemEqn»
      ([] : List T)
      («Literals.un» (leaf 13) «Translation.bnilT»)
      «Translation.bnilT»)
    («Literals.lemEqn»
      «Literals.b1c»
      («Literals.un» (leaf 13) («Translation.b0T» «Literals.vy»))
      («Literals.condB»
        «Literals.vy»
        («Translation.b1T» («Literals.un» (leaf 13) «Literals.vy»))
        «Translation.bnilT»))
    («Literals.lemEqn»
      «Literals.b1c»
      («Literals.un» (leaf 13) («Translation.b1T» «Literals.vy»))
      («Translation.b0T» «Literals.vy»))

def «Literals.lemCond» :=
  «Literals/ThmF.l6»
    («Literals.lemEqn»
      «Literals.b2c»
      («Literals.condB» «Translation.bnilT» «Literals.vx» «Literals.vy»)
      «Literals.vy»)
    («Literals.lemEqn»
      «Literals.b3c»
      («Literals.condB»
        («Translation.b0T» «Literals.vz»)
        «Literals.vx»
        «Literals.vy»)
      «Literals.vx»)
    («Literals.lemEqn»
      «Literals.b3c»
      («Literals.condB»
        («Translation.b1T» «Literals.vz»)
        «Literals.vx»
        «Literals.vy»)
      «Literals.vx»)
    («Literals.lemEqn»
      («Theory.l2» «Translation.ordTy» «Translation.ordTy»)
      («Literals.condO» «Translation.bnilT» «Literals.vx» «Literals.vy»)
      «Literals.vy»)
    («Literals.lemEqn»
      («Theory.l3»
        «Translation.ordTy»
        «Translation.ordTy»
        «Translation.bitsTy»)
      («Literals.condO»
        («Translation.b0T» «Literals.vz»)
        «Literals.vx»
        «Literals.vy»)
      «Literals.vx»)
    («Literals.lemEqn»
      («Theory.l3»
        «Translation.ordTy»
        «Translation.ordTy»
        «Translation.bitsTy»)
      («Literals.condO»
        («Translation.b1T» «Literals.vz»)
        «Literals.vx»
        «Literals.vy»)
      «Literals.vx»)

def «Literals.lemAdd» :=
  «Literals/Thms.append»
    («Literals/ThmF.l4»
      («Literals.lemEqn»
        «Literals.b1c»
        («Literals.bin» (leaf 15) «Literals.vy» «Translation.bnilT»)
        «Literals.vy»)
      («Literals.lemEqn»
        «Literals.b1c»
        («Literals.bin»
          (leaf 15)
          «Translation.bnilT»
          («Translation.b0T» «Literals.vy»))
        («Translation.b0T» «Literals.vy»))
      («Literals.lemEqn»
        «Literals.b1c»
        («Literals.bin»
          (leaf 15)
          «Translation.bnilT»
          («Translation.b1T» «Literals.vy»))
        («Translation.b1T» «Literals.vy»))
      («Literals.lemEqn»
        «Literals.b2c»
        («Literals.bin»
          (leaf 15)
          («Translation.b0T» «Literals.vx»)
          («Translation.b0T» «Literals.vy»))
        («Translation.b1T»
          («Literals.bin» (leaf 15) «Literals.vx» «Literals.vy»))))
    («Literals/ThmF.l6»
      («Literals.lemEqn»
        «Literals.b2c»
        («Literals.bin»
          (leaf 15)
          («Translation.b0T» «Literals.vx»)
          («Translation.b1T» «Literals.vy»))
        («Translation.b0T»
          («Literals.un»
            (leaf 11)
            («Literals.bin» (leaf 15) «Literals.vx» «Literals.vy»))))
      («Literals.lemEqn»
        «Literals.b2c»
        («Literals.bin»
          (leaf 15)
          («Translation.b1T» «Literals.vx»)
          («Translation.b0T» «Literals.vy»))
        («Translation.b0T»
          («Literals.un»
            (leaf 11)
            («Literals.bin» (leaf 15) «Literals.vx» «Literals.vy»))))
      («Literals.lemEqn»
        «Literals.b2c»
        («Literals.bin»
          (leaf 15)
          («Translation.b1T» «Literals.vx»)
          («Translation.b1T» «Literals.vy»))
        («Translation.b1T»
          («Literals.un»
            (leaf 11)
            («Literals.bin» (leaf 15) «Literals.vx» «Literals.vy»))))
      («Literals.lemEqn»
        «Literals.b1c»
        («Literals.bin» (leaf 21) «Literals.vy» «Translation.bnilT»)
        «Translation.bnilT»)
      («Literals.lemEqn»
        «Literals.b2c»
        («Literals.bin»
          (leaf 21)
          «Literals.vx»
          («Translation.b0T» «Literals.vy»))
        («Literals.bin»
          (leaf 15)
          («Literals.un»
            (leaf 14)
            («Literals.bin» (leaf 21) «Literals.vx» «Literals.vy»))
          «Literals.vx»))
      («Literals.lemEqn»
        «Literals.b2c»
        («Literals.bin»
          (leaf 21)
          «Literals.vx»
          («Translation.b1T» «Literals.vy»))
        («Literals.bin»
          (leaf 15)
          («Literals.un»
            (leaf 14)
            («Literals.bin» (leaf 21) «Literals.vx» «Literals.vy»))
          («Literals.un» (leaf 14) «Literals.vx»))))

def «Literals.lemEq» :=
  ((«Literals.lemEqn»
    «Literals.b1c»
    («Literals.bin» (leaf 18) «Literals.vy» «Translation.bnilT»)
    («Literals.isNilT» «Literals.vy»)) ::
    («Literals/ThmF.l6»
      («Literals.lemEqn»
        «Literals.b1c»
        («Literals.bin»
          (leaf 18)
          «Translation.bnilT»
          («Translation.b0T» «Literals.vy»))
        «Translation.bnilT»)
      («Literals.lemEqn»
        «Literals.b1c»
        («Literals.bin»
          (leaf 18)
          «Translation.bnilT»
          («Translation.b1T» «Literals.vy»))
        «Translation.bnilT»)
      («Literals.lemEqn»
        «Literals.b2c»
        («Literals.bin»
          (leaf 18)
          («Translation.b0T» «Literals.vx»)
          («Translation.b0T» «Literals.vy»))
        («Literals.bin» (leaf 18) «Literals.vx» «Literals.vy»))
      («Literals.lemEqn»
        «Literals.b2c»
        («Literals.bin»
          (leaf 18)
          («Translation.b0T» «Literals.vx»)
          («Translation.b1T» «Literals.vy»))
        «Translation.bnilT»)
      («Literals.lemEqn»
        «Literals.b2c»
        («Literals.bin»
          (leaf 18)
          («Translation.b1T» «Literals.vx»)
          («Translation.b0T» «Literals.vy»))
        «Translation.bnilT»)
      («Literals.lemEqn»
        «Literals.b2c»
        («Literals.bin»
          (leaf 18)
          («Translation.b1T» «Literals.vx»)
          («Translation.b1T» «Literals.vy»))
        («Literals.bin» (leaf 18) «Literals.vx» «Literals.vy»))))

def «Literals.o3c» :=
  «Theory.l3»
    «Translation.ordTy»
    «Translation.ordTy»
    «Translation.ordTy»

def «Literals.lemCmp» :=
  «Literals/Thms.append»
    ((«Literals.lemEqn»
      «Literals.b1c»
      («Literals.bin» (leaf 16) «Literals.vy» «Translation.bnilT»)
      («Literals.condO»
        «Literals.vy»
        «Translation.gtO»
        «Translation.eqO»)) ::
      («Literals/ThmF.l6»
        («Literals.lemEqn»
          «Literals.b1c»
          («Literals.bin»
            (leaf 16)
            «Translation.bnilT»
            («Translation.b0T» «Literals.vy»))
          «Translation.ltO»)
        («Literals.lemEqn»
          «Literals.b1c»
          («Literals.bin»
            (leaf 16)
            «Translation.bnilT»
            («Translation.b1T» «Literals.vy»))
          «Translation.ltO»)
        («Literals.lemEqn»
          «Literals.b2c»
          («Literals.bin»
            (leaf 16)
            («Translation.b0T» «Literals.vx»)
            («Translation.b0T» «Literals.vy»))
          («Translation.ifOrd»
            «Translation.ordTy»
            («Literals.bin» (leaf 16) «Literals.vx» «Literals.vy»)
            «Translation.ltO»
            «Translation.eqO»
            «Translation.gtO»))
        («Literals.lemEqn»
          «Literals.b2c»
          («Literals.bin»
            (leaf 16)
            («Translation.b0T» «Literals.vx»)
            («Translation.b1T» «Literals.vy»))
          («Translation.ifOrd»
            «Translation.ordTy»
            («Literals.bin» (leaf 16) «Literals.vx» «Literals.vy»)
            «Translation.ltO»
            «Translation.ltO»
            «Translation.gtO»))
        («Literals.lemEqn»
          «Literals.b2c»
          («Literals.bin»
            (leaf 16)
            («Translation.b1T» «Literals.vx»)
            («Translation.b0T» «Literals.vy»))
          («Translation.ifOrd»
            «Translation.ordTy»
            («Literals.bin» (leaf 16) «Literals.vx» «Literals.vy»)
            «Translation.ltO»
            «Translation.gtO»
            «Translation.gtO»))
        («Literals.lemEqn»
          «Literals.b2c»
          («Literals.bin»
            (leaf 16)
            («Translation.b1T» «Literals.vx»)
            («Translation.b1T» «Literals.vy»))
          («Translation.ifOrd»
            «Translation.ordTy»
            («Literals.bin» (leaf 16) «Literals.vx» «Literals.vy»)
            «Translation.ltO»
            «Translation.eqO»
            «Translation.gtO»))))
    ((«Literals.lemEqn»
      «Literals.o3c»
      («Translation.ifOrd»
        «Translation.ordTy»
        «Translation.ltO»
        «Literals.vz»
        «Literals.vx»
        «Literals.vy»)
      «Literals.vz») ::
      («Literals/ThmF.l6»
        («Literals.lemEqn»
          «Literals.o3c»
          («Translation.ifOrd»
            «Translation.ordTy»
            «Translation.eqO»
            «Literals.vz»
            «Literals.vx»
            «Literals.vy»)
          «Literals.vx»)
        («Literals.lemEqn»
          «Literals.o3c»
          («Translation.ifOrd»
            «Translation.ordTy»
            «Translation.gtO»
            «Literals.vz»
            «Literals.vx»
            «Literals.vy»)
          «Literals.vy»)
        («Literals.lemEqn»
          «Literals.b3c»
          («Translation.ifOrd»
            «Translation.bitsTy»
            «Translation.ltO»
            «Literals.vz»
            «Literals.vx»
            «Literals.vy»)
          «Literals.vz»)
        («Literals.lemEqn»
          «Literals.b3c»
          («Translation.ifOrd»
            «Translation.bitsTy»
            «Translation.eqO»
            «Literals.vz»
            «Literals.vx»
            «Literals.vy»)
          «Literals.vx»)
        («Literals.lemEqn»
          «Literals.b3c»
          («Translation.ifOrd»
            «Translation.bitsTy»
            «Translation.gtO»
            «Literals.vz»
            «Literals.vx»
            «Literals.vy»)
          «Literals.vy»)
        («Literals.lemEqn»
          «Literals.b2c»
          («Literals.bin» (leaf 17) «Literals.vx» «Literals.vy»)
          («Translation.ifOrd»
            «Translation.bitsTy»
            («Literals.bin» (leaf 16) «Literals.vx» «Literals.vy»)
            «Translation.trueT»
            «Translation.bnilT»
            «Translation.bnilT»))))

def «Literals.lemSub» :=
  «Literals/Thms.append»
    («Literals/ThmF.l4»
      («Literals.lemEqn»
        «Literals.b1c»
        («Literals.bin» (leaf 19) «Literals.vy» «Translation.bnilT»)
        «Literals.vy»)
      («Literals.lemEqn»
        «Literals.b1c»
        («Literals.bin»
          (leaf 19)
          «Translation.bnilT»
          («Translation.b0T» «Literals.vy»))
        «Translation.bnilT»)
      («Literals.lemEqn»
        «Literals.b1c»
        («Literals.bin»
          (leaf 19)
          «Translation.bnilT»
          («Translation.b1T» «Literals.vy»))
        «Translation.bnilT»)
      («Literals.lemEqn»
        «Literals.b2c»
        («Literals.bin»
          (leaf 19)
          («Translation.b0T» «Literals.vx»)
          («Translation.b0T» «Literals.vy»))
        («Literals.un»
          (leaf 14)
          («Literals.bin» (leaf 19) «Literals.vx» «Literals.vy»))))
    («Literals/ThmF.l4»
      («Literals.lemEqn»
        «Literals.b2c»
        («Literals.bin»
          (leaf 19)
          («Translation.b0T» «Literals.vx»)
          («Translation.b1T» «Literals.vy»))
        («Translation.b0T»
          («Literals.un»
            (leaf 13)
            («Literals.bin» (leaf 19) «Literals.vx» «Literals.vy»))))
      («Literals.lemEqn»
        «Literals.b2c»
        («Literals.bin»
          (leaf 19)
          («Translation.b1T» «Literals.vx»)
          («Translation.b0T» «Literals.vy»))
        («Translation.b0T»
          («Literals.bin» (leaf 19) «Literals.vx» «Literals.vy»)))
      («Literals.lemEqn»
        «Literals.b2c»
        («Literals.bin»
          (leaf 19)
          («Translation.b1T» «Literals.vx»)
          («Translation.b1T» «Literals.vy»))
        («Literals.un»
          (leaf 14)
          («Literals.bin» (leaf 19) «Literals.vx» «Literals.vy»)))
      («Literals.lemEqn»
        «Literals.b2c»
        («Literals.bin» (leaf 20) «Literals.vx» «Literals.vy»)
        («Literals.condB»
          («Literals.bin» (leaf 17) «Literals.vx» «Literals.vy»)
          «Translation.bnilT»
          («Literals.bin» (leaf 19) «Literals.vx» «Literals.vy»))))

def «Literals.lemDiv» :=
  ((«Literals.lemEqn»
    «Literals.b1c»
    («Literals.bin» (leaf 22) «Literals.vy» «Translation.bnilT»)
    («Language.mPair» «Translation.bnilT» «Literals.vy»)) ::
    («Literals/ThmF.l6»
      («Literals.lemEqn»
        «Literals.b1c»
        («Literals.bin»
          (leaf 22)
          «Translation.bnilT»
          («Translation.b0T» «Literals.vy»))
        («Language.mPair» «Translation.bnilT» «Translation.bnilT»))
      («Literals.lemEqn»
        «Literals.b1c»
        («Literals.bin»
          (leaf 22)
          «Translation.bnilT»
          («Translation.b1T» «Literals.vy»))
        («Language.mPair» «Translation.bnilT» «Translation.bnilT»))
      («Literals.lemEqn»
        «Literals.b2c»
        («Literals.bin»
          (leaf 22)
          («Translation.b0T» «Literals.vx»)
          («Translation.b0T» «Literals.vy»))
        («Literals.divRhs» (leaf 0) (leaf 0)))
      («Literals.lemEqn»
        «Literals.b2c»
        («Literals.bin»
          (leaf 22)
          («Translation.b0T» «Literals.vx»)
          («Translation.b1T» «Literals.vy»))
        («Literals.divRhs» (leaf 0) (leaf 1)))
      («Literals.lemEqn»
        «Literals.b2c»
        («Literals.bin»
          (leaf 22)
          («Translation.b1T» «Literals.vx»)
          («Translation.b0T» «Literals.vy»))
        («Literals.divRhs» (leaf 1) (leaf 0)))
      («Literals.lemEqn»
        «Literals.b2c»
        («Literals.bin»
          (leaf 22)
          («Translation.b1T» «Literals.vx»)
          («Translation.b1T» «Literals.vy»))
        («Literals.divRhs» (leaf 1) (leaf 1)))))

def «Literals.p3c» :=
  «Theory.l3» «Literals.pairTy» «Literals.pairTy» «Literals.pairTy»

def «Literals.p6c» :=
  «Theory.l6»
    «Literals.pairTy»
    «Literals.pairTy»
    «Literals.pairTy»
    «Translation.ordTy»
    «Literals.pairTy»
    «Literals.pairTy»

def «Literals.lemSel» :=
  «Literals/ThmF.l6»
    («Literals.lemEqn»
      «Literals.p3c»
      («Translation.ifOrd»
        «Literals.pairTy»
        «Translation.ltO»
        «Literals.vz»
        «Literals.vx»
        «Literals.vy»)
      «Literals.vz»)
    («Literals.lemEqn»
      «Literals.p3c»
      («Translation.ifOrd»
        «Literals.pairTy»
        «Translation.eqO»
        «Literals.vz»
        «Literals.vx»
        «Literals.vy»)
      «Literals.vx»)
    («Literals.lemEqn»
      «Literals.p3c»
      («Translation.ifOrd»
        «Literals.pairTy»
        «Translation.gtO»
        «Literals.vz»
        «Literals.vx»
        «Literals.vy»)
      «Literals.vy»)
    («Literals.lemEqn»
      «Literals.p6c»
      («Literals.selSel» «Translation.ltO»)
      («Language.var» (leaf 5)))
    («Literals.lemEqn»
      «Literals.p6c»
      («Literals.selSel» «Translation.eqO»)
      («Language.var» (leaf 4)))
    («Literals.lemEqn»
      «Literals.p6c»
      («Literals.selSel» «Translation.gtO»)
      «Literals.selIn»)

def «Literals.lemLog» :=
  «Literals/ThmF.l4»
    («Literals.lemEqn»
      ([] : List T)
      («Literals.lenOneT» «Translation.bnilT»)
      («Language.mPair» «Translation.bnilT» «Translation.bnilT»))
    («Literals.lemEqn»
      «Literals.b1c»
      («Literals.lenOneT» («Translation.b0T» «Literals.vy»))
      («Language.mPair»
        («Literals.un»
          (leaf 11)
          («Language.mFst» («Literals.lenOneT» «Literals.vy»)))
        («Language.mSnd» («Literals.lenOneT» «Literals.vy»))))
    («Literals.lemEqn»
      «Literals.b1c»
      («Literals.lenOneT» («Translation.b1T» «Literals.vy»))
      («Language.mPair»
        («Literals.un»
          (leaf 11)
          («Language.mFst» («Literals.lenOneT» «Literals.vy»)))
        «Translation.trueT»))
    («Literals.lemEqn»
      «Literals.b1c»
      («Literals.un» (leaf 23) «Literals.vy»)
      («Literals.condB»
        («Language.mSnd» («Literals.lenOneT» «Literals.vy»))
        («Language.mFst» («Literals.lenOneT» «Literals.vy»))
        («Literals.un»
          (leaf 13)
          («Language.mFst» («Literals.lenOneT» «Literals.vy»)))))

def «Literals.lemmas» :=
  «Literals/Thms.append»
    «Literals.lemSucc»
    («Literals/Thms.append»
      «Literals.lemPred»
      («Literals/Thms.append»
        «Literals.lemCond»
        («Literals/Thms.append»
          «Literals.lemAdd»
          («Literals/Thms.append»
            «Literals.lemEq»
            («Literals/Thms.append»
              «Literals.lemCmp»
              («Literals/Thms.append»
                «Literals.lemSub»
                («Literals/Thms.append»
                  «Literals.lemDiv»
                  («Literals/Thms.append» «Literals.lemSel» «Literals.lemLog»))))))))

def «Literals.lemmasIn» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T → T)
      (fun (x2 : T) (x3 : T → T) (x4 : T) =>
        «Prelude.and»
          (let x5 : T := «Derivation.thmAt» x0 (Const.add x1 x4);
           if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
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
             Const.equal x7 x2
           else
             let _ : List T := Const.children x5; leaf 0)
          (x3 (Const.add x4 (leaf 1))))
      (fun (_ : T) => leaf 1)
      «Literals.lemmas»
      (leaf 0);
    x2

def «Literals.sigOk» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List T) (x4 : List T) (x5 : T) =>
    let x6 : T := (let x6 : T := «Language.bindDL»
                     («Language/ODefinition.nthOf» («Language.gDefs» x0) x2)
                     «Language.defLanguage»;
                   if (Const.eq (Const.label x6) (leaf 1)).label ≠ 0 then
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
                     «Prelude.and»
                       («Prelude.and»
                         («Prelude.and»
                           (Const.eq («Language.ldArity» x8) («Prelude.length» x3))
                           («Base.allT» («Language.isTy» x0 x1) x3))
                         («Base.equalTs»
                           («Base.mapT»
                             (fun (x10 : T) => «PartialHorn.phSubst» x3 x10)
                             («Language.ldParams» x8))
                           x4))
                       (Const.equal («PartialHorn.phSubst» x3 («Language.ldType» x8)) x5)
                   else
                     let _ : List T := Const.children x6; leaf 0);
    x6

def «Literals.sigs» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Base.allT»
      (fun (x2 : T) =>
        «Literals.sigOk»
          x0
          x1
          (Const.child x2 (leaf 0))
          (Const.children (Const.child x2 (leaf 1)))
          (Const.children (Const.child x2 (leaf 2)))
          (Const.child x2 (leaf 3)))
      «Literals.syms»;
    x2

def «Literals.ready» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := «Prelude.and»
      («Prelude.and»
        («Literals.lemmasIn» x1 x2)
        («Literals.sigs» x0 (leaf 0)))
      («Prelude.and»
        (Const.equal
          («Derivation.typeIn» x0 (leaf 0) ([] : List T) «Translation.ltO»)
          («Prelude.some» «Translation.ordTy»))
        («Prelude.and»
          (Const.equal
            («Derivation.typeIn» x0 (leaf 0) ([] : List T) «Translation.eqO»)
            («Prelude.some» «Translation.ordTy»))
          (Const.equal
            («Derivation.typeIn» x0 (leaf 0) ([] : List T) «Translation.gtO»)
            («Prelude.some» «Translation.ordTy»))));
    x3

def «Machine.failV» :=
  «Language.mNode» (leaf 16) ([] : List T) ([] : List T)

def «Machine.delayed» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Language.mNode»
      (leaf 15)
      ([] : List T)
      («Theory.l2» («Base.getD» x0 «Machine.failV») x1);
    x2

def «Machine.delay» :=
  fun (x0 : T → List T → T → T)
    (x1 : T → T)
    (x2 : T)
    (x3 : List T)
    (x4 : T) =>
    let x5 : T := «Machine.delayed»
      («Base.bindO» (x0 x2 x3 x4) x1)
      («Language.mNode» (leaf 14) («Theory.l2» x2 x4) x3);
    x5

def «Machine.freeVar» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if (Const.lt x1 x0).label ≠ 0 then
      «Language.mNode»
        (leaf 0)
        («Prelude.single» (Const.sub (Const.sub x0 (leaf 1)) x1))
        ([] : List T)
    else
      «Language.mNode»
        (leaf 1)
        («Prelude.single» (Const.sub x1 x0))
        ([] : List T));
    x2

def «Machine.level» :=
  fun (x0 : T) =>
    let x1 : T := «Language.mNode»
      (leaf 0)
      («Prelude.single» x0)
      ([] : List T);
    x1

def «Machine.envSubst» :=
  fun (x0 : List T) (x1 : T) (x2 : T) =>
    let x3 : T := (if (Const.lt x2 («Prelude.length» x0)).label ≠ 0 then
      «Prelude.at» x0 x2
    else
      «Language.var» (Const.add (Const.sub x2 («Prelude.length» x0)) x1));
    x3

def «Machine.readStep» :=
  fun (x0 : T) (x1 : T) (x2 : List T) =>
    let x3 : T := (let x3 : T := Const.label x1;
                   if (Const.eq x3 (leaf 0)).label ≠ 0 then
                     «Language.var»
                       (Const.sub (Const.sub x0 (leaf 1)) («Language.mD» x1 (leaf 0)))
                   else
                     if (Const.eq x3 (leaf 1)).label ≠ 0 then
                       «Language.var» (Const.add x0 («Language.mD» x1 (leaf 0)))
                     else
                       if (Const.eq x3 (leaf 3)).label ≠ 0 then
                         «Language.mNode» (leaf 2) ([] : List T) x2
                       else
                         if (Const.eq x3 (leaf 4)).label ≠ 0 then
                           «Language.mLam»
                             («Language.mD» x1 (leaf 0))
                             («Language.subst»
                               («Language.mD» x1 (leaf 1))
                               (fun (x4 : T) =>
                                 «Language.liftS»
                                   («Machine.envSubst»
                                     x2
                                     (Const.sub x0 («Language.mD» x1 (leaf 2))))
                                   x4))
                         else
                           if (Const.eq x3 (leaf 5)).label ≠ 0 then
                             «Language.mNode»
                               (leaf 7)
                               (Const.children (Const.child x1 (leaf 0)))
                               x2
                           else
                             if (Const.eq x3 (leaf 6)).label ≠ 0 then
                               «Language.mNode» (leaf 6) ([] : List T) x2
                             else
                               if (Const.eq x3 (leaf 7)).label ≠ 0 then
                                 «Language.mNode» (leaf 3) ([] : List T) x2
                               else
                                 if (Const.eq x3 (leaf 8)).label ≠ 0 then
                                   «Language.mNode» (leaf 4) ([] : List T) x2
                                 else
                                   if (Const.eq x3 (leaf 9)).label ≠ 0 then
                                     if (Const.lt («Prelude.length» x2) (leaf 2)).label ≠ 0 then
                                       «Language.mNode» (leaf 8) ([] : List T) x2
                                     else
                                       «Language.mNatRec»
                                         («Prelude.at» x2 (leaf 0))
                                         («Language.subst»
                                           («Language.mD» x1 (leaf 0))
                                           (fun (x4 : T) =>
                                             «Language.liftS»
                                               («Machine.envSubst»
                                                 («Prelude.drop» (leaf 2) x2)
                                                 (Const.sub x0 («Language.mD» x1 (leaf 1))))
                                               x4))
                                         («Prelude.at» x2 (leaf 1))
                                   else
                                     if (Const.eq x3 (leaf 10)).label ≠ 0 then
                                       if (Const.lt («Prelude.length» x2) (leaf 2)).label ≠ 0 then
                                         «Language.mNode» (leaf 9) ([] : List T) x2
                                       else
                                         «Language.mListRec»
                                           («Prelude.at» x2 (leaf 0))
                                           («Language.subst»
                                             («Language.mD» x1 (leaf 0))
                                             (fun (x4 : T) =>
                                               «Language.liftS»
                                                 (fun (x5 : T) =>
                                                   «Language.liftS»
                                                     («Machine.envSubst»
                                                       («Prelude.drop» (leaf 2) x2)
                                                       (Const.sub x0 («Language.mD» x1 (leaf 1))))
                                                     x5)
                                                 x4))
                                           («Prelude.at» x2 (leaf 1))
                                     else
                                       if (Const.eq x3 (leaf 11)).label ≠ 0 then
                                         if («Base.isEmpty» x2).label ≠ 0 then
                                           «Language.mNode»
                                             (leaf 10)
                                             («Prelude.single» («Language.mD» x1 (leaf 0)))
                                             x2
                                         else
                                           «Language.mRoseRec»
                                             («Language.mD» x1 (leaf 0))
                                             («Language.subst»
                                               («Language.mD» x1 (leaf 1))
                                               (fun (x4 : T) =>
                                                 «Language.liftS»
                                                   («Machine.envSubst»
                                                     («Prelude.tail» x2)
                                                     (Const.sub x0 («Language.mD» x1 (leaf 2))))
                                                   x4))
                                             («Prelude.at» x2 (leaf 0))
                                       else
                                         if (Const.eq x3 (leaf 12)).label ≠ 0 then
                                           «Language.mNode»
                                             (leaf 11)
                                             (Const.children (Const.child x1 (leaf 0)))
                                             x2
                                         else
                                           if (Const.eq x3 (leaf 13)).label ≠ 0 then
                                             «Language.mNode» (leaf 12) ([] : List T) x2
                                           else
                                             if (Const.eq x3 (leaf 14)).label ≠ 0 then
                                               «Language.subst»
                                                 («Language.mD» x1 (leaf 0))
                                                 (fun (x4 : T) =>
                                                   «Machine.envSubst»
                                                     x2
                                                     (Const.sub x0 («Language.mD» x1 (leaf 1)))
                                                     x4)
                                             else
                                               if («Prelude.and»
                                                 (Const.eq x3 (leaf 15))
                                                 (Const.eq
                                                   («Prelude.length» x2)
                                                   (leaf 2))).label ≠ 0 then
                                                 «Prelude.at» x2 (leaf 1)
                                               else
                                                 «Language.mStar»);
    x3

def «Machine.readBack» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.para
      (α := T)
      (fun (x2 : T) (x3 : List T) =>
        «Machine.readStep» x0 x2 («Prelude.tail» x3))
      x1;
    x2

def «Machine.varLeaves» :=
  fun (x0 : T) =>
    let x1 : T := Const.para
      (α := T)
      (fun (x1 : T) (x2 : List T) =>
        «Prelude.and»
          (if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
            «Base.isEmpty» («Prelude.tail» x2)
          else
            leaf 1)
          («Base.allT» (fun (x3 : T) => x3) («Prelude.tail» x2)))
      x0;
    x1

def «Machine.evalDefn» :=
  fun (x0 : T)
    (x1 : T → T)
    (x2 : T → List T → T → T)
    (x3 : List T)
    (x4 : T)
    (x5 : T) =>
    let x6 : T := (let x6 : T := «Language.mD» x4 (leaf 0);
                   let x7 : List T := Const.children («Language.mD» x4 (leaf 1));
                   let x8 : T := «Prelude.some»
                     («Language.mNode»
                       (leaf 12)
                       (Const.children (Const.child x4 (leaf 0)))
                       x3);
                   let x9 : T := (if (x1 x6).label ≠ 0 then
                     «Language.bindDL»
                       («Language/ODefinition.nthOf» («Language.gDefs» x0) x6)
                       «Language.defLanguage»
                   else
                     «Language/OLDefn.nothing»);
                   if (Const.eq (Const.label x9) (leaf 1)).label ≠ 0 then
                     let x10 : List T := Const.children x9;
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
                     if (Const.eq
                       («Prelude.length» x3)
                       («Prelude.length» («Language.ldParams» x11))).label ≠ 0 then
                       x2
                         (if («Base.isEmpty» x7).label ≠ 0 then
                           «Language.ldBody» x11
                         else
                           «Language.osubst» x7 («Language.ldBody» x11))
                         x3
                         x5
                     else
                       x8
                   else
                     let _ : List T := Const.children x9; x8);
    x6

def «Machine.evalStep» :=
  fun (x0 : T)
    (x1 : T → T)
    (x2 : T → List T → T → T)
    (x3 : T → T)
    (x4 : T)
    (x5 : List T)
    (x6 : T) =>
    let x7 : T := (let x7 : T := Const.label x4;
                   let x8 : List T := «Language.mArgs» x4;
                   if (Const.eq x7 (leaf 0)).label ≠ 0 then
                     let x9 : T := «Language.mD» x4 (leaf 0);
                     «Prelude.some»
                       (if (Const.lt x9 («Prelude.length» x5)).label ≠ 0 then
                         «Prelude.at» x5 x9
                       else
                         «Machine.freeVar» x6 (Const.sub x9 («Prelude.length» x5)))
                   else
                     if («Language.mIs» (leaf 1) (leaf 0) x4).label ≠ 0 then
                       «Prelude.some» («Language.mNode» (leaf 2) ([] : List T) ([] : List T))
                     else
                       if («Language.mIs» (leaf 5) (leaf 1) x4).label ≠ 0 then
                         «Prelude.some»
                           («Language.mNode»
                             (leaf 4)
                             («Theory.l3»
                               («Language.mD» x4 (leaf 0))
                               («Language.mArg» x4 (leaf 0))
                               x6)
                             x5)
                       else
                         if («Prelude.and»
                           («Prelude.or» (Const.eq x7 (leaf 3)) (Const.eq x7 (leaf 4)))
                           (Const.eq («Prelude.length» x8) (leaf 1))).label ≠ 0 then
                           «Base.bindO»
                             (x2 («Language.mArg» x4 (leaf 0)) x5 x6)
                             (fun (x9 : T) =>
                               x3
                                 («Language.mNode»
                                   (if (Const.eq x7 (leaf 3)).label ≠ 0 then leaf 7 else leaf 8)
                                   ([] : List T)
                                   («Prelude.single» x9)))
                         else
                           if («Language.mIs» (leaf 6) (leaf 2) x4).label ≠ 0 then
                             «Base.bindO»
                               (x2 («Language.mArg» x4 (leaf 0)) x5 x6)
                               (fun (x9 : T) =>
                                 x3
                                   («Language.mNode»
                                     (leaf 6)
                                     ([] : List T)
                                     («Theory.l2»
                                       x9
                                       («Machine.delay»
                                         x2
                                         x3
                                         («Language.mArg» x4 (leaf 1))
                                         x5
                                         x6))))
                           else
                             if («Prelude.and»
                               («Prelude.or» (Const.eq x7 (leaf 8)) (Const.eq x7 (leaf 9)))
                               (Const.eq («Prelude.length» x8) (leaf 3))).label ≠ 0 then
                               «Base.bindO»
                                 (x2 («Language.mArg» x4 (leaf 2)) x5 x6)
                                 (fun (x9 : T) =>
                                   x3
                                     («Language.mNode»
                                       (if (Const.eq x7 (leaf 8)).label ≠ 0 then
                                         leaf 9
                                       else
                                         leaf 10)
                                       («Theory.l2» («Language.mArg» x4 (leaf 1)) x6)
                                       ((«Machine.delay»
                                         x2
                                         x3
                                         («Language.mArg» x4 (leaf 0))
                                         x5
                                         x6) ::
                                         (x9 :: x5))))
                             else
                               if («Language.mIs» (leaf 10) (leaf 2) x4).label ≠ 0 then
                                 «Base.bindO»
                                   (x2 («Language.mArg» x4 (leaf 1)) x5 x6)
                                   (fun (x9 : T) =>
                                     x3
                                       («Language.mNode»
                                         (leaf 11)
                                         («Theory.l3»
                                           («Language.mD» x4 (leaf 0))
                                           («Language.mArg» x4 (leaf 0))
                                           x6)
                                         (x9 :: x5)))
                               else
                                 let x9 : List
                                   T := «Base.mapT»
                                   (fun (x9 : T) => «Machine.delay» x2 x3 x9 x5 x6)
                                   x8;
                                 if (Const.eq x7 (leaf 11)).label ≠ 0 then
                                   «Machine.evalDefn» x0 x1 x2 x9 x4 x6
                                 else
                                   if (Const.eq x7 (leaf 2)).label ≠ 0 then
                                     «Prelude.some» («Language.mNode» (leaf 3) ([] : List T) x9)
                                   else
                                     if (Const.eq x7 (leaf 3)).label ≠ 0 then
                                       «Prelude.some» («Language.mNode» (leaf 7) ([] : List T) x9)
                                     else
                                       if (Const.eq x7 (leaf 4)).label ≠ 0 then
                                         «Prelude.some» («Language.mNode» (leaf 8) ([] : List T) x9)
                                       else
                                         if (Const.eq x7 (leaf 6)).label ≠ 0 then
                                           «Prelude.some»
                                             («Language.mNode» (leaf 6) ([] : List T) x9)
                                         else
                                           if (Const.eq x7 (leaf 7)).label ≠ 0 then
                                             «Prelude.some»
                                               («Language.mNode»
                                                 (leaf 5)
                                                 (Const.children (Const.child x4 (leaf 0)))
                                                 x9)
                                           else
                                             if (Const.eq x7 (leaf 12)).label ≠ 0 then
                                               «Prelude.some»
                                                 («Language.mNode» (leaf 13) ([] : List T) x9)
                                             else
                                               «Prelude.none»);
    x7

def «Machine.whnfApp» :=
  fun (x0 : T)
    (x1 : T → List T → T → T)
    (x2 : T → T)
    (x3 : T)
    (x4 : T) =>
    let x5 : T := «Base.bindO»
      (x2 x3)
      (fun (x5 : T) =>
        let x6 : T := «Prelude.some»
          («Language.mNode» (leaf 6) ([] : List T) («Theory.l2» x5 x4));
        if (Const.eq (Const.label x5) (leaf 4)).label ≠ 0 then
          «Base.bindO»
            (x1
              («Language.mD» x5 (leaf 1))
              (x4 :: («Language.mArgs» x5))
              («Language.mD» x5 (leaf 2)))
            x2
        else
          if («Prelude.and»
            («Language.mIs» (leaf 5) (leaf 1) x5)
            («Derivation.primIs»
              x0
              («Language.mD» x5 (leaf 0))
              «Derivation.casePrim»)).label ≠ 0 then
            «Base.bindO»
              (x2 x4)
              (fun (x7 : T) =>
                let x8 : T := «Prelude.some»
                  («Language.mNode» (leaf 6) ([] : List T) («Theory.l2» x5 x7));
                if («Prelude.and»
                  («Language.mIs» (leaf 5) (leaf 1) x7)
                  («Prelude.or»
                    («Derivation.primIs»
                      x0
                      («Language.mD» x7 (leaf 0))
                      «Derivation.inlPrim»)
                    («Derivation.primIs»
                      x0
                      («Language.mD» x7 (leaf 0))
                      «Derivation.inrPrim»))).label ≠ 0 then
                  «Base.bindO»
                    (x2 («Language.mArg» x5 (leaf 0)))
                    (fun (x9 : T) =>
                      if («Language.mIs» (leaf 3) (leaf 2) x9).label ≠ 0 then
                        x2
                          («Language.mNode»
                            (leaf 6)
                            ([] : List T)
                            («Theory.l2»
                              («Language.mArg»
                                x9
                                (if («Derivation.primIs»
                                  x0
                                  («Language.mD» x7 (leaf 0))
                                  «Derivation.inlPrim»).label ≠ 0 then
                                  leaf 0
                                else
                                  leaf 1))
                              («Language.mArg» x7 (leaf 0))))
                      else
                        x8)
                else
                  x8)
          else
            x6);
    x5

def «Machine.whnfNat» :=
  fun (x0 : T) (x1 : T → List T → T → T) (x2 : T → T) (x3 : T) =>
    let x4 : T := (let x4 : T := «Language.mD» x3 (leaf 0);
                   let x5 : T := «Language.mD» x3 (leaf 1);
                   let x6 : T := «Language.mArg» x3 (leaf 0);
                   let x7 : List T := «Prelude.drop» (leaf 2) («Language.mArgs» x3);
                   «Base.bindO»
                     (x2 («Language.mArg» x3 (leaf 1)))
                     (fun (x8 : T) =>
                       let x9 : T := «Prelude.some»
                         («Language.mNode» (leaf 9) («Theory.l2» x4 x5) (x6 :: (x8 :: x7)));
                       if («Prelude.and»
                         («Language.mIs» (leaf 5) (leaf 1) x8)
                         («Base.isEmpty»
                           (Const.children («Language.mD» x8 (leaf 1))))).label ≠ 0 then
                         let x10 : T := «Language.mArg» x8 (leaf 0);
                         if («Derivation.primIs»
                           x0
                           («Language.mD» x8 (leaf 0))
                           «Derivation.zeroPrim»).label ≠ 0 then
                           «Base.bindO»
                             (x2 x10)
                             (fun (x11 : T) =>
                               if («Language.mIs» (leaf 2) (leaf 0) x11).label ≠ 0 then
                                 x2 x6
                               else
                                 x9)
                         else
                           if («Derivation.primIs»
                             x0
                             («Language.mD» x8 (leaf 0))
                             «Derivation.succPrim»).label ≠ 0 then
                             let x11 : T := «Language.mNode»
                               (leaf 9)
                               («Theory.l2» x4 x5)
                               (x6 :: (x10 :: x7));
                             «Base.bindO» (x1 x4 ((«Machine.delayed» (x2 x11) x11) :: x7) x5) x2
                           else
                             x9
                       else
                         x9));
    x4

def «Machine.whnfList» :=
  fun (x0 : T) (x1 : T → List T → T → T) (x2 : T → T) (x3 : T) =>
    let x4 : T := (let x4 : T := «Language.mD» x3 (leaf 0);
                   let x5 : T := «Language.mD» x3 (leaf 1);
                   let x6 : T := «Language.mArg» x3 (leaf 0);
                   let x7 : List T := «Prelude.drop» (leaf 2) («Language.mArgs» x3);
                   «Base.bindO»
                     (x2 («Language.mArg» x3 (leaf 1)))
                     (fun (x8 : T) =>
                       let x9 : T := «Prelude.some»
                         («Language.mNode» (leaf 10) («Theory.l2» x4 x5) (x6 :: (x8 :: x7)));
                       if («Prelude.and»
                         («Language.mIs» (leaf 5) (leaf 1) x8)
                         (Const.eq
                           («Prelude.length» (Const.children («Language.mD» x8 (leaf 1))))
                           (leaf 1))).label ≠ 0 then
                         let x10 : T := «Language.mArg» x8 (leaf 0);
                         if («Derivation.primIs»
                           x0
                           («Language.mD» x8 (leaf 0))
                           «Derivation.nilPrim»).label ≠ 0 then
                           «Base.bindO»
                             (x2 x10)
                             (fun (x11 : T) =>
                               if («Language.mIs» (leaf 2) (leaf 0) x11).label ≠ 0 then
                                 x2 x6
                               else
                                 x9)
                         else
                           if («Derivation.primIs»
                             x0
                             («Language.mD» x8 (leaf 0))
                             «Derivation.consPrim»).label ≠ 0 then
                             «Base.bindO»
                               (x2 x10)
                               (fun (x11 : T) =>
                                 if («Language.mIs» (leaf 3) (leaf 2) x11).label ≠ 0 then
                                   let x12 : T := «Language.mNode»
                                     (leaf 10)
                                     («Theory.l2» x4 x5)
                                     (x6 :: ((«Language.mArg» x11 (leaf 1)) :: x7));
                                   «Base.bindO»
                                     (x1
                                       x4
                                       ((«Machine.delayed» (x2 x12) x12) ::
                                         ((«Language.mArg» x11 (leaf 0)) :: x7))
                                       x5)
                                     x2
                                 else
                                   x9)
                           else
                             x9
                       else
                         x9));
    x4

def «Machine.whnfRose» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T)
    (x3 : T → List T → T → T)
    (x4 : T → T)
    (x5 : T) =>
    let x6 : T := (let x6 : T := «Language.mD» x5 (leaf 0);
                   let x7 : T := «Language.mD» x5 (leaf 1);
                   let x8 : T := «Language.mD» x5 (leaf 2);
                   let x9 : List T := «Prelude.tail» («Language.mArgs» x5);
                   «Base.bindO»
                     (x4 («Language.mArg» x5 (leaf 0)))
                     (fun (x10 : T) =>
                       let x11 : T := «Prelude.some»
                         («Language.mNode» (leaf 11) («Theory.l3» x6 x7 x8) (x10 :: x9));
                       if («Prelude.and»
                         («Language.mIs» (leaf 5) (leaf 1) x10)
                         («Prelude.and»
                           («Prelude.or»
                             («Derivation.primIs»
                               x0
                               («Language.mD» x10 (leaf 0))
                               «Derivation.nodePrim»)
                             («Derivation.primIs»
                               x0
                               («Language.mD» x10 (leaf 0))
                               «Derivation.lnodePrim»))
                           («Prelude.and»
                             («Derivation.primIs» x0 x1 «Derivation.nilPrim»)
                             («Derivation.primIs» x0 x2 «Derivation.consPrim»)))).label ≠ 0 then
                         «Base.bindO»
                           (x4 («Language.mArg» x10 (leaf 0)))
                           (fun (x12 : T) =>
                             if («Language.mIs» (leaf 3) (leaf 2) x12).label ≠ 0 then
                               let x13 : T := «Language.mNode»
                                 (leaf 10)
                                 («Theory.l2»
                                   («Language.mArr»
                                     x2
                                     («Prelude.single» x6)
                                     («Language.mPair»
                                       («Language.mRoseRec»
                                         x6
                                         («Derivation.weakenStep2» x7)
                                         («Language.var» (leaf 1)))
                                       («Language.var» (leaf 0))))
                                   x8)
                                 ((«Language.mNode»
                                   (leaf 5)
                                   («Theory.l2» x1 (Const.node (leaf 0) («Prelude.single» x6)))
                                   («Prelude.single»
                                     («Language.mNode» (leaf 2) ([] : List T) ([] : List T)))) ::
                                   ((«Language.mArg» x12 (leaf 1)) :: x9));
                               «Base.bindO»
                                 (x3
                                   x7
                                   ((«Language.mNode»
                                     (leaf 3)
                                     ([] : List T)
                                     («Theory.l2»
                                       («Language.mArg» x12 (leaf 0))
                                       («Machine.delayed» (x4 x13) x13))) ::
                                     x9)
                                   x8)
                                 x4
                             else
                               x11)
                       else
                         x11));
    x6

def «Machine.whnfStep» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T)
    (x3 : T → List T → T → T)
    (x4 : T → T)
    (x5 : T) =>
    let x6 : T := (let x6 : T := Const.label x5;
                   let x7 : List T := «Language.mArgs» x5;
                   if («Language.mIs» (leaf 15) (leaf 2) x5).label ≠ 0 then
                     let x8 : T := «Language.mArg» x5 (leaf 0);
                     if (Const.eq (Const.label x8) (leaf 16)).label ≠ 0 then
                       «Prelude.none»
                     else
                       «Prelude.some» x8
                   else
                     if («Prelude.and»
                       («Prelude.or» (Const.eq x6 (leaf 7)) (Const.eq x6 (leaf 8)))
                       (Const.eq («Prelude.length» x7) (leaf 1))).label ≠ 0 then
                       «Base.bindO»
                         (x4 («Language.mArg» x5 (leaf 0)))
                         (fun (x8 : T) =>
                           if («Language.mIs» (leaf 3) (leaf 2) x8).label ≠ 0 then
                             x4
                               («Language.mArg»
                                 x8
                                 (if (Const.eq x6 (leaf 7)).label ≠ 0 then leaf 0 else leaf 1))
                           else
                             «Prelude.some»
                               («Language.mNode» x6 ([] : List T) («Prelude.single» x8)))
                     else
                       if («Language.mIs» (leaf 6) (leaf 2) x5).label ≠ 0 then
                         «Machine.whnfApp»
                           x0
                           x3
                           x4
                           («Language.mArg» x5 (leaf 0))
                           («Language.mArg» x5 (leaf 1))
                       else
                         if («Prelude.and»
                           (Const.eq x6 (leaf 9))
                           («Base.not» (Const.lt («Prelude.length» x7) (leaf 2)))).label ≠ 0 then
                           «Machine.whnfNat» x0 x3 x4 x5
                         else
                           if («Prelude.and»
                             (Const.eq x6 (leaf 10))
                             («Base.not» (Const.lt («Prelude.length» x7) (leaf 2)))).label ≠ 0 then
                             «Machine.whnfList» x0 x3 x4 x5
                           else
                             if («Prelude.and»
                               (Const.eq x6 (leaf 11))
                               («Base.not» («Base.isEmpty» x7))).label ≠ 0 then
                               «Machine.whnfRose» x0 x1 x2 x3 x4 x5
                             else
                               «Prelude.some» x5);
    x6

def «Machine.marked» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prelude.some»
      (Const.node (leaf 0) («Theory.l2» x0 x1));
    x2

def «Machine.nfTerm» :=
  fun (x0 : T) => let x1 : T := Const.child x0 (leaf 0); x1

def «Machine.nfMark» :=
  fun (x0 : T) => let x1 : T := Const.child x0 (leaf 1); x1

def «Machine.nfNode» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T → List T → T → T)
    (x3 : List T → T → T → T)
    (x4 : List T)
    (x5 : T)
    (x6 : T) =>
    let x7 : T := (let x7 : T := Const.label x6;
                   let x8 : List T := «Language.mArgs» x6;
                   if («Prelude.and»
                     (Const.eq x7 (leaf 9))
                     («Base.not» (Const.lt («Prelude.length» x8) (leaf 2)))).label ≠ 0 then
                     «Base.bindO»
                       (x3 x4 x5 («Prelude.at» x8 (leaf 0)))
                       (fun (x9 : T) =>
                         «Base.bindO»
                           (x3 x4 x5 («Prelude.at» x8 (leaf 1)))
                           (fun (x10 : T) =>
                             «Base.bindO»
                               («Derivation.typeIn» x0 x1 x4 («Machine.nfTerm» x9))
                               (fun (x11 : T) =>
                                 «Base.bindO»
                                   («Base.bindO»
                                     (x2
                                       («Language.mD» x6 (leaf 0))
                                       ((«Machine.level» x5) :: («Prelude.drop» (leaf 2) x8))
                                       («Language.mD» x6 (leaf 1)))
                                     (fun (x12 : T) => x3 (x11 :: x4) (Const.add x5 (leaf 1)) x12))
                                   (fun (x12 : T) =>
                                     «Machine.marked»
                                       («Language.mNatRec»
                                         («Machine.nfTerm» x9)
                                         («Machine.nfTerm» x12)
                                         («Machine.nfTerm» x10))
                                       («Prelude.or»
                                         («Machine.nfMark» x9)
                                         («Machine.nfMark» x10))))))
                   else
                     if («Prelude.and»
                       (Const.eq x7 (leaf 10))
                       («Base.not» (Const.lt («Prelude.length» x8) (leaf 2)))).label ≠ 0 then
                       «Base.bindO»
                         (x3 x4 x5 («Prelude.at» x8 (leaf 0)))
                         (fun (x9 : T) =>
                           «Base.bindO»
                             (x3 x4 x5 («Prelude.at» x8 (leaf 1)))
                             (fun (x10 : T) =>
                               «Base.bindO»
                                 («Derivation.typeIn» x0 x1 x4 («Machine.nfTerm» x9))
                                 (fun (x11 : T) =>
                                   «Base.bindO»
                                     («Base.bindO»
                                       («Derivation.typeIn» x0 x1 x4 («Machine.nfTerm» x10))
                                       «Language.listPart»)
                                     (fun (x12 : T) =>
                                       «Base.bindO»
                                         («Base.bindO»
                                           (x2
                                             («Language.mD» x6 (leaf 0))
                                             ((«Machine.level» (Const.add x5 (leaf 1))) ::
                                               ((«Machine.level» x5) ::
                                                 («Prelude.drop» (leaf 2) x8)))
                                             («Language.mD» x6 (leaf 1)))
                                           (fun (x13 : T) =>
                                             x3 (x11 :: (x12 :: x4)) (Const.add x5 (leaf 2)) x13))
                                         (fun (x13 : T) =>
                                           «Machine.marked»
                                             («Language.mListRec»
                                               («Machine.nfTerm» x9)
                                               («Machine.nfTerm» x13)
                                               («Machine.nfTerm» x10))
                                             («Prelude.or»
                                               («Machine.nfMark» x9)
                                               («Machine.nfMark» x10)))))))
                     else
                       if («Prelude.and»
                         (Const.eq x7 (leaf 11))
                         («Base.not» («Base.isEmpty» x8))).label ≠ 0 then
                         «Base.bindO»
                           (x3 x4 x5 («Prelude.at» x8 (leaf 0)))
                           (fun (x9 : T) =>
                             «Base.bindO»
                               («Base.bindO»
                                 («Derivation.typeIn» x0 x1 x4 («Machine.nfTerm» x9))
                                 «Language.roseLabel»)
                               (fun (x10 : T) =>
                                 «Base.bindO»
                                   («Base.bindO»
                                     (x2
                                       («Language.mD» x6 (leaf 1))
                                       ((«Machine.level» x5) :: («Prelude.tail» x8))
                                       («Language.mD» x6 (leaf 2)))
                                     (fun (x11 : T) =>
                                       x3
                                         ((«Theory.prod»
                                           x10
                                           («Theory.list» («Language.mD» x6 (leaf 0)))) ::
                                           x4)
                                         (Const.add x5 (leaf 1))
                                         x11))
                                   (fun (x11 : T) =>
                                     «Machine.marked»
                                       («Language.mRoseRec»
                                         («Language.mD» x6 (leaf 0))
                                         («Machine.nfTerm» x11)
                                         («Machine.nfTerm» x9))
                                       («Machine.nfMark» x9))))
                       else
                         if (Const.eq x7 (leaf 4)).label ≠ 0 then
                           «Base.bindO»
                             («Base.bindO»
                               (x2
                                 («Language.mD» x6 (leaf 1))
                                 ((«Machine.level» x5) :: x8)
                                 («Language.mD» x6 (leaf 2)))
                               (fun (x9 : T) =>
                                 x3 ((«Language.mD» x6 (leaf 0)) :: x4) (Const.add x5 (leaf 1)) x9))
                             (fun (x9 : T) =>
                               «Machine.marked»
                                 («Language.mLam» («Language.mD» x6 (leaf 0)) («Machine.nfTerm» x9))
                                 («Machine.nfMark» x9))
                         else
                           if («Prelude.or»
                             (Const.lt x7 (leaf 4))
                             («Prelude.or»
                               («Prelude.and» (Const.lt (leaf 4) x7) (Const.lt x7 (leaf 9)))
                               («Prelude.or»
                                 (Const.eq x7 (leaf 12))
                                 (Const.eq x7 (leaf 13))))).label ≠ 0 then
                             let x9 : List T := «Base.mapT» (fun (x9 : T) => x3 x4 x5 x9) x8;
                             if («Base.allT» «Prelude.isSome» x9).label ≠ 0 then
                               «Machine.marked»
                                 («Machine.readStep»
                                   x5
                                   x6
                                   («Base.mapT»
                                     (fun (x10 : T) => «Machine.nfTerm» («Prelude.get» x10))
                                     x9))
                                 («Base.anyT»
                                   (fun (x10 : T) => «Machine.nfMark» («Prelude.get» x10))
                                   x9)
                             else
                               «Prelude.none»
                           else
                             if (Const.eq x7 (leaf 16)).label ≠ 0 then
                               «Prelude.none»
                             else
                               «Machine.marked» («Machine.readBack» x5 x6) (leaf 0));
    x7

def «Machine.renorm» :=
  fun (x0 : T → List T → T → T)
    (x1 : List T → T → T → T)
    (x2 : List T)
    (x3 : T)
    (x4 : T) =>
    let x5 : T := «Base.bindO»
      («Base.bindO» (x0 x4 ([] : List T) x3) (fun (x5 : T) => x1 x2 x3 x5))
      (fun (x5 : T) => «Machine.marked» («Machine.nfTerm» x5) (leaf 1));
    x5

def «Machine.nfStep» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T → T → T → T)
    (x3 : T → List T → T → T)
    (x4 : T → T)
    (x5 : List T → T → T → T)
    (x6 : List T)
    (x7 : T)
    (x8 : T) =>
    let x9 : T := «Base.bindO»
      (x4 x8)
      (fun (x9 : T) =>
        «Base.bindO»
          («Machine.nfNode» x0 x1 x3 x5 x6 x7 x9)
          (fun (x10 : T) =>
            if («Prelude.and»
              («Machine.nfMark» x10)
              («Prelude.and»
                (Const.lt (leaf 5) (Const.label x9))
                (Const.lt (Const.label x9) (leaf 12)))).label ≠ 0 then
              «Machine.renorm» x3 x5 x6 x7 («Machine.nfTerm» x10)
            else
              let x11 : T := x2 x6 x7 («Machine.nfTerm» x10);
              if («Prelude.and»
                («Prelude.isSome» x11)
                («Machine.varLeaves» («Prelude.get» x11))).label ≠ 0 then
                «Machine.renorm» x3 x5 x6 x7 («Prelude.get» x11)
              else
                «Prelude.some» x10));
    x9

def «Machine.machStep» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T → T)
    (x3 : T)
    (x4 : T)
    (x5 : List T → T → T → T)
    (x6 : (T → List T → T → T) × ((T → T) × (List T → T → T → T))) =>
    let x7 : (T → List T → T → T) ×
      ((T → T) ×
        (List T →
          T →
            T →
              T)) := (let x7 : T → List T → T → T := (x6).1;
                      let x8 : T → T := ((x6).2).1;
                      let x9 : List T → T → T → T := ((x6).2).2;
                      (fun (x10 : T) (x11 : List T) (x12 : T) =>
                        «Machine.evalStep» x0 x2 x7 x8 x10 x11 x12,
                        (fun (x10 : T) => «Machine.whnfStep» x0 x3 x4 x7 x8 x10,
                          fun (x10 : List T) (x11 : T) (x12 : T) =>
                            «Machine.nfStep» x0 x1 x5 x7 x8 x9 x10 x11 x12)));
    x7

def «Machine.machine» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T → T)
    (x3 : T)
    (x4 : T)
    (x5 : List T → T → T → T)
    (x6 : T) =>
    let x7 : (T → List T → T → T) ×
      ((T → T) ×
        (List T →
          T →
            T →
              T)) := Const.iter
      (α := (T → List T → T → T) × ((T → T) × (List T → T → T → T)))
      («Machine.machStep» x0 x1 x2 x3 x4 x5)
      (fun (_ : T) (_ : List T) (_ : T) => «Prelude.none»,
        (fun (_ : T) => «Prelude.none»,
          fun (_ : List T) (_ : T) (_ : T) => «Prelude.none»))
      x6;
    x7

def «Machine.machineReduce» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T → T)
    (x3 : T)
    (x4 : T)
    (x5 : List T → T → T → T)
    (x6 : T)
    (x7 : List T)
    (x8 : T) =>
    let x9 : T := (let x9 : (T → List T → T → T) ×
                     ((T → T) ×
                       (List T → T → T → T)) := «Machine.machine» x0 x1 x2 x3 x4 x5 x6;
                   «Base.bindO»
                     («Base.bindO»
                       ((x9).1 x8 ([] : List T) (leaf 0))
                       (fun (x10 : T) => ((x9).2).2 x7 (leaf 0) x10))
                     (fun (x10 : T) => «Prelude.some» («Machine.nfTerm» x10)));
    x9

def «Conversion/RuleAt.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Conversion/EachRule.all» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «Prelude.and» (x0 x2) x3)
      (leaf 1)
      x1;
    x2

def «Conversion/EachRule.any» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «Prelude.or» (x0 x2) x3)
      (leaf 0)
      x1;
    x2

def «Conversion/EachRule.isEmpty» :=
  fun (x0 : List T) =>
    let x1 : T := Const.eq
      (Const.foldr
        (α := T)
        (β := T)
        (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
        (leaf 0)
        x0)
      (leaf 0);
    x1

def «Conversion/EachRule.take» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := (let x2 : T := Const.foldr
              (α := T)
              (β := T)
              (fun (_ : T) (x3 : T) => Const.add x3 (leaf 1))
              (leaf 0)
              x1;
            (Const.foldr
              (α := T)
              (β := T × List T)
              (fun (x3 : T) (x4 : T × List T) =>
                (Const.add (x4).1 (leaf 1),
                  if (Const.lt
                    (Const.sub (Const.sub x2 (x4).1) (leaf 1))
                    x0).label ≠ 0 then
                    (x3 :: (x4).2)
                  else
                    (x4).2))
              (leaf 0, ([] : List T))
              x1).2);
    x2

def «Conversion.ckNone» :=
  fun (_ : T) (_ : List T) (_ : T) (_ : List T) (_ : T) => leaf 0

def «Conversion.toRule» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := Const.label x0;
                   if (Const.lt x1 (leaf 37)).label ≠ 0 then
                     Const.node x1 («Prelude.single» (Const.child x0 (leaf 0)))
                   else
                     if (Const.eq x1 (leaf 39)).label ≠ 0 then
                       Const.node
                         (leaf 27)
                         («Prelude.single»
                           (Const.node
                             (leaf 0)
                             («Theory.l3»
                               («Language.mD» x0 (leaf 0))
                               («Language.mD» x0 (leaf 1))
                               (Const.node (leaf 0) ([] : List T)))))
                     else
                       Const.node
                         (leaf 1)
                         («Prelude.single» (Const.node (leaf 0) ([] : List T))));
    x1

def «Conversion.baseNode» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := Const.node
      x0
      (x1 ::
        («Base.mapT»
          «Conversion.toRule»
          («Prelude.tail» (Const.children x2))));
    x3

def «Conversion.ruleOf» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := Const.label x0;
                   let x2 : List T := Const.children x0;
                   if (Const.eq x1 (leaf 0)).label ≠ 0 then
                     «Prover.nrRule»
                       («Prelude.at» x2 (leaf 0))
                       («Derivation.terms» (Const.children («Prelude.at» x2 (leaf 1))))
                   else
                     if (Const.eq x1 (leaf 1)).label ≠ 0 then
                       «Prover.nrDelta» («Prelude.at» x2 (leaf 0))
                     else
                       if (Const.eq x1 (leaf 2)).label ≠ 0 then
                         «Prover.nrBelow»
                           («Prelude.at» x2 (leaf 0))
                           («Derivation.terms» (Const.children («Prelude.at» x2 (leaf 1))))
                       else
                         if (Const.eq x1 (leaf 4)).label ≠ 0 then
                           «Prover.nrThm»
                             («Prelude.at» x2 (leaf 0))
                             («Language.objs» (Const.children («Prelude.at» x2 (leaf 1))))
                         else
                           if (Const.eq x1 (leaf 5)).label ≠ 0 then
                             «Prover.nrThmAt»
                               («Prelude.at» x2 (leaf 0))
                               («Language.objs» (Const.children («Prelude.at» x2 (leaf 1))))
                               («Prelude.at» x2 (leaf 2))
                               («Prelude.at» x2 (leaf 3))
                           else
                             if (Const.eq x1 (leaf 6)).label ≠ 0 then
                               «Prover.nrHyp» («Prelude.at» x2 (leaf 0))
                             else
                               «Prover.nrUnit»);
    x1

def «Conversion.rulesOf» :=
  fun (x0 : List T) =>
    let x1 : List T := «Conversion/RuleAt.map» «Conversion.ruleOf» x0; x1

def «Conversion.stepNorm» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : List T) =>
    let x4 : T →
      List T →
        T →
          List T →
            T →
              T := (let x4 : List T →
                      List T →
                        T →
                          T := «Prover.normalize»
                      x0
                      x1
                      x2
                      («Conversion.rulesOf» (Const.children («Prelude.at» x3 (leaf 0))))
                      («Prelude.at» x3 (leaf 1));
                    fun (x5 : T) (x6 : List T) (x7 : T) (x8 : List T) (x9 : T) =>
                      if (x5).label ≠ 0 then
                        leaf 0
                      else
                        «Prover.bindNT»
                          (x4
                            x6
                            («Base.mapT» (fun (x10 : T) => «Derivation.weakenBy» x7 x10) x8)
                            x9)
                          (fun (x10 : T) => «Prelude.some» («Prover.nfTerm» x10)));
    x4

def «Conversion.stepEval» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : List T) =>
    let x4 : T →
      List T →
        T →
          List T →
            T →
              T := (let x4 : T →
                      List T →
                        List T →
                          T →
                            T := «Prover.eval»
                      x0
                      x1
                      x2
                      («Conversion.rulesOf» (Const.children («Prelude.at» x3 (leaf 0))))
                      («Prelude.at» x3 (leaf 1));
                    fun (x5 : T) (x6 : List T) (x7 : T) (x8 : List T) (x9 : T) =>
                      if (x5).label ≠ 0 then
                        leaf 0
                      else
                        «Prover.bindNT»
                          (x4
                            («Prelude.at» x3 (leaf 2))
                            x6
                            («Base.mapT» (fun (x10 : T) => «Derivation.weakenBy» x7 x10) x8)
                            x9)
                          (fun (x10 : T) => «Prelude.some» («Prover.nfTerm» x10)));
    x4

def «Conversion.applyInst» :=
  fun (x0 : List T) (x1 : T) (x2 : List T) (x3 : T) =>
    let x4 : T := (let x4 : T := «Derivation.thmAt» x0 x1;
                   if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
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
                     let x8 : T := «Prover.matchTerm»
                       (if («Base.isEmpty» x2).label ≠ 0 then
                         «Derivation.thConcl» x6
                       else
                         «Language.osubst» x2 («Derivation.thConcl» x6))
                       (leaf 0)
                       x3
                       («Prelude.replicate»
                         («Prelude.length» («Derivation.thCtx» x6))
                         «Prelude.none»);
                     if (Const.eq (Const.label x8) (leaf 1)).label ≠ 0 then
                       let x9 : List T := Const.children x8;
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
                       «Base.allSomeT» («Prover.assigned» x10)
                     else
                       let _ : List T := Const.children x8; «Prelude.none»
                   else
                     let _ : List T := Const.children x4; «Prelude.none»);
    x4

def «Conversion.stepApply» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : T)
    (x5 : List (T → List T → T → List T → T → T)) =>
    let x6 : T →
      List T →
        T →
          List T →
            T →
              T := (fun (x6 : T) (x7 : List T) (_ : T) (x9 : List T) (x10 : T) =>
      if (x6).label ≠ 0 then
        let x11 : T := «Conversion.applyInst»
          x1
          («Prelude.at» x3 (leaf 0))
          (Const.children («Prelude.at» x3 (leaf 1)))
          x10;
        if («Prelude.isSome» x11).label ≠ 0 then
          «Derivation.checkStep»
            x0
            x1
            x2
            («Conversion.baseNode»
              (leaf 27)
              (Const.node
                (leaf 0)
                («Theory.l3»
                  («Prelude.at» x3 (leaf 0))
                  («Prelude.at» x3 (leaf 1))
                  («Prelude.get» x11)))
              x4)
            x5
            (leaf 1)
            x7
            (leaf 0)
            x9
            x10
        else
          leaf 0
      else
        «Prelude.none»);
    x6

def «Conversion.stepLit» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : T →
      List T →
        T →
          List T →
            T →
              T := (fun (x2 : T) (_ : List T) (_ : T) (_ : List T) (x6 : T) =>
      if (x2).label ≠ 0 then
        leaf 0
      else
        if («Base.anyT»
          (fun (x7 : T) => Const.eq x7 («Prelude.at» x1 (leaf 0)))
          x0).label ≠ 0 then
          «Literals.litEval» x6
        else
          «Prelude.none»);
    x2

def «Conversion.machineReduceBy» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T → T)
    (x4 : T)
    (x5 : T)
    (x6 : List T)
    (x7 : T)
    (x8 : List T)
    (x9 : List T)
    (x10 : T) =>
    let x11 : T := (if («Conversion/EachRule.isEmpty» x6).label ≠ 0 then
      «Machine.machineReduce»
        x0
        x2
        x3
        x4
        x5
        (fun (_ : List T) (_ : T) (_ : T) => «Prelude.none»)
        x7
        x8
        x10
    else
      let x11 : List T →
        T →
          List T →
            T →
              T := «Prover.rootRewriteK»
        x0
        x1
        x2
        («Prover.indexRules» x1 («Prover.prepareRules» x1 x6))
        («Prover.prepareHyps» x9);
      «Machine.machineReduce»
        x0
        x2
        x3
        x4
        x5
        (fun (x12 : List T) (x13 : T) (x14 : T) =>
          let x15 : T := x11 x12 x13 x9 x14;
          if (Const.eq (Const.label x15) (leaf 1)).label ≠ 0 then
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
            «Prelude.some» («Language.p1» x17)
          else
            let _ : List T := Const.children x15; «Prelude.none»)
        x7
        x8
        x10);
    x11

def «Conversion.stepMachine» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : List T) =>
    let x4 : T →
      List T →
        T →
          List T →
            T →
              T := (let x4 : List T := Const.children («Prelude.at» x3 (leaf 2));
                    let x5 : List
                      T := «Conversion.rulesOf»
                      (Const.children («Prelude.at» x3 (leaf 5)));
                    fun (x6 : T) (x7 : List T) (x8 : T) (x9 : List T) (x10 : T) =>
                      if (x6).label ≠ 0 then
                        leaf 0
                      else
                        «Conversion.machineReduceBy»
                          x0
                          x1
                          x2
                          (fun (x11 : T) =>
                            «Prelude.and»
                              (Const.lt x11 («Prelude.at» x3 (leaf 1)))
                              («Base.not» («Base.anyT» (fun (x12 : T) => Const.eq x12 x11) x4)))
                          («Prelude.at» x3 (leaf 3))
                          («Prelude.at» x3 (leaf 4))
                          x5
                          («Prelude.at» x3 (leaf 0))
                          x7
                          (if («Conversion/EachRule.isEmpty» x5).label ≠ 0 then
                            ([] : List T)
                          else
                            «Base.mapT» (fun (x11 : T) => «Derivation.weakenBy» x8 x11) x9)
                          x10);
    x4

def «Conversion.convStep» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List T)
    (x3 : T)
    (x4 : T)
    (x5 : List (T → List T → T → List T → T → T)) =>
    let x6 : T →
      List T →
        T →
          List T →
            T →
              T := (let x6 : T := Const.label x4;
                    let x7 : T := Const.child x4 (leaf 0);
                    let x8 : List T := Const.children x7;
                    if (Const.lt x6 (leaf 37)).label ≠ 0 then
                      «Derivation.checkStep» x0 x1 x3 («Conversion.baseNode» x6 x7 x4) x5
                    else
                      if (Const.eq x6 (leaf 37)).label ≠ 0 then
                        «Conversion.stepNorm» x0 x1 x3 x8
                      else
                        if (Const.eq x6 (leaf 38)).label ≠ 0 then
                          «Conversion.stepEval» x0 x1 x3 x8
                        else
                          if (Const.eq x6 (leaf 39)).label ≠ 0 then
                            «Conversion.stepApply» x0 x1 x3 x8 x4 x5
                          else
                            if (Const.eq x6 (leaf 40)).label ≠ 0 then
                              «Conversion.stepLit» x2 x8
                            else
                              if (Const.eq x6 (leaf 41)).label ≠ 0 then
                                «Conversion.stepMachine» x0 x1 x3 x8
                              else
                                «Conversion.ckNone»);
    x6

def «Conversion.convCheck» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : T) (x4 : T) =>
    let x5 : T →
      List T →
        T →
          List T →
            T →
              T := Const.para
      (α := T → List T → T → List T → T → T)
      («Conversion.convStep» x0 x1 x2 x3)
      x4;
    x5

def «Conversion.thmConvChecks» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : T) (x4 : T) =>
    let x5 : T := (let x5 : T := «Derivation.thArity» x3;
                   let x6 : List T := «Derivation.thCtx» x3;
                   if («Prelude.and»
                     («Base.allT» («Language.isTy» x0 x5) x6)
                     («Prelude.and»
                       («Base.allT»
                         («Derivation.isFormula» x0 x5 x6)
                         («Derivation.thHyps» x3))
                       («Derivation.isFormula»
                         x0
                         x5
                         x6
                         («Derivation.thConcl» x3)))).label ≠ 0 then
                     «Conversion.convCheck»
                       x0
                       x1
                       x2
                       x5
                       x4
                       (leaf 1)
                       x6
                       (leaf 0)
                       («Derivation.thHyps» x3)
                       («Derivation.thConcl» x3)
                   else
                     leaf 0);
    x5

end GebMirror.Metalogic

end
