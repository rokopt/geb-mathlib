module

public import GebMirror.Metalogic.Checker

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «Translation/OpSigs.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Translation/OpSigs.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Translation/OpSigs.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Translation/OpSigs.reverse» :=
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

def «Translation/OpSigs.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Translation/OpSigs.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Translation/OpSigs.tail» x1 x0;
    x2

def «Translation/OpSigs.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Translation/OpSigs.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Translation/PrimF.l2» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List T := (x0 :: (x1 :: ([] : List T))); x2

def «Translation/PrimF.l3» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : List T := (x0 :: («Translation/PrimF.l2» x1 x2)); x3

def «Translation/PrimF.l4» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : List T := (x0 :: («Translation/PrimF.l3» x1 x2 x3)); x4

def «Translation/PrimF.l5» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : List T := (x0 :: («Translation/PrimF.l4» x1 x2 x3 x4)); x5

def «Translation/PrimF.l6» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : List T := (x0 :: («Translation/PrimF.l5» x1 x2 x3 x4 x5)); x6

def «Translation/LDefnL.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Translation/LDefnL.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Translation/LDefnL.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Translation/LDefnL.reverse» :=
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

def «Translation/LDefnL.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Translation/LDefnL.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Translation/LDefnL.tail» x1 x0;
    x2

def «Translation/LDefnL.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Translation/LDefnL.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Translation/KTyL.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Translation/KTyL.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Translation/KTyL.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Translation/KTyL.reverse» :=
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

def «Translation/KTyL.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Translation/KTyL.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Translation/KTyL.tail» x1 x0;
    x2

def «Translation/KTyL.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Translation/KTyL.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Translation/DefLang.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Translation.bitTy» := «Theory.coprod» «Theory.one» «Theory.one»

def «Translation.bitsTy» := «Theory.list» «Translation.bitTy»

def «Translation.treeTy» := «Theory.lrose» «Translation.bitsTy»

def «Translation.ordTy» :=
  «Theory.coprod» «Theory.one» «Translation.bitTy»

def «Translation.trTy» :=
  fun (x0 : T) =>
    let x1 : T := Const.fold
      (α := T)
      (fun (x1 : T) (x2 : List T) =>
        let x3 : T := «Prelude.length» x2;
        if (Const.eq x3 (leaf 0)).label ≠ 0 then
          if (Const.eq x1 (leaf 0)).label ≠ 0 then
            «Prelude.some» «Translation.treeTy»
          else
            if (Const.eq x1 (leaf 1)).label ≠ 0 then
              «Prelude.some» «Theory.one»
            else
              «Prelude.none»
        else
          if (Const.eq x3 (leaf 1)).label ≠ 0 then
            if (Const.eq x1 (leaf 4)).label ≠ 0 then
              «Base.mapO» «Theory.list» («Prelude.at» x2 (leaf 0))
            else
              «Prelude.none»
          else
            if (Const.eq x3 (leaf 2)).label ≠ 0 then
              if (Const.eq x1 (leaf 2)).label ≠ 0 then
                «Base.bindO»
                  («Prelude.at» x2 (leaf 0))
                  (fun (x4 : T) =>
                    «Base.mapO» («Theory.prod» x4) («Prelude.at» x2 (leaf 1)))
              else
                if (Const.eq x1 (leaf 3)).label ≠ 0 then
                  «Base.bindO»
                    («Prelude.at» x2 (leaf 0))
                    (fun (x4 : T) =>
                      «Base.mapO» («Theory.exp» x4) («Prelude.at» x2 (leaf 1)))
                else
                  «Prelude.none»
            else
              «Prelude.none»)
      x0;
    x1

def «Translation.trPrims» :=
  «Translation/PrimF.l6»
    «Derivation.nilPrim»
    «Derivation.consPrim»
    «Derivation.lnodePrim»
    «Derivation.inlPrim»
    «Derivation.inrPrim»
    «Derivation.casePrim»

def «Translation.nilT» :=
  fun (x0 : T) =>
    let x1 : T := «Language.mArr»
      (leaf 0)
      («Prelude.single» x0)
      «Language.mStar»;
    x1

def «Translation.consT» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Language.mArr»
      (leaf 1)
      («Prelude.single» x0)
      («Language.mPair» x1 x2);
    x3

def «Translation.nodeT» :=
  fun (x0 : T) =>
    let x1 : T := «Language.mArr»
      (leaf 2)
      («Prelude.single» «Translation.bitsTy»)
      x0;
    x1

def «Translation.bit0T» :=
  «Language.mArr»
    (leaf 3)
    («Theory.l2» «Theory.one» «Theory.one»)
    «Language.mStar»

def «Translation.bit1T» :=
  «Language.mArr»
    (leaf 4)
    («Theory.l2» «Theory.one» «Theory.one»)
    «Language.mStar»

def «Translation.ifBit» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «Language.app»
      («Language.mArr»
        (leaf 5)
        («Theory.l3» «Theory.one» «Theory.one» x0)
        («Language.mPair»
          («Language.mLam» «Theory.one» («Derivation.weaken1» x2))
          («Language.mLam» «Theory.one» («Derivation.weaken1» x3))))
      x1;
    x4

def «Translation.ltO» :=
  «Language.mArr»
    (leaf 3)
    («Theory.l2» «Theory.one» «Translation.bitTy»)
    «Language.mStar»

def «Translation.eqO» :=
  «Language.mArr»
    (leaf 4)
    («Theory.l2» «Theory.one» «Translation.bitTy»)
    «Translation.bit0T»

def «Translation.gtO» :=
  «Language.mArr»
    (leaf 4)
    («Theory.l2» «Theory.one» «Translation.bitTy»)
    «Translation.bit1T»

def «Translation.ifOrd» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := «Language.app»
      («Language.mArr»
        (leaf 5)
        («Theory.l3» «Theory.one» «Translation.bitTy» x0)
        («Language.mPair»
          («Language.mLam» «Theory.one» («Derivation.weaken1» x2))
          («Language.mLam»
            «Translation.bitTy»
            («Translation.ifBit»
              x0
              («Language.var» (leaf 0))
              («Derivation.weaken1» x3)
              («Derivation.weaken1» x4)))))
      x1;
    x5

def «Translation.leafT» :=
  fun (x0 : T) =>
    let x1 : T := «Translation.nodeT»
      («Language.mPair» x0 («Translation.nilT» «Translation.treeTy»));
    x1

def «Translation.call» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) =>
    let x3 : T := «Language.mDefn» x0 x1 («Prelude.reverse» x2); x3

def «Translation.mkDefn» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T) =>
    let x4 : T := «Language.ldefn»
      x0
      («Language.objs» («Prelude.reverse» x1))
      x2
      x3;
    x4

def «Translation.bnilT» :=
  «Translation.call» (leaf 0) ([] : List T) ([] : List T)

def «Translation.b0T» :=
  fun (x0 : T) =>
    let x1 : T := «Translation.call»
      (leaf 1)
      ([] : List T)
      («Prelude.single» x0);
    x1

def «Translation.b1T» :=
  fun (x0 : T) =>
    let x1 : T := «Translation.call»
      (leaf 2)
      ([] : List T)
      («Prelude.single» x0);
    x1

def «Translation.trueT» := «Translation.b0T» «Translation.bnilT»

def «Translation.trNumeral» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := Const.add x0 (leaf 1);
                   Const.foldr
                     (α := T)
                     (β := T)
                     (fun (x2 : T) (x3 : T) =>
                       if (x2).label ≠ 0 then «Translation.b1T» x3 else «Translation.b0T» x3)
                     «Translation.bnilT»
                     («Prelude.digitsLsb» (leaf 2) x1 (Const.log2 x1)));
    x1

def «Translation.quoteT» :=
  fun (x0 : T) =>
    let x1 : T := Const.fold
      (α := T)
      (fun (x1 : T) (x2 : List T) =>
        «Translation.nodeT»
          («Language.mPair»
            («Translation.trNumeral» x1)
            (Const.foldr
              (α := T)
              (β := T)
              («Translation.consT» «Translation.treeTy»)
              («Translation.nilT» «Translation.treeTy»)
              x2)))
      x0;
    x1

def «Translation.condT» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «Translation.call»
      (leaf 6)
      («Prelude.single» x0)
      («Theory.l3» x1 x2 x3);
    x4

def «Translation.lcaseB» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := «Translation.call»
      (leaf 9)
      («Theory.l2» x0 x1)
      («Theory.l3»
        x2
        («Language.mLam» «Theory.one» («Derivation.weaken1» x3))
        x4);
    x5

def «Translation.cmpT» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Translation.call»
      (leaf 16)
      ([] : List T)
      («Theory.l2» x0 x1);
    x2

def «Translation.digitT» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Translation.ifBit»
      «Translation.bitTy»
      x0
      («Translation.ifBit»
        «Translation.bitTy»
        x1
        «Translation.bit1T»
        «Translation.bit0T»)
      («Translation.ifBit»
        «Translation.bitTy»
        x1
        «Translation.bit0T»
        «Translation.bit1T»);
    x2

def «Translation.bitOrdT» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Translation.ifBit»
      «Translation.ordTy»
      x0
      («Translation.ifBit»
        «Translation.ordTy»
        x1
        «Translation.eqO»
        «Translation.ltO»)
      («Translation.ifBit»
        «Translation.ordTy»
        x1
        «Translation.gtO»
        «Translation.eqO»);
    x2

def «Translation.X0» := «Theory.x» (leaf 0)

def «Translation.X1» := «Theory.x» (leaf 1)

def «Translation.lbBnil» :=
  «Translation.mkDefn»
    (leaf 0)
    ([] : List T)
    «Translation.bitsTy»
    («Translation.nilT» «Translation.bitTy»)

def «Translation.lbB0» :=
  «Translation.mkDefn»
    (leaf 0)
    («Prelude.single» «Translation.bitsTy»)
    «Translation.bitsTy»
    («Translation.consT»
      «Translation.bitTy»
      «Translation.bit0T»
      («Language.var» (leaf 0)))

def «Translation.lbB1» :=
  «Translation.mkDefn»
    (leaf 0)
    («Prelude.single» «Translation.bitsTy»)
    «Translation.bitsTy»
    («Translation.consT»
      «Translation.bitTy»
      «Translation.bit1T»
      («Language.var» (leaf 0)))

def «Translation.lbLab» :=
  «Translation.mkDefn»
    (leaf 0)
    («Prelude.single» «Translation.treeTy»)
    «Translation.bitsTy»
    («Language.mRoseRec»
      «Translation.bitsTy»
      («Language.mFst» («Language.var» (leaf 0)))
      («Language.var» (leaf 0)))

def «Translation.lbUnnode» :=
  «Translation.mkDefn»
    (leaf 0)
    («Prelude.single» «Translation.treeTy»)
    («Theory.prod»
      «Translation.bitsTy»
      («Theory.list» «Translation.treeTy»))
    («Language.mRoseRec»
      («Theory.prod»
        «Translation.bitsTy»
        («Theory.list» «Translation.treeTy»))
      («Language.mPair»
        («Language.mFst» («Language.var» (leaf 0)))
        («Language.mListRec»
          («Translation.nilT» «Translation.treeTy»)
          («Translation.consT»
            «Translation.treeTy»
            («Translation.nodeT» («Language.var» (leaf 1)))
            («Language.var» (leaf 0)))
          («Language.mSnd» («Language.var» (leaf 0)))))
      («Language.var» (leaf 0)))

def «Translation.lbChildren» :=
  «Translation.mkDefn»
    (leaf 0)
    («Prelude.single» «Translation.treeTy»)
    («Theory.list» «Translation.treeTy»)
    («Language.mSnd»
      («Translation.call»
        (leaf 4)
        ([] : List T)
        («Prelude.single» («Language.var» (leaf 0)))))

def «Translation.lbCond» :=
  «Translation.mkDefn»
    (leaf 1)
    («Theory.l3» «Translation.bitsTy» «Translation.X0» «Translation.X0»)
    «Translation.X0»
    («Language.app»
      («Language.app»
        («Language.mListRec»
          («Language.mLam»
            «Translation.X0»
            («Language.mLam» «Translation.X0» («Language.var» (leaf 0))))
          («Language.mLam»
            «Translation.X0»
            («Language.mLam» «Translation.X0» («Language.var» (leaf 1))))
          («Language.var» (leaf 2)))
        («Language.var» (leaf 1)))
      («Language.var» (leaf 0)))

def «Translation.lbTail» :=
  «Translation.mkDefn»
    (leaf 1)
    («Prelude.single» («Theory.list» «Translation.X0»))
    («Theory.list» «Translation.X0»)
    («Language.mSnd»
      («Language.mListRec»
        («Language.mPair»
          («Translation.nilT» «Translation.X0»)
          («Translation.nilT» «Translation.X0»))
        («Language.mPair»
          («Translation.consT»
            «Translation.X0»
            («Language.var» (leaf 1))
            («Language.mFst» («Language.var» (leaf 0))))
          («Language.mFst» («Language.var» (leaf 0))))
        («Language.var» (leaf 0))))

def «Translation.lbHeadD» :=
  «Translation.mkDefn»
    (leaf 1)
    («Theory.l2» «Translation.X0» («Theory.list» «Translation.X0»))
    «Translation.X0»
    («Language.app»
      («Language.mListRec»
        («Language.mLam» «Translation.X0» («Language.var» (leaf 0)))
        («Language.mLam» «Translation.X0» («Language.var» (leaf 2)))
        («Language.var» (leaf 0)))
      («Language.var» (leaf 1)))

def «Translation.lbLcase» :=
  let x0 : T := «Theory.exp»
    «Translation.X0»
    («Theory.exp» («Theory.list» «Translation.X0») «Translation.X1»);
  let x1 : T := «Theory.prod»
    («Theory.exp» «Theory.one» «Translation.X1»)
    x0;
  let x2 : T := «Language.mFst»
    («Language.app» («Language.var» (leaf 1)) («Language.var» (leaf 0)));
  «Translation.mkDefn»
    (leaf 2)
    («Theory.l3»
      («Theory.list» «Translation.X0»)
      («Theory.exp» «Theory.one» «Translation.X1»)
      x0)
    «Translation.X1»
    («Language.mSnd»
      («Language.app»
        («Language.mListRec»
          («Language.mLam»
            x1
            («Language.mPair»
              («Translation.nilT» «Translation.X0»)
              («Language.app»
                («Language.mFst» («Language.var» (leaf 0)))
                «Language.mStar»)))
          («Language.mLam»
            x1
            («Language.mPair»
              («Translation.consT» «Translation.X0» («Language.var» (leaf 2)) x2)
              («Language.app»
                («Language.app»
                  («Language.mSnd» («Language.var» (leaf 0)))
                  («Language.var» (leaf 2)))
                x2)))
          («Language.var» (leaf 2)))
        («Language.mPair»
          («Language.var» (leaf 1))
          («Language.var» (leaf 0)))))

def «Translation.lbIsNil» :=
  «Translation.mkDefn»
    (leaf 1)
    («Prelude.single» («Theory.list» «Translation.X0»))
    «Translation.bitsTy»
    («Language.mListRec»
      «Translation.trueT»
      «Translation.bnilT»
      («Language.var» (leaf 0)))

def «Translation.lbSucc» :=
  «Translation.mkDefn»
    (leaf 0)
    («Prelude.single» «Translation.bitsTy»)
    «Translation.bitsTy»
    («Language.mSnd»
      («Language.mListRec»
        («Language.mPair» «Translation.bnilT» «Translation.trueT»)
        («Language.mPair»
          («Translation.consT»
            «Translation.bitTy»
            («Language.var» (leaf 1))
            («Language.mFst» («Language.var» (leaf 0))))
          («Translation.ifBit»
            «Translation.bitsTy»
            («Language.var» (leaf 1))
            («Translation.b1T» («Language.mFst» («Language.var» (leaf 0))))
            («Translation.b0T» («Language.mSnd» («Language.var» (leaf 0))))))
        («Language.var» (leaf 0))))

def «Translation.lbLength» :=
  «Translation.mkDefn»
    (leaf 1)
    («Prelude.single» («Theory.list» «Translation.X0»))
    «Translation.bitsTy»
    («Language.mListRec»
      «Translation.bnilT»
      («Translation.call»
        (leaf 11)
        ([] : List T)
        («Prelude.single» («Language.var» (leaf 0))))
      («Language.var» (leaf 0)))

def «Translation.lbPred» :=
  «Translation.mkDefn»
    (leaf 0)
    («Prelude.single» «Translation.bitsTy»)
    «Translation.bitsTy»
    («Language.mSnd»
      («Language.mListRec»
        («Language.mPair» «Translation.bnilT» «Translation.bnilT»)
        («Language.mPair»
          («Translation.consT»
            «Translation.bitTy»
            («Language.var» (leaf 1))
            («Language.mFst» («Language.var» (leaf 0))))
          («Translation.ifBit»
            «Translation.bitsTy»
            («Language.var» (leaf 1))
            («Translation.condT»
              «Translation.bitsTy»
              («Language.mFst» («Language.var» (leaf 0)))
              («Translation.b1T» («Language.mSnd» («Language.var» (leaf 0))))
              «Translation.bnilT»)
            («Translation.b0T» («Language.mFst» («Language.var» (leaf 0))))))
        («Language.var» (leaf 0))))

def «Translation.lbDbl» :=
  «Translation.mkDefn»
    (leaf 0)
    («Prelude.single» «Translation.bitsTy»)
    «Translation.bitsTy»
    («Language.mSnd»
      («Language.mListRec»
        («Language.mPair» «Translation.bnilT» «Translation.bnilT»)
        («Language.mPair»
          («Translation.consT»
            «Translation.bitTy»
            («Language.var» (leaf 1))
            («Language.mFst» («Language.var» (leaf 0))))
          («Translation.ifBit»
            «Translation.bitsTy»
            («Language.var» (leaf 1))
            («Translation.b1T» («Language.mSnd» («Language.var» (leaf 0))))
            («Translation.b1T»
              («Translation.b0T» («Language.mFst» («Language.var» (leaf 0)))))))
        («Language.var» (leaf 0))))

def «Translation.lbAdd» :=
  «Translation.mkDefn»
    (leaf 0)
    («Theory.l2» «Translation.bitsTy» «Translation.bitsTy»)
    «Translation.bitsTy»
    («Language.app»
      («Language.mSnd»
        («Language.mListRec»
          («Language.mPair»
            «Translation.bnilT»
            («Language.mLam» «Translation.bitsTy» («Language.var» (leaf 0))))
          («Language.mPair»
            («Translation.consT»
              «Translation.bitTy»
              («Language.var» (leaf 1))
              («Language.mFst» («Language.var» (leaf 0))))
            («Language.mLam»
              «Translation.bitsTy»
              («Translation.lcaseB»
                «Translation.bitTy»
                «Translation.bitsTy»
                («Language.var» (leaf 0))
                («Translation.consT»
                  «Translation.bitTy»
                  («Language.var» (leaf 2))
                  («Language.mFst» («Language.var» (leaf 1))))
                («Language.mLam»
                  «Translation.bitTy»
                  («Language.mLam»
                    «Translation.bitsTy»
                    («Translation.consT»
                      «Translation.bitTy»
                      («Translation.digitT»
                        («Language.var» (leaf 1))
                        («Language.var» (leaf 4)))
                      («Language.app»
                        («Language.mLam»
                          «Translation.bitsTy»
                          («Translation.ifBit»
                            «Translation.bitsTy»
                            («Language.var» (leaf 2))
                            («Translation.ifBit»
                              «Translation.bitsTy»
                              («Language.var» (leaf 5))
                              («Language.var» (leaf 0))
                              («Translation.call»
                                (leaf 11)
                                ([] : List T)
                                («Prelude.single» («Language.var» (leaf 0)))))
                            («Translation.call»
                              (leaf 11)
                              ([] : List T)
                              («Prelude.single» («Language.var» (leaf 0))))))
                        («Language.app»
                          («Language.mSnd» («Language.var» (leaf 3)))
                          («Language.var» (leaf 0))))))))))
          («Language.var» (leaf 0))))
      («Language.var» (leaf 1)))

def «Translation.lbCmp» :=
  «Translation.mkDefn»
    (leaf 0)
    («Theory.l2» «Translation.bitsTy» «Translation.bitsTy»)
    «Translation.ordTy»
    («Language.app»
      («Language.mListRec»
        («Language.mLam»
          «Translation.bitsTy»
          («Translation.condT»
            «Translation.ordTy»
            («Language.var» (leaf 0))
            «Translation.gtO»
            «Translation.eqO»))
        («Language.mLam»
          «Translation.bitsTy»
          («Translation.lcaseB»
            «Translation.bitTy»
            «Translation.ordTy»
            («Language.var» (leaf 0))
            «Translation.ltO»
            («Language.mLam»
              «Translation.bitTy»
              («Language.mLam»
                «Translation.bitsTy»
                («Translation.ifOrd»
                  «Translation.ordTy»
                  («Language.app» («Language.var» (leaf 3)) («Language.var» (leaf 0)))
                  «Translation.ltO»
                  («Translation.bitOrdT»
                    («Language.var» (leaf 1))
                    («Language.var» (leaf 4)))
                  «Translation.gtO»)))))
        («Language.var» (leaf 0)))
      («Language.var» (leaf 1)))

def «Translation.lbLtB» :=
  «Translation.mkDefn»
    (leaf 0)
    («Theory.l2» «Translation.bitsTy» «Translation.bitsTy»)
    «Translation.bitsTy»
    («Translation.ifOrd»
      «Translation.bitsTy»
      («Translation.cmpT»
        («Language.var» (leaf 1))
        («Language.var» (leaf 0)))
      «Translation.trueT»
      «Translation.bnilT»
      «Translation.bnilT»)

def «Translation.lbEqB» :=
  «Translation.mkDefn»
    (leaf 0)
    («Theory.l2» «Translation.bitsTy» «Translation.bitsTy»)
    «Translation.bitsTy»
    («Language.app»
      («Language.mListRec»
        («Language.mLam»
          «Translation.bitsTy»
          («Translation.call»
            (leaf 10)
            («Prelude.single» «Translation.bitTy»)
            («Prelude.single» («Language.var» (leaf 0)))))
        («Language.mLam»
          «Translation.bitsTy»
          («Translation.lcaseB»
            «Translation.bitTy»
            «Translation.bitsTy»
            («Language.var» (leaf 0))
            «Translation.bnilT»
            («Language.mLam»
              «Translation.bitTy»
              («Language.mLam»
                «Translation.bitsTy»
                («Translation.ifBit»
                  «Translation.bitsTy»
                  («Language.var» (leaf 1))
                  («Translation.ifBit»
                    «Translation.bitsTy»
                    («Language.var» (leaf 4))
                    («Language.app» («Language.var» (leaf 3)) («Language.var» (leaf 0)))
                    «Translation.bnilT»)
                  («Translation.ifBit»
                    «Translation.bitsTy»
                    («Language.var» (leaf 4))
                    «Translation.bnilT»
                    («Language.app»
                      («Language.var» (leaf 3))
                      («Language.var» (leaf 0)))))))))
        («Language.var» (leaf 0)))
      («Language.var» (leaf 1)))

def «Translation.lbSubE» :=
  «Translation.mkDefn»
    (leaf 0)
    («Theory.l2» «Translation.bitsTy» «Translation.bitsTy»)
    «Translation.bitsTy»
    («Language.app»
      («Language.mListRec»
        («Language.mLam» «Translation.bitsTy» («Language.var» (leaf 0)))
        («Language.mLam»
          «Translation.bitsTy»
          («Translation.lcaseB»
            «Translation.bitTy»
            «Translation.bitsTy»
            («Language.var» (leaf 0))
            «Translation.bnilT»
            («Language.mLam»
              «Translation.bitTy»
              («Language.mLam»
                «Translation.bitsTy»
                («Language.app»
                  («Language.mLam»
                    «Translation.bitsTy»
                    («Translation.ifBit»
                      «Translation.bitsTy»
                      («Language.var» (leaf 2))
                      («Translation.ifBit»
                        «Translation.bitsTy»
                        («Language.var» (leaf 5))
                        («Translation.call»
                          (leaf 14)
                          ([] : List T)
                          («Prelude.single» («Language.var» (leaf 0))))
                        («Translation.b0T»
                          («Translation.call»
                            (leaf 13)
                            ([] : List T)
                            («Prelude.single» («Language.var» (leaf 0))))))
                      («Translation.ifBit»
                        «Translation.bitsTy»
                        («Language.var» (leaf 5))
                        («Translation.b0T» («Language.var» (leaf 0)))
                        («Translation.call»
                          (leaf 14)
                          ([] : List T)
                          («Prelude.single» («Language.var» (leaf 0)))))))
                  («Language.app»
                    («Language.var» (leaf 3))
                    («Language.var» (leaf 0))))))))
        («Language.var» (leaf 0)))
      («Language.var» (leaf 1)))

def «Translation.lbSub» :=
  «Translation.mkDefn»
    (leaf 0)
    («Theory.l2» «Translation.bitsTy» «Translation.bitsTy»)
    «Translation.bitsTy»
    («Translation.condT»
      «Translation.bitsTy»
      («Translation.call»
        (leaf 17)
        ([] : List T)
        («Theory.l2» («Language.var» (leaf 1)) («Language.var» (leaf 0))))
      «Translation.bnilT»
      («Translation.call»
        (leaf 19)
        ([] : List T)
        («Theory.l2» («Language.var» (leaf 1)) («Language.var» (leaf 0)))))

def «Translation.lbMul» :=
  «Translation.mkDefn»
    (leaf 0)
    («Theory.l2» «Translation.bitsTy» «Translation.bitsTy»)
    «Translation.bitsTy»
    («Language.app»
      («Language.mListRec»
        («Language.mLam» «Translation.bitsTy» «Translation.bnilT»)
        («Language.mLam»
          «Translation.bitsTy»
          («Translation.call»
            (leaf 15)
            ([] : List T)
            («Theory.l2»
              («Translation.call»
                (leaf 14)
                ([] : List T)
                («Prelude.single»
                  («Language.app» («Language.var» (leaf 1)) («Language.var» (leaf 0)))))
              («Translation.ifBit»
                «Translation.bitsTy»
                («Language.var» (leaf 2))
                («Language.var» (leaf 0))
                («Translation.call»
                  (leaf 14)
                  ([] : List T)
                  («Prelude.single» («Language.var» (leaf 0))))))))
        («Language.var» (leaf 0)))
      («Language.var» (leaf 1)))

def «Translation.lbDivMod» :=
  let x0 : T := «Theory.prod» «Translation.bitsTy» «Translation.bitsTy»;
  «Translation.mkDefn»
    (leaf 0)
    («Theory.l2» «Translation.bitsTy» «Translation.bitsTy»)
    x0
    («Translation.condT»
      x0
      («Language.var» (leaf 0))
      («Language.app»
        («Language.mListRec»
          («Language.mLam»
            «Translation.bitsTy»
            («Language.mPair» «Translation.bnilT» «Translation.bnilT»))
          («Language.mLam»
            «Translation.bitsTy»
            («Language.app»
              («Language.mLam»
                x0
                («Language.app»
                  («Language.mLam»
                    «Translation.bitsTy»
                    («Translation.ifOrd»
                      x0
                      («Translation.cmpT»
                        («Language.var» (leaf 0))
                        («Language.var» (leaf 2)))
                      («Language.mPair»
                        («Translation.call»
                          (leaf 14)
                          ([] : List T)
                          («Prelude.single» («Language.mFst» («Language.var» (leaf 1)))))
                        («Language.var» (leaf 0)))
                      («Language.mPair»
                        («Translation.b0T» («Language.mFst» («Language.var» (leaf 1))))
                        «Translation.bnilT»)
                      («Translation.ifOrd»
                        x0
                        («Translation.cmpT»
                          («Language.var» (leaf 0))
                          («Translation.call»
                            (leaf 14)
                            ([] : List T)
                            («Prelude.single» («Language.var» (leaf 2)))))
                        («Language.mPair»
                          («Translation.b0T» («Language.mFst» («Language.var» (leaf 1))))
                          («Translation.call»
                            (leaf 19)
                            ([] : List T)
                            («Theory.l2» («Language.var» (leaf 0)) («Language.var» (leaf 2)))))
                        («Language.mPair»
                          («Translation.b1T» («Language.mFst» («Language.var» (leaf 1))))
                          «Translation.bnilT»)
                        («Language.mPair»
                          («Translation.b1T» («Language.mFst» («Language.var» (leaf 1))))
                          «Translation.bnilT»))))
                  («Translation.consT»
                    «Translation.bitTy»
                    («Language.var» (leaf 3))
                    («Language.mSnd» («Language.var» (leaf 0))))))
              («Language.app» («Language.var» (leaf 1)) («Language.var» (leaf 0)))))
          («Language.var» (leaf 1)))
        («Language.var» (leaf 0)))
      («Language.mPair» «Translation.bnilT» («Language.var» (leaf 1))))

def «Translation.lbLog2» :=
  let x0 : T := «Theory.prod» «Translation.bitsTy» «Translation.bitsTy»;
  «Translation.mkDefn»
    (leaf 0)
    («Prelude.single» «Translation.bitsTy»)
    «Translation.bitsTy»
    («Language.app»
      («Language.mLam»
        x0
        («Translation.condT»
          «Translation.bitsTy»
          («Language.mSnd» («Language.var» (leaf 0)))
          («Language.mFst» («Language.var» (leaf 0)))
          («Translation.call»
            (leaf 13)
            ([] : List T)
            («Prelude.single» («Language.mFst» («Language.var» (leaf 0)))))))
      («Language.mListRec»
        («Language.mPair» «Translation.bnilT» «Translation.bnilT»)
        («Language.app»
          («Language.mLam»
            x0
            («Language.mPair»
              («Translation.call»
                (leaf 11)
                ([] : List T)
                («Prelude.single» («Language.mFst» («Language.var» (leaf 0)))))
              («Translation.ifBit»
                «Translation.bitsTy»
                («Language.var» (leaf 2))
                («Language.mSnd» («Language.var» (leaf 0)))
                «Translation.trueT»)))
          («Language.var» (leaf 0)))
        («Language.var» (leaf 0))))

def «Translation.lbIter» :=
  let x0 : T := «Theory.exp» «Translation.X0» «Translation.X0»;
  «Translation.mkDefn»
    (leaf 1)
    («Theory.l3» «Translation.bitsTy» x0 «Translation.X0»)
    «Translation.X0»
    («Language.app»
      («Language.app»
        («Language.mListRec»
          («Language.mLam»
            x0
            («Language.mLam» «Translation.X0» («Language.var» (leaf 0))))
          («Language.mLam»
            x0
            («Language.mLam»
              «Translation.X0»
              («Language.app»
                («Language.mLam»
                  «Translation.X0»
                  («Translation.ifBit»
                    «Translation.X0»
                    («Language.var» (leaf 4))
                    («Language.app» («Language.var» (leaf 2)) («Language.var» (leaf 0)))
                    («Language.app»
                      («Language.var» (leaf 2))
                      («Language.app»
                        («Language.var» (leaf 2))
                        («Language.var» (leaf 0))))))
                («Language.app»
                  («Language.app» («Language.var» (leaf 2)) («Language.var» (leaf 1)))
                  («Language.app»
                    («Language.app» («Language.var» (leaf 2)) («Language.var» (leaf 1)))
                    («Language.var» (leaf 0)))))))
          («Language.var» (leaf 2)))
        («Language.var» (leaf 1)))
      («Language.var» (leaf 0)))

def «Translation.lbMapApp» :=
  «Translation.mkDefn»
    (leaf 2)
    («Theory.l2»
      («Theory.list» («Theory.exp» «Translation.X0» «Translation.X1»))
      «Translation.X0»)
    («Theory.list» «Translation.X1»)
    («Language.app»
      («Language.mListRec»
        («Language.mLam»
          «Translation.X0»
          («Translation.nilT» «Translation.X1»))
        («Language.mLam»
          «Translation.X0»
          («Translation.consT»
            «Translation.X1»
            («Language.app» («Language.var» (leaf 2)) («Language.var» (leaf 0)))
            («Language.app» («Language.var» (leaf 1)) («Language.var» (leaf 0)))))
        («Language.var» (leaf 1)))
      («Language.var» (leaf 0)))

def «Translation.lbAnd» :=
  «Translation.mkDefn»
    (leaf 0)
    («Theory.l2» «Translation.bitsTy» «Translation.bitsTy»)
    «Translation.bitsTy»
    («Translation.condT»
      «Translation.bitsTy»
      («Language.var» (leaf 1))
      («Language.var» (leaf 0))
      «Translation.bnilT»)

def «Translation.lbAllZip» :=
  «Translation.mkDefn»
    (leaf 0)
    («Theory.l2»
      («Theory.list»
        («Theory.exp» «Translation.treeTy» «Translation.bitsTy»))
      («Theory.list» «Translation.treeTy»))
    «Translation.bitsTy»
    («Language.app»
      («Language.mListRec»
        («Language.mLam»
          («Theory.list» «Translation.treeTy»)
          («Translation.call»
            (leaf 10)
            («Prelude.single» «Translation.treeTy»)
            («Prelude.single» («Language.var» (leaf 0)))))
        («Language.mLam»
          («Theory.list» «Translation.treeTy»)
          («Translation.condT»
            «Translation.bitsTy»
            («Translation.call»
              (leaf 10)
              («Prelude.single» «Translation.treeTy»)
              («Prelude.single» («Language.var» (leaf 0))))
            «Translation.bnilT»
            («Translation.call»
              (leaf 26)
              ([] : List T)
              («Theory.l2»
                («Language.app»
                  («Language.var» (leaf 2))
                  («Translation.call»
                    (leaf 8)
                    («Prelude.single» «Translation.treeTy»)
                    («Theory.l2»
                      («Translation.leafT» «Translation.bnilT»)
                      («Language.var» (leaf 0)))))
                («Language.app»
                  («Language.var» (leaf 1))
                  («Translation.call»
                    (leaf 7)
                    («Prelude.single» «Translation.treeTy»)
                    («Prelude.single» («Language.var» (leaf 0)))))))))
        («Language.var» (leaf 1)))
      («Language.var» (leaf 0)))

def «Translation.lbEqual» :=
  «Translation.mkDefn»
    (leaf 0)
    («Theory.l2» «Translation.treeTy» «Translation.treeTy»)
    «Translation.bitsTy»
    («Language.app»
      («Language.mRoseRec»
        («Theory.exp» «Translation.treeTy» «Translation.bitsTy»)
        («Language.mLam»
          «Translation.treeTy»
          («Translation.call»
            (leaf 26)
            ([] : List T)
            («Theory.l2»
              («Translation.call»
                (leaf 18)
                ([] : List T)
                («Theory.l2»
                  («Language.mFst» («Language.var» (leaf 1)))
                  («Translation.call»
                    (leaf 3)
                    ([] : List T)
                    («Prelude.single» («Language.var» (leaf 0))))))
              («Translation.call»
                (leaf 27)
                ([] : List T)
                («Theory.l2»
                  («Language.mSnd» («Language.var» (leaf 1)))
                  («Translation.call»
                    (leaf 5)
                    ([] : List T)
                    («Prelude.single» («Language.var» (leaf 0)))))))))
        («Language.var» (leaf 1)))
      («Language.var» (leaf 0)))

def «Translation.lib» :=
  («Translation.lbBnil» ::
    («Translation.lbB0» ::
      («Translation.lbB1» ::
        («Translation.lbLab» ::
          («Translation.lbUnnode» ::
            («Translation.lbChildren» ::
              («Translation.lbCond» ::
                («Translation.lbTail» ::
                  («Translation.lbHeadD» ::
                    («Translation.lbLcase» ::
                      («Translation.lbIsNil» ::
                        («Translation.lbSucc» ::
                          («Translation.lbLength» ::
                            («Translation.lbPred» ::
                              («Translation.lbDbl» ::
                                («Translation.lbAdd» ::
                                  («Translation.lbCmp» ::
                                    («Translation.lbLtB» ::
                                      («Translation.lbEqB» ::
                                        («Translation.lbSubE» ::
                                          («Translation.lbSub» ::
                                            («Translation.lbMul» ::
                                              («Translation.lbDivMod» ::
                                                («Translation.lbLog2» ::
                                                  («Translation.lbIter» ::
                                                    («Translation.lbMapApp» ::
                                                      («Translation.lbAnd» ::
                                                        («Translation.lbAllZip» ::
                                                          («Translation.lbEqual» ::
                                                            ([] : List T))))))))))))))))))))))))))))))

def «Translation.foldT» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «Theory.exp»
                     «Translation.treeTy»
                     («Theory.exp» («Theory.list» x0) x0);
                   «Language.mLam»
                     x1
                     («Language.mLam»
                       «Translation.treeTy»
                       («Language.app»
                         («Language.mRoseRec»
                           («Theory.exp» x1 x0)
                           («Language.mLam»
                             x1
                             («Language.app»
                               («Language.app»
                                 («Language.var» (leaf 0))
                                 («Translation.leafT» («Language.mFst» («Language.var» (leaf 1)))))
                               («Translation.call»
                                 (leaf 25)
                                 («Theory.l2» x1 x0)
                                 («Theory.l2»
                                   («Language.mSnd» («Language.var» (leaf 1)))
                                   («Language.var» (leaf 0))))))
                           («Language.var» (leaf 0)))
                         («Language.var» (leaf 1)))));
    x1

def «Translation.fstsT» :=
  fun (x0 : T) =>
    let x1 : T := «Language.mListRec»
      («Translation.nilT» «Translation.treeTy»)
      («Translation.consT»
        «Translation.treeTy»
        («Language.mFst» («Language.var» (leaf 1)))
        («Language.var» (leaf 0)))
      x0;
    x1

def «Translation.sndsT» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Language.mListRec»
      («Translation.nilT» x0)
      («Translation.consT»
        x0
        («Language.mSnd» («Language.var» (leaf 1)))
        («Language.var» (leaf 0)))
      x1;
    x2

def «Translation.paraT» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «Theory.exp»
                     «Translation.treeTy»
                     («Theory.exp» («Theory.list» x0) x0);
                   let x2 : T := «Theory.prod» «Translation.treeTy» x0;
                   «Language.mLam»
                     x1
                     («Language.mLam»
                       «Translation.treeTy»
                       («Language.mSnd»
                         («Language.app»
                           («Language.mRoseRec»
                             («Theory.exp» x1 x2)
                             («Language.mLam»
                               x1
                               («Language.app»
                                 («Language.mLam»
                                   («Theory.list» x2)
                                   («Language.app»
                                     («Language.mLam»
                                       «Translation.treeTy»
                                       («Language.mPair»
                                         («Language.var» (leaf 0))
                                         («Language.app»
                                           («Language.app»
                                             («Language.var» (leaf 2))
                                             («Language.var» (leaf 0)))
                                           («Translation.sndsT» x0 («Language.var» (leaf 1))))))
                                     («Translation.nodeT»
                                       («Language.mPair»
                                         («Language.mFst» («Language.var» (leaf 2)))
                                         («Translation.fstsT» («Language.var» (leaf 0)))))))
                                 («Translation.call»
                                   (leaf 25)
                                   («Theory.l2» x1 x2)
                                   («Theory.l2»
                                     («Language.mSnd» («Language.var» (leaf 1)))
                                     («Language.var» (leaf 0))))))
                             («Language.var» (leaf 0)))
                           («Language.var» (leaf 1))))));
    x1

def «Translation.iterT» :=
  fun (x0 : T) =>
    let x1 : T := «Language.mLam»
      («Theory.exp» x0 x0)
      («Language.mLam»
        x0
        («Language.mLam»
          «Translation.treeTy»
          («Translation.call»
            (leaf 24)
            («Prelude.single» x0)
            («Theory.l3»
              («Translation.call»
                (leaf 3)
                ([] : List T)
                («Prelude.single» («Language.var» (leaf 0))))
              («Language.var» (leaf 2))
              («Language.var» (leaf 1))))));
    x1

def «Translation.foldrT» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := «Theory.prod» («Theory.exp» x0 («Theory.exp» x1 x1)) x1;
                   «Language.mLam»
                     («Theory.exp» x0 («Theory.exp» x1 x1))
                     («Language.mLam»
                       x1
                       («Language.mLam»
                         («Theory.list» x0)
                         («Language.app»
                           («Language.mListRec»
                             («Language.mLam» x2 («Language.mSnd» («Language.var» (leaf 0))))
                             («Language.mLam»
                               x2
                               («Language.app»
                                 («Language.app»
                                   («Language.mFst» («Language.var» (leaf 0)))
                                   («Language.var» (leaf 2)))
                                 («Language.app»
                                   («Language.var» (leaf 1))
                                   («Language.var» (leaf 0)))))
                             («Language.var» (leaf 0)))
                           («Language.mPair»
                             («Language.var» (leaf 2))
                             («Language.var» (leaf 1)))))));
    x2

def «Translation.lcaseT» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Language.mLam»
      («Theory.list» x0)
      («Language.mLam»
        x1
        («Language.mLam»
          («Theory.exp» x0 («Theory.exp» («Theory.list» x0) x1))
          («Translation.lcaseB»
            x0
            x1
            («Language.var» (leaf 2))
            («Language.var» (leaf 1))
            («Language.var» (leaf 0)))));
    x2

def «Translation.labT» :=
  fun (x0 : T) =>
    let x1 : T := «Translation.call»
      (leaf 3)
      ([] : List T)
      («Prelude.single» x0);
    x1

def «Translation.binT» :=
  fun (x0 : T → T → T) =>
    let x1 : T := «Language.mLam»
      «Translation.treeTy»
      («Language.mLam»
        «Translation.treeTy»
        («Translation.leafT»
          (x0
            («Translation.labT» («Language.var» (leaf 1)))
            («Translation.labT» («Language.var» (leaf 0))))));
    x1

def «Translation.primT» :=
  fun (x0 : T) =>
    let x1 : T := (if (Const.eq x0 (leaf 0)).label ≠ 0 then
      «Prelude.some»
        («Language.mLam»
          «Translation.treeTy»
          («Translation.leafT» («Translation.labT» («Language.var» (leaf 0)))))
    else
      if (Const.eq x0 (leaf 1)).label ≠ 0 then
        «Prelude.some»
          («Language.mLam»
            «Translation.treeTy»
            («Translation.leafT»
              («Translation.call»
                (leaf 12)
                («Prelude.single» «Translation.treeTy»)
                («Prelude.single»
                  («Translation.call»
                    (leaf 5)
                    ([] : List T)
                    («Prelude.single» («Language.var» (leaf 0))))))))
      else
        if (Const.eq x0 (leaf 2)).label ≠ 0 then
          «Prelude.some»
            («Language.mLam»
              «Translation.treeTy»
              («Language.mLam»
                «Translation.treeTy»
                («Translation.call»
                  (leaf 8)
                  («Prelude.single» «Translation.treeTy»)
                  («Theory.l2»
                    («Translation.leafT» «Translation.bnilT»)
                    («Translation.call»
                      (leaf 24)
                      («Prelude.single» («Theory.list» «Translation.treeTy»))
                      («Theory.l3»
                        («Translation.labT» («Language.var» (leaf 0)))
                        («Language.mLam»
                          («Theory.list» «Translation.treeTy»)
                          («Translation.call»
                            (leaf 7)
                            («Prelude.single» «Translation.treeTy»)
                            («Prelude.single» («Language.var» (leaf 0)))))
                        («Translation.call»
                          (leaf 5)
                          ([] : List T)
                          («Prelude.single» («Language.var» (leaf 1))))))))))
        else
          if (Const.eq x0 (leaf 3)).label ≠ 0 then
            «Prelude.some»
              («Language.mLam»
                «Translation.treeTy»
                («Language.mLam»
                  («Theory.list» «Translation.treeTy»)
                  («Translation.nodeT»
                    («Language.mPair»
                      («Translation.labT» («Language.var» (leaf 1)))
                      («Language.var» (leaf 0))))))
          else
            if (Const.eq x0 (leaf 4)).label ≠ 0 then
              «Prelude.some»
                («Language.mLam»
                  «Translation.treeTy»
                  («Translation.call»
                    (leaf 5)
                    ([] : List T)
                    («Prelude.single» («Language.var» (leaf 0)))))
            else
              if (Const.eq x0 (leaf 5)).label ≠ 0 then
                «Prelude.some»
                  («Translation.binT»
                    (fun (x1 : T) (x2 : T) =>
                      «Translation.call» (leaf 15) ([] : List T) («Theory.l2» x1 x2)))
              else
                if (Const.eq x0 (leaf 6)).label ≠ 0 then
                  «Prelude.some»
                    («Translation.binT»
                      (fun (x1 : T) (x2 : T) =>
                        «Translation.call» (leaf 20) ([] : List T) («Theory.l2» x1 x2)))
                else
                  if (Const.eq x0 (leaf 7)).label ≠ 0 then
                    «Prelude.some»
                      («Translation.binT»
                        (fun (x1 : T) (x2 : T) =>
                          «Translation.call» (leaf 21) ([] : List T) («Theory.l2» x1 x2)))
                  else
                    if (Const.eq x0 (leaf 8)).label ≠ 0 then
                      «Prelude.some»
                        («Translation.binT»
                          (fun (x1 : T) (x2 : T) =>
                            «Language.mFst»
                              («Translation.call» (leaf 22) ([] : List T) («Theory.l2» x1 x2))))
                    else
                      if (Const.eq x0 (leaf 9)).label ≠ 0 then
                        «Prelude.some»
                          («Translation.binT»
                            (fun (x1 : T) (x2 : T) =>
                              «Language.mSnd»
                                («Translation.call» (leaf 22) ([] : List T) («Theory.l2» x1 x2))))
                      else
                        if (Const.eq x0 (leaf 10)).label ≠ 0 then
                          «Prelude.some»
                            («Translation.binT»
                              (fun (x1 : T) (x2 : T) =>
                                «Translation.call» (leaf 18) ([] : List T) («Theory.l2» x1 x2)))
                        else
                          if (Const.eq x0 (leaf 11)).label ≠ 0 then
                            «Prelude.some»
                              («Translation.binT»
                                (fun (x1 : T) (x2 : T) =>
                                  «Translation.call» (leaf 17) ([] : List T) («Theory.l2» x1 x2)))
                          else
                            if (Const.eq x0 (leaf 12)).label ≠ 0 then
                              «Prelude.some»
                                («Language.mLam»
                                  «Translation.treeTy»
                                  («Language.mLam»
                                    «Translation.treeTy»
                                    («Translation.leafT»
                                      («Translation.call»
                                        (leaf 28)
                                        ([] : List T)
                                        («Theory.l2»
                                          («Language.var» (leaf 1))
                                          («Language.var» (leaf 0)))))))
                            else
                              if (Const.eq x0 (leaf 13)).label ≠ 0 then
                                «Prelude.some»
                                  («Language.mLam»
                                    «Translation.treeTy»
                                    («Translation.leafT»
                                      («Translation.call»
                                        (leaf 23)
                                        ([] : List T)
                                        («Prelude.single»
                                          («Translation.labT» («Language.var» (leaf 0)))))))
                              else
                                «Prelude.none»);
    x1

def «Translation.kArrowParts» :=
  fun (x0 : T) =>
    let x1 : T := (if («Prelude.and»
      (Const.eq (Const.label x0) (leaf 3))
      (Const.eq (Const.arity x0) (leaf 2))).label ≠ 0 then
      «Language/OTPair.just»
        («Language.pr» (Const.child x0 (leaf 0)) (Const.child x0 (leaf 1)))
    else
      «Language/OTPair.nothing»);
    x1

def «Translation.kProdParts» :=
  fun (x0 : T) =>
    let x1 : T := (if («Prelude.and»
      (Const.eq (Const.label x0) (leaf 2))
      (Const.eq (Const.arity x0) (leaf 2))).label ≠ 0 then
      «Language/OTPair.just»
        («Language.pr» (Const.child x0 (leaf 0)) (Const.child x0 (leaf 1)))
    else
      «Language/OTPair.nothing»);
    x1

def «Translation.kListPart» :=
  fun (x0 : T) =>
    let x1 : T := (if («Prelude.and»
      (Const.eq (Const.label x0) (leaf 4))
      (Const.eq (Const.arity x0) (leaf 1))).label ≠ 0 then
      «Prelude.some» (Const.child x0 (leaf 0))
    else
      «Prelude.none»);
    x1

def «Translation/TrFs.tail» :=
  fun (x0 : List (List T → List T → T)) =>
    Const.lcase
      (α := List T → List T → T)
      (β := List (List T → List T → T))
      x0
      ([] : List (List T → List T → T))
      (fun (_ : List T → List T → T) (x2 : List (List T → List T → T)) =>
        x2)

def «Translation.trAt» :=
  fun (x0 : List (List T → List T → T)) (x1 : T) =>
    let x2 : List T →
      List T →
        T := Const.lcase
      (α := List T → List T → T)
      (β := List T → List T → T)
      (Const.iter
        (α := List (List T → List T → T))
        «Translation/TrFs.tail»
        x0
        x1)
      (fun (_ : List T) (_ : List T) => «Language/OTPair.nothing»)
      (fun (x2 : List T → List T → T) (_ : List (List T → List T → T)) =>
        x2);
    x2

def «Translation.bindP» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x1 x3
                   else
                     «Language/OTPair.nothing»);
    x2

def «Translation.bindTy» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (if («Prelude.isSome» x0).label ≠ 0 then
      x1 («Prelude.get» x0)
    else
      «Language/OTPair.nothing»);
    x2

def «Translation.mapTy» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (if («Prelude.isSome» x1).label ≠ 0 then
      «Language/OTPair.just» (x0 («Prelude.get» x1))
    else
      «Language/OTPair.nothing»);
    x2

def «Translation.termStep» :=
  fun (x0 : T) (x1 : List (List T → List T → T)) =>
    let x2 : List T →
      List T →
        T := (fun (x2 : List T) (x3 : List T) =>
      let x4 : T := Const.label x0;
      let x5 : T := Const.arity x0;
      let x6 : T := Const.child x0 (leaf 0);
      let x7 : T := Const.child x0 (leaf 1);
      if (Const.eq x4 (leaf 8)).label ≠ 0 then
        if (Const.eq x5 (leaf 1)).label ≠ 0 then
          «Translation.bindTy»
            («Prelude.nth» x3 (Const.label x6))
            (fun (x8 : T) =>
              «Language/OTPair.just»
                («Language.pr» x8 («Language.var» (Const.label x6))))
        else
          «Language/OTPair.nothing»
      else
        if (Const.eq x4 (leaf 9)).label ≠ 0 then
          if (Const.eq x5 (leaf 2)).label ≠ 0 then
            if («Check.isTy» x6).label ≠ 0 then
              «Translation.bindP»
                («Translation.trAt» x1 (leaf 1) x2 (x6 :: x3))
                (fun (x8 : T) =>
                  «Translation.mapTy»
                    (fun (x9 : T) =>
                      «Language.pr»
                        («Check.tyArrow» x6 («Language.p1» x8))
                        («Language.mLam» x9 («Language.p2» x8)))
                    («Translation.trTy» x6))
            else
              «Language/OTPair.nothing»
          else
            «Language/OTPair.nothing»
        else
          if (Const.eq x4 (leaf 10)).label ≠ 0 then
            if (Const.eq x5 (leaf 2)).label ≠ 0 then
              «Translation.bindP»
                («Translation.trAt» x1 (leaf 0) x2 x3)
                (fun (x8 : T) =>
                  «Translation.bindP»
                    («Translation.trAt» x1 (leaf 1) x2 x3)
                    (fun (x9 : T) =>
                      «Translation.bindP»
                        («Translation.kArrowParts» («Language.p1» x8))
                        (fun (x10 : T) =>
                          if (Const.equal («Language.p1» x9) («Language.p1» x10)).label ≠ 0 then
                            «Language/OTPair.just»
                              («Language.pr»
                                («Language.p2» x10)
                                («Language.app» («Language.p2» x8) («Language.p2» x9)))
                          else
                            «Language/OTPair.nothing»)))
            else
              «Language/OTPair.nothing»
          else
            if (Const.eq x4 (leaf 11)).label ≠ 0 then
              if (Const.eq x5 (leaf 0)).label ≠ 0 then
                «Language/OTPair.just» («Language.pr» (leaf 1) «Language.mStar»)
              else
                «Language/OTPair.nothing»
            else
              if (Const.eq x4 (leaf 12)).label ≠ 0 then
                if (Const.eq x5 (leaf 2)).label ≠ 0 then
                  «Translation.bindP»
                    («Translation.trAt» x1 (leaf 0) x2 x3)
                    (fun (x8 : T) =>
                      «Translation.bindP»
                        («Translation.trAt» x1 (leaf 1) x2 x3)
                        (fun (x9 : T) =>
                          «Language/OTPair.just»
                            («Language.pr»
                              («Reader.node2» (leaf 2) («Language.p1» x8) («Language.p1» x9))
                              («Language.mPair» («Language.p2» x8) («Language.p2» x9)))))
                else
                  «Language/OTPair.nothing»
              else
                if (Const.eq x4 (leaf 13)).label ≠ 0 then
                  if (Const.eq x5 (leaf 1)).label ≠ 0 then
                    «Translation.bindP»
                      («Translation.trAt» x1 (leaf 0) x2 x3)
                      (fun (x8 : T) =>
                        «Translation.bindP»
                          («Translation.kProdParts» («Language.p1» x8))
                          (fun (x9 : T) =>
                            «Language/OTPair.just»
                              («Language.pr»
                                («Language.p1» x9)
                                («Language.mFst» («Language.p2» x8)))))
                  else
                    «Language/OTPair.nothing»
                else
                  if (Const.eq x4 (leaf 14)).label ≠ 0 then
                    if (Const.eq x5 (leaf 1)).label ≠ 0 then
                      «Translation.bindP»
                        («Translation.trAt» x1 (leaf 0) x2 x3)
                        (fun (x8 : T) =>
                          «Translation.bindP»
                            («Translation.kProdParts» («Language.p1» x8))
                            (fun (x9 : T) =>
                              «Language/OTPair.just»
                                («Language.pr»
                                  («Language.p2» x9)
                                  («Language.mSnd» («Language.p2» x8)))))
                    else
                      «Language/OTPair.nothing»
                  else
                    if (Const.eq x4 (leaf 15)).label ≠ 0 then
                      if (Const.eq x5 (leaf 1)).label ≠ 0 then
                        «Language/OTPair.just»
                          («Language.pr» (leaf 0) («Translation.quoteT» x6))
                      else
                        «Language/OTPair.nothing»
                    else
                      if (Const.eq x4 (leaf 16)).label ≠ 0 then
                        if (Const.eq x5 (leaf 3)).label ≠ 0 then
                          «Translation.bindP»
                            («Translation.trAt» x1 (leaf 0) x2 x3)
                            (fun (x8 : T) =>
                              «Translation.bindP»
                                («Translation.trAt» x1 (leaf 1) x2 x3)
                                (fun (x9 : T) =>
                                  «Translation.bindP»
                                    («Translation.trAt» x1 (leaf 2) x2 x3)
                                    (fun (x10 : T) =>
                                      if («Prelude.and»
                                        (Const.equal («Language.p1» x8) (leaf 0))
                                        (Const.equal
                                          («Language.p1» x10)
                                          («Language.p1» x9))).label ≠ 0 then
                                        «Translation.mapTy»
                                          (fun (x11 : T) =>
                                            «Language.pr»
                                              («Language.p1» x9)
                                              («Translation.condT»
                                                x11
                                                («Translation.labT» («Language.p2» x8))
                                                («Language.p2» x9)
                                                («Language.p2» x10)))
                                          («Translation.trTy» («Language.p1» x9))
                                      else
                                        «Language/OTPair.nothing»)))
                        else
                          «Language/OTPair.nothing»
                      else
                        if (Const.eq x4 (leaf 17)).label ≠ 0 then
                          if (Const.eq x5 (leaf 1)).label ≠ 0 then
                            «Translation.mapTy»
                              (fun (x8 : T) =>
                                «Language.pr» («Check.foldTy» x6) («Translation.foldT» x8))
                              («Translation.trTy» x6)
                          else
                            «Language/OTPair.nothing»
                        else
                          if (Const.eq x4 (leaf 18)).label ≠ 0 then
                            if (Const.eq x5 (leaf 1)).label ≠ 0 then
                              «Translation.mapTy»
                                (fun (x8 : T) =>
                                  «Language.pr» («Check.iterTy» x6) («Translation.iterT» x8))
                                («Translation.trTy» x6)
                            else
                              «Language/OTPair.nothing»
                          else
                            if (Const.eq x4 (leaf 19)).label ≠ 0 then
                              if (Const.eq x5 (leaf 1)).label ≠ 0 then
                                «Translation.mapTy»
                                  (fun (x8 : T) =>
                                    «Language.pr» («Check.tyList» x6) («Translation.nilT» x8))
                                  («Translation.trTy» x6)
                              else
                                «Language/OTPair.nothing»
                            else
                              if (Const.eq x4 (leaf 20)).label ≠ 0 then
                                if (Const.eq x5 (leaf 2)).label ≠ 0 then
                                  «Translation.bindP»
                                    («Translation.trAt» x1 (leaf 0) x2 x3)
                                    (fun (x8 : T) =>
                                      «Translation.bindP»
                                        («Translation.trAt» x1 (leaf 1) x2 x3)
                                        (fun (x9 : T) =>
                                          «Translation.bindTy»
                                            («Translation.kListPart» («Language.p1» x9))
                                            (fun (x10 : T) =>
                                              if (Const.equal («Language.p1» x8) x10).label ≠ 0 then
                                                «Translation.mapTy»
                                                  (fun (x11 : T) =>
                                                    «Language.pr»
                                                      («Language.p1» x9)
                                                      («Translation.consT»
                                                        x11
                                                        («Language.p2» x8)
                                                        («Language.p2» x9)))
                                                  («Translation.trTy» x10)
                                              else
                                                «Language/OTPair.nothing»)))
                                else
                                  «Language/OTPair.nothing»
                              else
                                if (Const.eq x4 (leaf 21)).label ≠ 0 then
                                  if (Const.eq x5 (leaf 2)).label ≠ 0 then
                                    «Translation.bindTy»
                                      («Translation.trTy» x6)
                                      (fun (x8 : T) =>
                                        «Translation.mapTy»
                                          (fun (x9 : T) =>
                                            «Language.pr»
                                              («Check.foldrTy» x6 x7)
                                              («Translation.foldrT» x8 x9))
                                          («Translation.trTy» x7))
                                  else
                                    «Language/OTPair.nothing»
                                else
                                  if (Const.eq x4 (leaf 22)).label ≠ 0 then
                                    if (Const.eq x5 (leaf 1)).label ≠ 0 then
                                      «Translation.bindTy»
                                        («Prelude.nth» «Check.primTypes» (Const.label x6))
                                        (fun (x8 : T) =>
                                          «Translation.mapTy»
                                            (fun (x9 : T) => «Language.pr» x8 x9)
                                            («Translation.primT» (Const.label x6)))
                                    else
                                      «Language/OTPair.nothing»
                                  else
                                    if (Const.eq x4 (leaf 23)).label ≠ 0 then
                                      if (Const.eq x5 (leaf 1)).label ≠ 0 then
                                        «Translation.bindTy»
                                          («Prelude.nth» x2 (Const.label x6))
                                          (fun (x8 : T) =>
                                            «Language/OTPair.just»
                                              («Language.pr»
                                                x8
                                                («Translation.call»
                                                  (Const.add
                                                    («Translation/LDefnL.length» «Translation.lib»)
                                                    (Const.label x6))
                                                  ([] : List T)
                                                  ([] : List T))))
                                      else
                                        «Language/OTPair.nothing»
                                    else
                                      if (Const.eq x4 (leaf 24)).label ≠ 0 then
                                        if (Const.eq x5 (leaf 2)).label ≠ 0 then
                                          «Translation.bindTy»
                                            («Translation.trTy» x6)
                                            (fun (x8 : T) =>
                                              «Translation.mapTy»
                                                (fun (x9 : T) =>
                                                  «Language.pr»
                                                    («Check.lcaseTy» x6 x7)
                                                    («Translation.lcaseT» x8 x9))
                                                («Translation.trTy» x7))
                                        else
                                          «Language/OTPair.nothing»
                                      else
                                        if (Const.eq x4 (leaf 25)).label ≠ 0 then
                                          if (Const.eq x5 (leaf 1)).label ≠ 0 then
                                            «Translation.mapTy»
                                              (fun (x8 : T) =>
                                                «Language.pr»
                                                  («Check.foldTy» x6)
                                                  («Translation.paraT» x8))
                                              («Translation.trTy» x6)
                                          else
                                            «Language/OTPair.nothing»
                                        else
                                          «Language/OTPair.nothing»);
    x2

def «Translation.term» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.para
      (α := List T → List T → T)
      «Translation.termStep»
      x2
      x0
      x1;
    x3

def «Translation.ktys» := fun (x0 : List T) => Const.node (leaf 0) x0

def «Translation.ldefns» :=
  fun (x0 : List T) => Const.node (leaf 0) x0

def «Translation.trState» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Translation/OTrState.nothing» :=
  Const.node (leaf 0) ([] : List T)

def «Translation/OTrState.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Translation/OTrState.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let _ : T := Const.child x1 (leaf 0); leaf 1
                   else
                     leaf 0);
    x1

def «Translation/OTrState.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x3
                   else
                     x0);
    x2

def «Translation/OTrState.nthOf» :=
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
      «Translation/OTrState.nothing»
      (fun (x2 : T) (_ : List T) => «Translation/OTrState.just» x2);
    x2

def «Translation/OTrState.allJust» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x4 : T := Const.child x3 (leaf 0); ((x2).1, (x4 :: (x2).2))
        else
          (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Translation.stTypes» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let x4 : T := x2;
            let x5 : List
              T := Const.iter
              (α := List T)
              (fun (x5 : List T) =>
                Const.lcase
                  (α := T)
                  (β := List T)
                  x5
                  ([] : List T)
                  (fun (_ : T) (x7 : List T) => x7))
              (Const.children x4)
              (leaf 0);
            x5);
    x1

def «Translation.stDefns» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let x3 : T := Const.child x1 (leaf 1);
            let x4 : T := x3;
            let x5 : List
              T := Const.iter
              (α := List T)
              (fun (x5 : List T) =>
                Const.lcase
                  (α := T)
                  (β := List T)
                  x5
                  ([] : List T)
                  (fun (_ : T) (x7 : List T) => x7))
              (Const.children x4)
              (leaf 0);
            x5);
    x1

def «Translation.bindSS» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x1 x3
                   else
                     «Translation/OTrState.nothing»);
    x2

def «Translation.bindPS» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x1 x3
                   else
                     «Translation/OTrState.nothing»);
    x2

def «Translation.mapTS» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (if («Prelude.isSome» x1).label ≠ 0 then
      «Translation/OTrState.just» (x0 («Prelude.get» x1))
    else
      «Translation/OTrState.nothing»);
    x2

def «Translation.program» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x1 : T) (x2 : T) =>
        «Translation.bindSS»
          x2
          (fun (x3 : T) =>
            let x4 : List T := «Translation.stTypes» x3;
            let x5 : List T := «Translation.stDefns» x3;
            «Translation.bindPS»
              («Translation.term» x4 ([] : List T) x1)
              (fun (x6 : T) =>
                «Translation.mapTS»
                  (fun (x7 : T) =>
                    «Translation.trState»
                      («Translation.ktys»
                        («Translation/KTyL.append»
                          x4
                          («Translation/KTyL.single» («Language.p1» x6))))
                      («Translation.ldefns»
                        («Translation/LDefnL.append»
                          x5
                          («Translation/LDefnL.single»
                            («Translation.mkDefn»
                              (leaf 0)
                              ([] : List T)
                              x7
                              («Language.p2» x6))))))
                  («Translation.trTy» («Language.p1» x6)))))
      («Translation/OTrState.just»
        («Translation.trState»
          («Translation.ktys» ([] : List T))
          («Translation.ldefns» ([] : List T))))
      («Prelude.reverse» x0);
    x1

def «Translation.trGlobals» :=
  fun (x0 : List T) =>
    let x1 : T := «Language.globals»
      («Language.prims» «Translation.trPrims»)
      («Language.defs»
        («Translation/DefLang.map»
          «Language.defLang»
          («Translation/LDefnL.append» «Translation.lib» x0)))
      («Translation/OpSigs.length» «Theory.sig»);
    x1

def «Translation.geqn» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «Translation.gthm» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Translation.gthmCtx» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let x4 : T := x2;
            let x5 : List
              T := Const.iter
              (α := List T)
              (fun (x5 : List T) =>
                Const.lcase
                  (α := T)
                  (β := List T)
                  x5
                  ([] : List T)
                  (fun (_ : T) (x7 : List T) => x7))
              (Const.children x4)
              (leaf 0);
            x5);
    x1

def «Translation.gthmEqn» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1); x3);
    x1

def «Translation.geqnLhs» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2); x3);
    x1

def «Translation.geqnRhs» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let x4 : T := Const.child x1 (leaf 2); x4);
    x1

def «Translation/OObjs.nothing» := Const.node (leaf 0) ([] : List T)

def «Translation/OObjs.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Translation/OObjs.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let _ : T := Const.child x1 (leaf 0); leaf 1
                   else
                     leaf 0);
    x1

def «Translation/OObjs.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x3
                   else
                     x0);
    x2

def «Translation/OObjs.nthOf» :=
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
      «Translation/OObjs.nothing»
      (fun (x2 : T) (_ : List T) => «Translation/OObjs.just» x2);
    x2

def «Translation/OObjs.allJust» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x4 : T := Const.child x3 (leaf 0); ((x2).1, (x4 :: (x2).2))
        else
          (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Translation.allSomeObjs» :=
  fun (x0 : List T) =>
    let x1 : T := (if («Base.allT» «Prelude.isSome» x0).label ≠ 0 then
      «Translation/OObjs.just»
        («Language.objs» («Base.mapT» «Prelude.get» x0))
    else
      «Translation/OObjs.nothing»);
    x1

def «Translation.bindOH» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x1 x3
                   else
                     «Derivation/OThm.nothing»);
    x2

def «Translation.bindPH» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x1 x3
                   else
                     «Derivation/OThm.nothing»);
    x2

def «Translation.mapPH» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); «Derivation/OThm.just» (x0 x3)
                   else
                     «Derivation/OThm.nothing»);
    x2

def «Translation.thm» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (let x2 : List T := «Translation.gthmCtx» x1;
                   let x3 : T := «Translation.gthmEqn» x1;
                   «Translation.bindOH»
                     («Translation.allSomeObjs» («Base.mapT» «Translation.trTy» x2))
                     (fun (x4 : T) =>
                       «Translation.bindPH»
                         («Translation.term» x0 x2 («Translation.geqnLhs» x3))
                         (fun (x5 : T) =>
                           «Translation.mapPH»
                             (fun (x6 : T) =>
                               «Derivation.mkThm»
                                 (leaf 0)
                                 x4
                                 («Derivation.terms» ([] : List T))
                                 («Language.mEq» («Language.p2» x5) («Language.p2» x6)))
                             («Translation.term» x0 x2 («Translation.geqnRhs» x3)))));
    x2

end GebMirror.Metalogic

end
