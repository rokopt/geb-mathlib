module

public import GebMirror.Metalogic.Checker

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «bitTy» := «coprod» «one» «one»

def «bitsTy» := «list» «bitTy»

def «treeTy» := «lrose» «bitsTy»

def «ordTy» := «coprod» «one» «bitTy»

def «trTy» :=
  fun (x0 : T) =>
    let x1 : T := Const.fold
      (α := T)
      (fun (x1 : T) (x2 : List T) =>
        let x3 : T := «length» x2;
        if (Const.eq x3 (leaf 0)).label ≠ 0 then
          if (Const.eq x1 (leaf 0)).label ≠ 0 then
            «some» «treeTy»
          else
            if (Const.eq x1 (leaf 1)).label ≠ 0 then «some» «one» else «none»
        else
          if (Const.eq x3 (leaf 1)).label ≠ 0 then
            if (Const.eq x1 (leaf 4)).label ≠ 0 then
              «mapO» «list» («at» x2 (leaf 0))
            else
              «none»
          else
            if (Const.eq x3 (leaf 2)).label ≠ 0 then
              if (Const.eq x1 (leaf 2)).label ≠ 0 then
                «bindO»
                  («at» x2 (leaf 0))
                  (fun (x4 : T) => «mapO» («prod» x4) («at» x2 (leaf 1)))
              else
                if (Const.eq x1 (leaf 3)).label ≠ 0 then
                  «bindO»
                    («at» x2 (leaf 0))
                    (fun (x4 : T) => «mapO» («exp» x4) («at» x2 (leaf 1)))
                else
                  «none»
            else
              «none»)
      x0;
    x1

def «trPrims» :=
  «l6» «nilPrim» «consPrim» «lnodePrim» «inlPrim» «inrPrim» «casePrim»

def «nilT» :=
  fun (x0 : T) =>
    let x1 : T := «mArr» (leaf 0) («single» x0) «mStar»; x1

def «consT» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «mArr» (leaf 1) («single» x0) («mPair» x1 x2); x3

def «nodeT» :=
  fun (x0 : T) =>
    let x1 : T := «mArr» (leaf 2) («single» «bitsTy») x0; x1

def «bit0T» := «mArr» (leaf 3) («l2» «one» «one») «mStar»

def «bit1T» := «mArr» (leaf 4) («l2» «one» «one») «mStar»

def «ifBit» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «mApp»
      («mArr»
        (leaf 5)
        («l3» «one» «one» x0)
        («mPair» («mLam» «one» («weaken1» x2)) («mLam» «one» («weaken1» x3))))
      x1;
    x4

def «ltO» := «mArr» (leaf 3) («l2» «one» «bitTy») «mStar»

def «eqO» := «mArr» (leaf 4) («l2» «one» «bitTy») «bit0T»

def «gtO» := «mArr» (leaf 4) («l2» «one» «bitTy») «bit1T»

def «ifOrd» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := «mApp»
      («mArr»
        (leaf 5)
        («l3» «one» «bitTy» x0)
        («mPair»
          («mLam» «one» («weaken1» x2))
          («mLam»
            «bitTy»
            («ifBit» x0 («mVar» (leaf 0)) («weaken1» x3) («weaken1» x4)))))
      x1;
    x5

def «leafT» :=
  fun (x0 : T) =>
    let x1 : T := «nodeT» («mPair» x0 («nilT» «treeTy»)); x1

def «call» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) =>
    let x3 : T := «mDefn» x0 x1 («reverse» x2); x3

def «mkDefn» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T) =>
    let x4 : T := «ldefn» x0 (Const.node (leaf 0) («reverse» x1)) x2 x3;
    x4

def «bnilT» := «call» (leaf 0) ([] : List T) ([] : List T)

def «b0T» :=
  fun (x0 : T) =>
    let x1 : T := «call» (leaf 1) ([] : List T) («single» x0); x1

def «b1T» :=
  fun (x0 : T) =>
    let x1 : T := «call» (leaf 2) ([] : List T) («single» x0); x1

def «trueT» := «b0T» «bnilT»

def «trNumeral» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := Const.add x0 (leaf 1);
                   Const.foldr
                     (α := T)
                     (β := T)
                     (fun (x2 : T) (x3 : T) =>
                       if (x2).label ≠ 0 then «b1T» x3 else «b0T» x3)
                     «bnilT»
                     («digitsLsb» (leaf 2) x1 (Const.log2 x1)));
    x1

def «quoteT» :=
  fun (x0 : T) =>
    let x1 : T := Const.fold
      (α := T)
      (fun (x1 : T) (x2 : List T) =>
        «nodeT»
          («mPair»
            («trNumeral» x1)
            (Const.foldr
              (α := T)
              (β := T)
              («consT» «treeTy»)
              («nilT» «treeTy»)
              x2)))
      x0;
    x1

def «condT» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «call» (leaf 6) («single» x0) («l3» x1 x2 x3); x4

def «lcaseB» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := «call»
      (leaf 9)
      («l2» x0 x1)
      («l3» x2 («mLam» «one» («weaken1» x3)) x4);
    x5

def «cmpT» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «call» (leaf 16) ([] : List T) («l2» x0 x1); x2

def «digitT» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «ifBit»
      «bitTy»
      x0
      («ifBit» «bitTy» x1 «bit1T» «bit0T»)
      («ifBit» «bitTy» x1 «bit0T» «bit1T»);
    x2

def «bitOrdT» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «ifBit»
      «ordTy»
      x0
      («ifBit» «ordTy» x1 «eqO» «ltO»)
      («ifBit» «ordTy» x1 «gtO» «eqO»);
    x2

def «X0» := «x» (leaf 0)

def «X1» := «x» (leaf 1)

def «lbBnil» :=
  «mkDefn» (leaf 0) ([] : List T) «bitsTy» («nilT» «bitTy»)

def «lbB0» :=
  «mkDefn»
    (leaf 0)
    («single» «bitsTy»)
    «bitsTy»
    («consT» «bitTy» «bit0T» («mVar» (leaf 0)))

def «lbB1» :=
  «mkDefn»
    (leaf 0)
    («single» «bitsTy»)
    «bitsTy»
    («consT» «bitTy» «bit1T» («mVar» (leaf 0)))

def «lbLab» :=
  «mkDefn»
    (leaf 0)
    («single» «treeTy»)
    «bitsTy»
    («mRoseRec» «bitsTy» («mFst» («mVar» (leaf 0))) («mVar» (leaf 0)))

def «lbUnnode» :=
  «mkDefn»
    (leaf 0)
    («single» «treeTy»)
    («prod» «bitsTy» («list» «treeTy»))
    («mRoseRec»
      («prod» «bitsTy» («list» «treeTy»))
      («mPair»
        («mFst» («mVar» (leaf 0)))
        («mListRec»
          («nilT» «treeTy»)
          («consT» «treeTy» («nodeT» («mVar» (leaf 1))) («mVar» (leaf 0)))
          («mSnd» («mVar» (leaf 0)))))
      («mVar» (leaf 0)))

def «lbChildren» :=
  «mkDefn»
    (leaf 0)
    («single» «treeTy»)
    («list» «treeTy»)
    («mSnd» («call» (leaf 4) ([] : List T) («single» («mVar» (leaf 0)))))

def «lbCond» :=
  «mkDefn»
    (leaf 1)
    («l3» «bitsTy» «X0» «X0»)
    «X0»
    («mApp»
      («mApp»
        («mListRec»
          («mLam» «X0» («mLam» «X0» («mVar» (leaf 0))))
          («mLam» «X0» («mLam» «X0» («mVar» (leaf 1))))
          («mVar» (leaf 2)))
        («mVar» (leaf 1)))
      («mVar» (leaf 0)))

def «lbTail» :=
  «mkDefn»
    (leaf 1)
    («single» («list» «X0»))
    («list» «X0»)
    («mSnd»
      («mListRec»
        («mPair» («nilT» «X0») («nilT» «X0»))
        («mPair»
          («consT» «X0» («mVar» (leaf 1)) («mFst» («mVar» (leaf 0))))
          («mFst» («mVar» (leaf 0))))
        («mVar» (leaf 0))))

def «lbHeadD» :=
  «mkDefn»
    (leaf 1)
    («l2» «X0» («list» «X0»))
    «X0»
    («mApp»
      («mListRec»
        («mLam» «X0» («mVar» (leaf 0)))
        («mLam» «X0» («mVar» (leaf 2)))
        («mVar» (leaf 0)))
      («mVar» (leaf 1)))

def «lbLcase» :=
  let x0 : T := «exp» «X0» («exp» («list» «X0») «X1»);
  let x1 : T := «prod» («exp» «one» «X1») x0;
  let x2 : T := «mFst» («mApp» («mVar» (leaf 1)) («mVar» (leaf 0)));
  «mkDefn»
    (leaf 2)
    («l3» («list» «X0») («exp» «one» «X1») x0)
    «X1»
    («mSnd»
      («mApp»
        («mListRec»
          («mLam»
            x1
            («mPair» («nilT» «X0») («mApp» («mFst» («mVar» (leaf 0))) «mStar»)))
          («mLam»
            x1
            («mPair»
              («consT» «X0» («mVar» (leaf 2)) x2)
              («mApp» («mApp» («mSnd» («mVar» (leaf 0))) («mVar» (leaf 2))) x2)))
          («mVar» (leaf 2)))
        («mPair» («mVar» (leaf 1)) («mVar» (leaf 0)))))

def «lbIsNil» :=
  «mkDefn»
    (leaf 1)
    («single» («list» «X0»))
    «bitsTy»
    («mListRec» «trueT» «bnilT» («mVar» (leaf 0)))

def «lbSucc» :=
  «mkDefn»
    (leaf 0)
    («single» «bitsTy»)
    «bitsTy»
    («mSnd»
      («mListRec»
        («mPair» «bnilT» «trueT»)
        («mPair»
          («consT» «bitTy» («mVar» (leaf 1)) («mFst» («mVar» (leaf 0))))
          («ifBit»
            «bitsTy»
            («mVar» (leaf 1))
            («b1T» («mFst» («mVar» (leaf 0))))
            («b0T» («mSnd» («mVar» (leaf 0))))))
        («mVar» (leaf 0))))

def «lbLength» :=
  «mkDefn»
    (leaf 1)
    («single» («list» «X0»))
    «bitsTy»
    («mListRec»
      «bnilT»
      («call» (leaf 11) ([] : List T) («single» («mVar» (leaf 0))))
      («mVar» (leaf 0)))

def «lbPred» :=
  «mkDefn»
    (leaf 0)
    («single» «bitsTy»)
    «bitsTy»
    («mSnd»
      («mListRec»
        («mPair» «bnilT» «bnilT»)
        («mPair»
          («consT» «bitTy» («mVar» (leaf 1)) («mFst» («mVar» (leaf 0))))
          («ifBit»
            «bitsTy»
            («mVar» (leaf 1))
            («condT»
              «bitsTy»
              («mFst» («mVar» (leaf 0)))
              («b1T» («mSnd» («mVar» (leaf 0))))
              «bnilT»)
            («b0T» («mFst» («mVar» (leaf 0))))))
        («mVar» (leaf 0))))

def «lbDbl» :=
  «mkDefn»
    (leaf 0)
    («single» «bitsTy»)
    «bitsTy»
    («mSnd»
      («mListRec»
        («mPair» «bnilT» «bnilT»)
        («mPair»
          («consT» «bitTy» («mVar» (leaf 1)) («mFst» («mVar» (leaf 0))))
          («ifBit»
            «bitsTy»
            («mVar» (leaf 1))
            («b1T» («mSnd» («mVar» (leaf 0))))
            («b1T» («b0T» («mFst» («mVar» (leaf 0)))))))
        («mVar» (leaf 0))))

def «lbAdd» :=
  «mkDefn»
    (leaf 0)
    («l2» «bitsTy» «bitsTy»)
    «bitsTy»
    («mApp»
      («mSnd»
        («mListRec»
          («mPair» «bnilT» («mLam» «bitsTy» («mVar» (leaf 0))))
          («mPair»
            («consT» «bitTy» («mVar» (leaf 1)) («mFst» («mVar» (leaf 0))))
            («mLam»
              «bitsTy»
              («lcaseB»
                «bitTy»
                «bitsTy»
                («mVar» (leaf 0))
                («consT» «bitTy» («mVar» (leaf 2)) («mFst» («mVar» (leaf 1))))
                («mLam»
                  «bitTy»
                  («mLam»
                    «bitsTy»
                    («consT»
                      «bitTy»
                      («digitT» («mVar» (leaf 1)) («mVar» (leaf 4)))
                      («mApp»
                        («mLam»
                          «bitsTy»
                          («ifBit»
                            «bitsTy»
                            («mVar» (leaf 2))
                            («ifBit»
                              «bitsTy»
                              («mVar» (leaf 5))
                              («mVar» (leaf 0))
                              («call» (leaf 11) ([] : List T) («single» («mVar» (leaf 0)))))
                            («call» (leaf 11) ([] : List T) («single» («mVar» (leaf 0))))))
                        («mApp» («mSnd» («mVar» (leaf 3))) («mVar» (leaf 0))))))))))
          («mVar» (leaf 0))))
      («mVar» (leaf 1)))

def «lbCmp» :=
  «mkDefn»
    (leaf 0)
    («l2» «bitsTy» «bitsTy»)
    «ordTy»
    («mApp»
      («mListRec»
        («mLam» «bitsTy» («condT» «ordTy» («mVar» (leaf 0)) «gtO» «eqO»))
        («mLam»
          «bitsTy»
          («lcaseB»
            «bitTy»
            «ordTy»
            («mVar» (leaf 0))
            «ltO»
            («mLam»
              «bitTy»
              («mLam»
                «bitsTy»
                («ifOrd»
                  «ordTy»
                  («mApp» («mVar» (leaf 3)) («mVar» (leaf 0)))
                  «ltO»
                  («bitOrdT» («mVar» (leaf 1)) («mVar» (leaf 4)))
                  «gtO»)))))
        («mVar» (leaf 0)))
      («mVar» (leaf 1)))

def «lbLtB» :=
  «mkDefn»
    (leaf 0)
    («l2» «bitsTy» «bitsTy»)
    «bitsTy»
    («ifOrd»
      «bitsTy»
      («cmpT» («mVar» (leaf 1)) («mVar» (leaf 0)))
      «trueT»
      «bnilT»
      «bnilT»)

def «lbEqB» :=
  «mkDefn»
    (leaf 0)
    («l2» «bitsTy» «bitsTy»)
    «bitsTy»
    («mApp»
      («mListRec»
        («mLam»
          «bitsTy»
          («call» (leaf 10) («single» «bitTy») («single» («mVar» (leaf 0)))))
        («mLam»
          «bitsTy»
          («lcaseB»
            «bitTy»
            «bitsTy»
            («mVar» (leaf 0))
            «bnilT»
            («mLam»
              «bitTy»
              («mLam»
                «bitsTy»
                («ifBit»
                  «bitsTy»
                  («mVar» (leaf 1))
                  («ifBit»
                    «bitsTy»
                    («mVar» (leaf 4))
                    («mApp» («mVar» (leaf 3)) («mVar» (leaf 0)))
                    «bnilT»)
                  («ifBit»
                    «bitsTy»
                    («mVar» (leaf 4))
                    «bnilT»
                    («mApp» («mVar» (leaf 3)) («mVar» (leaf 0)))))))))
        («mVar» (leaf 0)))
      («mVar» (leaf 1)))

def «lbSubE» :=
  «mkDefn»
    (leaf 0)
    («l2» «bitsTy» «bitsTy»)
    «bitsTy»
    («mApp»
      («mListRec»
        («mLam» «bitsTy» («mVar» (leaf 0)))
        («mLam»
          «bitsTy»
          («lcaseB»
            «bitTy»
            «bitsTy»
            («mVar» (leaf 0))
            «bnilT»
            («mLam»
              «bitTy»
              («mLam»
                «bitsTy»
                («mApp»
                  («mLam»
                    «bitsTy»
                    («ifBit»
                      «bitsTy»
                      («mVar» (leaf 2))
                      («ifBit»
                        «bitsTy»
                        («mVar» (leaf 5))
                        («call» (leaf 14) ([] : List T) («single» («mVar» (leaf 0))))
                        («b0T» («call» (leaf 13) ([] : List T) («single» («mVar» (leaf 0))))))
                      («ifBit»
                        «bitsTy»
                        («mVar» (leaf 5))
                        («b0T» («mVar» (leaf 0)))
                        («call» (leaf 14) ([] : List T) («single» («mVar» (leaf 0)))))))
                  («mApp» («mVar» (leaf 3)) («mVar» (leaf 0))))))))
        («mVar» (leaf 0)))
      («mVar» (leaf 1)))

def «lbSub» :=
  «mkDefn»
    (leaf 0)
    («l2» «bitsTy» «bitsTy»)
    «bitsTy»
    («condT»
      «bitsTy»
      («call»
        (leaf 17)
        ([] : List T)
        («l2» («mVar» (leaf 1)) («mVar» (leaf 0))))
      «bnilT»
      («call»
        (leaf 19)
        ([] : List T)
        («l2» («mVar» (leaf 1)) («mVar» (leaf 0)))))

def «lbMul» :=
  «mkDefn»
    (leaf 0)
    («l2» «bitsTy» «bitsTy»)
    «bitsTy»
    («mApp»
      («mListRec»
        («mLam» «bitsTy» «bnilT»)
        («mLam»
          «bitsTy»
          («call»
            (leaf 15)
            ([] : List T)
            («l2»
              («call»
                (leaf 14)
                ([] : List T)
                («single» («mApp» («mVar» (leaf 1)) («mVar» (leaf 0)))))
              («ifBit»
                «bitsTy»
                («mVar» (leaf 2))
                («mVar» (leaf 0))
                («call» (leaf 14) ([] : List T) («single» («mVar» (leaf 0))))))))
        («mVar» (leaf 0)))
      («mVar» (leaf 1)))

def «lbDivMod» :=
  let x0 : T := «prod» «bitsTy» «bitsTy»;
  «mkDefn»
    (leaf 0)
    («l2» «bitsTy» «bitsTy»)
    x0
    («condT»
      x0
      («mVar» (leaf 0))
      («mApp»
        («mListRec»
          («mLam» «bitsTy» («mPair» «bnilT» «bnilT»))
          («mLam»
            «bitsTy»
            («mApp»
              («mLam»
                x0
                («mApp»
                  («mLam»
                    «bitsTy»
                    («ifOrd»
                      x0
                      («cmpT» («mVar» (leaf 0)) («mVar» (leaf 2)))
                      («mPair»
                        («call» (leaf 14) ([] : List T) («single» («mFst» («mVar» (leaf 1)))))
                        («mVar» (leaf 0)))
                      («mPair» («b0T» («mFst» («mVar» (leaf 1)))) «bnilT»)
                      («ifOrd»
                        x0
                        («cmpT»
                          («mVar» (leaf 0))
                          («call» (leaf 14) ([] : List T) («single» («mVar» (leaf 2)))))
                        («mPair»
                          («b0T» («mFst» («mVar» (leaf 1))))
                          («call»
                            (leaf 19)
                            ([] : List T)
                            («l2» («mVar» (leaf 0)) («mVar» (leaf 2)))))
                        («mPair» («b1T» («mFst» («mVar» (leaf 1)))) «bnilT»)
                        («mPair» («b1T» («mFst» («mVar» (leaf 1)))) «bnilT»))))
                  («consT» «bitTy» («mVar» (leaf 3)) («mSnd» («mVar» (leaf 0))))))
              («mApp» («mVar» (leaf 1)) («mVar» (leaf 0)))))
          («mVar» (leaf 1)))
        («mVar» (leaf 0)))
      («mPair» «bnilT» («mVar» (leaf 1))))

def «lbLog2» :=
  let x0 : T := «prod» «bitsTy» «bitsTy»;
  «mkDefn»
    (leaf 0)
    («single» «bitsTy»)
    «bitsTy»
    («mApp»
      («mLam»
        x0
        («condT»
          «bitsTy»
          («mSnd» («mVar» (leaf 0)))
          («mFst» («mVar» (leaf 0)))
          («call»
            (leaf 13)
            ([] : List T)
            («single» («mFst» («mVar» (leaf 0)))))))
      («mListRec»
        («mPair» «bnilT» «bnilT»)
        («mApp»
          («mLam»
            x0
            («mPair»
              («call» (leaf 11) ([] : List T) («single» («mFst» («mVar» (leaf 0)))))
              («ifBit»
                «bitsTy»
                («mVar» (leaf 2))
                («mSnd» («mVar» (leaf 0)))
                «trueT»)))
          («mVar» (leaf 0)))
        («mVar» (leaf 0))))

def «lbIter» :=
  let x0 : T := «exp» «X0» «X0»;
  «mkDefn»
    (leaf 1)
    («l3» «bitsTy» x0 «X0»)
    «X0»
    («mApp»
      («mApp»
        («mListRec»
          («mLam» x0 («mLam» «X0» («mVar» (leaf 0))))
          («mLam»
            x0
            («mLam»
              «X0»
              («mApp»
                («mLam»
                  «X0»
                  («ifBit»
                    «X0»
                    («mVar» (leaf 4))
                    («mApp» («mVar» (leaf 2)) («mVar» (leaf 0)))
                    («mApp»
                      («mVar» (leaf 2))
                      («mApp» («mVar» (leaf 2)) («mVar» (leaf 0))))))
                («mApp»
                  («mApp» («mVar» (leaf 2)) («mVar» (leaf 1)))
                  («mApp»
                    («mApp» («mVar» (leaf 2)) («mVar» (leaf 1)))
                    («mVar» (leaf 0)))))))
          («mVar» (leaf 2)))
        («mVar» (leaf 1)))
      («mVar» (leaf 0)))

def «lbMapApp» :=
  «mkDefn»
    (leaf 2)
    («l2» («list» («exp» «X0» «X1»)) «X0»)
    («list» «X1»)
    («mApp»
      («mListRec»
        («mLam» «X0» («nilT» «X1»))
        («mLam»
          «X0»
          («consT»
            «X1»
            («mApp» («mVar» (leaf 2)) («mVar» (leaf 0)))
            («mApp» («mVar» (leaf 1)) («mVar» (leaf 0)))))
        («mVar» (leaf 1)))
      («mVar» (leaf 0)))

def «lbAnd» :=
  «mkDefn»
    (leaf 0)
    («l2» «bitsTy» «bitsTy»)
    «bitsTy»
    («condT» «bitsTy» («mVar» (leaf 1)) («mVar» (leaf 0)) «bnilT»)

def «lbAllZip» :=
  «mkDefn»
    (leaf 0)
    («l2» («list» («exp» «treeTy» «bitsTy»)) («list» «treeTy»))
    «bitsTy»
    («mApp»
      («mListRec»
        («mLam»
          («list» «treeTy»)
          («call» (leaf 10) («single» «treeTy») («single» («mVar» (leaf 0)))))
        («mLam»
          («list» «treeTy»)
          («condT»
            «bitsTy»
            («call» (leaf 10) («single» «treeTy») («single» («mVar» (leaf 0))))
            «bnilT»
            («call»
              (leaf 26)
              ([] : List T)
              («l2»
                («mApp»
                  («mVar» (leaf 2))
                  («call»
                    (leaf 8)
                    («single» «treeTy»)
                    («l2» («leafT» «bnilT») («mVar» (leaf 0)))))
                («mApp»
                  («mVar» (leaf 1))
                  («call»
                    (leaf 7)
                    («single» «treeTy»)
                    («single» («mVar» (leaf 0)))))))))
        («mVar» (leaf 1)))
      («mVar» (leaf 0)))

def «lbEqual» :=
  «mkDefn»
    (leaf 0)
    («l2» «treeTy» «treeTy»)
    «bitsTy»
    («mApp»
      («mRoseRec»
        («exp» «treeTy» «bitsTy»)
        («mLam»
          «treeTy»
          («call»
            (leaf 26)
            ([] : List T)
            («l2»
              («call»
                (leaf 18)
                ([] : List T)
                («l2»
                  («mFst» («mVar» (leaf 1)))
                  («call» (leaf 3) ([] : List T) («single» («mVar» (leaf 0))))))
              («call»
                (leaf 27)
                ([] : List T)
                («l2»
                  («mSnd» («mVar» (leaf 1)))
                  («call» (leaf 5) ([] : List T) («single» («mVar» (leaf 0)))))))))
        («mVar» (leaf 1)))
      («mVar» (leaf 0)))

def «lib» :=
  («lbBnil» ::
    («lbB0» ::
      («lbB1» ::
        («lbLab» ::
          («lbUnnode» ::
            («lbChildren» ::
              («lbCond» ::
                («lbTail» ::
                  («lbHeadD» ::
                    («lbLcase» ::
                      («lbIsNil» ::
                        («lbSucc» ::
                          («lbLength» ::
                            («lbPred» ::
                              («lbDbl» ::
                                («lbAdd» ::
                                  («lbCmp» ::
                                    («lbLtB» ::
                                      («lbEqB» ::
                                        («lbSubE» ::
                                          («lbSub» ::
                                            («lbMul» ::
                                              («lbDivMod» ::
                                                («lbLog2» ::
                                                  («lbIter» ::
                                                    («lbMapApp» ::
                                                      («lbAnd» ::
                                                        («lbAllZip» ::
                                                          («lbEqual» ::
                                                            ([] : List T))))))))))))))))))))))))))))))

def «foldT» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «exp» «treeTy» («exp» («list» x0) x0);
                   «mLam»
                     x1
                     («mLam»
                       «treeTy»
                       («mApp»
                         («mRoseRec»
                           («exp» x1 x0)
                           («mLam»
                             x1
                             («mApp»
                               («mApp» («mVar» (leaf 0)) («leafT» («mFst» («mVar» (leaf 1)))))
                               («call»
                                 (leaf 25)
                                 («l2» x1 x0)
                                 («l2» («mSnd» («mVar» (leaf 1))) («mVar» (leaf 0))))))
                           («mVar» (leaf 0)))
                         («mVar» (leaf 1)))));
    x1

def «fstsT» :=
  fun (x0 : T) =>
    let x1 : T := «mListRec»
      («nilT» «treeTy»)
      («consT» «treeTy» («mFst» («mVar» (leaf 1))) («mVar» (leaf 0)))
      x0;
    x1

def «sndsT» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «mListRec»
      («nilT» x0)
      («consT» x0 («mSnd» («mVar» (leaf 1))) («mVar» (leaf 0)))
      x1;
    x2

def «paraT» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «exp» «treeTy» («exp» («list» x0) x0);
                   let x2 : T := «prod» «treeTy» x0;
                   «mLam»
                     x1
                     («mLam»
                       «treeTy»
                       («mSnd»
                         («mApp»
                           («mRoseRec»
                             («exp» x1 x2)
                             («mLam»
                               x1
                               («mApp»
                                 («mLam»
                                   («list» x2)
                                   («mApp»
                                     («mLam»
                                       «treeTy»
                                       («mPair»
                                         («mVar» (leaf 0))
                                         («mApp»
                                           («mApp» («mVar» (leaf 2)) («mVar» (leaf 0)))
                                           («sndsT» x0 («mVar» (leaf 1))))))
                                     («nodeT»
                                       («mPair»
                                         («mFst» («mVar» (leaf 2)))
                                         («fstsT» («mVar» (leaf 0)))))))
                                 («call»
                                   (leaf 25)
                                   («l2» x1 x2)
                                   («l2» («mSnd» («mVar» (leaf 1))) («mVar» (leaf 0))))))
                             («mVar» (leaf 0)))
                           («mVar» (leaf 1))))));
    x1

def «iterT» :=
  fun (x0 : T) =>
    let x1 : T := «mLam»
      («exp» x0 x0)
      («mLam»
        x0
        («mLam»
          «treeTy»
          («call»
            (leaf 24)
            («single» x0)
            («l3»
              («call» (leaf 3) ([] : List T) («single» («mVar» (leaf 0))))
              («mVar» (leaf 2))
              («mVar» (leaf 1))))));
    x1

def «foldrT» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := «prod» («exp» x0 («exp» x1 x1)) x1;
                   «mLam»
                     («exp» x0 («exp» x1 x1))
                     («mLam»
                       x1
                       («mLam»
                         («list» x0)
                         («mApp»
                           («mListRec»
                             («mLam» x2 («mSnd» («mVar» (leaf 0))))
                             («mLam»
                               x2
                               («mApp»
                                 («mApp» («mFst» («mVar» (leaf 0))) («mVar» (leaf 2)))
                                 («mApp» («mVar» (leaf 1)) («mVar» (leaf 0)))))
                             («mVar» (leaf 0)))
                           («mPair» («mVar» (leaf 2)) («mVar» (leaf 1)))))));
    x2

def «lcaseT» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «mLam»
      («list» x0)
      («mLam»
        x1
        («mLam»
          («exp» x0 («exp» («list» x0) x1))
          («lcaseB»
            x0
            x1
            («mVar» (leaf 2))
            («mVar» (leaf 1))
            («mVar» (leaf 0)))));
    x2

def «labT» :=
  fun (x0 : T) =>
    let x1 : T := «call» (leaf 3) ([] : List T) («single» x0); x1

def «binT» :=
  fun (x0 : T → T → T) =>
    let x1 : T := «mLam»
      «treeTy»
      («mLam»
        «treeTy»
        («leafT» (x0 («labT» («mVar» (leaf 1))) («labT» («mVar» (leaf 0))))));
    x1

def «primT» :=
  fun (x0 : T) =>
    let x1 : T := (if (Const.eq x0 (leaf 0)).label ≠ 0 then
      «some» («mLam» «treeTy» («leafT» («labT» («mVar» (leaf 0)))))
    else
      if (Const.eq x0 (leaf 1)).label ≠ 0 then
        «some»
          («mLam»
            «treeTy»
            («leafT»
              («call»
                (leaf 12)
                («single» «treeTy»)
                («single»
                  («call» (leaf 5) ([] : List T) («single» («mVar» (leaf 0))))))))
      else
        if (Const.eq x0 (leaf 2)).label ≠ 0 then
          «some»
            («mLam»
              «treeTy»
              («mLam»
                «treeTy»
                («call»
                  (leaf 8)
                  («single» «treeTy»)
                  («l2»
                    («leafT» «bnilT»)
                    («call»
                      (leaf 24)
                      («single» («list» «treeTy»))
                      («l3»
                        («labT» («mVar» (leaf 0)))
                        («mLam»
                          («list» «treeTy»)
                          («call» (leaf 7) («single» «treeTy») («single» («mVar» (leaf 0)))))
                        («call» (leaf 5) ([] : List T) («single» («mVar» (leaf 1))))))))))
        else
          if (Const.eq x0 (leaf 3)).label ≠ 0 then
            «some»
              («mLam»
                «treeTy»
                («mLam»
                  («list» «treeTy»)
                  («nodeT» («mPair» («labT» («mVar» (leaf 1))) («mVar» (leaf 0))))))
          else
            if (Const.eq x0 (leaf 4)).label ≠ 0 then
              «some»
                («mLam»
                  «treeTy»
                  («call» (leaf 5) ([] : List T) («single» («mVar» (leaf 0)))))
            else
              if (Const.eq x0 (leaf 5)).label ≠ 0 then
                «some»
                  («binT»
                    (fun (x1 : T) (x2 : T) =>
                      «call» (leaf 15) ([] : List T) («l2» x1 x2)))
              else
                if (Const.eq x0 (leaf 6)).label ≠ 0 then
                  «some»
                    («binT»
                      (fun (x1 : T) (x2 : T) =>
                        «call» (leaf 20) ([] : List T) («l2» x1 x2)))
                else
                  if (Const.eq x0 (leaf 7)).label ≠ 0 then
                    «some»
                      («binT»
                        (fun (x1 : T) (x2 : T) =>
                          «call» (leaf 21) ([] : List T) («l2» x1 x2)))
                  else
                    if (Const.eq x0 (leaf 8)).label ≠ 0 then
                      «some»
                        («binT»
                          (fun (x1 : T) (x2 : T) =>
                            «mFst» («call» (leaf 22) ([] : List T) («l2» x1 x2))))
                    else
                      if (Const.eq x0 (leaf 9)).label ≠ 0 then
                        «some»
                          («binT»
                            (fun (x1 : T) (x2 : T) =>
                              «mSnd» («call» (leaf 22) ([] : List T) («l2» x1 x2))))
                      else
                        if (Const.eq x0 (leaf 10)).label ≠ 0 then
                          «some»
                            («binT»
                              (fun (x1 : T) (x2 : T) =>
                                «call» (leaf 18) ([] : List T) («l2» x1 x2)))
                        else
                          if (Const.eq x0 (leaf 11)).label ≠ 0 then
                            «some»
                              («binT»
                                (fun (x1 : T) (x2 : T) =>
                                  «call» (leaf 17) ([] : List T) («l2» x1 x2)))
                          else
                            if (Const.eq x0 (leaf 12)).label ≠ 0 then
                              «some»
                                («mLam»
                                  «treeTy»
                                  («mLam»
                                    «treeTy»
                                    («leafT»
                                      («call»
                                        (leaf 28)
                                        ([] : List T)
                                        («l2» («mVar» (leaf 1)) («mVar» (leaf 0)))))))
                            else
                              if (Const.eq x0 (leaf 13)).label ≠ 0 then
                                «some»
                                  («mLam»
                                    «treeTy»
                                    («leafT»
                                      («call»
                                        (leaf 23)
                                        ([] : List T)
                                        («single» («labT» («mVar» (leaf 0)))))))
                              else
                                «none»);
    x1

def «kArrowParts» :=
  fun (x0 : T) =>
    let x1 : T := (if («and»
      (Const.eq (Const.label x0) (leaf 3))
      (Const.eq (Const.arity x0) (leaf 2))).label ≠ 0 then
      «some» («pr» (Const.child x0 (leaf 0)) (Const.child x0 (leaf 1)))
    else
      «none»);
    x1

def «kProdParts» :=
  fun (x0 : T) =>
    let x1 : T := (if («and»
      (Const.eq (Const.label x0) (leaf 2))
      (Const.eq (Const.arity x0) (leaf 2))).label ≠ 0 then
      «some» («pr» (Const.child x0 (leaf 0)) (Const.child x0 (leaf 1)))
    else
      «none»);
    x1

def «kListPart» :=
  fun (x0 : T) =>
    let x1 : T := (if («and»
      (Const.eq (Const.label x0) (leaf 4))
      (Const.eq (Const.arity x0) (leaf 1))).label ≠ 0 then
      «some» (Const.child x0 (leaf 0))
    else
      «none»);
    x1

def «trTail» :=
  fun (x0 : List (List T → List T → T)) =>
    let x1 : List
      (List T →
        List T →
          T) := Const.lcase
      (α := List T → List T → T)
      (β := List (List T → List T → T))
      x0
      ([] : List (List T → List T → T))
      (fun (_ : List T → List T → T) (x2 : List (List T → List T → T)) =>
        x2);
    x1

def «trAt» :=
  fun (x0 : List (List T → List T → T)) (x1 : T) =>
    let x2 : List T →
      List T →
        T := Const.lcase
      (α := List T → List T → T)
      (β := List T → List T → T)
      (Const.iter (α := List (List T → List T → T)) «trTail» x0 x1)
      (fun (_ : List T) (_ : List T) => «none»)
      (fun (x2 : List T → List T → T) (_ : List (List T → List T → T)) =>
        x2);
    x2

def «termStep» :=
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
          «bindO»
            («nth» x3 (Const.label x6))
            (fun (x8 : T) => «some» («pr» x8 («mVar» (Const.label x6))))
        else
          «none»
      else
        if (Const.eq x4 (leaf 9)).label ≠ 0 then
          if (Const.eq x5 (leaf 2)).label ≠ 0 then
            if («isTy» x6).label ≠ 0 then
              «bindO»
                («trAt» x1 (leaf 1) x2 (x6 :: x3))
                (fun (x8 : T) =>
                  «mapO»
                    (fun (x9 : T) => «pr» («tyArrow» x6 («p1» x8)) («mLam» x9 («p2» x8)))
                    («trTy» x6))
            else
              «none»
          else
            «none»
        else
          if (Const.eq x4 (leaf 10)).label ≠ 0 then
            if (Const.eq x5 (leaf 2)).label ≠ 0 then
              «bindO»
                («trAt» x1 (leaf 0) x2 x3)
                (fun (x8 : T) =>
                  «bindO»
                    («trAt» x1 (leaf 1) x2 x3)
                    (fun (x9 : T) =>
                      «bindO»
                        («kArrowParts» («p1» x8))
                        (fun (x10 : T) =>
                          if (Const.equal («p1» x9) («p1» x10)).label ≠ 0 then
                            «some» («pr» («p2» x10) («mApp» («p2» x8) («p2» x9)))
                          else
                            «none»)))
            else
              «none»
          else
            if (Const.eq x4 (leaf 11)).label ≠ 0 then
              if (Const.eq x5 (leaf 0)).label ≠ 0 then
                «some» («pr» (leaf 1) «mStar»)
              else
                «none»
            else
              if (Const.eq x4 (leaf 12)).label ≠ 0 then
                if (Const.eq x5 (leaf 2)).label ≠ 0 then
                  «bindO»
                    («trAt» x1 (leaf 0) x2 x3)
                    (fun (x8 : T) =>
                      «bindO»
                        («trAt» x1 (leaf 1) x2 x3)
                        (fun (x9 : T) =>
                          «some»
                            («pr»
                              («node2» (leaf 2) («p1» x8) («p1» x9))
                              («mPair» («p2» x8) («p2» x9)))))
                else
                  «none»
              else
                if (Const.eq x4 (leaf 13)).label ≠ 0 then
                  if (Const.eq x5 (leaf 1)).label ≠ 0 then
                    «bindO»
                      («trAt» x1 (leaf 0) x2 x3)
                      (fun (x8 : T) =>
                        «bindO»
                          («kProdParts» («p1» x8))
                          (fun (x9 : T) => «some» («pr» («p1» x9) («mFst» («p2» x8)))))
                  else
                    «none»
                else
                  if (Const.eq x4 (leaf 14)).label ≠ 0 then
                    if (Const.eq x5 (leaf 1)).label ≠ 0 then
                      «bindO»
                        («trAt» x1 (leaf 0) x2 x3)
                        (fun (x8 : T) =>
                          «bindO»
                            («kProdParts» («p1» x8))
                            (fun (x9 : T) => «some» («pr» («p2» x9) («mSnd» («p2» x8)))))
                    else
                      «none»
                  else
                    if (Const.eq x4 (leaf 15)).label ≠ 0 then
                      if (Const.eq x5 (leaf 1)).label ≠ 0 then
                        «some» («pr» (leaf 0) («quoteT» x6))
                      else
                        «none»
                    else
                      if (Const.eq x4 (leaf 16)).label ≠ 0 then
                        if (Const.eq x5 (leaf 3)).label ≠ 0 then
                          «bindO»
                            («trAt» x1 (leaf 0) x2 x3)
                            (fun (x8 : T) =>
                              «bindO»
                                («trAt» x1 (leaf 1) x2 x3)
                                (fun (x9 : T) =>
                                  «bindO»
                                    («trAt» x1 (leaf 2) x2 x3)
                                    (fun (x10 : T) =>
                                      if («and»
                                        (Const.equal («p1» x8) (leaf 0))
                                        (Const.equal («p1» x10) («p1» x9))).label ≠ 0 then
                                        «mapO»
                                          (fun (x11 : T) =>
                                            «pr»
                                              («p1» x9)
                                              («condT» x11 («labT» («p2» x8)) («p2» x9) («p2» x10)))
                                          («trTy» («p1» x9))
                                      else
                                        «none»)))
                        else
                          «none»
                      else
                        if (Const.eq x4 (leaf 17)).label ≠ 0 then
                          if (Const.eq x5 (leaf 1)).label ≠ 0 then
                            «mapO» (fun (x8 : T) => «pr» («foldTy» x6) («foldT» x8)) («trTy» x6)
                          else
                            «none»
                        else
                          if (Const.eq x4 (leaf 18)).label ≠ 0 then
                            if (Const.eq x5 (leaf 1)).label ≠ 0 then
                              «mapO» (fun (x8 : T) => «pr» («iterTy» x6) («iterT» x8)) («trTy» x6)
                            else
                              «none»
                          else
                            if (Const.eq x4 (leaf 19)).label ≠ 0 then
                              if (Const.eq x5 (leaf 1)).label ≠ 0 then
                                «mapO» (fun (x8 : T) => «pr» («tyList» x6) («nilT» x8)) («trTy» x6)
                              else
                                «none»
                            else
                              if (Const.eq x4 (leaf 20)).label ≠ 0 then
                                if (Const.eq x5 (leaf 2)).label ≠ 0 then
                                  «bindO»
                                    («trAt» x1 (leaf 0) x2 x3)
                                    (fun (x8 : T) =>
                                      «bindO»
                                        («trAt» x1 (leaf 1) x2 x3)
                                        (fun (x9 : T) =>
                                          «bindO»
                                            («kListPart» («p1» x9))
                                            (fun (x10 : T) =>
                                              if (Const.equal («p1» x8) x10).label ≠ 0 then
                                                «mapO»
                                                  (fun (x11 : T) =>
                                                    «pr»
                                                      («p1» x9)
                                                      («consT» x11 («p2» x8) («p2» x9)))
                                                  («trTy» x10)
                                              else
                                                «none»)))
                                else
                                  «none»
                              else
                                if (Const.eq x4 (leaf 21)).label ≠ 0 then
                                  if (Const.eq x5 (leaf 2)).label ≠ 0 then
                                    «bindO»
                                      («trTy» x6)
                                      (fun (x8 : T) =>
                                        «mapO»
                                          (fun (x9 : T) => «pr» («foldrTy» x6 x7) («foldrT» x8 x9))
                                          («trTy» x7))
                                  else
                                    «none»
                                else
                                  if (Const.eq x4 (leaf 22)).label ≠ 0 then
                                    if (Const.eq x5 (leaf 1)).label ≠ 0 then
                                      «bindO»
                                        («nth» «primTypes» (Const.label x6))
                                        (fun (x8 : T) =>
                                          «mapO»
                                            (fun (x9 : T) => «pr» x8 x9)
                                            («primT» (Const.label x6)))
                                    else
                                      «none»
                                  else
                                    if (Const.eq x4 (leaf 23)).label ≠ 0 then
                                      if (Const.eq x5 (leaf 1)).label ≠ 0 then
                                        «bindO»
                                          («nth» x2 (Const.label x6))
                                          (fun (x8 : T) =>
                                            «some»
                                              («pr»
                                                x8
                                                («call»
                                                  (Const.add («length» «lib») (Const.label x6))
                                                  ([] : List T)
                                                  ([] : List T))))
                                      else
                                        «none»
                                    else
                                      if (Const.eq x4 (leaf 24)).label ≠ 0 then
                                        if (Const.eq x5 (leaf 2)).label ≠ 0 then
                                          «bindO»
                                            («trTy» x6)
                                            (fun (x8 : T) =>
                                              «mapO»
                                                (fun (x9 : T) =>
                                                  «pr» («lcaseTy» x6 x7) («lcaseT» x8 x9))
                                                («trTy» x7))
                                        else
                                          «none»
                                      else
                                        if (Const.eq x4 (leaf 25)).label ≠ 0 then
                                          if (Const.eq x5 (leaf 1)).label ≠ 0 then
                                            «mapO»
                                              (fun (x8 : T) => «pr» («foldTy» x6) («paraT» x8))
                                              («trTy» x6)
                                          else
                                            «none»
                                        else
                                          «none»);
    x2

def «term» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.para
      (α := List T → List T → T)
      «termStep»
      x2
      x0
      x1;
    x3

def «program» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x1 : T) (x2 : T) =>
        «bindO»
          x2
          (fun (x3 : T) =>
            let x4 : List T := Const.children («p1» x3);
            let x5 : List T := Const.children («p2» x3);
            «bindO»
              («term» x4 ([] : List T) x1)
              (fun (x6 : T) =>
                «mapO»
                  (fun (x7 : T) =>
                    «pr»
                      (Const.node (leaf 0) («append» x4 («single» («p1» x6))))
                      (Const.node
                        (leaf 0)
                        («append»
                          x5
                          («single» («mkDefn» (leaf 0) ([] : List T) x7 («p2» x6))))))
                  («trTy» («p1» x6)))))
      («some»
        («pr»
          (Const.node (leaf 0) ([] : List T))
          (Const.node (leaf 0) ([] : List T))))
      («reverse» x0);
    x1

def «trGlobals» :=
  fun (x0 : List T) =>
    let x1 : T := «globals»
      (Const.node (leaf 0) «trPrims»)
      (Const.node (leaf 0) («mapT» «defLang» («append» «lib» x0)))
      («length» «sig»);
    x1

def «thm» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (let x2 : List T := Const.children (Const.child x1 (leaf 0));
                   let x3 : T := Const.child x1 (leaf 1);
                   «bindO»
                     («allSomeT» («mapT» «trTy» x2))
                     (fun (x4 : T) =>
                       «bindO»
                         («term» x0 x2 (Const.child x3 (leaf 1)))
                         (fun (x5 : T) =>
                           «mapO»
                             (fun (x6 : T) =>
                               «mkThm»
                                 (leaf 0)
                                 x4
                                 (Const.node (leaf 0) ([] : List T))
                                 («mEq» («p2» x5) («p2» x6)))
                             («term» x0 x2 (Const.child x3 (leaf 2))))));
    x2

end GebMirror.Metalogic

end
