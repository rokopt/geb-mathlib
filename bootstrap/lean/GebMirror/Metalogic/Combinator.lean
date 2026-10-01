module

public import GebMirror.Metalogic.Tactics

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «cHyp» :=
  fun (x0 : T) =>
    let x1 : T := Const.node
      (leaf 0)
      («single» (Const.node x0 ([] : List T)));
    x1

def «cRefl» :=
  fun (x0 : T) =>
    let x1 : T := Const.node
      (leaf 1)
      («single» (Const.node x0 ([] : List T)));
    x1

def «cSymm» :=
  fun (x0 : T) => let x1 : T := Const.node (leaf 2) («single» x0); x1

def «cTrans» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.node (leaf 3) («l2» x0 x1); x2

def «cCong» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.node (leaf 4) (x0 :: x1); x2

def «cStrict» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.node
      (leaf 5)
      («l2» (Const.node x0 ([] : List T)) x1);
    x2

def «cAx» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : List T) =>
    let x4 : T := Const.node
      (leaf 6)
      ((Const.node x0 ([] : List T)) :: («append» x1 («append» x2 x3)));
    x4

def «cThm» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : List T) =>
    let x4 : T := Const.node
      (leaf 8)
      ((Const.node x0 ([] : List T)) :: («append» x1 («append» x2 x3)));
    x4

def «scope» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «scCtx» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1); Const.children x2);
    x1

def «scHyps» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let x3 : T := Const.child x1 (leaf 1); Const.children x3);
    x1

def «scSeq» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «mkSeq» («scCtx» x0) («scHyps» x0) x1; x2

def «scCite» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := «length» («scCtx» x0);
                   «cThm»
                     x1
                     («mapT» «phVar» («range» x2))
                     («mapT» «cRefl» («range» x2))
                     («mapT» «cHyp» («range» («length» («scHyps» x0)))));
    x2

def «pst» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    Const.node
      (leaf 0)
      (x0 :: (x1 :: (x2 :: (x3 :: (x4 :: (x5 :: ([] : List T)))))))

def «stDev» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2);
            let _ : T := Const.child x1 (leaf 3);
            let _ : T := Const.child x1 (leaf 4);
            let _ : T := Const.child x1 (leaf 5); Const.children x2);
    x1

def «stMemo» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let x3 : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2);
            let _ : T := Const.child x1 (leaf 3);
            let _ : T := Const.child x1 (leaf 4);
            let _ : T := Const.child x1 (leaf 5); Const.children x3);
    x1

def «stNfs» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let x4 : T := Const.child x1 (leaf 2);
            let _ : T := Const.child x1 (leaf 3);
            let _ : T := Const.child x1 (leaf 4);
            let _ : T := Const.child x1 (leaf 5); Const.children x4);
    x1

def «stDefs» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2);
            let x5 : T := Const.child x1 (leaf 3);
            let _ : T := Const.child x1 (leaf 4);
            let _ : T := Const.child x1 (leaf 5); Const.children x5);
    x1

def «stSig» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2);
            let _ : T := Const.child x1 (leaf 3);
            let x6 : T := Const.child x1 (leaf 4);
            let _ : T := Const.child x1 (leaf 5); Const.children x6);
    x1

def «stInfer» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let _ : T := Const.child x1 (leaf 3);
                   let _ : T := Const.child x1 (leaf 4);
                   let x7 : T := Const.child x1 (leaf 5); x7);
    x1

def «withDev» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := (let x2 : T := x0;
                   let _ : T := Const.child x2 (leaf 0);
                   let x4 : T := Const.child x2 (leaf 1);
                   let x5 : T := Const.child x2 (leaf 2);
                   let x6 : T := Const.child x2 (leaf 3);
                   let x7 : T := Const.child x2 (leaf 4);
                   let x8 : T := Const.child x2 (leaf 5);
                   «pst» (Const.node (leaf 0) x1) x4 x5 x6 x7 x8);
    x2

def «withMemo» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := (let x2 : T := x0;
                   let x3 : T := Const.child x2 (leaf 0);
                   let _ : T := Const.child x2 (leaf 1);
                   let x5 : T := Const.child x2 (leaf 2);
                   let x6 : T := Const.child x2 (leaf 3);
                   let x7 : T := Const.child x2 (leaf 4);
                   let x8 : T := Const.child x2 (leaf 5);
                   «pst» x3 (Const.node (leaf 0) x1) x5 x6 x7 x8);
    x2

def «withNfs» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := (let x2 : T := x0;
                   let x3 : T := Const.child x2 (leaf 0);
                   let x4 : T := Const.child x2 (leaf 1);
                   let _ : T := Const.child x2 (leaf 2);
                   let x6 : T := Const.child x2 (leaf 3);
                   let x7 : T := Const.child x2 (leaf 4);
                   let x8 : T := Const.child x2 (leaf 5);
                   «pst» x3 x4 (Const.node (leaf 0) x1) x6 x7 x8);
    x2

def «tableFind» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        if (Const.equal («at» (Const.children x2) (leaf 0)) x1).label ≠ 0 then
          «some» («at» (Const.children x2) (leaf 1))
        else
          x3)
      «none»
      x0;
    x2

def «tableInsert» :=
  fun (x0 : List T) (x1 : T) (x2 : T) =>
    let x3 : List T := ((Const.node (leaf 0) («l2» x1 x2)) :: x0); x3

def «pty» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) (x6 : T) =>
    Const.node
      (leaf 0)
      (x0 :: (x1 :: (x2 :: (x3 :: (x4 :: (x5 :: (x6 :: ([] : List T))))))))

def «tyT» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let _ : T := Const.child x1 (leaf 3);
                   let _ : T := Const.child x1 (leaf 4);
                   let _ : T := Const.child x1 (leaf 5);
                   let _ : T := Const.child x1 (leaf 6); x2);
    x1

def «tySort» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let _ : T := Const.child x1 (leaf 3);
                   let _ : T := Const.child x1 (leaf 4);
                   let _ : T := Const.child x1 (leaf 5);
                   let _ : T := Const.child x1 (leaf 6); x3);
    x1

def «tyDfd» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let x4 : T := Const.child x1 (leaf 2);
                   let _ : T := Const.child x1 (leaf 3);
                   let _ : T := Const.child x1 (leaf 4);
                   let _ : T := Const.child x1 (leaf 5);
                   let _ : T := Const.child x1 (leaf 6); x4);
    x1

def «tyLo» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let x5 : T := Const.child x1 (leaf 3);
                   let _ : T := Const.child x1 (leaf 4);
                   let _ : T := Const.child x1 (leaf 5);
                   let _ : T := Const.child x1 (leaf 6); x5);
    x1

def «tyLoC» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let _ : T := Const.child x1 (leaf 3);
                   let x6 : T := Const.child x1 (leaf 4);
                   let _ : T := Const.child x1 (leaf 5);
                   let _ : T := Const.child x1 (leaf 6); x6);
    x1

def «tyHi» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let _ : T := Const.child x1 (leaf 3);
                   let _ : T := Const.child x1 (leaf 4);
                   let x7 : T := Const.child x1 (leaf 5);
                   let _ : T := Const.child x1 (leaf 6); x7);
    x1

def «tyHiC» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let _ : T := Const.child x1 (leaf 3);
                   let _ : T := Const.child x1 (leaf 4);
                   let _ : T := Const.child x1 (leaf 5);
                   let x8 : T := Const.child x1 (leaf 6); x8);
    x1

def «pmPure» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «some» (Const.node (leaf 0) («l2» x0 x2)));
    x1

def «pmFail» := fun (_ : T) (_ : T) => let x2 : T := «none»; x2

def «pmBind» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      «bindO»
        (x0 x2 x3)
        (fun (x4 : T) =>
          x1
            («at» (Const.children x4) (leaf 0))
            x2
            («at» (Const.children x4) (leaf 1))));
    x2

def «pmOr» :=
  fun (x0 : T → T → T) (x1 : T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if («isSome» x4).label ≠ 0 then x4 else x1 x2 x3);
    x2

def «pmGet» :=
  fun (_ : T) (x1 : T) =>
    let x2 : T := «some» (Const.node (leaf 0) («l2» x1 x1)); x2

def «pmRead» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «some» (Const.node (leaf 0) («l2» x0 x1)); x2

def «pmSet» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (_ : T) =>
      «some» (Const.node (leaf 0) («l2» (leaf 0) x0)));
    x1

def «pmGuard» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      if (x0).label ≠ 0 then
        «some» (Const.node (leaf 0) («l2» (leaf 0) x2))
      else
        «none»);
    x1

def «pmMapM» :=
  fun (x0 : T → T → T → T) (x1 : List T) =>
    let x2 : T →
      T →
        T := Const.foldr
      (α := T)
      (β := T → T → T)
      (fun (x2 : T) (x3 : T → T → T) =>
        «pmBind»
          (x0 x2)
          (fun (x4 : T) =>
            «pmBind»
              x3
              (fun (x5 : T) =>
                «pmPure» (Const.node (leaf 0) (x4 :: (Const.children x5))))))
      («pmPure» (Const.node (leaf 0) ([] : List T)))
      x1;
    x2

def «pmSeq» :=
  fun (x0 : List (T → T → T)) =>
    let x1 : T →
      T →
        T := Const.foldr
      (α := T → T → T)
      (β := T → T → T)
      (fun (x1 : T → T → T) (x2 : T → T → T) =>
        «pmBind»
          x1
          (fun (x3 : T) =>
            «pmBind»
              x2
              (fun (x4 : T) =>
                «pmPure» (Const.node (leaf 0) (x3 :: (Const.children x4))))))
      («pmPure» (Const.node (leaf 0) ([] : List T)))
      x0;
    x1

def «findIdxT» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : T := (Const.foldr
      (α := T)
      (β := T × T)
      (fun (x2 : T) (x3 : T × T) =>
        (Const.sub (x3).1 (leaf 1),
          if (x0 x2).label ≠ 0 then
            «some» (Const.sub (x3).1 (leaf 1))
          else
            (x3).2))
      («length» x1, «none»)
      x1).2;
    x2

def «axiomAt» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (if (Const.lt x0 («length» «axioms»)).label ≠ 0 then
      «pmPure» («at» «axioms» x0)
    else
      «pmBind»
        «pmGet»
        (fun (x1 : T) =>
          let x2 : T := Const.sub x0 («length» «axioms»);
          let x3 : T := «nth» («stDefs» x1) (Const.div x2 (leaf 2));
          if («isSome» x3).label ≠ 0 then
            let x4 : T := «nth»
              («pdAxioms»
                (Const.add («length» «sig») (Const.div x2 (leaf 2)))
                («get» x3))
              (Const.mod x2 (leaf 2));
            if («isSome» x4).label ≠ 0 then «pmPure» («get» x4) else «pmFail»
          else
            «pmFail»));
    x1

def «addLemma» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      «some»
        (Const.node
          (leaf 0)
          («l2»
            («scCite» x2 («length» («stDev» x3)))
            («withDev»
              x3
              («append»
                («stDev» x3)
                («single» (Const.node (leaf 0) («l2» («scSeq» x2 x0) x1))))))));
    x2

def «lookup» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «some»
        (Const.node (leaf 0) («l2» («tableFind» («stMemo» x2) x0) x2)));
    x1

def «memoize» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «some»
        (Const.node
          (leaf 0)
          («l2»
            (leaf 0)
            («withMemo» x2 («tableInsert» («stMemo» x2) («tyT» x0) x0)))));
    x1

def «memoRet» :=
  fun (x0 : T) =>
    let x1 : T →
      T → T := «pmBind» («memoize» x0) (fun (_ : T) => «pmPure» x0);
    x1

def «dfdCert» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      if («stInfer» x3).label ≠ 0 then
        «some»
          (Const.node (leaf 0) («l2» (Const.node (leaf 9) («single» x0)) x3))
      else
        «addLemma» («dfd» x0) x1 x2 x3);
    x2

def «eqCert» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      if («stInfer» x3).label ≠ 0 then
        «some»
          (Const.node
            (leaf 0)
            («l2» (Const.node (leaf 10) («l2» («eqLhs» x0) («eqRhs» x0))) x3))
      else
        «addLemma» x0 x1 x2 x3);
    x2

def «objEq» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T →
      T →
        T := (fun (_ : T) (x3 : T) =>
      if («and»
        (Const.eq («tySort» x0) (leaf 0))
        («and»
          (Const.eq («tySort» x1) (leaf 0))
          (Const.equal («tyLo» x0) («tyLo» x1)))).label ≠ 0 then
        «some»
          (Const.node
            (leaf 0)
            («l2»
              (if («stInfer» x3).label ≠ 0 then
                Const.node (leaf 10) («l2» («tyT» x0) («tyT» x1))
              else
                «cTrans» («tyLoC» x0) («cSymm» («tyLoC» x1)))
              x3))
      else
        «none»);
    x2

def «proveHyp» :=
  fun (x0 : List T → T → T → T → T) (x1 : List T) (x2 : T) =>
    let x3 : T →
      T →
        T := «pmBind»
      (x0 x1 («eqLhs» x2))
      (fun (x3 : T) =>
        if (Const.equal («eqLhs» x2) («eqRhs» x2)).label ≠ 0 then
          «pmPure» («tyDfd» x3)
        else
          «pmBind» (x0 x1 («eqRhs» x2)) (fun (x4 : T) => «objEq» x3 x4));
    x3

def «pBound» :=
  fun (x0 : List T → T → T → T → T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : T) =>
    let x5 : T →
      T →
        T := «pmBind»
      («axiomAt» x3)
      (fun (x5 : T) =>
        «pmBind»
          («pmMapM»
            (fun (x6 : T) =>
              if (Const.equal x6 («dfd» («opVars» x2 («length» x1)))).label ≠ 0 then
                «pmPure» x4
              else
                «proveHyp» x0 x1 x6)
            («seqHyps» x5))
          (fun (x6 : T) =>
            let x7 : T := «cAx»
              x3
              («mapT» «tyT» x1)
              («mapT» «tyDfd» x1)
              (Const.children x6);
            «pmBind»
              (x0 x1 («eqRhs» («seqConcl» x5)))
              (fun (x8 : T) =>
                «pmPure»
                  (Const.node
                    (leaf 0)
                    («l2» («tyLo» x8) («cTrans» x7 («tyLoC» x8)))))));
    x5

def «typeDefined» :=
  fun (x0 : List T → T → T → T → T) (x1 : T) (x2 : T) (x3 : List T) =>
    let x4 : T →
      T →
        T := «pmBind»
      «pmGet»
      (fun (x4 : T) =>
        let x5 : T := «nth» («stDefs» x4) x1;
        if («isSome» x5).label ≠ 0 then
          let x6 : List T := «mapT» «tyT» x3;
          let x7 : T := «phOp» (Const.add («length» «sig») x1) x6;
          «pmBind»
            (x0 x3 («pdBody» («get» x5)))
            (fun (x8 : T) =>
              «pmBind»
                «pmGet»
                (fun (x9 : T) =>
                  if («stInfer» x9).label ≠ 0 then
                    let x10 : T := Const.node (leaf 9) («single» x7);
                    «memoRet»
                      (if (Const.eq x2 (leaf 0)).label ≠ 0 then
                        «pty»
                          x7
                          (leaf 0)
                          x10
                          («tyLo» x8)
                          (Const.node (leaf 10) («l2» x7 («tyLo» x8)))
                          («tyLo» x8)
                          (Const.node (leaf 10) («l2» x7 («tyLo» x8)))
                      else
                        «pty»
                          x7
                          (leaf 1)
                          x10
                          («tyLo» x8)
                          (Const.node (leaf 10) («l2» («dom» x7) («tyLo» x8)))
                          («tyHi» x8)
                          (Const.node (leaf 10) («l2» («cod» x7) («tyHi» x8))))
                  else
                    «pmBind»
                      («addLemma»
                        («eqn» x7 («tyT» x8))
                        («cAx»
                          («defAxIdx» x1)
                          x6
                          («mapT» «tyDfd» x3)
                          («single» («tyDfd» x8))))
                      (fun (x10 : T) =>
                        «pmBind»
                          («addLemma» («dfd» x7) («cTrans» x10 («cSymm» x10)))
                          (fun (x11 : T) =>
                            if (Const.eq x2 (leaf 0)).label ≠ 0 then
                              «pmBind»
                                («addLemma» («eqn» x7 («tyLo» x8)) («cTrans» x10 («tyLoC» x8)))
                                (fun (x12 : T) =>
                                  «memoRet» («pty» x7 (leaf 0) x11 («tyLo» x8) x12 («tyLo» x8) x12))
                            else
                              «pmBind»
                                («addLemma»
                                  («eqn» («dom» x7) («tyLo» x8))
                                  («cTrans»
                                    («cCong»
                                      («cAx» (leaf 0) («single» x7) («single» x11) ([] : List T))
                                      («single» x10))
                                    («tyLoC» x8)))
                                (fun (x12 : T) =>
                                  «pmBind»
                                    («addLemma»
                                      («eqn» («cod» x7) («tyHi» x8))
                                      («cTrans»
                                        («cCong»
                                          («cAx»
                                            (leaf 1)
                                            («single» x7)
                                            («single» x11)
                                            ([] : List T))
                                          («single» x10))
                                        («tyHiC» x8)))
                                    (fun (x13 : T) =>
                                      «memoRet»
                                        («pty»
                                          x7
                                          (leaf 1)
                                          x11
                                          («tyLo» x8)
                                          x12
                                          («tyHi» x8)
                                          x13)))))))
        else
          «pmFail»);
    x4

def «typeOpDfd» :=
  fun (x0 : List T → T → T → T → T) (x1 : T) (x2 : List T) =>
    let x3 : T →
      T →
        T := (let x3 : List T := «mapT» «tyT» x2;
              let x4 : T := «nth» «dfdRules» x1;
              if («and» («isSome» x4) («isSome» («get» x4))).label ≠ 0 then
                let x5 : T := «get» («get» x4);
                let x6 : T := «at» (Const.children x5) (leaf 0);
                if (Const.eq (Const.label x5) (leaf 0)).label ≠ 0 then
                  «pmBind»
                    («axiomAt» x6)
                    (fun (x7 : T) =>
                      «pmBind»
                        («pmMapM» («proveHyp» x0 x2) («seqHyps» x7))
                        (fun (x8 : T) =>
                          «pmPure» («cAx» x6 x3 («mapT» «tyDfd» x2) (Const.children x8))))
                else
                  if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
                    «pmPure»
                      («cStrict» (leaf 0) («cAx» x6 x3 («mapT» «tyDfd» x2) ([] : List T)))
                  else
                    let x7 : T := «cAx» x6 ([] : List T) ([] : List T) ([] : List T);
                    «pmPure» («cTrans» («cSymm» x7) x7)
              else
                «pmFail»);
    x3

def «typeOpObj» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List T) =>
    let x4 : T →
      T →
        T := (let x4 : T := «phOp»
                x0
                («mapT»
                  (fun (x4 : T) =>
                    if (Const.eq («tySort» x4) (leaf 0)).label ≠ 0 then
                      «tyLo» x4
                    else
                      «tyT» x4)
                  x3);
              if (Const.equal x4 x1).label ≠ 0 then
                «pmPure» («pty» x1 (leaf 0) x2 x1 x2 x1 x2)
              else
                «pmBind»
                  («eqCert»
                    («eqn» x1 x4)
                    («cCong»
                      x2
                      («mapT»
                        (fun (x5 : T) =>
                          if (Const.eq («tySort» x5) (leaf 0)).label ≠ 0 then
                            «tyLoC» x5
                          else
                            «tyDfd» x5)
                        x3)))
                  (fun (x5 : T) => «pmPure» («pty» x1 (leaf 0) x2 x4 x5 x4 x5)));
    x4

def «typeOpTy» :=
  fun (x0 : List T → T → T → T → T)
    (x1 : T)
    (x2 : T)
    (x3 : T)
    (x4 : T)
    (x5 : List T) =>
    let x6 : T →
      T →
        T := (if (Const.eq x2 (leaf 0)).label ≠ 0 then
      if («and»
        (Const.eq x1 (leaf 0))
        (Const.eq («length» x5) (leaf 1))).label ≠ 0 then
        let x6 : T := «at» x5 (leaf 0);
        «pmPure»
          («pty»
            x3
            (leaf 0)
            x4
            («tyLo» x6)
            («tyLoC» x6)
            («tyLo» x6)
            («tyLoC» x6))
      else
        if («and»
          (Const.eq x1 (leaf 1))
          (Const.eq («length» x5) (leaf 1))).label ≠ 0 then
          let x6 : T := «at» x5 (leaf 0);
          «pmPure»
            («pty»
              x3
              (leaf 0)
              x4
              («tyHi» x6)
              («tyHiC» x6)
              («tyHi» x6)
              («tyHiC» x6))
        else
          «typeOpObj» x1 x3 x4 x5
    else
      let x6 : T := «nth» «domRules» x1;
      let x7 : T := «nth» «codRules» x1;
      if («and»
        («and» («isSome» x6) («isSome» («get» x6)))
        («and» («isSome» x7) («isSome» («get» x7)))).label ≠ 0 then
        «pmBind»
          («pBound» x0 x5 x1 («get» («get» x6)) x4)
          (fun (x8 : T) =>
            «pmBind»
              («pBound» x0 x5 x1 («get» («get» x7)) x4)
              (fun (x9 : T) =>
                «pmBind»
                  («eqCert»
                    («eqn» («dom» x3) («at» (Const.children x8) (leaf 0)))
                    («at» (Const.children x8) (leaf 1)))
                  (fun (x10 : T) =>
                    «pmBind»
                      («eqCert»
                        («eqn» («cod» x3) («at» (Const.children x9) (leaf 0)))
                        («at» (Const.children x9) (leaf 1)))
                      (fun (x11 : T) =>
                        «pmPure»
                          («pty»
                            x3
                            (leaf 1)
                            x4
                            («at» (Const.children x8) (leaf 0))
                            x10
                            («at» (Const.children x9) (leaf 0))
                            x11)))))
      else
        «pmFail»);
    x6

def «typeOp» :=
  fun (x0 : List T → T → T → T → T) (x1 : T) (x2 : List T) =>
    let x3 : T →
      T →
        T := «pmBind»
      «pmGet»
      (fun (x3 : T) =>
        let x4 : T := «nth» («stSig» x3) x1;
        if («isSome» x4).label ≠ 0 then
          let x5 : T := «get» x4;
          if («equalTs» («mapT» «tySort» x2) («opArgs» x5)).label ≠ 0 then
            if (Const.lt x1 («length» «sig»)).label ≠ 0 then
              let x6 : T := «phOp» x1 («mapT» «tyT» x2);
              «pmBind»
                («typeOpDfd» x0 x1 x2)
                (fun (x7 : T) =>
                  «pmBind»
                    («dfdCert» x6 x7)
                    (fun (x8 : T) =>
                      «pmBind» («typeOpTy» x0 x1 («opSort» x5) x6 x8 x2) «memoRet»))
            else
              «typeDefined» x0 (Const.sub x1 («length» «sig»)) («opSort» x5) x2
          else
            «pmFail»
        else
          «pmFail»);
    x3

def «typeStep» :=
  fun (x0 : List T → T → T → T → T)
    (x1 : T → T → T → T)
    (x2 : T → T)
    (x3 : T)
    (x4 : List (T → T → T)) =>
    let x5 : T →
      T →
        T := (let x5 : T := Const.label x3;
              if (Const.eq x5 (leaf 0)).label ≠ 0 then
                if (Const.eq («length» (Const.children x3)) (leaf 1)).label ≠ 0 then
                  x1 (Const.label («at» (Const.children x3) (leaf 0)))
                else
                  «pmFail»
              else
                «pmBind»
                  («lookup» (x2 x3))
                  (fun (x6 : T) =>
                    if («isSome» x6).label ≠ 0 then
                      «pmPure» («get» x6)
                    else
                      «pmBind»
                        («pmSeq» x4)
                        (fun (x7 : T) =>
                          «typeOp» x0 (Const.sub x5 (leaf 1)) (Const.children x7))));
    x5

def «varSide» :=
  fun (x0 : T → T → T → T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T →
      T →
        T := (fun (x5 : T) (x6 : T) =>
      let x7 : T := «phOp» x3 («single» («phVar» x1));
      let x8 : T := «findIdxT»
        (fun (x8 : T) => Const.equal («eqLhs» x8) x7)
        («scHyps» x5);
      if («isSome» x8).label ≠ 0 then
        let x9 : T := «get» x8;
        let x10 : T := «nth» («scHyps» x5) x9;
        if («isSome» x10).label ≠ 0 then
          «pmBind»
            (x0 («eqRhs» («get» x10)))
            (fun (x11 : T) =>
              «pmPure»
                (Const.node
                  (leaf 0)
                  («l2»
                    («tyLo» x11)
                    (if (x2).label ≠ 0 then
                      Const.node (leaf 10) («l2» x7 («tyLo» x11))
                    else
                      «cTrans» («cHyp» x9) («tyLoC» x11)))))
            x5
            x6
        else
          «none»
      else
        «some»
          (Const.node
            (leaf 0)
            («l2»
              (Const.node
                (leaf 0)
                («l2»
                  x7
                  («cAx»
                    x4
                    («single» («phVar» x1))
                    («single» («cRefl» x1))
                    ([] : List T))))
              x6)));
    x5

def «typeVar» :=
  fun (x0 : T → T → T → T) (x1 : T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := «nth» («scCtx» x2) x1;
      if («isSome» x4).label ≠ 0 then
        let x5 : T := «get» x4;
        if (Const.eq x5 (leaf 0)).label ≠ 0 then
          «some»
            (Const.node
              (leaf 0)
              («l2»
                («pty»
                  («phVar» x1)
                  (leaf 0)
                  («cRefl» x1)
                  («phVar» x1)
                  («cRefl» x1)
                  («phVar» x1)
                  («cRefl» x1))
                x3))
        else
          if (Const.eq x5 (leaf 1)).label ≠ 0 then
            let x6 : T := «stInfer» x3;
            «pmBind»
              («varSide» x0 x1 x6 (leaf 0) (leaf 0))
              (fun (x7 : T) =>
                «pmBind»
                  («varSide» x0 x1 x6 (leaf 1) (leaf 1))
                  (fun (x8 : T) =>
                    «pmPure»
                      («pty»
                        («phVar» x1)
                        (leaf 1)
                        («cRefl» x1)
                        («at» (Const.children x7) (leaf 0))
                        («at» (Const.children x7) (leaf 1))
                        («at» (Const.children x8) (leaf 0))
                        («at» (Const.children x8) (leaf 1)))))
              x2
              x3
          else
            «none»
      else
        «none»);
    x2

def «typers» :=
  fun (x0 : T) =>
    let x1 : (List T → T → T → T → T) ×
      (T →
        T →
          T →
            T) := Const.iter
      (α := (List T → T → T → T → T) × (T → T → T → T))
      (fun (x1 : (List T → T → T → T → T) × (T → T → T → T)) =>
        (fun (x2 : List T) (x3 : T) =>
          Const.para
            (α := T → T → T)
            («typeStep»
              (x1).1
              (fun (x4 : T) =>
                let x5 : T := «nth» x2 x4;
                if («isSome» x5).label ≠ 0 then «pmPure» («get» x5) else «pmFail»)
              («phSubst» («mapT» «tyT» x2)))
            x3,
          fun (x2 : T) =>
            Const.para
              (α := T → T → T)
              («typeStep» (x1).1 («typeVar» (x1).2) (fun (x3 : T) => x3))
              x2))
      (fun (_ : List T) (_ : T) => «pmFail», fun (_ : T) => «pmFail»)
      x0;
    x1

def «typeTerm» :=
  fun (x0 : T) => let x1 : T → T → T := («typers» (leaf 8)).2 x0; x1

def «typePattern» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T → T → T := («typers» (leaf 8)).1 x0 x1; x2

def «pmRun» :=
  fun (x0 : T) (x1 : List T) (x2 : T → T → T) (x3 : List T) (x4 : T) =>
    let x5 : T := «mapO»
      (fun (x5 : T) =>
        Const.node
          (leaf 0)
          («l2»
            («at» (Const.children x5) (leaf 0))
            (Const.node (leaf 0) («stDev» («at» (Const.children x5) (leaf 1))))))
      (x2
        x0
        («pst»
          (Const.node (leaf 0) x1)
          (Const.node (leaf 0) ([] : List T))
          (Const.node (leaf 0) ([] : List T))
          (Const.node (leaf 0) x3)
          (Const.node
            (leaf 0)
            («append»
              «sig»
              («mapT»
                (fun (x5 : T) =>
                  «opSig» (Const.node (leaf 0) («pdCtx» x5)) («pdSort» x5))
                x3)))
          x4));
    x5

def «srcAx» :=
  fun (x0 : T) => Const.node (leaf 0) (x0 :: ([] : List T))

def «srcThm» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «srcSeq» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (let x1 : T := «at» (Const.children x0) (leaf 0);
              if (Const.eq (Const.label x0) (leaf 0)).label ≠ 0 then
                «axiomAt» x1
              else
                «pmBind»
                  «pmGet»
                  (fun (x2 : T) =>
                    let x3 : T := «nth» («stDev» x2) x1;
                    if («isSome» x3).label ≠ 0 then
                      «pmPure» («at» (Const.children («get» x3)) (leaf 0))
                    else
                      «pmFail»));
    x1

def «srcCert» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : List T) =>
    let x4 : T := (if (Const.eq (Const.label x0) (leaf 0)).label ≠ 0 then
      «cAx» («at» (Const.children x0) (leaf 0)) x1 x2 x3
    else
      «cThm» («at» (Const.children x0) (leaf 0)) x1 x2 x3);
    x4

def «rwRule» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «rwSrc» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2); x2);
    x1

def «rwFlip» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2); x3);
    x1

def «rwAvoid» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let x4 : T := Const.child x1 (leaf 2); Const.children x4);
    x1

def «matchSt» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «msSigma» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1); Const.children x2);
    x1

def «msObjs» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let x3 : T := Const.child x1 (leaf 1); Const.children x3);
    x1

def «msDefer» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «matchSt»
      (Const.node (leaf 0) («msSigma» x0))
      (Const.node
        (leaf 0)
        ((Const.node (leaf 0) («l2» x1 x2)) :: («msObjs» x0)));
    x3

def «matchKids» :=
  fun (x0 : List (T → T → T)) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.foldr
      (α := T → T → T)
      (β := List T → T → T)
      (fun (x3 : T → T → T) (x4 : List T → T → T) (x5 : List T) (x6 : T) =>
        Const.lcase
          (α := T)
          (β := T)
          x5
          («some» x6)
          (fun (x7 : T) (x8 : List T) =>
            «bindO» (x3 x7 x6) (fun (x9 : T) => x4 x8 x9)))
      (fun (_ : List T) (x4 : T) => «some» x4)
      x0
      x1
      x2;
    x3

def «matchStepP» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) (x3 : List (T → T → T)) =>
    let x4 : T →
      T →
        T := (fun (x4 : T) (x5 : T) =>
      let x6 : T := Const.label x2;
      if (Const.eq x6 (leaf 0)).label ≠ 0 then
        if (Const.eq («length» (Const.children x2)) (leaf 1)).label ≠ 0 then
          let x7 : T := Const.label («at» (Const.children x2) (leaf 0));
          let x8 : T := «nth» («msSigma» x5) x7;
          if («isSome» x8).label ≠ 0 then
            if («isSome» («get» x8)).label ≠ 0 then
              if (Const.equal («get» («get» x8)) x4).label ≠ 0 then
                «some» x5
              else
                if (Const.equal («nth» x1 x7) («some» (leaf 0))).label ≠ 0 then
                  «some» («msDefer» x5 x2 x4)
                else
                  «none»
            else
              «some»
                («matchSt»
                  (Const.node (leaf 0) («setAt» («msSigma» x5) x7 («some» x4)))
                  (Const.node (leaf 0) («msObjs» x5)))
          else
            «none»
        else
          «none»
      else
        if (Const.equal («sortOf» x0 x1 x2) («some» (leaf 0))).label ≠ 0 then
          «some» («msDefer» x5 x2 x4)
        else
          if («and»
            (Const.eq (Const.label x4) x6)
            (Const.eq
              («length» (Const.children x4))
              («length» (Const.children x2)))).label ≠ 0 then
            «matchKids» x3 (Const.children x4) x5
          else
            «none»);
    x4

def «matchPat» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := Const.para
      (α := T → T → T)
      («matchStepP» x0 x1)
      x2
      x3
      x4;
    x5

def «bridgeKids» :=
  fun (x0 : List (T → T → T → T)) (x1 : List T) =>
    let x2 : T →
      T →
        T := Const.foldr
      (α := T → T → T → T)
      (β := List T → T → T → T)
      (fun (x2 : T → T → T → T) (x3 : List T → T → T → T) (x4 : List T) =>
        Const.lcase
          (α := T)
          (β := T → T → T)
          x4
          («pmPure» (Const.node (leaf 0) ([] : List T)))
          (fun (x5 : T) (x6 : List T) =>
            «pmBind»
              (x2 x5)
              (fun (x7 : T) =>
                «pmBind»
                  (x3 x6)
                  (fun (x8 : T) =>
                    «pmPure» (Const.node (leaf 0) (x7 :: (Const.children x8)))))))
      (fun (_ : List T) => «pmPure» (Const.node (leaf 0) ([] : List T)))
      x0
      x1;
    x2

def «bridgeStep» :=
  fun (x0 : List T) (x1 : T) (x2 : List (T → T → T → T)) =>
    let x3 : T →
      T →
        T →
          T := (fun (x3 : T) =>
      «pmBind»
        («typeTerm» x3)
        (fun (x4 : T) =>
          if (Const.equal («phSubst» («mapT» «tyT» x0) x1) x3).label ≠ 0 then
            «pmPure» («tyDfd» x4)
          else
            if (Const.eq («tySort» x4) (leaf 0)).label ≠ 0 then
              «pmBind» («typePattern» x0 x1) (fun (x5 : T) => «objEq» x4 x5)
            else
              if («or»
                (Const.eq (Const.label x1) (leaf 0))
                («not»
                  (Const.eq
                    («length» (Const.children x3))
                    («length» (Const.children x1))))).label ≠ 0 then
                «pmFail»
              else
                «pmBind»
                  («bridgeKids» x2 (Const.children x3))
                  (fun (x5 : T) =>
                    «pmPure» («cCong» («tyDfd» x4) (Const.children x5)))));
    x3

def «bridge» :=
  fun (x0 : List T) (x1 : T) (x2 : T) =>
    let x3 : T →
      T → T := Const.para (α := T → T → T → T) («bridgeStep» x0) x1 x2;
    x3

def «applyRule» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T →
      T →
        T := «pmBind»
      («pmGuard»
        («not»
          («anyT»
            (fun (x2 : T) => Const.eq (Const.label x1) x2)
            («rwAvoid» x0))))
      (fun (_ : T) =>
        «pmBind»
          («srcSeq» («rwSrc» x0))
          (fun (x3 : T) =>
            let x4 : T := (if («rwFlip» x0).label ≠ 0 then
              «eqRhs» («seqConcl» x3)
            else
              «eqLhs» («seqConcl» x3));
            let x5 : T := (if («rwFlip» x0).label ≠ 0 then
              «eqLhs» («seqConcl» x3)
            else
              «eqRhs» («seqConcl» x3));
            «pmBind»
              «pmGet»
              (fun (x6 : T) =>
                let x7 : T := «matchPat»
                  («stSig» x6)
                  («seqCtx» x3)
                  x4
                  x1
                  («matchSt»
                    (Const.node (leaf 0) («mapT» (fun (_ : T) => «none») («seqCtx» x3)))
                    (Const.node (leaf 0) ([] : List T)));
                if («isSome» x7).label ≠ 0 then
                  let x8 : T := «get» x7;
                  let x9 : T := «allSomeT» («msSigma» x8);
                  if («isSome» x9).label ≠ 0 then
                    let x10 : List T := Const.children («get» x9);
                    «pmBind»
                      («pmMapM» «typeTerm» x10)
                      (fun (x11 : T) =>
                        let x12 : List T := Const.children x11;
                        «pmBind»
                          («pmMapM»
                            (fun (x13 : T) =>
                              «pmBind»
                                («typePattern» x12 («at» (Const.children x13) (leaf 0)))
                                (fun (x14 : T) =>
                                  «pmBind»
                                    («typeTerm» («at» (Const.children x13) (leaf 1)))
                                    (fun (x15 : T) => «objEq» x14 x15)))
                            («msObjs» x8))
                          (fun (_ : T) =>
                            «pmBind»
                              («bridge» x12 x4 x1)
                              (fun (x14 : T) =>
                                «pmBind»
                                  («pmMapM» («proveHyp» «typePattern» x12) («seqHyps» x3))
                                  (fun (x15 : T) =>
                                    let x16 : T := «srcCert»
                                      («rwSrc» x0)
                                      x10
                                      («mapT» «tyDfd» x12)
                                      (Const.children x15);
                                    «pmPure»
                                      (Const.node
                                        (leaf 0)
                                        («l2»
                                          («phSubst» x10 x5)
                                          («cTrans»
                                            x14
                                            (if («rwFlip» x0).label ≠ 0 then
                                              «cSymm» x16
                                            else
                                              x16))))))))
                  else
                    «pmFail»
                else
                  «pmFail»)));
    x2

def «firstRule» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T →
      T →
        T := Const.foldr
      (α := T)
      (β := T → T → T)
      (fun (x2 : T) (x3 : T → T → T) => «pmOr» («applyRule» x2 x1) x3)
      «pmFail»
      x0;
    x2

def «assocLeft» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (if («and»
      (Const.eq (Const.label x0) (leaf 4))
      (Const.eq («length» (Const.children x0)) (leaf 2))).label ≠ 0 then
      let x1 : T := «at» (Const.children x0) (leaf 0);
      let x2 : T := «at» (Const.children x0) (leaf 1);
      if («and»
        (Const.eq (Const.label x2) (leaf 4))
        (Const.eq («length» (Const.children x2)) (leaf 2))).label ≠ 0 then
        let x3 : T := «at» (Const.children x2) (leaf 0);
        let x4 : T := «at» (Const.children x2) (leaf 1);
        «pmBind»
          («typeTerm» x0)
          (fun (x5 : T) =>
            «pmBind»
              («typeTerm» x1)
              (fun (x6 : T) =>
                «pmBind»
                  («typeTerm» x3)
                  (fun (x7 : T) =>
                    «pmBind»
                      («typeTerm» x4)
                      (fun (x8 : T) =>
                        «pmPure»
                          (Const.node
                            (leaf 0)
                            («l4»
                              x1
                              x3
                              x4
                              («cAx»
                                (leaf 7)
                                («l3» x1 x3 x4)
                                («l3» («tyDfd» x6) («tyDfd» x7) («tyDfd» x8))
                                («single» («tyDfd» x5)))))))))
      else
        «pmFail»
    else
      «pmFail»);
    x1

def «rewriteRoot» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T →
      T →
        T := «pmOr»
      («firstRule» x0 x1)
      («pmBind»
        («assocLeft» x1)
        (fun (x2 : T) =>
          let x3 : T := «at» (Const.children x2) (leaf 0);
          let x4 : T := «at» (Const.children x2) (leaf 1);
          let x5 : T := «at» (Const.children x2) (leaf 2);
          let x6 : T := «at» (Const.children x2) (leaf 3);
          «pmBind»
            («firstRule» x0 («comp» x3 x4))
            (fun (x7 : T) =>
              «pmBind»
                («typeTerm» («comp» («comp» x3 x4) x5))
                (fun (x8 : T) =>
                  «pmBind»
                    («typeTerm» x5)
                    (fun (x9 : T) =>
                      «pmPure»
                        (Const.node
                          (leaf 0)
                          («l2»
                            («comp» («at» (Const.children x7) (leaf 0)) x5)
                            («cTrans»
                              x6
                              («cCong»
                                («tyDfd» x8)
                                («l2» («at» (Const.children x7) (leaf 1)) («tyDfd» x9)))))))))));
    x2

def «lookupNf» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «some» (Const.node (leaf 0) («l2» («tableFind» («stNfs» x2) x0) x2)));
    x1

def «memoizeNf» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T →
      T →
        T := «pmBind»
      (if (Const.equal x0 x1).label ≠ 0 then
        «pmPure» x2
      else
        «addLemma» («eqn» x0 x1) x2)
      (fun (x3 : T) (_ : T) (x5 : T) =>
        «some»
          (Const.node
            (leaf 0)
            («l2»
              (Const.node (leaf 0) («l2» x1 x3))
              («withNfs»
                x5
                («tableInsert»
                  («stNfs» x5)
                  x0
                  (Const.node (leaf 0) («l2» x1 x3)))))));
    x3

def «normStepP» :=
  fun (x0 : List T)
    (x1 : T → T → T → T)
    (x2 : T)
    (x3 : List (T → T → T)) =>
    let x4 : T →
      T →
        T := «pmBind»
      («lookupNf» x2)
      (fun (x4 : T) =>
        if («isSome» x4).label ≠ 0 then
          «pmPure» («get» x4)
        else
          «pmBind»
            («typeTerm» x2)
            (fun (x5 : T) =>
              if (Const.eq («tySort» x5) (leaf 0)).label ≠ 0 then
                «pmPure» (Const.node (leaf 0) («l2» («tyLo» x5) («tyLoC» x5)))
              else
                if (Const.eq (Const.label x2) (leaf 0)).label ≠ 0 then
                  «pmPure» (Const.node (leaf 0) («l2» x2 («tyDfd» x5)))
                else
                  «pmBind»
                    («pmSeq» x3)
                    (fun (x6 : T) =>
                      let x7 : List T := Const.children x6;
                      let x8 : T := Const.node
                        (Const.label x2)
                        («mapT» (fun (x8 : T) => «at» (Const.children x8) (leaf 0)) x7);
                      let x9 : T := (if (Const.equal x8 x2).label ≠ 0 then
                        «tyDfd» x5
                      else
                        «cCong»
                          («tyDfd» x5)
                          («mapT» (fun (x9 : T) => «at» (Const.children x9) (leaf 1)) x7));
                      «pmBind»
                        («pmOr»
                          («pmBind»
                            («rewriteRoot» x0 x8)
                            (fun (x10 : T) => «pmPure» («some» x10)))
                          («pmPure» «none»))
                        (fun (x10 : T) =>
                          if («isSome» x10).label ≠ 0 then
                            let x11 : T := «get» x10;
                            «pmBind»
                              (x1 («at» (Const.children x11) (leaf 0)))
                              (fun (x12 : T) =>
                                «memoizeNf»
                                  x2
                                  («at» (Const.children x12) (leaf 0))
                                  («cTrans»
                                    x9
                                    («cTrans»
                                      («at» (Const.children x11) (leaf 1))
                                      («at» (Const.children x12) (leaf 1)))))
                          else
                            «memoizeNf» x2 x8 x9))));
    x4

def «normalizers» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T →
      T →
        T →
          T := Const.iter
      (α := T → T → T → T)
      (fun (x2 : T → T → T → T) (x3 : T) =>
        Const.para (α := T → T → T) («normStepP» x0 x2) x3)
      (fun (_ : T) => «pmFail»)
      x1;
    x2

def «pNormalize» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T → T → T := «normalizers» x0 (leaf 64) x1; x2

def «beforeTerminal» := «length» «categoryAxioms»

def «beforeProduct» :=
  Const.add «beforeTerminal» («length» «terminalAxioms»)

def «beforeExponential» :=
  Const.add
    «beforeProduct»
    (Const.add
      («length» «productAxioms»)
      (Const.add
        («length» «equalizerAxioms»)
        (Const.add
          («length» «initialAxioms»)
          (Const.add
            («length» «coproductAxioms»)
            («length» «coequalizerAxioms»)))))

def «beforeNat» :=
  Const.add
    «beforeExponential»
    (Const.add
      («length» «exponentialAxioms»)
      («length» «classifierAxioms»))

def «beforeList» := Const.add «beforeNat» («length» «natAxioms»)

def «pInst» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T →
      T →
        T := «pmBind»
      («srcSeq» x0)
      (fun (x2 : T) =>
        «pmBind»
          («pmMapM» «typeTerm» x1)
          (fun (x3 : T) =>
            let x4 : List T := Const.children x3;
            «pmBind»
              («pmMapM» («proveHyp» «typePattern» x4) («seqHyps» x2))
              (fun (x5 : T) =>
                «pmPure»
                  (Const.node
                    (leaf 0)
                    («l2»
                      («eqSubst» x1 («seqConcl» x2))
                      («srcCert» x0 x1 («mapT» «tyDfd» x4) (Const.children x5)))))));
    x2

def «etaExpand» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := «pmBind»
      («typeTerm» x0)
      (fun (x1 : T) =>
        let x2 : T := «tyHi» x1;
        if («and»
          (Const.eq (Const.label x2) (leaf 7))
          (Const.eq («length» (Const.children x2)) (leaf 2))).label ≠ 0 then
          «pmBind»
            («pInst»
              («srcAx» (Const.add «beforeProduct» (leaf 11)))
              («l3»
                x0
                («at» (Const.children x2) (leaf 0))
                («at» (Const.children x2) (leaf 1))))
            (fun (x3 : T) =>
              «pmPure»
                (Const.node
                  (leaf 0)
                  («l2»
                    («eqLhs» («at» (Const.children x3) (leaf 0)))
                    («cSymm» («at» (Const.children x3) (leaf 1))))))
        else
          «pmFail»);
    x1

def «rwAx» :=
  fun (x0 : T) =>
    let x1 : T := «rwRule»
      («srcAx» x0)
      (leaf 0)
      (Const.node (leaf 0) ([] : List T));
    x1

def «rwThm» :=
  fun (x0 : T) =>
    let x1 : T := «rwRule»
      («srcThm» x0)
      (leaf 0)
      (Const.node (leaf 0) ([] : List T));
    x1

def «deltaRule» :=
  fun (x0 : T) => let x1 : T := «rwAx» («defAxIdx» x0); x1

def «pByNorm» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T →
      T →
        T := «pmBind»
      («pNormalize» x0 («eqLhs» x1))
      (fun (x2 : T) =>
        «pmBind»
          («pNormalize» x0 («eqRhs» x1))
          (fun (x3 : T) =>
            «pmBind»
              («pmGuard»
                (Const.equal
                  («at» (Const.children x2) (leaf 0))
                  («at» (Const.children x3) (leaf 0))))
              (fun (_ : T) =>
                «pmPure»
                  («cTrans»
                    («at» (Const.children x2) (leaf 1))
                    («cSymm» («at» (Const.children x3) (leaf 1)))))));
    x2

def «proveSeq» :=
  fun (x0 : T) (x1 : T → T → T) (x2 : List T) (x3 : T) (x4 : List T) =>
    let x5 : T := «bindO»
      («pmRun»
        («scope»
          (Const.node (leaf 0) («seqCtx» x0))
          (Const.node (leaf 0) («seqHyps» x0)))
        x4
        x1
        x2
        x3)
      (fun (x5 : T) =>
        let x6 : List T := Const.children («at» (Const.children x5) (leaf 1));
        «some»
          (Const.node
            (leaf 0)
            («l2»
              («length» x6)
              (Const.node
                (leaf 0)
                («append»
                  x6
                  («single»
                    (Const.node
                      (leaf 0)
                      («l2» x0 («at» (Const.children x5) (leaf 0))))))))));
    x5

def «normalizeThm» :=
  fun (x0 : List T) (x1 : T) (x2 : List T) (x3 : T) (x4 : List T) =>
    let x5 : T := «bindO»
      («nth» x4 x1)
      (fun (x5 : T) =>
        let x6 : T := «at» (Const.children x5) (leaf 0);
        let x7 : T := «scope»
          (Const.node (leaf 0) («seqCtx» x6))
          (Const.node (leaf 0) («seqHyps» x6));
        «bindO»
          («pmRun» x7 x4 («pNormalize» x0 («eqLhs» («seqConcl» x6))) x2 x3)
          (fun (x8 : T) =>
            let x9 : T := «at» (Const.children x8) (leaf 0);
            let x10 : List
              T := Const.children («at» (Const.children x8) (leaf 1));
            «some»
              (Const.node
                (leaf 0)
                («l2»
                  («length» x10)
                  (Const.node
                    (leaf 0)
                    («append»
                      x10
                      («single»
                        (Const.node
                          (leaf 0)
                          («l2»
                            («scSeq»
                              x7
                              («eqn» («at» (Const.children x9) (leaf 0)) («eqRhs» («seqConcl» x6))))
                            («cTrans»
                              («cSymm» («at» (Const.children x9) (leaf 1)))
                              («scCite» x7 x1)))))))))));
    x5

def «instBy» :=
  fun (x0 : List T) (x1 : T) (x2 : List T) =>
    let x3 : T →
      T →
        T := «pmBind»
      («srcSeq» x1)
      (fun (x3 : T) =>
        «pmBind»
          («pmMapM» «typeTerm» x2)
          (fun (x4 : T) =>
            let x5 : List T := Const.children x4;
            «pmBind»
              («pmMapM»
                (fun (x6 : T) =>
                  «pmOr»
                    («proveHyp» «typePattern» x5 x6)
                    («pByNorm» x0 («eqSubst» x2 x6)))
                («seqHyps» x3))
              (fun (x6 : T) =>
                «pmPure»
                  (Const.node
                    (leaf 0)
                    («l2»
                      («eqSubst» x2 («seqConcl» x3))
                      («srcCert» x1 x2 («mapT» «tyDfd» x5) (Const.children x6)))))));
    x3

def «congStep» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List (T → T → T → T)) =>
    let x4 : T →
      T →
        T →
          T := (fun (x4 : T) =>
      «pmBind»
        («typeTerm» x2)
        (fun (x5 : T) =>
          if (Const.equal x2 x4).label ≠ 0 then
            «pmPure» («tyDfd» x5)
          else
            if («and»
              (Const.equal x2 («eqLhs» x0))
              (Const.equal x4 («eqRhs» x0))).label ≠ 0 then
              «pmPure» x1
            else
              if (Const.eq («tySort» x5) (leaf 0)).label ≠ 0 then
                «pmBind» («typeTerm» x4) (fun (x6 : T) => «objEq» x5 x6)
              else
                if («or»
                  (Const.eq (Const.label x2) (leaf 0))
                  («or»
                    («not» (Const.eq (Const.label x4) (Const.label x2)))
                    («not»
                      (Const.eq
                        («length» (Const.children x4))
                        («length» (Const.children x2)))))).label ≠ 0 then
                  «pmFail»
                else
                  «pmBind»
                    («bridgeKids» x3 (Const.children x4))
                    (fun (x6 : T) =>
                      «pmPure» («cCong» («tyDfd» x5) (Const.children x6)))));
    x4

def «congBy» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T →
      T → T := Const.para (α := T → T → T → T) («congStep» x0 x1) x2 x3;
    x4

def «natRecUniq» :=
  fun (x0 : List T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T →
      T →
        T := «pmBind»
      («instBy»
        x0
        («srcAx» (Const.add «beforeNat» (leaf 12)))
        («l3» x1 x2 x3))
      (fun (x4 : T) => «pmPure» («at» (Const.children x4) (leaf 1)));
    x4

def «listRecUniq» :=
  fun (x0 : List T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T →
      T →
        T := «pmBind»
      («instBy»
        x0
        («srcAx» (Const.add «beforeList» (leaf 13)))
        («l4» x1 x2 x3 x4))
      (fun (x5 : T) => «pmPure» («at» (Const.children x5) (leaf 1)));
    x5

def «byNatInduction» :=
  fun (x0 : List T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T →
      T →
        T := «pmBind»
      («natRecUniq» x0 x1 x2 («eqLhs» x3))
      (fun (x4 : T) =>
        «pmBind»
          («natRecUniq» x0 x1 x2 («eqRhs» x3))
          (fun (x5 : T) => «pmPure» («cTrans» x4 («cSymm» x5))));
    x4

def «byListInduction» :=
  fun (x0 : List T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T →
      T →
        T := «pmBind»
      («listRecUniq» x0 x1 x2 x3 («eqLhs» x4))
      (fun (x5 : T) =>
        «pmBind»
          («listRecUniq» x0 x1 x2 x3 («eqRhs» x4))
          (fun (x6 : T) => «pmPure» («cTrans» x5 («cSymm» x6))));
    x5

def «byListParamInduction» :=
  fun (x0 : List T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T →
      T →
        T := «pmBind»
      («typeTerm» («eqLhs» x4))
      (fun (x5 : T) =>
        let x6 : T := «tyLo» x5;
        if («and»
          (Const.eq (Const.label x6) (leaf 7))
          (Const.eq («length» (Const.children x6)) (leaf 2))).label ≠ 0 then
          let x7 : T := «at» (Const.children x6) (leaf 0);
          let x8 : T := «at» (Const.children x6) (leaf 1);
          let x9 : T := «tyHi» x5;
          let x10 : T := «exp» x8 x9;
          let x11 : T := «prod» x1 x10;
          let x12 : T := «curry» «one» x8 («comp» x2 («cSnd» «one» x8));
          let x13 : T := «curry»
            x11
            x8
            («comp»
              x3
              («cPair»
                («cPair»
                  («comp» («cFst» x1 x10) («cFst» x11 x8))
                  («comp»
                    («ev» x8 x9)
                    («cPair» («comp» («cSnd» x1 x10) («cFst» x11 x8)) («cSnd» x11 x8))))
                («cSnd» x11 x8)));
          let x14 : T := «curry» x7 x8 («eqLhs» x4);
          let x15 : T := «curry» x7 x8 («eqRhs» x4);
          «pmBind»
            («byListInduction» x0 x1 x12 x13 («eqn» x14 x15))
            (fun (x16 : T) =>
              «pmBind»
                («pInst»
                  («srcAx» (Const.add «beforeExponential» (leaf 7)))
                  («l3» x7 x8 («eqLhs» x4)))
                (fun (x17 : T) =>
                  «pmBind»
                    («pInst»
                      («srcAx» (Const.add «beforeExponential» (leaf 7)))
                      («l3» x7 x8 («eqRhs» x4)))
                    (fun (x18 : T) =>
                      «pmBind»
                        («congBy»
                          («eqn» x14 x15)
                          x16
                          («eqLhs» («at» (Const.children x17) (leaf 0)))
                          («eqLhs» («at» (Const.children x18) (leaf 0))))
                        (fun (x19 : T) =>
                          «pmPure»
                            («cTrans»
                              («cSymm» («at» (Const.children x17) (leaf 1)))
                              («cTrans» x19 («at» (Const.children x18) (leaf 1))))))))
        else
          «pmFail»);
    x5

def «baseRules» :=
  ((«rwRule»
    («srcAx» (leaf 7))
    (leaf 1)
    (Const.node (leaf 0) ([] : List T))) ::
    ((«rwAx» (leaf 10)) ::
      ((«rwAx» (leaf 11)) ::
        ((«rwAx» (Const.add «beforeProduct» (leaf 9))) ::
          ((«rwAx» (Const.add «beforeProduct» (leaf 10))) ::
            ((«rwAx» (Const.add «beforeProduct» (leaf 11))) ::
              ((«rwRule»
                («srcAx» (Const.add «beforeTerminal» (leaf 3)))
                (leaf 0)
                (Const.node (leaf 0) («l2» (leaf 3) (leaf 6)))) ::
                ((«rwAx» (Const.add «beforeNat» (leaf 10))) ::
                  ((«rwAx» (Const.add «beforeNat» (leaf 11))) ::
                    («l2»
                      («rwAx» (Const.add «beforeList» (leaf 11)))
                      («rwAx» (Const.add «beforeList» (leaf 12)))))))))))))

def «compPairSeq» :=
  «mkSeq»
    («l3» (leaf 1) (leaf 1) (leaf 1))
    («l2»
      («eqn» («dom» («x» (leaf 1))) («dom» («x» (leaf 0))))
      («eqn» («cod» («x» (leaf 2))) («dom» («x» (leaf 0)))))
    («eqn»
      («comp» («cPair» («x» (leaf 0)) («x» (leaf 1))) («x» (leaf 2)))
      («cPair»
        («comp» («x» (leaf 0)) («x» (leaf 2)))
        («comp» («x» (leaf 1)) («x» (leaf 2)))))

def «pairFstSndSeq» :=
  «mkSeq»
    («l2» (leaf 0) (leaf 0))
    ([] : List T)
    («eqn»
      («cPair»
        («cFst» («x» (leaf 0)) («x» (leaf 1)))
        («cSnd» («x» (leaf 0)) («x» (leaf 1))))
      («idt» («prod» («x» (leaf 0)) («x» (leaf 1)))))

def «evCurrySeq» :=
  «mkSeq»
    («l5» (leaf 0) (leaf 0) (leaf 1) (leaf 1) (leaf 1))
    («l4»
      («eqn» («dom» («x» (leaf 2))) («prod» («x» (leaf 0)) («x» (leaf 1))))
      («eqn» («cod» («x» (leaf 3))) («x» (leaf 0)))
      («eqn» («cod» («x» (leaf 4))) («x» (leaf 1)))
      («eqn» («dom» («x» (leaf 4))) («dom» («x» (leaf 3)))))
    («eqn»
      («comp»
        («ev» («x» (leaf 1)) («cod» («x» (leaf 2))))
        («cPair»
          («comp»
            («curry» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))
            («x» (leaf 3)))
          («x» (leaf 4))))
      («comp» («x» (leaf 2)) («cPair» («x» (leaf 3)) («x» (leaf 4)))))

def «evCurry0Seq» :=
  «mkSeq»
    («l4» (leaf 0) (leaf 0) (leaf 1) (leaf 1))
    («l3»
      («eqn» («dom» («x» (leaf 2))) («prod» («x» (leaf 0)) («x» (leaf 1))))
      («eqn» («cod» («x» (leaf 3))) («x» (leaf 1)))
      («eqn» («dom» («x» (leaf 3))) («x» (leaf 0))))
    («eqn»
      («comp»
        («ev» («x» (leaf 1)) («cod» («x» (leaf 2))))
        («cPair»
          («curry» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))
          («x» (leaf 3))))
      («comp»
        («x» (leaf 2))
        («cPair» («idt» («x» (leaf 0))) («x» (leaf 3)))))

def «curryNatSeq» :=
  «mkSeq»
    («l4» (leaf 0) (leaf 0) (leaf 1) (leaf 1))
    («l2»
      («eqn» («dom» («x» (leaf 2))) («prod» («x» (leaf 0)) («x» (leaf 1))))
      («eqn» («cod» («x» (leaf 3))) («x» (leaf 0))))
    («eqn»
      («comp»
        («curry» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))
        («x» (leaf 3)))
      («curry»
        («dom» («x» (leaf 3)))
        («x» (leaf 1))
        («comp»
          («x» (leaf 2))
          («prodMapLeft» («x» (leaf 3)) («x» (leaf 1))))))

def «bangOneSeq» :=
  «mkSeq»
    ([] : List T)
    ([] : List T)
    («eqn» («bang» «one») («idt» «one»))

def «seqLhs» :=
  fun (x0 : T) => let x1 : T := «eqLhs» («seqConcl» x0); x1

def «seqRhs» :=
  fun (x0 : T) => let x1 : T := «eqRhs» («seqConcl» x0); x1

def «compPairProof» :=
  «pmBind»
    («etaExpand» («seqLhs» «compPairSeq»))
    (fun (x0 : T) =>
      «pmBind»
        («pNormalize» «baseRules» («at» (Const.children x0) (leaf 0)))
        (fun (x1 : T) =>
          «pmBind»
            («pmGuard»
              (Const.equal
                («at» (Const.children x1) (leaf 0))
                («seqRhs» «compPairSeq»)))
            (fun (_ : T) =>
              «pmPure»
                («cTrans»
                  («at» (Const.children x0) (leaf 1))
                  («at» (Const.children x1) (leaf 1))))))

def «pairFstSndProof» :=
  let x0 : T := «prod» («x» (leaf 0)) («x» (leaf 1));
  «pmBind»
    («pInst»
      («srcAx» (Const.add «beforeProduct» (leaf 11)))
      («l3» («idt» x0) («x» (leaf 0)) («x» (leaf 1))))
    (fun (x1 : T) =>
      «pmBind»
        («pNormalize»
          «baseRules»
          («eqLhs» («at» (Const.children x1) (leaf 0))))
        (fun (x2 : T) =>
          «pmBind»
            («pmGuard»
              (Const.equal
                («at» (Const.children x2) (leaf 0))
                («seqLhs» «pairFstSndSeq»)))
            (fun (_ : T) =>
              «pmPure»
                («cTrans»
                  («cSymm» («at» (Const.children x2) (leaf 1)))
                  («at» (Const.children x1) (leaf 1))))))

def «evCurryProof» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (let x1 : List T := «append» «baseRules» («single» («rwThm» x0));
              «pmBind»
                («pInst»
                  («srcAx» (Const.add «beforeExponential» (leaf 7)))
                  («l3» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2))))
                (fun (x2 : T) =>
                  let x3 : T := «cPair» («x» (leaf 3)) («x» (leaf 4));
                  let x4 : T := «comp» («eqLhs» («at» (Const.children x2) (leaf 0))) x3;
                  «pmBind»
                    («pNormalize» x1 x4)
                    (fun (x5 : T) =>
                      «pmBind»
                        («pNormalize» x1 («seqLhs» «evCurrySeq»))
                        (fun (x6 : T) =>
                          «pmBind»
                            («pmGuard»
                              (Const.equal
                                («at» (Const.children x5) (leaf 0))
                                («at» (Const.children x6) (leaf 0))))
                            (fun (_ : T) =>
                              «pmBind»
                                («typeTerm» x4)
                                (fun (x8 : T) =>
                                  «pmBind»
                                    («typeTerm» x3)
                                    (fun (x9 : T) =>
                                      «pmPure»
                                        («cTrans»
                                          («cTrans»
                                            («at» (Const.children x6) (leaf 1))
                                            («cSymm» («at» (Const.children x5) (leaf 1))))
                                          («cCong»
                                            («tyDfd» x8)
                                            («l2»
                                              («at» (Const.children x2) (leaf 1))
                                              («tyDfd» x9)))))))))));
    x1

def «evCurry0Proof» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := «pmBind»
      («pInst»
        («srcThm» x0)
        («l5»
          («x» (leaf 0))
          («x» (leaf 1))
          («x» (leaf 2))
          («idt» («x» (leaf 0)))
          («x» (leaf 3))))
      (fun (x1 : T) =>
        let x2 : T := «at» (Const.children x1) (leaf 0);
        «pmBind»
          («pNormalize» «baseRules» («eqLhs» x2))
          (fun (x3 : T) =>
            «pmBind»
              («pmGuard»
                («and»
                  (Const.equal
                    («at» (Const.children x3) (leaf 0))
                    («seqLhs» «evCurry0Seq»))
                  (Const.equal («eqRhs» x2) («seqRhs» «evCurry0Seq»))))
              (fun (_ : T) =>
                «pmPure»
                  («cTrans»
                    («cSymm» («at» (Const.children x3) (leaf 1)))
                    («at» (Const.children x1) (leaf 1))))));
    x1

def «curryNatProof» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T →
      T →
        T := (let x2 : List
                T := «append» «baseRules» («l2» («rwThm» x0) («rwThm» x1));
              let x3 : T := «seqLhs» «curryNatSeq»;
              «pmBind»
                («pInst»
                  («srcAx» (Const.add «beforeExponential» (leaf 8)))
                  («l4»
                    («dom» («x» (leaf 3)))
                    («x» (leaf 1))
                    («cod» («x» (leaf 2)))
                    x3))
                (fun (x4 : T) =>
                  «pmBind»
                    («pNormalize» x2 («eqLhs» («at» (Const.children x4) (leaf 0))))
                    (fun (x5 : T) =>
                      «pmBind»
                        («pNormalize» x2 («seqRhs» «curryNatSeq»))
                        (fun (x6 : T) =>
                          «pmBind»
                            («pmGuard»
                              (Const.equal
                                («at» (Const.children x5) (leaf 0))
                                («at» (Const.children x6) (leaf 0))))
                            (fun (_ : T) =>
                              «pmPure»
                                («cTrans»
                                  («cSymm» («at» (Const.children x4) (leaf 1)))
                                  («cTrans»
                                    («at» (Const.children x5) (leaf 1))
                                    («cSymm» («at» (Const.children x6) (leaf 1))))))))));
    x2

def «bangOneProof» :=
  «pmBind»
    («pInst»
      («srcAx» (Const.add «beforeTerminal» (leaf 3)))
      («single» («idt» «one»)))
    (fun (x0 : T) =>
      «pmBind»
        («pNormalize»
          «baseRules»
          («eqRhs» («at» (Const.children x0) (leaf 0))))
        (fun (x1 : T) =>
          «pmBind»
            («pmGuard»
              (Const.equal («at» (Const.children x1) (leaf 0)) («bang» «one»)))
            (fun (_ : T) =>
              «pmPure»
                («cSymm»
                  («cTrans»
                    («at» (Const.children x0) (leaf 1))
                    («at» (Const.children x1) (leaf 1)))))))

def «libraryWith» :=
  fun (x0 : T) =>
    let x1 : T := «bindO»
      («proveSeq»
        «compPairSeq»
        «compPairProof»
        ([] : List T)
        x0
        ([] : List T))
      (fun (x1 : T) =>
        let x2 : T := «at» (Const.children x1) (leaf 0);
        «bindO»
          («proveSeq»
            «pairFstSndSeq»
            «pairFstSndProof»
            ([] : List T)
            x0
            (Const.children («at» (Const.children x1) (leaf 1))))
          (fun (x3 : T) =>
            let x4 : T := «at» (Const.children x3) (leaf 0);
            «bindO»
              («proveSeq»
                «evCurrySeq»
                («evCurryProof» x2)
                ([] : List T)
                x0
                (Const.children («at» (Const.children x3) (leaf 1))))
              (fun (x5 : T) =>
                let x6 : T := «at» (Const.children x5) (leaf 0);
                «bindO»
                  («proveSeq»
                    «evCurry0Seq»
                    («evCurry0Proof» x6)
                    ([] : List T)
                    x0
                    (Const.children («at» (Const.children x5) (leaf 1))))
                  (fun (x7 : T) =>
                    let x8 : T := «at» (Const.children x7) (leaf 0);
                    «bindO»
                      («proveSeq»
                        «curryNatSeq»
                        («curryNatProof» x2 x6)
                        ([] : List T)
                        x0
                        (Const.children («at» (Const.children x7) (leaf 1))))
                      (fun (x9 : T) =>
                        let x10 : T := «at» (Const.children x9) (leaf 0);
                        «bindO»
                          («proveSeq»
                            «bangOneSeq»
                            «bangOneProof»
                            ([] : List T)
                            x0
                            (Const.children («at» (Const.children x9) (leaf 1))))
                          (fun (x11 : T) =>
                            «some»
                              (Const.node
                                (leaf 0)
                                («l2»
                                  (Const.node
                                    (leaf 0)
                                    («l6» x2 x4 x6 x8 x10 («at» (Const.children x11) (leaf 0))))
                                  («at» (Const.children x11) (leaf 1))))))))));
    x1

def «libRules» :=
  fun (x0 : T) =>
    let x1 : List
      T := «append»
      «baseRules»
      («l5»
        («rwThm» («at» (Const.children x0) (leaf 0)))
        («rwThm» («at» (Const.children x0) (leaf 1)))
        («rwThm» («at» (Const.children x0) (leaf 4)))
        («rwThm» («at» (Const.children x0) (leaf 3)))
        («rwThm» («at» (Const.children x0) (leaf 5))));
    x1

end GebMirror.Metalogic

end
