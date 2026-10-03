module

public import GebMirror.Metalogic.Tactics

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «Combinator.cHyp» :=
  fun (x0 : T) =>
    let x1 : T := Const.node
      (leaf 0)
      («Prelude.single» (Const.node x0 ([] : List T)));
    x1

def «Combinator.cRefl» :=
  fun (x0 : T) =>
    let x1 : T := Const.node
      (leaf 1)
      («Prelude.single» (Const.node x0 ([] : List T)));
    x1

def «Combinator.cSymm» :=
  fun (x0 : T) =>
    let x1 : T := Const.node (leaf 2) («Prelude.single» x0); x1

def «Combinator.cTrans» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.node (leaf 3) («Theory.l2» x0 x1); x2

def «Combinator.cCong» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.node (leaf 4) (x0 :: x1); x2

def «Combinator.cStrict» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.node
      (leaf 5)
      («Theory.l2» (Const.node x0 ([] : List T)) x1);
    x2

def «Combinator.cAx» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : List T) =>
    let x4 : T := Const.node
      (leaf 6)
      ((Const.node x0 ([] : List T)) ::
        («Prelude.append» x1 («Prelude.append» x2 x3)));
    x4

def «Combinator.cThm» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : List T) =>
    let x4 : T := Const.node
      (leaf 8)
      ((Const.node x0 ([] : List T)) ::
        («Prelude.append» x1 («Prelude.append» x2 x3)));
    x4

def «Combinator.scope» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator.scCtx» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1); Const.children x2);
    x1

def «Combinator.scHyps» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let x3 : T := Const.child x1 (leaf 1); Const.children x3);
    x1

def «Combinator.scSeq» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «PartialHorn.mkSeq»
      («Combinator.scCtx» x0)
      («Combinator.scHyps» x0)
      x1;
    x2

def «Combinator.scCite» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := «Prelude.length» («Combinator.scCtx» x0);
                   «Combinator.cThm»
                     x1
                     («Base.mapT» «PartialHorn.phVar» («Base.range» x2))
                     («Base.mapT» «Combinator.cRefl» («Base.range» x2))
                     («Base.mapT»
                       «Combinator.cHyp»
                       («Base.range» («Prelude.length» («Combinator.scHyps» x0)))));
    x2

def «Combinator.pst» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    Const.node
      (leaf 0)
      (x0 :: (x1 :: (x2 :: (x3 :: (x4 :: (x5 :: ([] : List T)))))))

def «Combinator.stDev» :=
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

def «Combinator.stMemo» :=
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

def «Combinator.stNfs» :=
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

def «Combinator.stDefs» :=
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

def «Combinator.stSig» :=
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

def «Combinator.stInfer» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let _ : T := Const.child x1 (leaf 3);
                   let _ : T := Const.child x1 (leaf 4);
                   let x7 : T := Const.child x1 (leaf 5); x7);
    x1

def «Combinator.withDev» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := (let x2 : T := x0;
                   let _ : T := Const.child x2 (leaf 0);
                   let x4 : T := Const.child x2 (leaf 1);
                   let x5 : T := Const.child x2 (leaf 2);
                   let x6 : T := Const.child x2 (leaf 3);
                   let x7 : T := Const.child x2 (leaf 4);
                   let x8 : T := Const.child x2 (leaf 5);
                   «Combinator.pst» (Const.node (leaf 0) x1) x4 x5 x6 x7 x8);
    x2

def «Combinator.withMemo» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := (let x2 : T := x0;
                   let x3 : T := Const.child x2 (leaf 0);
                   let _ : T := Const.child x2 (leaf 1);
                   let x5 : T := Const.child x2 (leaf 2);
                   let x6 : T := Const.child x2 (leaf 3);
                   let x7 : T := Const.child x2 (leaf 4);
                   let x8 : T := Const.child x2 (leaf 5);
                   «Combinator.pst» x3 (Const.node (leaf 0) x1) x5 x6 x7 x8);
    x2

def «Combinator.withNfs» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := (let x2 : T := x0;
                   let x3 : T := Const.child x2 (leaf 0);
                   let x4 : T := Const.child x2 (leaf 1);
                   let _ : T := Const.child x2 (leaf 2);
                   let x6 : T := Const.child x2 (leaf 3);
                   let x7 : T := Const.child x2 (leaf 4);
                   let x8 : T := Const.child x2 (leaf 5);
                   «Combinator.pst» x3 x4 (Const.node (leaf 0) x1) x6 x7 x8);
    x2

def «Combinator.tableFind» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        if (Const.equal
          («Prelude.at» (Const.children x2) (leaf 0))
          x1).label ≠ 0 then
          «Prelude.some» («Prelude.at» (Const.children x2) (leaf 1))
        else
          x3)
      «Prelude.none»
      x0;
    x2

def «Combinator.tableInsert» :=
  fun (x0 : List T) (x1 : T) (x2 : T) =>
    let x3 : List T := ((Const.node (leaf 0) («Theory.l2» x1 x2)) :: x0);
    x3

def «Combinator.pty» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) (x6 : T) =>
    Const.node
      (leaf 0)
      (x0 :: (x1 :: (x2 :: (x3 :: (x4 :: (x5 :: (x6 :: ([] : List T))))))))

def «Combinator.tyT» :=
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

def «Combinator.tySort» :=
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

def «Combinator.tyDfd» :=
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

def «Combinator.tyLo» :=
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

def «Combinator.tyLoC» :=
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

def «Combinator.tyHi» :=
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

def «Combinator.tyHiC» :=
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

def «Combinator.pmPure» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «Prelude.some» (Const.node (leaf 0) («Theory.l2» x0 x2)));
    x1

def «Combinator.pmFail» :=
  fun (_ : T) (_ : T) => let x2 : T := «Prelude.none»; x2

def «Combinator.pmBind» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      «Base.bindO»
        (x0 x2 x3)
        (fun (x4 : T) =>
          x1
            («Prelude.at» (Const.children x4) (leaf 0))
            x2
            («Prelude.at» (Const.children x4) (leaf 1))));
    x2

def «Combinator.pmOr» :=
  fun (x0 : T → T → T) (x1 : T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if («Prelude.isSome» x4).label ≠ 0 then x4 else x1 x2 x3);
    x2

def «Combinator.pmGet» :=
  fun (_ : T) (x1 : T) =>
    let x2 : T := «Prelude.some»
      (Const.node (leaf 0) («Theory.l2» x1 x1));
    x2

def «Combinator.pmRead» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prelude.some»
      (Const.node (leaf 0) («Theory.l2» x0 x1));
    x2

def «Combinator.pmSet» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (_ : T) =>
      «Prelude.some» (Const.node (leaf 0) («Theory.l2» (leaf 0) x0)));
    x1

def «Combinator.pmGuard» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      if (x0).label ≠ 0 then
        «Prelude.some» (Const.node (leaf 0) («Theory.l2» (leaf 0) x2))
      else
        «Prelude.none»);
    x1

def «Combinator.pmMapM» :=
  fun (x0 : T → T → T → T) (x1 : List T) =>
    let x2 : T →
      T →
        T := Const.foldr
      (α := T)
      (β := T → T → T)
      (fun (x2 : T) (x3 : T → T → T) =>
        «Combinator.pmBind»
          (x0 x2)
          (fun (x4 : T) =>
            «Combinator.pmBind»
              x3
              (fun (x5 : T) =>
                «Combinator.pmPure»
                  (Const.node (leaf 0) (x4 :: (Const.children x5))))))
      («Combinator.pmPure» (Const.node (leaf 0) ([] : List T)))
      x1;
    x2

def «Combinator.pmSeq» :=
  fun (x0 : List (T → T → T)) =>
    let x1 : T →
      T →
        T := Const.foldr
      (α := T → T → T)
      (β := T → T → T)
      (fun (x1 : T → T → T) (x2 : T → T → T) =>
        «Combinator.pmBind»
          x1
          (fun (x3 : T) =>
            «Combinator.pmBind»
              x2
              (fun (x4 : T) =>
                «Combinator.pmPure»
                  (Const.node (leaf 0) (x3 :: (Const.children x4))))))
      («Combinator.pmPure» (Const.node (leaf 0) ([] : List T)))
      x0;
    x1

def «Combinator.findIdxT» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : T := (Const.foldr
      (α := T)
      (β := T × T)
      (fun (x2 : T) (x3 : T × T) =>
        (Const.sub (x3).1 (leaf 1),
          if (x0 x2).label ≠ 0 then
            «Prelude.some» (Const.sub (x3).1 (leaf 1))
          else
            (x3).2))
      («Prelude.length» x1, «Prelude.none»)
      x1).2;
    x2

def «Combinator.axiomAt» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (if (Const.lt
      x0
      («Prelude.length» «Theory.axioms»)).label ≠ 0 then
      «Combinator.pmPure» («Prelude.at» «Theory.axioms» x0)
    else
      «Combinator.pmBind»
        «Combinator.pmGet»
        (fun (x1 : T) =>
          let x2 : T := Const.sub x0 («Prelude.length» «Theory.axioms»);
          let x3 : T := «Prelude.nth»
            («Combinator.stDefs» x1)
            (Const.div x2 (leaf 2));
          if («Prelude.isSome» x3).label ≠ 0 then
            let x4 : T := «Prelude.nth»
              («PartialHorn.pdAxioms»
                (Const.add («Prelude.length» «Theory.sig») (Const.div x2 (leaf 2)))
                («Prelude.get» x3))
              (Const.mod x2 (leaf 2));
            if («Prelude.isSome» x4).label ≠ 0 then
              «Combinator.pmPure» («Prelude.get» x4)
            else
              «Combinator.pmFail»
          else
            «Combinator.pmFail»));
    x1

def «Combinator.addLemma» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      «Prelude.some»
        (Const.node
          (leaf 0)
          («Theory.l2»
            («Combinator.scCite» x2 («Prelude.length» («Combinator.stDev» x3)))
            («Combinator.withDev»
              x3
              («Prelude.append»
                («Combinator.stDev» x3)
                («Prelude.single»
                  (Const.node
                    (leaf 0)
                    («Theory.l2» («Combinator.scSeq» x2 x0) x1))))))));
    x2

def «Combinator.lookup» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «Prelude.some»
        (Const.node
          (leaf 0)
          («Theory.l2»
            («Combinator.tableFind» («Combinator.stMemo» x2) x0)
            x2)));
    x1

def «Combinator.memoize» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «Prelude.some»
        (Const.node
          (leaf 0)
          («Theory.l2»
            (leaf 0)
            («Combinator.withMemo»
              x2
              («Combinator.tableInsert»
                («Combinator.stMemo» x2)
                («Combinator.tyT» x0)
                x0)))));
    x1

def «Combinator.memoRet» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := «Combinator.pmBind»
      («Combinator.memoize» x0)
      (fun (_ : T) => «Combinator.pmPure» x0);
    x1

def «Combinator.dfdCert» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      if («Combinator.stInfer» x3).label ≠ 0 then
        «Prelude.some»
          (Const.node
            (leaf 0)
            («Theory.l2» (Const.node (leaf 9) («Prelude.single» x0)) x3))
      else
        «Combinator.addLemma» («Theory.dfd» x0) x1 x2 x3);
    x2

def «Combinator.eqCert» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      if («Combinator.stInfer» x3).label ≠ 0 then
        «Prelude.some»
          (Const.node
            (leaf 0)
            («Theory.l2»
              (Const.node
                (leaf 10)
                («Theory.l2» («PartialHorn.eqLhs» x0) («PartialHorn.eqRhs» x0)))
              x3))
      else
        «Combinator.addLemma» x0 x1 x2 x3);
    x2

def «Combinator.objEq» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T →
      T →
        T := (fun (_ : T) (x3 : T) =>
      if («Prelude.and»
        (Const.eq («Combinator.tySort» x0) (leaf 0))
        («Prelude.and»
          (Const.eq («Combinator.tySort» x1) (leaf 0))
          (Const.equal
            («Combinator.tyLo» x0)
            («Combinator.tyLo» x1)))).label ≠ 0 then
        «Prelude.some»
          (Const.node
            (leaf 0)
            («Theory.l2»
              (if («Combinator.stInfer» x3).label ≠ 0 then
                Const.node
                  (leaf 10)
                  («Theory.l2» («Combinator.tyT» x0) («Combinator.tyT» x1))
              else
                «Combinator.cTrans»
                  («Combinator.tyLoC» x0)
                  («Combinator.cSymm» («Combinator.tyLoC» x1)))
              x3))
      else
        «Prelude.none»);
    x2

def «Combinator.proveHyp» :=
  fun (x0 : List T → T → T → T → T) (x1 : List T) (x2 : T) =>
    let x3 : T →
      T →
        T := «Combinator.pmBind»
      (x0 x1 («PartialHorn.eqLhs» x2))
      (fun (x3 : T) =>
        if (Const.equal
          («PartialHorn.eqLhs» x2)
          («PartialHorn.eqRhs» x2)).label ≠ 0 then
          «Combinator.pmPure» («Combinator.tyDfd» x3)
        else
          «Combinator.pmBind»
            (x0 x1 («PartialHorn.eqRhs» x2))
            (fun (x4 : T) => «Combinator.objEq» x3 x4));
    x3

def «Combinator.pBound» :=
  fun (x0 : List T → T → T → T → T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : T) =>
    let x5 : T →
      T →
        T := «Combinator.pmBind»
      («Combinator.axiomAt» x3)
      (fun (x5 : T) =>
        «Combinator.pmBind»
          («Combinator.pmMapM»
            (fun (x6 : T) =>
              if (Const.equal
                x6
                («Theory.dfd»
                  («PartialHorn.opVars» x2 («Prelude.length» x1)))).label ≠ 0 then
                «Combinator.pmPure» x4
              else
                «Combinator.proveHyp» x0 x1 x6)
            («PartialHorn.seqHyps» x5))
          (fun (x6 : T) =>
            let x7 : T := «Combinator.cAx»
              x3
              («Base.mapT» «Combinator.tyT» x1)
              («Base.mapT» «Combinator.tyDfd» x1)
              (Const.children x6);
            «Combinator.pmBind»
              (x0 x1 («PartialHorn.eqRhs» («PartialHorn.seqConcl» x5)))
              (fun (x8 : T) =>
                «Combinator.pmPure»
                  (Const.node
                    (leaf 0)
                    («Theory.l2»
                      («Combinator.tyLo» x8)
                      («Combinator.cTrans» x7 («Combinator.tyLoC» x8)))))));
    x5

def «Combinator.typeDefined» :=
  fun (x0 : List T → T → T → T → T) (x1 : T) (x2 : T) (x3 : List T) =>
    let x4 : T →
      T →
        T := «Combinator.pmBind»
      «Combinator.pmGet»
      (fun (x4 : T) =>
        let x5 : T := «Prelude.nth» («Combinator.stDefs» x4) x1;
        if («Prelude.isSome» x5).label ≠ 0 then
          let x6 : List T := «Base.mapT» «Combinator.tyT» x3;
          let x7 : T := «PartialHorn.phOp»
            (Const.add («Prelude.length» «Theory.sig») x1)
            x6;
          «Combinator.pmBind»
            (x0 x3 («PartialHorn.pdBody» («Prelude.get» x5)))
            (fun (x8 : T) =>
              «Combinator.pmBind»
                «Combinator.pmGet»
                (fun (x9 : T) =>
                  if («Combinator.stInfer» x9).label ≠ 0 then
                    let x10 : T := Const.node (leaf 9) («Prelude.single» x7);
                    «Combinator.memoRet»
                      (if (Const.eq x2 (leaf 0)).label ≠ 0 then
                        «Combinator.pty»
                          x7
                          (leaf 0)
                          x10
                          («Combinator.tyLo» x8)
                          (Const.node (leaf 10) («Theory.l2» x7 («Combinator.tyLo» x8)))
                          («Combinator.tyLo» x8)
                          (Const.node (leaf 10) («Theory.l2» x7 («Combinator.tyLo» x8)))
                      else
                        «Combinator.pty»
                          x7
                          (leaf 1)
                          x10
                          («Combinator.tyLo» x8)
                          (Const.node
                            (leaf 10)
                            («Theory.l2» («Theory.dom» x7) («Combinator.tyLo» x8)))
                          («Combinator.tyHi» x8)
                          (Const.node
                            (leaf 10)
                            («Theory.l2» («Theory.cod» x7) («Combinator.tyHi» x8))))
                  else
                    «Combinator.pmBind»
                      («Combinator.addLemma»
                        («PartialHorn.eqn» x7 («Combinator.tyT» x8))
                        («Combinator.cAx»
                          («Infer.defAxIdx» x1)
                          x6
                          («Base.mapT» «Combinator.tyDfd» x3)
                          («Prelude.single» («Combinator.tyDfd» x8))))
                      (fun (x10 : T) =>
                        «Combinator.pmBind»
                          («Combinator.addLemma»
                            («Theory.dfd» x7)
                            («Combinator.cTrans» x10 («Combinator.cSymm» x10)))
                          (fun (x11 : T) =>
                            if (Const.eq x2 (leaf 0)).label ≠ 0 then
                              «Combinator.pmBind»
                                («Combinator.addLemma»
                                  («PartialHorn.eqn» x7 («Combinator.tyLo» x8))
                                  («Combinator.cTrans» x10 («Combinator.tyLoC» x8)))
                                (fun (x12 : T) =>
                                  «Combinator.memoRet»
                                    («Combinator.pty»
                                      x7
                                      (leaf 0)
                                      x11
                                      («Combinator.tyLo» x8)
                                      x12
                                      («Combinator.tyLo» x8)
                                      x12))
                            else
                              «Combinator.pmBind»
                                («Combinator.addLemma»
                                  («PartialHorn.eqn» («Theory.dom» x7) («Combinator.tyLo» x8))
                                  («Combinator.cTrans»
                                    («Combinator.cCong»
                                      («Combinator.cAx»
                                        (leaf 0)
                                        («Prelude.single» x7)
                                        («Prelude.single» x11)
                                        ([] : List T))
                                      («Prelude.single» x10))
                                    («Combinator.tyLoC» x8)))
                                (fun (x12 : T) =>
                                  «Combinator.pmBind»
                                    («Combinator.addLemma»
                                      («PartialHorn.eqn» («Theory.cod» x7) («Combinator.tyHi» x8))
                                      («Combinator.cTrans»
                                        («Combinator.cCong»
                                          («Combinator.cAx»
                                            (leaf 1)
                                            («Prelude.single» x7)
                                            («Prelude.single» x11)
                                            ([] : List T))
                                          («Prelude.single» x10))
                                        («Combinator.tyHiC» x8)))
                                    (fun (x13 : T) =>
                                      «Combinator.memoRet»
                                        («Combinator.pty»
                                          x7
                                          (leaf 1)
                                          x11
                                          («Combinator.tyLo» x8)
                                          x12
                                          («Combinator.tyHi» x8)
                                          x13)))))))
        else
          «Combinator.pmFail»);
    x4

def «Combinator.typeOpDfd» :=
  fun (x0 : List T → T → T → T → T) (x1 : T) (x2 : List T) =>
    let x3 : T →
      T →
        T := (let x3 : List T := «Base.mapT» «Combinator.tyT» x2;
              let x4 : T := «Prelude.nth» «Infer.dfdRules» x1;
              if («Prelude.and»
                («Prelude.isSome» x4)
                («Prelude.isSome» («Prelude.get» x4))).label ≠ 0 then
                let x5 : T := «Prelude.get» («Prelude.get» x4);
                let x6 : T := «Prelude.at» (Const.children x5) (leaf 0);
                if (Const.eq (Const.label x5) (leaf 0)).label ≠ 0 then
                  «Combinator.pmBind»
                    («Combinator.axiomAt» x6)
                    (fun (x7 : T) =>
                      «Combinator.pmBind»
                        («Combinator.pmMapM»
                          («Combinator.proveHyp» x0 x2)
                          («PartialHorn.seqHyps» x7))
                        (fun (x8 : T) =>
                          «Combinator.pmPure»
                            («Combinator.cAx»
                              x6
                              x3
                              («Base.mapT» «Combinator.tyDfd» x2)
                              (Const.children x8))))
                else
                  if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
                    «Combinator.pmPure»
                      («Combinator.cStrict»
                        (leaf 0)
                        («Combinator.cAx»
                          x6
                          x3
                          («Base.mapT» «Combinator.tyDfd» x2)
                          ([] : List T)))
                  else
                    let x7 : T := «Combinator.cAx»
                      x6
                      ([] : List T)
                      ([] : List T)
                      ([] : List T);
                    «Combinator.pmPure» («Combinator.cTrans» («Combinator.cSymm» x7) x7)
              else
                «Combinator.pmFail»);
    x3

def «Combinator.typeOpObj» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List T) =>
    let x4 : T →
      T →
        T := (let x4 : T := «PartialHorn.phOp»
                x0
                («Base.mapT»
                  (fun (x4 : T) =>
                    if (Const.eq («Combinator.tySort» x4) (leaf 0)).label ≠ 0 then
                      «Combinator.tyLo» x4
                    else
                      «Combinator.tyT» x4)
                  x3);
              if (Const.equal x4 x1).label ≠ 0 then
                «Combinator.pmPure» («Combinator.pty» x1 (leaf 0) x2 x1 x2 x1 x2)
              else
                «Combinator.pmBind»
                  («Combinator.eqCert»
                    («PartialHorn.eqn» x1 x4)
                    («Combinator.cCong»
                      x2
                      («Base.mapT»
                        (fun (x5 : T) =>
                          if (Const.eq («Combinator.tySort» x5) (leaf 0)).label ≠ 0 then
                            «Combinator.tyLoC» x5
                          else
                            «Combinator.tyDfd» x5)
                        x3)))
                  (fun (x5 : T) =>
                    «Combinator.pmPure» («Combinator.pty» x1 (leaf 0) x2 x4 x5 x4 x5)));
    x4

def «Combinator.typeOpTy» :=
  fun (x0 : List T → T → T → T → T)
    (x1 : T)
    (x2 : T)
    (x3 : T)
    (x4 : T)
    (x5 : List T) =>
    let x6 : T →
      T →
        T := (if (Const.eq x2 (leaf 0)).label ≠ 0 then
      if («Prelude.and»
        (Const.eq x1 (leaf 0))
        (Const.eq («Prelude.length» x5) (leaf 1))).label ≠ 0 then
        let x6 : T := «Prelude.at» x5 (leaf 0);
        «Combinator.pmPure»
          («Combinator.pty»
            x3
            (leaf 0)
            x4
            («Combinator.tyLo» x6)
            («Combinator.tyLoC» x6)
            («Combinator.tyLo» x6)
            («Combinator.tyLoC» x6))
      else
        if («Prelude.and»
          (Const.eq x1 (leaf 1))
          (Const.eq («Prelude.length» x5) (leaf 1))).label ≠ 0 then
          let x6 : T := «Prelude.at» x5 (leaf 0);
          «Combinator.pmPure»
            («Combinator.pty»
              x3
              (leaf 0)
              x4
              («Combinator.tyHi» x6)
              («Combinator.tyHiC» x6)
              («Combinator.tyHi» x6)
              («Combinator.tyHiC» x6))
        else
          «Combinator.typeOpObj» x1 x3 x4 x5
    else
      let x6 : T := «Prelude.nth» «Infer.domRules» x1;
      let x7 : T := «Prelude.nth» «Infer.codRules» x1;
      if («Prelude.and»
        («Prelude.and»
          («Prelude.isSome» x6)
          («Prelude.isSome» («Prelude.get» x6)))
        («Prelude.and»
          («Prelude.isSome» x7)
          («Prelude.isSome» («Prelude.get» x7)))).label ≠ 0 then
        «Combinator.pmBind»
          («Combinator.pBound» x0 x5 x1 («Prelude.get» («Prelude.get» x6)) x4)
          (fun (x8 : T) =>
            «Combinator.pmBind»
              («Combinator.pBound» x0 x5 x1 («Prelude.get» («Prelude.get» x7)) x4)
              (fun (x9 : T) =>
                «Combinator.pmBind»
                  («Combinator.eqCert»
                    («PartialHorn.eqn»
                      («Theory.dom» x3)
                      («Prelude.at» (Const.children x8) (leaf 0)))
                    («Prelude.at» (Const.children x8) (leaf 1)))
                  (fun (x10 : T) =>
                    «Combinator.pmBind»
                      («Combinator.eqCert»
                        («PartialHorn.eqn»
                          («Theory.cod» x3)
                          («Prelude.at» (Const.children x9) (leaf 0)))
                        («Prelude.at» (Const.children x9) (leaf 1)))
                      (fun (x11 : T) =>
                        «Combinator.pmPure»
                          («Combinator.pty»
                            x3
                            (leaf 1)
                            x4
                            («Prelude.at» (Const.children x8) (leaf 0))
                            x10
                            («Prelude.at» (Const.children x9) (leaf 0))
                            x11)))))
      else
        «Combinator.pmFail»);
    x6

def «Combinator.typeOp» :=
  fun (x0 : List T → T → T → T → T) (x1 : T) (x2 : List T) =>
    let x3 : T →
      T →
        T := «Combinator.pmBind»
      «Combinator.pmGet»
      (fun (x3 : T) =>
        let x4 : T := «Prelude.nth» («Combinator.stSig» x3) x1;
        if («Prelude.isSome» x4).label ≠ 0 then
          let x5 : T := «Prelude.get» x4;
          if («Base.equalTs»
            («Base.mapT» «Combinator.tySort» x2)
            («PartialHorn.opArgs» x5)).label ≠ 0 then
            if (Const.lt x1 («Prelude.length» «Theory.sig»)).label ≠ 0 then
              let x6 : T := «PartialHorn.phOp» x1 («Base.mapT» «Combinator.tyT» x2);
              «Combinator.pmBind»
                («Combinator.typeOpDfd» x0 x1 x2)
                (fun (x7 : T) =>
                  «Combinator.pmBind»
                    («Combinator.dfdCert» x6 x7)
                    (fun (x8 : T) =>
                      «Combinator.pmBind»
                        («Combinator.typeOpTy» x0 x1 («PartialHorn.opSort» x5) x6 x8 x2)
                        «Combinator.memoRet»))
            else
              «Combinator.typeDefined»
                x0
                (Const.sub x1 («Prelude.length» «Theory.sig»))
                («PartialHorn.opSort» x5)
                x2
          else
            «Combinator.pmFail»
        else
          «Combinator.pmFail»);
    x3

def «Combinator.typeStep» :=
  fun (x0 : List T → T → T → T → T)
    (x1 : T → T → T → T)
    (x2 : T → T)
    (x3 : T)
    (x4 : List (T → T → T)) =>
    let x5 : T →
      T →
        T := (let x5 : T := Const.label x3;
              if (Const.eq x5 (leaf 0)).label ≠ 0 then
                if (Const.eq
                  («Prelude.length» (Const.children x3))
                  (leaf 1)).label ≠ 0 then
                  x1 (Const.label («Prelude.at» (Const.children x3) (leaf 0)))
                else
                  «Combinator.pmFail»
              else
                «Combinator.pmBind»
                  («Combinator.lookup» (x2 x3))
                  (fun (x6 : T) =>
                    if («Prelude.isSome» x6).label ≠ 0 then
                      «Combinator.pmPure» («Prelude.get» x6)
                    else
                      «Combinator.pmBind»
                        («Combinator.pmSeq» x4)
                        (fun (x7 : T) =>
                          «Combinator.typeOp» x0 (Const.sub x5 (leaf 1)) (Const.children x7))));
    x5

def «Combinator.varSide» :=
  fun (x0 : T → T → T → T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T →
      T →
        T := (fun (x5 : T) (x6 : T) =>
      let x7 : T := «PartialHorn.phOp»
        x3
        («Prelude.single» («PartialHorn.phVar» x1));
      let x8 : T := «Combinator.findIdxT»
        (fun (x8 : T) => Const.equal («PartialHorn.eqLhs» x8) x7)
        («Combinator.scHyps» x5);
      if («Prelude.isSome» x8).label ≠ 0 then
        let x9 : T := «Prelude.get» x8;
        let x10 : T := «Prelude.nth» («Combinator.scHyps» x5) x9;
        if («Prelude.isSome» x10).label ≠ 0 then
          «Combinator.pmBind»
            (x0 («PartialHorn.eqRhs» («Prelude.get» x10)))
            (fun (x11 : T) =>
              «Combinator.pmPure»
                (Const.node
                  (leaf 0)
                  («Theory.l2»
                    («Combinator.tyLo» x11)
                    (if (x2).label ≠ 0 then
                      Const.node (leaf 10) («Theory.l2» x7 («Combinator.tyLo» x11))
                    else
                      «Combinator.cTrans»
                        («Combinator.cHyp» x9)
                        («Combinator.tyLoC» x11)))))
            x5
            x6
        else
          «Prelude.none»
      else
        «Prelude.some»
          (Const.node
            (leaf 0)
            («Theory.l2»
              (Const.node
                (leaf 0)
                («Theory.l2»
                  x7
                  («Combinator.cAx»
                    x4
                    («Prelude.single» («PartialHorn.phVar» x1))
                    («Prelude.single» («Combinator.cRefl» x1))
                    ([] : List T))))
              x6)));
    x5

def «Combinator.typeVar» :=
  fun (x0 : T → T → T → T) (x1 : T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := «Prelude.nth» («Combinator.scCtx» x2) x1;
      if («Prelude.isSome» x4).label ≠ 0 then
        let x5 : T := «Prelude.get» x4;
        if (Const.eq x5 (leaf 0)).label ≠ 0 then
          «Prelude.some»
            (Const.node
              (leaf 0)
              («Theory.l2»
                («Combinator.pty»
                  («PartialHorn.phVar» x1)
                  (leaf 0)
                  («Combinator.cRefl» x1)
                  («PartialHorn.phVar» x1)
                  («Combinator.cRefl» x1)
                  («PartialHorn.phVar» x1)
                  («Combinator.cRefl» x1))
                x3))
        else
          if (Const.eq x5 (leaf 1)).label ≠ 0 then
            let x6 : T := «Combinator.stInfer» x3;
            «Combinator.pmBind»
              («Combinator.varSide» x0 x1 x6 (leaf 0) (leaf 0))
              (fun (x7 : T) =>
                «Combinator.pmBind»
                  («Combinator.varSide» x0 x1 x6 (leaf 1) (leaf 1))
                  (fun (x8 : T) =>
                    «Combinator.pmPure»
                      («Combinator.pty»
                        («PartialHorn.phVar» x1)
                        (leaf 1)
                        («Combinator.cRefl» x1)
                        («Prelude.at» (Const.children x7) (leaf 0))
                        («Prelude.at» (Const.children x7) (leaf 1))
                        («Prelude.at» (Const.children x8) (leaf 0))
                        («Prelude.at» (Const.children x8) (leaf 1)))))
              x2
              x3
          else
            «Prelude.none»
      else
        «Prelude.none»);
    x2

def «Combinator.typers» :=
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
            («Combinator.typeStep»
              (x1).1
              (fun (x4 : T) =>
                let x5 : T := «Prelude.nth» x2 x4;
                if («Prelude.isSome» x5).label ≠ 0 then
                  «Combinator.pmPure» («Prelude.get» x5)
                else
                  «Combinator.pmFail»)
              («PartialHorn.phSubst» («Base.mapT» «Combinator.tyT» x2)))
            x3,
          fun (x2 : T) =>
            Const.para
              (α := T → T → T)
              («Combinator.typeStep»
                (x1).1
                («Combinator.typeVar» (x1).2)
                (fun (x3 : T) => x3))
              x2))
      (fun (_ : List T) (_ : T) => «Combinator.pmFail»,
        fun (_ : T) => «Combinator.pmFail»)
      x0;
    x1

def «Combinator.typeTerm» :=
  fun (x0 : T) =>
    let x1 : T → T → T := («Combinator.typers» (leaf 8)).2 x0; x1

def «Combinator.typePattern» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T → T → T := («Combinator.typers» (leaf 8)).1 x0 x1; x2

def «Combinator.pmRun» :=
  fun (x0 : T) (x1 : List T) (x2 : T → T → T) (x3 : List T) (x4 : T) =>
    let x5 : T := «Base.mapO»
      (fun (x5 : T) =>
        Const.node
          (leaf 0)
          («Theory.l2»
            («Prelude.at» (Const.children x5) (leaf 0))
            (Const.node
              (leaf 0)
              («Combinator.stDev» («Prelude.at» (Const.children x5) (leaf 1))))))
      (x2
        x0
        («Combinator.pst»
          (Const.node (leaf 0) x1)
          (Const.node (leaf 0) ([] : List T))
          (Const.node (leaf 0) ([] : List T))
          (Const.node (leaf 0) x3)
          (Const.node
            (leaf 0)
            («Prelude.append»
              «Theory.sig»
              («Base.mapT»
                (fun (x5 : T) =>
                  «PartialHorn.opSig»
                    (Const.node (leaf 0) («PartialHorn.pdCtx» x5))
                    («PartialHorn.pdSort» x5))
                x3)))
          x4));
    x5

def «Combinator.srcAx» :=
  fun (x0 : T) => Const.node (leaf 0) (x0 :: ([] : List T))

def «Combinator.srcThm» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Combinator.srcSeq» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (let x1 : T := «Prelude.at» (Const.children x0) (leaf 0);
              if (Const.eq (Const.label x0) (leaf 0)).label ≠ 0 then
                «Combinator.axiomAt» x1
              else
                «Combinator.pmBind»
                  «Combinator.pmGet»
                  (fun (x2 : T) =>
                    let x3 : T := «Prelude.nth» («Combinator.stDev» x2) x1;
                    if («Prelude.isSome» x3).label ≠ 0 then
                      «Combinator.pmPure»
                        («Prelude.at» (Const.children («Prelude.get» x3)) (leaf 0))
                    else
                      «Combinator.pmFail»));
    x1

def «Combinator.srcCert» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : List T) =>
    let x4 : T := (if (Const.eq (Const.label x0) (leaf 0)).label ≠ 0 then
      «Combinator.cAx» («Prelude.at» (Const.children x0) (leaf 0)) x1 x2 x3
    else
      «Combinator.cThm»
        («Prelude.at» (Const.children x0) (leaf 0))
        x1
        x2
        x3);
    x4

def «Combinator.rwRule» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «Combinator.rwSrc» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2); x2);
    x1

def «Combinator.rwFlip» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2); x3);
    x1

def «Combinator.rwAvoid» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let x4 : T := Const.child x1 (leaf 2); Const.children x4);
    x1

def «Combinator.matchSt» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator.msSigma» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1); Const.children x2);
    x1

def «Combinator.msObjs» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let x3 : T := Const.child x1 (leaf 1); Const.children x3);
    x1

def «Combinator.msDefer» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Combinator.matchSt»
      (Const.node (leaf 0) («Combinator.msSigma» x0))
      (Const.node
        (leaf 0)
        ((Const.node (leaf 0) («Theory.l2» x1 x2)) ::
          («Combinator.msObjs» x0)));
    x3

def «Combinator.matchKids» :=
  fun (x0 : List (T → T → T)) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.foldr
      (α := T → T → T)
      (β := List T → T → T)
      (fun (x3 : T → T → T) (x4 : List T → T → T) (x5 : List T) (x6 : T) =>
        Const.lcase
          (α := T)
          (β := T)
          x5
          («Prelude.some» x6)
          (fun (x7 : T) (x8 : List T) =>
            «Base.bindO» (x3 x7 x6) (fun (x9 : T) => x4 x8 x9)))
      (fun (_ : List T) (x4 : T) => «Prelude.some» x4)
      x0
      x1
      x2;
    x3

def «Combinator.matchStepP» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) (x3 : List (T → T → T)) =>
    let x4 : T →
      T →
        T := (fun (x4 : T) (x5 : T) =>
      let x6 : T := Const.label x2;
      if (Const.eq x6 (leaf 0)).label ≠ 0 then
        if (Const.eq
          («Prelude.length» (Const.children x2))
          (leaf 1)).label ≠ 0 then
          let x7 : T := Const.label («Prelude.at» (Const.children x2) (leaf 0));
          let x8 : T := «Prelude.nth» («Combinator.msSigma» x5) x7;
          if («Prelude.isSome» x8).label ≠ 0 then
            if («Prelude.isSome» («Prelude.get» x8)).label ≠ 0 then
              if (Const.equal («Prelude.get» («Prelude.get» x8)) x4).label ≠ 0 then
                «Prelude.some» x5
              else
                if (Const.equal
                  («Prelude.nth» x1 x7)
                  («Prelude.some» (leaf 0))).label ≠ 0 then
                  «Prelude.some» («Combinator.msDefer» x5 x2 x4)
                else
                  «Prelude.none»
            else
              «Prelude.some»
                («Combinator.matchSt»
                  (Const.node
                    (leaf 0)
                    («Prover.setAt» («Combinator.msSigma» x5) x7 («Prelude.some» x4)))
                  (Const.node (leaf 0) («Combinator.msObjs» x5)))
          else
            «Prelude.none»
        else
          «Prelude.none»
      else
        if (Const.equal
          («PartialHorn.sortOf» x0 x1 x2)
          («Prelude.some» (leaf 0))).label ≠ 0 then
          «Prelude.some» («Combinator.msDefer» x5 x2 x4)
        else
          if («Prelude.and»
            (Const.eq (Const.label x4) x6)
            (Const.eq
              («Prelude.length» (Const.children x4))
              («Prelude.length» (Const.children x2)))).label ≠ 0 then
            «Combinator.matchKids» x3 (Const.children x4) x5
          else
            «Prelude.none»);
    x4

def «Combinator.matchPat» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := Const.para
      (α := T → T → T)
      («Combinator.matchStepP» x0 x1)
      x2
      x3
      x4;
    x5

def «Combinator.bridgeKids» :=
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
          («Combinator.pmPure» (Const.node (leaf 0) ([] : List T)))
          (fun (x5 : T) (x6 : List T) =>
            «Combinator.pmBind»
              (x2 x5)
              (fun (x7 : T) =>
                «Combinator.pmBind»
                  (x3 x6)
                  (fun (x8 : T) =>
                    «Combinator.pmPure»
                      (Const.node (leaf 0) (x7 :: (Const.children x8)))))))
      (fun (_ : List T) =>
        «Combinator.pmPure» (Const.node (leaf 0) ([] : List T)))
      x0
      x1;
    x2

def «Combinator.bridgeStep» :=
  fun (x0 : List T) (x1 : T) (x2 : List (T → T → T → T)) =>
    let x3 : T →
      T →
        T →
          T := (fun (x3 : T) =>
      «Combinator.pmBind»
        («Combinator.typeTerm» x3)
        (fun (x4 : T) =>
          if (Const.equal
            («PartialHorn.phSubst» («Base.mapT» «Combinator.tyT» x0) x1)
            x3).label ≠ 0 then
            «Combinator.pmPure» («Combinator.tyDfd» x4)
          else
            if (Const.eq («Combinator.tySort» x4) (leaf 0)).label ≠ 0 then
              «Combinator.pmBind»
                («Combinator.typePattern» x0 x1)
                (fun (x5 : T) => «Combinator.objEq» x4 x5)
            else
              if («Prelude.or»
                (Const.eq (Const.label x1) (leaf 0))
                («Base.not»
                  (Const.eq
                    («Prelude.length» (Const.children x3))
                    («Prelude.length» (Const.children x1))))).label ≠ 0 then
                «Combinator.pmFail»
              else
                «Combinator.pmBind»
                  («Combinator.bridgeKids» x2 (Const.children x3))
                  (fun (x5 : T) =>
                    «Combinator.pmPure»
                      («Combinator.cCong» («Combinator.tyDfd» x4) (Const.children x5)))));
    x3

def «Combinator.bridge» :=
  fun (x0 : List T) (x1 : T) (x2 : T) =>
    let x3 : T →
      T →
        T := Const.para
      (α := T → T → T → T)
      («Combinator.bridgeStep» x0)
      x1
      x2;
    x3

def «Combinator.applyRule» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T →
      T →
        T := «Combinator.pmBind»
      («Combinator.pmGuard»
        («Base.not»
          («Base.anyT»
            (fun (x2 : T) => Const.eq (Const.label x1) x2)
            («Combinator.rwAvoid» x0))))
      (fun (_ : T) =>
        «Combinator.pmBind»
          («Combinator.srcSeq» («Combinator.rwSrc» x0))
          (fun (x3 : T) =>
            let x4 : T := (if («Combinator.rwFlip» x0).label ≠ 0 then
              «PartialHorn.eqRhs» («PartialHorn.seqConcl» x3)
            else
              «PartialHorn.eqLhs» («PartialHorn.seqConcl» x3));
            let x5 : T := (if («Combinator.rwFlip» x0).label ≠ 0 then
              «PartialHorn.eqLhs» («PartialHorn.seqConcl» x3)
            else
              «PartialHorn.eqRhs» («PartialHorn.seqConcl» x3));
            «Combinator.pmBind»
              «Combinator.pmGet»
              (fun (x6 : T) =>
                let x7 : T := «Combinator.matchPat»
                  («Combinator.stSig» x6)
                  («PartialHorn.seqCtx» x3)
                  x4
                  x1
                  («Combinator.matchSt»
                    (Const.node
                      (leaf 0)
                      («Base.mapT»
                        (fun (_ : T) => «Prelude.none»)
                        («PartialHorn.seqCtx» x3)))
                    (Const.node (leaf 0) ([] : List T)));
                if («Prelude.isSome» x7).label ≠ 0 then
                  let x8 : T := «Prelude.get» x7;
                  let x9 : T := «Base.allSomeT» («Combinator.msSigma» x8);
                  if («Prelude.isSome» x9).label ≠ 0 then
                    let x10 : List T := Const.children («Prelude.get» x9);
                    «Combinator.pmBind»
                      («Combinator.pmMapM» «Combinator.typeTerm» x10)
                      (fun (x11 : T) =>
                        let x12 : List T := Const.children x11;
                        «Combinator.pmBind»
                          («Combinator.pmMapM»
                            (fun (x13 : T) =>
                              «Combinator.pmBind»
                                («Combinator.typePattern»
                                  x12
                                  («Prelude.at» (Const.children x13) (leaf 0)))
                                (fun (x14 : T) =>
                                  «Combinator.pmBind»
                                    («Combinator.typeTerm»
                                      («Prelude.at» (Const.children x13) (leaf 1)))
                                    (fun (x15 : T) => «Combinator.objEq» x14 x15)))
                            («Combinator.msObjs» x8))
                          (fun (_ : T) =>
                            «Combinator.pmBind»
                              («Combinator.bridge» x12 x4 x1)
                              (fun (x14 : T) =>
                                «Combinator.pmBind»
                                  («Combinator.pmMapM»
                                    («Combinator.proveHyp» «Combinator.typePattern» x12)
                                    («PartialHorn.seqHyps» x3))
                                  (fun (x15 : T) =>
                                    let x16 : T := «Combinator.srcCert»
                                      («Combinator.rwSrc» x0)
                                      x10
                                      («Base.mapT» «Combinator.tyDfd» x12)
                                      (Const.children x15);
                                    «Combinator.pmPure»
                                      (Const.node
                                        (leaf 0)
                                        («Theory.l2»
                                          («PartialHorn.phSubst» x10 x5)
                                          («Combinator.cTrans»
                                            x14
                                            (if («Combinator.rwFlip» x0).label ≠ 0 then
                                              «Combinator.cSymm» x16
                                            else
                                              x16))))))))
                  else
                    «Combinator.pmFail»
                else
                  «Combinator.pmFail»)));
    x2

def «Combinator.firstRule» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T →
      T →
        T := Const.foldr
      (α := T)
      (β := T → T → T)
      (fun (x2 : T) (x3 : T → T → T) =>
        «Combinator.pmOr» («Combinator.applyRule» x2 x1) x3)
      «Combinator.pmFail»
      x0;
    x2

def «Combinator.assocLeft» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (if («Prelude.and»
      (Const.eq (Const.label x0) (leaf 4))
      (Const.eq
        («Prelude.length» (Const.children x0))
        (leaf 2))).label ≠ 0 then
      let x1 : T := «Prelude.at» (Const.children x0) (leaf 0);
      let x2 : T := «Prelude.at» (Const.children x0) (leaf 1);
      if («Prelude.and»
        (Const.eq (Const.label x2) (leaf 4))
        (Const.eq
          («Prelude.length» (Const.children x2))
          (leaf 2))).label ≠ 0 then
        let x3 : T := «Prelude.at» (Const.children x2) (leaf 0);
        let x4 : T := «Prelude.at» (Const.children x2) (leaf 1);
        «Combinator.pmBind»
          («Combinator.typeTerm» x0)
          (fun (x5 : T) =>
            «Combinator.pmBind»
              («Combinator.typeTerm» x1)
              (fun (x6 : T) =>
                «Combinator.pmBind»
                  («Combinator.typeTerm» x3)
                  (fun (x7 : T) =>
                    «Combinator.pmBind»
                      («Combinator.typeTerm» x4)
                      (fun (x8 : T) =>
                        «Combinator.pmPure»
                          (Const.node
                            (leaf 0)
                            («Theory.l4»
                              x1
                              x3
                              x4
                              («Combinator.cAx»
                                (leaf 7)
                                («Theory.l3» x1 x3 x4)
                                («Theory.l3»
                                  («Combinator.tyDfd» x6)
                                  («Combinator.tyDfd» x7)
                                  («Combinator.tyDfd» x8))
                                («Prelude.single» («Combinator.tyDfd» x5)))))))))
      else
        «Combinator.pmFail»
    else
      «Combinator.pmFail»);
    x1

def «Combinator.rewriteRoot» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T →
      T →
        T := «Combinator.pmOr»
      («Combinator.firstRule» x0 x1)
      («Combinator.pmBind»
        («Combinator.assocLeft» x1)
        (fun (x2 : T) =>
          let x3 : T := «Prelude.at» (Const.children x2) (leaf 0);
          let x4 : T := «Prelude.at» (Const.children x2) (leaf 1);
          let x5 : T := «Prelude.at» (Const.children x2) (leaf 2);
          let x6 : T := «Prelude.at» (Const.children x2) (leaf 3);
          «Combinator.pmBind»
            («Combinator.firstRule» x0 («Theory.comp» x3 x4))
            (fun (x7 : T) =>
              «Combinator.pmBind»
                («Combinator.typeTerm» («Theory.comp» («Theory.comp» x3 x4) x5))
                (fun (x8 : T) =>
                  «Combinator.pmBind»
                    («Combinator.typeTerm» x5)
                    (fun (x9 : T) =>
                      «Combinator.pmPure»
                        (Const.node
                          (leaf 0)
                          («Theory.l2»
                            («Theory.comp» («Prelude.at» (Const.children x7) (leaf 0)) x5)
                            («Combinator.cTrans»
                              x6
                              («Combinator.cCong»
                                («Combinator.tyDfd» x8)
                                («Theory.l2»
                                  («Prelude.at» (Const.children x7) (leaf 1))
                                  («Combinator.tyDfd» x9)))))))))));
    x2

def «Combinator.lookupNf» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «Prelude.some»
        (Const.node
          (leaf 0)
          («Theory.l2»
            («Combinator.tableFind» («Combinator.stNfs» x2) x0)
            x2)));
    x1

def «Combinator.memoizeNf» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T →
      T →
        T := «Combinator.pmBind»
      (if (Const.equal x0 x1).label ≠ 0 then
        «Combinator.pmPure» x2
      else
        «Combinator.addLemma» («PartialHorn.eqn» x0 x1) x2)
      (fun (x3 : T) (_ : T) (x5 : T) =>
        «Prelude.some»
          (Const.node
            (leaf 0)
            («Theory.l2»
              (Const.node (leaf 0) («Theory.l2» x1 x3))
              («Combinator.withNfs»
                x5
                («Combinator.tableInsert»
                  («Combinator.stNfs» x5)
                  x0
                  (Const.node (leaf 0) («Theory.l2» x1 x3)))))));
    x3

def «Combinator.normStepP» :=
  fun (x0 : List T)
    (x1 : T → T → T → T)
    (x2 : T)
    (x3 : List (T → T → T)) =>
    let x4 : T →
      T →
        T := «Combinator.pmBind»
      («Combinator.lookupNf» x2)
      (fun (x4 : T) =>
        if («Prelude.isSome» x4).label ≠ 0 then
          «Combinator.pmPure» («Prelude.get» x4)
        else
          «Combinator.pmBind»
            («Combinator.typeTerm» x2)
            (fun (x5 : T) =>
              if (Const.eq («Combinator.tySort» x5) (leaf 0)).label ≠ 0 then
                «Combinator.pmPure»
                  (Const.node
                    (leaf 0)
                    («Theory.l2» («Combinator.tyLo» x5) («Combinator.tyLoC» x5)))
              else
                if (Const.eq (Const.label x2) (leaf 0)).label ≠ 0 then
                  «Combinator.pmPure»
                    (Const.node (leaf 0) («Theory.l2» x2 («Combinator.tyDfd» x5)))
                else
                  «Combinator.pmBind»
                    («Combinator.pmSeq» x3)
                    (fun (x6 : T) =>
                      let x7 : List T := Const.children x6;
                      let x8 : T := Const.node
                        (Const.label x2)
                        («Base.mapT»
                          (fun (x8 : T) => «Prelude.at» (Const.children x8) (leaf 0))
                          x7);
                      let x9 : T := (if (Const.equal x8 x2).label ≠ 0 then
                        «Combinator.tyDfd» x5
                      else
                        «Combinator.cCong»
                          («Combinator.tyDfd» x5)
                          («Base.mapT»
                            (fun (x9 : T) => «Prelude.at» (Const.children x9) (leaf 1))
                            x7));
                      «Combinator.pmBind»
                        («Combinator.pmOr»
                          («Combinator.pmBind»
                            («Combinator.rewriteRoot» x0 x8)
                            (fun (x10 : T) => «Combinator.pmPure» («Prelude.some» x10)))
                          («Combinator.pmPure» «Prelude.none»))
                        (fun (x10 : T) =>
                          if («Prelude.isSome» x10).label ≠ 0 then
                            let x11 : T := «Prelude.get» x10;
                            «Combinator.pmBind»
                              (x1 («Prelude.at» (Const.children x11) (leaf 0)))
                              (fun (x12 : T) =>
                                «Combinator.memoizeNf»
                                  x2
                                  («Prelude.at» (Const.children x12) (leaf 0))
                                  («Combinator.cTrans»
                                    x9
                                    («Combinator.cTrans»
                                      («Prelude.at» (Const.children x11) (leaf 1))
                                      («Prelude.at» (Const.children x12) (leaf 1)))))
                          else
                            «Combinator.memoizeNf» x2 x8 x9))));
    x4

def «Combinator.normalizers» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T →
      T →
        T →
          T := Const.iter
      (α := T → T → T → T)
      (fun (x2 : T → T → T → T) (x3 : T) =>
        Const.para (α := T → T → T) («Combinator.normStepP» x0 x2) x3)
      (fun (_ : T) => «Combinator.pmFail»)
      x1;
    x2

def «Combinator.pNormalize» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T → T → T := «Combinator.normalizers» x0 (leaf 64) x1; x2

def «Combinator.beforeTerminal» :=
  «Prelude.length» «Theory.categoryAxioms»

def «Combinator.beforeProduct» :=
  Const.add
    «Combinator.beforeTerminal»
    («Prelude.length» «Theory.terminalAxioms»)

def «Combinator.beforeExponential» :=
  Const.add
    «Combinator.beforeProduct»
    (Const.add
      («Prelude.length» «Theory.productAxioms»)
      (Const.add
        («Prelude.length» «Theory.equalizerAxioms»)
        (Const.add
          («Prelude.length» «Theory.initialAxioms»)
          (Const.add
            («Prelude.length» «Theory.coproductAxioms»)
            («Prelude.length» «Theory.coequalizerAxioms»)))))

def «Combinator.beforeNat» :=
  Const.add
    «Combinator.beforeExponential»
    (Const.add
      («Prelude.length» «Theory.exponentialAxioms»)
      («Prelude.length» «Theory.classifierAxioms»))

def «Combinator.beforeList» :=
  Const.add «Combinator.beforeNat» («Prelude.length» «Theory.natAxioms»)

def «Combinator.pInst» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T →
      T →
        T := «Combinator.pmBind»
      («Combinator.srcSeq» x0)
      (fun (x2 : T) =>
        «Combinator.pmBind»
          («Combinator.pmMapM» «Combinator.typeTerm» x1)
          (fun (x3 : T) =>
            let x4 : List T := Const.children x3;
            «Combinator.pmBind»
              («Combinator.pmMapM»
                («Combinator.proveHyp» «Combinator.typePattern» x4)
                («PartialHorn.seqHyps» x2))
              (fun (x5 : T) =>
                «Combinator.pmPure»
                  (Const.node
                    (leaf 0)
                    («Theory.l2»
                      («PartialHorn.eqSubst» x1 («PartialHorn.seqConcl» x2))
                      («Combinator.srcCert»
                        x0
                        x1
                        («Base.mapT» «Combinator.tyDfd» x4)
                        (Const.children x5)))))));
    x2

def «Combinator.etaExpand» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := «Combinator.pmBind»
      («Combinator.typeTerm» x0)
      (fun (x1 : T) =>
        let x2 : T := «Combinator.tyHi» x1;
        if («Prelude.and»
          (Const.eq (Const.label x2) (leaf 7))
          (Const.eq
            («Prelude.length» (Const.children x2))
            (leaf 2))).label ≠ 0 then
          «Combinator.pmBind»
            («Combinator.pInst»
              («Combinator.srcAx» (Const.add «Combinator.beforeProduct» (leaf 11)))
              («Theory.l3»
                x0
                («Prelude.at» (Const.children x2) (leaf 0))
                («Prelude.at» (Const.children x2) (leaf 1))))
            (fun (x3 : T) =>
              «Combinator.pmPure»
                (Const.node
                  (leaf 0)
                  («Theory.l2»
                    («PartialHorn.eqLhs» («Prelude.at» (Const.children x3) (leaf 0)))
                    («Combinator.cSymm» («Prelude.at» (Const.children x3) (leaf 1))))))
        else
          «Combinator.pmFail»);
    x1

def «Combinator.rwAx» :=
  fun (x0 : T) =>
    let x1 : T := «Combinator.rwRule»
      («Combinator.srcAx» x0)
      (leaf 0)
      (Const.node (leaf 0) ([] : List T));
    x1

def «Combinator.rwThm» :=
  fun (x0 : T) =>
    let x1 : T := «Combinator.rwRule»
      («Combinator.srcThm» x0)
      (leaf 0)
      (Const.node (leaf 0) ([] : List T));
    x1

def «Combinator.deltaRule» :=
  fun (x0 : T) =>
    let x1 : T := «Combinator.rwAx» («Infer.defAxIdx» x0); x1

def «Combinator.pByNorm» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T →
      T →
        T := «Combinator.pmBind»
      («Combinator.pNormalize» x0 («PartialHorn.eqLhs» x1))
      (fun (x2 : T) =>
        «Combinator.pmBind»
          («Combinator.pNormalize» x0 («PartialHorn.eqRhs» x1))
          (fun (x3 : T) =>
            «Combinator.pmBind»
              («Combinator.pmGuard»
                (Const.equal
                  («Prelude.at» (Const.children x2) (leaf 0))
                  («Prelude.at» (Const.children x3) (leaf 0))))
              (fun (_ : T) =>
                «Combinator.pmPure»
                  («Combinator.cTrans»
                    («Prelude.at» (Const.children x2) (leaf 1))
                    («Combinator.cSymm» («Prelude.at» (Const.children x3) (leaf 1)))))));
    x2

def «Combinator.proveSeq» :=
  fun (x0 : T) (x1 : T → T → T) (x2 : List T) (x3 : T) (x4 : List T) =>
    let x5 : T := «Base.bindO»
      («Combinator.pmRun»
        («Combinator.scope»
          (Const.node (leaf 0) («PartialHorn.seqCtx» x0))
          (Const.node (leaf 0) («PartialHorn.seqHyps» x0)))
        x4
        x1
        x2
        x3)
      (fun (x5 : T) =>
        let x6 : List
          T := Const.children («Prelude.at» (Const.children x5) (leaf 1));
        «Prelude.some»
          (Const.node
            (leaf 0)
            («Theory.l2»
              («Prelude.length» x6)
              (Const.node
                (leaf 0)
                («Prelude.append»
                  x6
                  («Prelude.single»
                    (Const.node
                      (leaf 0)
                      («Theory.l2» x0 («Prelude.at» (Const.children x5) (leaf 0))))))))));
    x5

def «Combinator.normalizeThm» :=
  fun (x0 : List T) (x1 : T) (x2 : List T) (x3 : T) (x4 : List T) =>
    let x5 : T := «Base.bindO»
      («Prelude.nth» x4 x1)
      (fun (x5 : T) =>
        let x6 : T := «Prelude.at» (Const.children x5) (leaf 0);
        let x7 : T := «Combinator.scope»
          (Const.node (leaf 0) («PartialHorn.seqCtx» x6))
          (Const.node (leaf 0) («PartialHorn.seqHyps» x6));
        «Base.bindO»
          («Combinator.pmRun»
            x7
            x4
            («Combinator.pNormalize»
              x0
              («PartialHorn.eqLhs» («PartialHorn.seqConcl» x6)))
            x2
            x3)
          (fun (x8 : T) =>
            let x9 : T := «Prelude.at» (Const.children x8) (leaf 0);
            let x10 : List
              T := Const.children («Prelude.at» (Const.children x8) (leaf 1));
            «Prelude.some»
              (Const.node
                (leaf 0)
                («Theory.l2»
                  («Prelude.length» x10)
                  (Const.node
                    (leaf 0)
                    («Prelude.append»
                      x10
                      («Prelude.single»
                        (Const.node
                          (leaf 0)
                          («Theory.l2»
                            («Combinator.scSeq»
                              x7
                              («PartialHorn.eqn»
                                («Prelude.at» (Const.children x9) (leaf 0))
                                («PartialHorn.eqRhs» («PartialHorn.seqConcl» x6))))
                            («Combinator.cTrans»
                              («Combinator.cSymm» («Prelude.at» (Const.children x9) (leaf 1)))
                              («Combinator.scCite» x7 x1)))))))))));
    x5

def «Combinator.instBy» :=
  fun (x0 : List T) (x1 : T) (x2 : List T) =>
    let x3 : T →
      T →
        T := «Combinator.pmBind»
      («Combinator.srcSeq» x1)
      (fun (x3 : T) =>
        «Combinator.pmBind»
          («Combinator.pmMapM» «Combinator.typeTerm» x2)
          (fun (x4 : T) =>
            let x5 : List T := Const.children x4;
            «Combinator.pmBind»
              («Combinator.pmMapM»
                (fun (x6 : T) =>
                  «Combinator.pmOr»
                    («Combinator.proveHyp» «Combinator.typePattern» x5 x6)
                    («Combinator.pByNorm» x0 («PartialHorn.eqSubst» x2 x6)))
                («PartialHorn.seqHyps» x3))
              (fun (x6 : T) =>
                «Combinator.pmPure»
                  (Const.node
                    (leaf 0)
                    («Theory.l2»
                      («PartialHorn.eqSubst» x2 («PartialHorn.seqConcl» x3))
                      («Combinator.srcCert»
                        x1
                        x2
                        («Base.mapT» «Combinator.tyDfd» x5)
                        (Const.children x6)))))));
    x3

def «Combinator.congStep» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List (T → T → T → T)) =>
    let x4 : T →
      T →
        T →
          T := (fun (x4 : T) =>
      «Combinator.pmBind»
        («Combinator.typeTerm» x2)
        (fun (x5 : T) =>
          if (Const.equal x2 x4).label ≠ 0 then
            «Combinator.pmPure» («Combinator.tyDfd» x5)
          else
            if («Prelude.and»
              (Const.equal x2 («PartialHorn.eqLhs» x0))
              (Const.equal x4 («PartialHorn.eqRhs» x0))).label ≠ 0 then
              «Combinator.pmPure» x1
            else
              if (Const.eq («Combinator.tySort» x5) (leaf 0)).label ≠ 0 then
                «Combinator.pmBind»
                  («Combinator.typeTerm» x4)
                  (fun (x6 : T) => «Combinator.objEq» x5 x6)
              else
                if («Prelude.or»
                  (Const.eq (Const.label x2) (leaf 0))
                  («Prelude.or»
                    («Base.not» (Const.eq (Const.label x4) (Const.label x2)))
                    («Base.not»
                      (Const.eq
                        («Prelude.length» (Const.children x4))
                        («Prelude.length» (Const.children x2)))))).label ≠ 0 then
                  «Combinator.pmFail»
                else
                  «Combinator.pmBind»
                    («Combinator.bridgeKids» x3 (Const.children x4))
                    (fun (x6 : T) =>
                      «Combinator.pmPure»
                        («Combinator.cCong» («Combinator.tyDfd» x5) (Const.children x6)))));
    x4

def «Combinator.congBy» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T →
      T →
        T := Const.para
      (α := T → T → T → T)
      («Combinator.congStep» x0 x1)
      x2
      x3;
    x4

def «Combinator.natRecUniq» :=
  fun (x0 : List T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T →
      T →
        T := «Combinator.pmBind»
      («Combinator.instBy»
        x0
        («Combinator.srcAx» (Const.add «Combinator.beforeNat» (leaf 12)))
        («Theory.l3» x1 x2 x3))
      (fun (x4 : T) =>
        «Combinator.pmPure» («Prelude.at» (Const.children x4) (leaf 1)));
    x4

def «Combinator.listRecUniq» :=
  fun (x0 : List T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T →
      T →
        T := «Combinator.pmBind»
      («Combinator.instBy»
        x0
        («Combinator.srcAx» (Const.add «Combinator.beforeList» (leaf 13)))
        («Theory.l4» x1 x2 x3 x4))
      (fun (x5 : T) =>
        «Combinator.pmPure» («Prelude.at» (Const.children x5) (leaf 1)));
    x5

def «Combinator.byNatInduction» :=
  fun (x0 : List T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T →
      T →
        T := «Combinator.pmBind»
      («Combinator.natRecUniq» x0 x1 x2 («PartialHorn.eqLhs» x3))
      (fun (x4 : T) =>
        «Combinator.pmBind»
          («Combinator.natRecUniq» x0 x1 x2 («PartialHorn.eqRhs» x3))
          (fun (x5 : T) =>
            «Combinator.pmPure»
              («Combinator.cTrans» x4 («Combinator.cSymm» x5))));
    x4

def «Combinator.byListInduction» :=
  fun (x0 : List T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T →
      T →
        T := «Combinator.pmBind»
      («Combinator.listRecUniq» x0 x1 x2 x3 («PartialHorn.eqLhs» x4))
      (fun (x5 : T) =>
        «Combinator.pmBind»
          («Combinator.listRecUniq» x0 x1 x2 x3 («PartialHorn.eqRhs» x4))
          (fun (x6 : T) =>
            «Combinator.pmPure»
              («Combinator.cTrans» x5 («Combinator.cSymm» x6))));
    x5

def «Combinator.byListParamInduction» :=
  fun (x0 : List T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T →
      T →
        T := «Combinator.pmBind»
      («Combinator.typeTerm» («PartialHorn.eqLhs» x4))
      (fun (x5 : T) =>
        let x6 : T := «Combinator.tyLo» x5;
        if («Prelude.and»
          (Const.eq (Const.label x6) (leaf 7))
          (Const.eq
            («Prelude.length» (Const.children x6))
            (leaf 2))).label ≠ 0 then
          let x7 : T := «Prelude.at» (Const.children x6) (leaf 0);
          let x8 : T := «Prelude.at» (Const.children x6) (leaf 1);
          let x9 : T := «Combinator.tyHi» x5;
          let x10 : T := «Theory.exp» x8 x9;
          let x11 : T := «Theory.prod» x1 x10;
          let x12 : T := «Theory.curry»
            «Theory.one»
            x8
            («Theory.comp» x2 («Theory.cSnd» «Theory.one» x8));
          let x13 : T := «Theory.curry»
            x11
            x8
            («Theory.comp»
              x3
              («Theory.cPair»
                («Theory.cPair»
                  («Theory.comp» («Theory.cFst» x1 x10) («Theory.cFst» x11 x8))
                  («Theory.comp»
                    («Theory.ev» x8 x9)
                    («Theory.cPair»
                      («Theory.comp» («Theory.cSnd» x1 x10) («Theory.cFst» x11 x8))
                      («Theory.cSnd» x11 x8))))
                («Theory.cSnd» x11 x8)));
          let x14 : T := «Theory.curry» x7 x8 («PartialHorn.eqLhs» x4);
          let x15 : T := «Theory.curry» x7 x8 («PartialHorn.eqRhs» x4);
          «Combinator.pmBind»
            («Combinator.byListInduction»
              x0
              x1
              x12
              x13
              («PartialHorn.eqn» x14 x15))
            (fun (x16 : T) =>
              «Combinator.pmBind»
                («Combinator.pInst»
                  («Combinator.srcAx»
                    (Const.add «Combinator.beforeExponential» (leaf 7)))
                  («Theory.l3» x7 x8 («PartialHorn.eqLhs» x4)))
                (fun (x17 : T) =>
                  «Combinator.pmBind»
                    («Combinator.pInst»
                      («Combinator.srcAx»
                        (Const.add «Combinator.beforeExponential» (leaf 7)))
                      («Theory.l3» x7 x8 («PartialHorn.eqRhs» x4)))
                    (fun (x18 : T) =>
                      «Combinator.pmBind»
                        («Combinator.congBy»
                          («PartialHorn.eqn» x14 x15)
                          x16
                          («PartialHorn.eqLhs» («Prelude.at» (Const.children x17) (leaf 0)))
                          («PartialHorn.eqLhs» («Prelude.at» (Const.children x18) (leaf 0))))
                        (fun (x19 : T) =>
                          «Combinator.pmPure»
                            («Combinator.cTrans»
                              («Combinator.cSymm» («Prelude.at» (Const.children x17) (leaf 1)))
                              («Combinator.cTrans»
                                x19
                                («Prelude.at» (Const.children x18) (leaf 1))))))))
        else
          «Combinator.pmFail»);
    x5

def «Combinator.baseRules» :=
  ((«Combinator.rwRule»
    («Combinator.srcAx» (leaf 7))
    (leaf 1)
    (Const.node (leaf 0) ([] : List T))) ::
    ((«Combinator.rwAx» (leaf 10)) ::
      ((«Combinator.rwAx» (leaf 11)) ::
        ((«Combinator.rwAx»
          (Const.add «Combinator.beforeProduct» (leaf 9))) ::
          ((«Combinator.rwAx»
            (Const.add «Combinator.beforeProduct» (leaf 10))) ::
            ((«Combinator.rwAx»
              (Const.add «Combinator.beforeProduct» (leaf 11))) ::
              ((«Combinator.rwRule»
                («Combinator.srcAx» (Const.add «Combinator.beforeTerminal» (leaf 3)))
                (leaf 0)
                (Const.node (leaf 0) («Theory.l2» (leaf 3) (leaf 6)))) ::
                ((«Combinator.rwAx» (Const.add «Combinator.beforeNat» (leaf 10))) ::
                  ((«Combinator.rwAx» (Const.add «Combinator.beforeNat» (leaf 11))) ::
                    («Theory.l2»
                      («Combinator.rwAx» (Const.add «Combinator.beforeList» (leaf 11)))
                      («Combinator.rwAx»
                        (Const.add «Combinator.beforeList» (leaf 12)))))))))))))

def «Combinator.compPairSeq» :=
  «PartialHorn.mkSeq»
    («Theory.l3» (leaf 1) (leaf 1) (leaf 1))
    («Theory.l2»
      («PartialHorn.eqn»
        («Theory.dom» («Theory.x» (leaf 1)))
        («Theory.dom» («Theory.x» (leaf 0))))
      («PartialHorn.eqn»
        («Theory.cod» («Theory.x» (leaf 2)))
        («Theory.dom» («Theory.x» (leaf 0)))))
    («PartialHorn.eqn»
      («Theory.comp»
        («Theory.cPair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))
        («Theory.x» (leaf 2)))
      («Theory.cPair»
        («Theory.comp» («Theory.x» (leaf 0)) («Theory.x» (leaf 2)))
        («Theory.comp» («Theory.x» (leaf 1)) («Theory.x» (leaf 2)))))

def «Combinator.pairFstSndSeq» :=
  «PartialHorn.mkSeq»
    («Theory.l2» (leaf 0) (leaf 0))
    ([] : List T)
    («PartialHorn.eqn»
      («Theory.cPair»
        («Theory.cFst» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))
        («Theory.cSnd» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
      («Theory.idt»
        («Theory.prod» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))

def «Combinator.evCurrySeq» :=
  «PartialHorn.mkSeq»
    («Theory.l5» (leaf 0) (leaf 0) (leaf 1) (leaf 1) (leaf 1))
    («Theory.l4»
      («PartialHorn.eqn»
        («Theory.dom» («Theory.x» (leaf 2)))
        («Theory.prod» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
      («PartialHorn.eqn»
        («Theory.cod» («Theory.x» (leaf 3)))
        («Theory.x» (leaf 0)))
      («PartialHorn.eqn»
        («Theory.cod» («Theory.x» (leaf 4)))
        («Theory.x» (leaf 1)))
      («PartialHorn.eqn»
        («Theory.dom» («Theory.x» (leaf 4)))
        («Theory.dom» («Theory.x» (leaf 3)))))
    («PartialHorn.eqn»
      («Theory.comp»
        («Theory.ev»
          («Theory.x» (leaf 1))
          («Theory.cod» («Theory.x» (leaf 2))))
        («Theory.cPair»
          («Theory.comp»
            («Theory.curry»
              («Theory.x» (leaf 0))
              («Theory.x» (leaf 1))
              («Theory.x» (leaf 2)))
            («Theory.x» (leaf 3)))
          («Theory.x» (leaf 4))))
      («Theory.comp»
        («Theory.x» (leaf 2))
        («Theory.cPair» («Theory.x» (leaf 3)) («Theory.x» (leaf 4)))))

def «Combinator.evCurry0Seq» :=
  «PartialHorn.mkSeq»
    («Theory.l4» (leaf 0) (leaf 0) (leaf 1) (leaf 1))
    («Theory.l3»
      («PartialHorn.eqn»
        («Theory.dom» («Theory.x» (leaf 2)))
        («Theory.prod» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
      («PartialHorn.eqn»
        («Theory.cod» («Theory.x» (leaf 3)))
        («Theory.x» (leaf 1)))
      («PartialHorn.eqn»
        («Theory.dom» («Theory.x» (leaf 3)))
        («Theory.x» (leaf 0))))
    («PartialHorn.eqn»
      («Theory.comp»
        («Theory.ev»
          («Theory.x» (leaf 1))
          («Theory.cod» («Theory.x» (leaf 2))))
        («Theory.cPair»
          («Theory.curry»
            («Theory.x» (leaf 0))
            («Theory.x» (leaf 1))
            («Theory.x» (leaf 2)))
          («Theory.x» (leaf 3))))
      («Theory.comp»
        («Theory.x» (leaf 2))
        («Theory.cPair»
          («Theory.idt» («Theory.x» (leaf 0)))
          («Theory.x» (leaf 3)))))

def «Combinator.curryNatSeq» :=
  «PartialHorn.mkSeq»
    («Theory.l4» (leaf 0) (leaf 0) (leaf 1) (leaf 1))
    («Theory.l2»
      («PartialHorn.eqn»
        («Theory.dom» («Theory.x» (leaf 2)))
        («Theory.prod» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
      («PartialHorn.eqn»
        («Theory.cod» («Theory.x» (leaf 3)))
        («Theory.x» (leaf 0))))
    («PartialHorn.eqn»
      («Theory.comp»
        («Theory.curry»
          («Theory.x» (leaf 0))
          («Theory.x» (leaf 1))
          («Theory.x» (leaf 2)))
        («Theory.x» (leaf 3)))
      («Theory.curry»
        («Theory.dom» («Theory.x» (leaf 3)))
        («Theory.x» (leaf 1))
        («Theory.comp»
          («Theory.x» (leaf 2))
          («Theory.prodMapLeft» («Theory.x» (leaf 3)) («Theory.x» (leaf 1))))))

def «Combinator.bangOneSeq» :=
  «PartialHorn.mkSeq»
    ([] : List T)
    ([] : List T)
    («PartialHorn.eqn»
      («Theory.bang» «Theory.one»)
      («Theory.idt» «Theory.one»))

def «Combinator.seqLhs» :=
  fun (x0 : T) =>
    let x1 : T := «PartialHorn.eqLhs» («PartialHorn.seqConcl» x0); x1

def «Combinator.seqRhs» :=
  fun (x0 : T) =>
    let x1 : T := «PartialHorn.eqRhs» («PartialHorn.seqConcl» x0); x1

def «Combinator.compPairProof» :=
  «Combinator.pmBind»
    («Combinator.etaExpand»
      («Combinator.seqLhs» «Combinator.compPairSeq»))
    (fun (x0 : T) =>
      «Combinator.pmBind»
        («Combinator.pNormalize»
          «Combinator.baseRules»
          («Prelude.at» (Const.children x0) (leaf 0)))
        (fun (x1 : T) =>
          «Combinator.pmBind»
            («Combinator.pmGuard»
              (Const.equal
                («Prelude.at» (Const.children x1) (leaf 0))
                («Combinator.seqRhs» «Combinator.compPairSeq»)))
            (fun (_ : T) =>
              «Combinator.pmPure»
                («Combinator.cTrans»
                  («Prelude.at» (Const.children x0) (leaf 1))
                  («Prelude.at» (Const.children x1) (leaf 1))))))

def «Combinator.pairFstSndProof» :=
  let x0 : T := «Theory.prod»
    («Theory.x» (leaf 0))
    («Theory.x» (leaf 1));
  «Combinator.pmBind»
    («Combinator.pInst»
      («Combinator.srcAx» (Const.add «Combinator.beforeProduct» (leaf 11)))
      («Theory.l3»
        («Theory.idt» x0)
        («Theory.x» (leaf 0))
        («Theory.x» (leaf 1))))
    (fun (x1 : T) =>
      «Combinator.pmBind»
        («Combinator.pNormalize»
          «Combinator.baseRules»
          («PartialHorn.eqLhs» («Prelude.at» (Const.children x1) (leaf 0))))
        (fun (x2 : T) =>
          «Combinator.pmBind»
            («Combinator.pmGuard»
              (Const.equal
                («Prelude.at» (Const.children x2) (leaf 0))
                («Combinator.seqLhs» «Combinator.pairFstSndSeq»)))
            (fun (_ : T) =>
              «Combinator.pmPure»
                («Combinator.cTrans»
                  («Combinator.cSymm» («Prelude.at» (Const.children x2) (leaf 1)))
                  («Prelude.at» (Const.children x1) (leaf 1))))))

def «Combinator.evCurryProof» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (let x1 : List
                T := «Prelude.append»
                «Combinator.baseRules»
                («Prelude.single» («Combinator.rwThm» x0));
              «Combinator.pmBind»
                («Combinator.pInst»
                  («Combinator.srcAx»
                    (Const.add «Combinator.beforeExponential» (leaf 7)))
                  («Theory.l3»
                    («Theory.x» (leaf 0))
                    («Theory.x» (leaf 1))
                    («Theory.x» (leaf 2))))
                (fun (x2 : T) =>
                  let x3 : T := «Theory.cPair»
                    («Theory.x» (leaf 3))
                    («Theory.x» (leaf 4));
                  let x4 : T := «Theory.comp»
                    («PartialHorn.eqLhs» («Prelude.at» (Const.children x2) (leaf 0)))
                    x3;
                  «Combinator.pmBind»
                    («Combinator.pNormalize» x1 x4)
                    (fun (x5 : T) =>
                      «Combinator.pmBind»
                        («Combinator.pNormalize»
                          x1
                          («Combinator.seqLhs» «Combinator.evCurrySeq»))
                        (fun (x6 : T) =>
                          «Combinator.pmBind»
                            («Combinator.pmGuard»
                              (Const.equal
                                («Prelude.at» (Const.children x5) (leaf 0))
                                («Prelude.at» (Const.children x6) (leaf 0))))
                            (fun (_ : T) =>
                              «Combinator.pmBind»
                                («Combinator.typeTerm» x4)
                                (fun (x8 : T) =>
                                  «Combinator.pmBind»
                                    («Combinator.typeTerm» x3)
                                    (fun (x9 : T) =>
                                      «Combinator.pmPure»
                                        («Combinator.cTrans»
                                          («Combinator.cTrans»
                                            («Prelude.at» (Const.children x6) (leaf 1))
                                            («Combinator.cSymm»
                                              («Prelude.at» (Const.children x5) (leaf 1))))
                                          («Combinator.cCong»
                                            («Combinator.tyDfd» x8)
                                            («Theory.l2»
                                              («Prelude.at» (Const.children x2) (leaf 1))
                                              («Combinator.tyDfd» x9)))))))))));
    x1

def «Combinator.evCurry0Proof» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := «Combinator.pmBind»
      («Combinator.pInst»
        («Combinator.srcThm» x0)
        («Theory.l5»
          («Theory.x» (leaf 0))
          («Theory.x» (leaf 1))
          («Theory.x» (leaf 2))
          («Theory.idt» («Theory.x» (leaf 0)))
          («Theory.x» (leaf 3))))
      (fun (x1 : T) =>
        let x2 : T := «Prelude.at» (Const.children x1) (leaf 0);
        «Combinator.pmBind»
          («Combinator.pNormalize»
            «Combinator.baseRules»
            («PartialHorn.eqLhs» x2))
          (fun (x3 : T) =>
            «Combinator.pmBind»
              («Combinator.pmGuard»
                («Prelude.and»
                  (Const.equal
                    («Prelude.at» (Const.children x3) (leaf 0))
                    («Combinator.seqLhs» «Combinator.evCurry0Seq»))
                  (Const.equal
                    («PartialHorn.eqRhs» x2)
                    («Combinator.seqRhs» «Combinator.evCurry0Seq»))))
              (fun (_ : T) =>
                «Combinator.pmPure»
                  («Combinator.cTrans»
                    («Combinator.cSymm» («Prelude.at» (Const.children x3) (leaf 1)))
                    («Prelude.at» (Const.children x1) (leaf 1))))));
    x1

def «Combinator.curryNatProof» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T →
      T →
        T := (let x2 : List
                T := «Prelude.append»
                «Combinator.baseRules»
                («Theory.l2» («Combinator.rwThm» x0) («Combinator.rwThm» x1));
              let x3 : T := «Combinator.seqLhs» «Combinator.curryNatSeq»;
              «Combinator.pmBind»
                («Combinator.pInst»
                  («Combinator.srcAx»
                    (Const.add «Combinator.beforeExponential» (leaf 8)))
                  («Theory.l4»
                    («Theory.dom» («Theory.x» (leaf 3)))
                    («Theory.x» (leaf 1))
                    («Theory.cod» («Theory.x» (leaf 2)))
                    x3))
                (fun (x4 : T) =>
                  «Combinator.pmBind»
                    («Combinator.pNormalize»
                      x2
                      («PartialHorn.eqLhs» («Prelude.at» (Const.children x4) (leaf 0))))
                    (fun (x5 : T) =>
                      «Combinator.pmBind»
                        («Combinator.pNormalize»
                          x2
                          («Combinator.seqRhs» «Combinator.curryNatSeq»))
                        (fun (x6 : T) =>
                          «Combinator.pmBind»
                            («Combinator.pmGuard»
                              (Const.equal
                                («Prelude.at» (Const.children x5) (leaf 0))
                                («Prelude.at» (Const.children x6) (leaf 0))))
                            (fun (_ : T) =>
                              «Combinator.pmPure»
                                («Combinator.cTrans»
                                  («Combinator.cSymm» («Prelude.at» (Const.children x4) (leaf 1)))
                                  («Combinator.cTrans»
                                    («Prelude.at» (Const.children x5) (leaf 1))
                                    («Combinator.cSymm»
                                      («Prelude.at» (Const.children x6) (leaf 1))))))))));
    x2

def «Combinator.bangOneProof» :=
  «Combinator.pmBind»
    («Combinator.pInst»
      («Combinator.srcAx» (Const.add «Combinator.beforeTerminal» (leaf 3)))
      («Prelude.single» («Theory.idt» «Theory.one»)))
    (fun (x0 : T) =>
      «Combinator.pmBind»
        («Combinator.pNormalize»
          «Combinator.baseRules»
          («PartialHorn.eqRhs» («Prelude.at» (Const.children x0) (leaf 0))))
        (fun (x1 : T) =>
          «Combinator.pmBind»
            («Combinator.pmGuard»
              (Const.equal
                («Prelude.at» (Const.children x1) (leaf 0))
                («Theory.bang» «Theory.one»)))
            (fun (_ : T) =>
              «Combinator.pmPure»
                («Combinator.cSymm»
                  («Combinator.cTrans»
                    («Prelude.at» (Const.children x0) (leaf 1))
                    («Prelude.at» (Const.children x1) (leaf 1)))))))

def «Combinator.libraryWith» :=
  fun (x0 : T) =>
    let x1 : T := «Base.bindO»
      («Combinator.proveSeq»
        «Combinator.compPairSeq»
        «Combinator.compPairProof»
        ([] : List T)
        x0
        ([] : List T))
      (fun (x1 : T) =>
        let x2 : T := «Prelude.at» (Const.children x1) (leaf 0);
        «Base.bindO»
          («Combinator.proveSeq»
            «Combinator.pairFstSndSeq»
            «Combinator.pairFstSndProof»
            ([] : List T)
            x0
            (Const.children («Prelude.at» (Const.children x1) (leaf 1))))
          (fun (x3 : T) =>
            let x4 : T := «Prelude.at» (Const.children x3) (leaf 0);
            «Base.bindO»
              («Combinator.proveSeq»
                «Combinator.evCurrySeq»
                («Combinator.evCurryProof» x2)
                ([] : List T)
                x0
                (Const.children («Prelude.at» (Const.children x3) (leaf 1))))
              (fun (x5 : T) =>
                let x6 : T := «Prelude.at» (Const.children x5) (leaf 0);
                «Base.bindO»
                  («Combinator.proveSeq»
                    «Combinator.evCurry0Seq»
                    («Combinator.evCurry0Proof» x6)
                    ([] : List T)
                    x0
                    (Const.children («Prelude.at» (Const.children x5) (leaf 1))))
                  (fun (x7 : T) =>
                    let x8 : T := «Prelude.at» (Const.children x7) (leaf 0);
                    «Base.bindO»
                      («Combinator.proveSeq»
                        «Combinator.curryNatSeq»
                        («Combinator.curryNatProof» x2 x6)
                        ([] : List T)
                        x0
                        (Const.children («Prelude.at» (Const.children x7) (leaf 1))))
                      (fun (x9 : T) =>
                        let x10 : T := «Prelude.at» (Const.children x9) (leaf 0);
                        «Base.bindO»
                          («Combinator.proveSeq»
                            «Combinator.bangOneSeq»
                            «Combinator.bangOneProof»
                            ([] : List T)
                            x0
                            (Const.children («Prelude.at» (Const.children x9) (leaf 1))))
                          (fun (x11 : T) =>
                            «Prelude.some»
                              (Const.node
                                (leaf 0)
                                («Theory.l2»
                                  (Const.node
                                    (leaf 0)
                                    («Theory.l6»
                                      x2
                                      x4
                                      x6
                                      x8
                                      x10
                                      («Prelude.at» (Const.children x11) (leaf 0))))
                                  («Prelude.at» (Const.children x11) (leaf 1))))))))));
    x1

def «Combinator.libRules» :=
  fun (x0 : T) =>
    let x1 : List
      T := «Prelude.append»
      «Combinator.baseRules»
      («Theory.l5»
        («Combinator.rwThm» («Prelude.at» (Const.children x0) (leaf 0)))
        («Combinator.rwThm» («Prelude.at» (Const.children x0) (leaf 1)))
        («Combinator.rwThm» («Prelude.at» (Const.children x0) (leaf 4)))
        («Combinator.rwThm» («Prelude.at» (Const.children x0) (leaf 3)))
        («Combinator.rwThm» («Prelude.at» (Const.children x0) (leaf 5))));
    x1

end GebMirror.Metalogic

end
