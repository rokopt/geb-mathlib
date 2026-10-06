module

public import GebMirror.Metalogic.Tactics

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «Combinator/Seqs.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Combinator/Seqs.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Combinator/Seqs.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Combinator/Seqs.reverse» :=
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

def «Combinator/Seqs.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Combinator/Seqs.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Combinator/Seqs.tail» x1 x0;
    x2

def «Combinator/Seqs.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Combinator/Seqs.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Combinator/OpSigs.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Combinator/OpSigs.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Combinator/OpSigs.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Combinator/OpSigs.reverse» :=
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

def «Combinator/OpSigs.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Combinator/OpSigs.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Combinator/OpSigs.tail» x1 x0;
    x2

def «Combinator/OpSigs.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Combinator/OpSigs.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Combinator/Eqns.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Combinator/Eqns.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Combinator/Eqns.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Combinator/Eqns.reverse» :=
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

def «Combinator/Eqns.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Combinator/Eqns.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Combinator/Eqns.tail» x1 x0;
    x2

def «Combinator/Eqns.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Combinator/Eqns.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Combinator/EqnL.l2» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List T := (x0 :: (x1 :: ([] : List T))); x2

def «Combinator/EqnL.l3» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : List T := (x0 :: («Combinator/EqnL.l2» x1 x2)); x3

def «Combinator/EqnL.l4» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : List T := (x0 :: («Combinator/EqnL.l3» x1 x2 x3)); x4

def «Combinator/EqnL.l5» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : List T := (x0 :: («Combinator/EqnL.l4» x1 x2 x3 x4)); x5

def «Combinator/EqnL.l6» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : List T := (x0 :: («Combinator/EqnL.l5» x1 x2 x3 x4 x5)); x6

def «Combinator/OODfd.nothing» := Const.node (leaf 0) ([] : List T)

def «Combinator/OODfd.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Combinator/OODfd.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let _ : T := Const.child x1 (leaf 0); leaf 1
                   else
                     leaf 0);
    x1

def «Combinator/OODfd.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x3
                   else
                     x0);
    x2

def «Combinator/OODfd.nthOf» :=
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
      «Combinator/OODfd.nothing»
      (fun (x2 : T) (_ : List T) => «Combinator/OODfd.just» x2);
    x2

def «Combinator/OODfd.allJust» :=
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

def «Combinator/PairT.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

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

def «Combinator.certs» := fun (x0 : List T) => Const.node (leaf 0) x0

def «Combinator.certsOf» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : List
              T := Const.iter
              (α := List T)
              (fun (x2 : List T) =>
                Const.lcase
                  (α := T)
                  (β := List T)
                  x2
                  ([] : List T)
                  (fun (_ : T) (x4 : List T) => x4))
              (Const.children x1)
              (leaf 0);
            x2);
    x1

def «Combinator.scope» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator.scCtx» :=
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

def «Combinator.scHyps» :=
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
                       («Base.range» («Combinator/Eqns.length» («Combinator.scHyps» x0)))));
    x2

def «Combinator.pty» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) (x6 : T) =>
    Const.node
      (leaf 0)
      (x0 :: (x1 :: (x2 :: (x3 :: (x4 :: (x5 :: (x6 :: ([] : List T))))))))

def «Combinator/OPTy.nothing» := Const.node (leaf 0) ([] : List T)

def «Combinator/OPTy.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Combinator/OPTy.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let _ : T := Const.child x1 (leaf 0); leaf 1
                   else
                     leaf 0);
    x1

def «Combinator/OPTy.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x3
                   else
                     x0);
    x2

def «Combinator/OPTy.nthOf» :=
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
      «Combinator/OPTy.nothing»
      (fun (x2 : T) (_ : List T) => «Combinator/OPTy.just» x2);
    x2

def «Combinator/OPTy.allJust» :=
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

def «Combinator/TyL.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Combinator/TyL.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Combinator/TyL.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Combinator/TyL.reverse» :=
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

def «Combinator/TyL.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Combinator/TyL.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Combinator/TyL.tail» x1 x0;
    x2

def «Combinator/TyL.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Combinator/TyL.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Combinator/YT.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Combinator.ptys» := fun (x0 : List T) => Const.node (leaf 0) x0

def «Combinator.ptysOf» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : List
              T := Const.iter
              (α := List T)
              (fun (x2 : List T) =>
                Const.lcase
                  (α := T)
                  (β := List T)
                  x2
                  ([] : List T)
                  (fun (_ : T) (x4 : List T) => x4))
              (Const.children x1)
              (leaf 0);
            x2);
    x1

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

def «Combinator.pty0» :=
  «Combinator.pty»
    (leaf 0)
    (leaf 0)
    (leaf 0)
    (leaf 0)
    (leaf 0)
    (leaf 0)
    (leaf 0)

def «Combinator.devEntry» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator/DevL.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Combinator/DevL.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Combinator/DevL.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Combinator/DevL.reverse» :=
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

def «Combinator/DevL.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Combinator/DevL.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Combinator/DevL.tail» x1 x0;
    x2

def «Combinator/DevL.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Combinator/DevL.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Combinator/ODev.nothing» := Const.node (leaf 0) ([] : List T)

def «Combinator/ODev.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Combinator/ODev.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let _ : T := Const.child x1 (leaf 0); leaf 1
                   else
                     leaf 0);
    x1

def «Combinator/ODev.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x3
                   else
                     x0);
    x2

def «Combinator/ODev.nthOf» :=
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
      «Combinator/ODev.nothing»
      (fun (x2 : T) (_ : List T) => «Combinator/ODev.just» x2);
    x2

def «Combinator/ODev.allJust» :=
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

def «Combinator.devSeq» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1); x2);
    x1

def «Combinator.devs» := fun (x0 : List T) => Const.node (leaf 0) x0

def «Combinator.memoEntry» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator.memos» := fun (x0 : List T) => Const.node (leaf 0) x0

def «Combinator.pairs» := fun (x0 : List T) => Const.node (leaf 0) x0

def «Combinator.pairsOf» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : List
              T := Const.iter
              (α := List T)
              (fun (x2 : List T) =>
                Const.lcase
                  (α := T)
                  (β := List T)
                  x2
                  ([] : List T)
                  (fun (_ : T) (x4 : List T) => x4))
              (Const.children x1)
              (leaf 0);
            x2);
    x1

def «Combinator.nfEntry» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator.nfList» := fun (x0 : List T) => Const.node (leaf 0) x0

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
            let _ : T := Const.child x1 (leaf 5);
            let x8 : T := x2;
            let x9 : List
              T := Const.iter
              (α := List T)
              (fun (x9 : List T) =>
                Const.lcase
                  (α := T)
                  (β := List T)
                  x9
                  ([] : List T)
                  (fun (_ : T) (x11 : List T) => x11))
              (Const.children x8)
              (leaf 0);
            x9);
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
            let _ : T := Const.child x1 (leaf 5);
            let x8 : T := x3;
            let x9 : List
              T := Const.iter
              (α := List T)
              (fun (x9 : List T) =>
                Const.lcase
                  (α := T)
                  (β := List T)
                  x9
                  ([] : List T)
                  (fun (_ : T) (x11 : List T) => x11))
              (Const.children x8)
              (leaf 0);
            x9);
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
            let _ : T := Const.child x1 (leaf 5);
            let x8 : T := x4;
            let x9 : List
              T := Const.iter
              (α := List T)
              (fun (x9 : List T) =>
                Const.lcase
                  (α := T)
                  (β := List T)
                  x9
                  ([] : List T)
                  (fun (_ : T) (x11 : List T) => x11))
              (Const.children x8)
              (leaf 0);
            x9);
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
            let _ : T := Const.child x1 (leaf 5);
            let x8 : T := x5;
            let x9 : List
              T := Const.iter
              (α := List T)
              (fun (x9 : List T) =>
                Const.lcase
                  (α := T)
                  (β := List T)
                  x9
                  ([] : List T)
                  (fun (_ : T) (x11 : List T) => x11))
              (Const.children x8)
              (leaf 0);
            x9);
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
            let _ : T := Const.child x1 (leaf 5);
            let x8 : T := x6;
            let x9 : List
              T := Const.iter
              (α := List T)
              (fun (x9 : List T) =>
                Const.lcase
                  (α := T)
                  (β := List T)
                  x9
                  ([] : List T)
                  (fun (_ : T) (x11 : List T) => x11))
              (Const.children x8)
              (leaf 0);
            x9);
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
                   «Combinator.pst» («Combinator.devs» x1) x4 x5 x6 x7 x8);
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
                   «Combinator.pst» x3 («Combinator.memos» x1) x5 x6 x7 x8);
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
                   «Combinator.pst» x3 x4 («Combinator.nfList» x1) x6 x7 x8);
    x2

def «Combinator.memoFind» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        let x4 : T := x2;
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := Const.child x4 (leaf 1);
        if (Const.equal x5 x1).label ≠ 0 then
          «Combinator/OPTy.just» x6
        else
          x3)
      «Combinator/OPTy.nothing»
      x0;
    x2

def «Combinator.nfFind» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        let x4 : T := x2;
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := Const.child x4 (leaf 1);
        if (Const.equal x5 x1).label ≠ 0 then
          «Language/OTPair.just» x6
        else
          x3)
      «Language/OTPair.nothing»
      x0;
    x2

def «Combinator.eqnCert» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator.ecEqn» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1); x2);
    x1

def «Combinator.ecCert» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1); x3);
    x1

def «Combinator.assoc» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: (x3 :: ([] : List T)))))

def «Combinator/CT.res» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator/CT.bad» := Const.node (leaf 0) ([] : List T)

def «Combinator/CT.ok» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Combinator/CT.pure» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «Combinator/CT.ok» («Combinator/CT.res» x0 x2));
    x1

def «Combinator/CT.fail» :=
  fun (_ : T) (_ : T) => let x2 : T := «Combinator/CT.bad»; x2

def «Combinator/CT.orElse» :=
  fun (x0 : T → T → T) (x1 : T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      let x5 : T := x4;
      if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
        let _ : T := Const.child x5 (leaf 0); x4
      else
        x1 x2 x3);
    x2

def «Combinator/CY.res» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator/CY.bad» := Const.node (leaf 0) ([] : List T)

def «Combinator/CY.ok» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Combinator/CY.pure» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «Combinator/CY.ok» («Combinator/CY.res» x0 x2));
    x1

def «Combinator/CY.fail» :=
  fun (_ : T) (_ : T) => let x2 : T := «Combinator/CY.bad»; x2

def «Combinator/CY.orElse» :=
  fun (x0 : T → T → T) (x1 : T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      let x5 : T := x4;
      if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
        let _ : T := Const.child x5 (leaf 0); x4
      else
        x1 x2 x3);
    x2

def «Combinator/CQ.res» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator/CQ.bad» := Const.node (leaf 0) ([] : List T)

def «Combinator/CQ.ok» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Combinator/CQ.pure» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «Combinator/CQ.ok» («Combinator/CQ.res» x0 x2));
    x1

def «Combinator/CQ.fail» :=
  fun (_ : T) (_ : T) => let x2 : T := «Combinator/CQ.bad»; x2

def «Combinator/CQ.orElse» :=
  fun (x0 : T → T → T) (x1 : T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      let x5 : T := x4;
      if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
        let _ : T := Const.child x5 (leaf 0); x4
      else
        x1 x2 x3);
    x2

def «Combinator/CS.res» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator/CS.bad» := Const.node (leaf 0) ([] : List T)

def «Combinator/CS.ok» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Combinator/CS.pure» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «Combinator/CS.ok» («Combinator/CS.res» x0 x2));
    x1

def «Combinator/CS.fail» :=
  fun (_ : T) (_ : T) => let x2 : T := «Combinator/CS.bad»; x2

def «Combinator/CS.orElse» :=
  fun (x0 : T → T → T) (x1 : T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      let x5 : T := x4;
      if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
        let _ : T := Const.child x5 (leaf 0); x4
      else
        x1 x2 x3);
    x2

def «Combinator/CP.res» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator/CP.bad» := Const.node (leaf 0) ([] : List T)

def «Combinator/CP.ok» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Combinator/CP.pure» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «Combinator/CP.ok» («Combinator/CP.res» x0 x2));
    x1

def «Combinator/CP.fail» :=
  fun (_ : T) (_ : T) => let x2 : T := «Combinator/CP.bad»; x2

def «Combinator/CP.orElse» :=
  fun (x0 : T → T → T) (x1 : T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      let x5 : T := x4;
      if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
        let _ : T := Const.child x5 (leaf 0); x4
      else
        x1 x2 x3);
    x2

def «Combinator/CE.res» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator/CE.bad» := Const.node (leaf 0) ([] : List T)

def «Combinator/CE.ok» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Combinator/CE.pure» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «Combinator/CE.ok» («Combinator/CE.res» x0 x2));
    x1

def «Combinator/CE.fail» :=
  fun (_ : T) (_ : T) => let x2 : T := «Combinator/CE.bad»; x2

def «Combinator/CE.orElse» :=
  fun (x0 : T → T → T) (x1 : T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      let x5 : T := x4;
      if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
        let _ : T := Const.child x5 (leaf 0); x4
      else
        x1 x2 x3);
    x2

def «Combinator/CC.res» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator/CC.bad» := Const.node (leaf 0) ([] : List T)

def «Combinator/CC.ok» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Combinator/CC.pure» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «Combinator/CC.ok» («Combinator/CC.res» x0 x2));
    x1

def «Combinator/CC.fail» :=
  fun (_ : T) (_ : T) => let x2 : T := «Combinator/CC.bad»; x2

def «Combinator/CC.orElse» :=
  fun (x0 : T → T → T) (x1 : T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      let x5 : T := x4;
      if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
        let _ : T := Const.child x5 (leaf 0); x4
      else
        x1 x2 x3);
    x2

def «Combinator/CYs.res» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator/CYs.bad» := Const.node (leaf 0) ([] : List T)

def «Combinator/CYs.ok» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Combinator/CYs.pure» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «Combinator/CYs.ok» («Combinator/CYs.res» x0 x2));
    x1

def «Combinator/CYs.fail» :=
  fun (_ : T) (_ : T) => let x2 : T := «Combinator/CYs.bad»; x2

def «Combinator/CYs.orElse» :=
  fun (x0 : T → T → T) (x1 : T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      let x5 : T := x4;
      if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
        let _ : T := Const.child x5 (leaf 0); x4
      else
        x1 x2 x3);
    x2

def «Combinator/CPs.res» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator/CPs.bad» := Const.node (leaf 0) ([] : List T)

def «Combinator/CPs.ok» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Combinator/CPs.pure» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «Combinator/CPs.ok» («Combinator/CPs.res» x0 x2));
    x1

def «Combinator/CPs.fail» :=
  fun (_ : T) (_ : T) => let x2 : T := «Combinator/CPs.bad»; x2

def «Combinator/CPs.orElse» :=
  fun (x0 : T → T → T) (x1 : T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      let x5 : T := x4;
      if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
        let _ : T := Const.child x5 (leaf 0); x4
      else
        x1 x2 x3);
    x2

def «Combinator/COY.res» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator/COY.bad» := Const.node (leaf 0) ([] : List T)

def «Combinator/COY.ok» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Combinator/COY.pure» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «Combinator/COY.ok» («Combinator/COY.res» x0 x2));
    x1

def «Combinator/COY.fail» :=
  fun (_ : T) (_ : T) => let x2 : T := «Combinator/COY.bad»; x2

def «Combinator/COY.orElse» :=
  fun (x0 : T → T → T) (x1 : T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      let x5 : T := x4;
      if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
        let _ : T := Const.child x5 (leaf 0); x4
      else
        x1 x2 x3);
    x2

def «Combinator/COP.res» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator/COP.bad» := Const.node (leaf 0) ([] : List T)

def «Combinator/COP.ok» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Combinator/COP.pure» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «Combinator/COP.ok» («Combinator/COP.res» x0 x2));
    x1

def «Combinator/COP.fail» :=
  fun (_ : T) (_ : T) => let x2 : T := «Combinator/COP.bad»; x2

def «Combinator/COP.orElse» :=
  fun (x0 : T → T → T) (x1 : T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      let x5 : T := x4;
      if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
        let _ : T := Const.child x5 (leaf 0); x4
      else
        x1 x2 x3);
    x2

def «Combinator/CA.res» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator/CA.bad» := Const.node (leaf 0) ([] : List T)

def «Combinator/CA.ok» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Combinator/CA.pure» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «Combinator/CA.ok» («Combinator/CA.res» x0 x2));
    x1

def «Combinator/CA.fail» :=
  fun (_ : T) (_ : T) => let x2 : T := «Combinator/CA.bad»; x2

def «Combinator/CA.orElse» :=
  fun (x0 : T → T → T) (x1 : T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      let x5 : T := x4;
      if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
        let _ : T := Const.child x5 (leaf 0); x4
      else
        x1 x2 x3);
    x2

def «Combinator.bindTToT» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CT.bad»);
    x2

def «Combinator.bindTToY» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CY.bad»);
    x2

def «Combinator.bindTToP» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CP.bad»);
    x2

def «Combinator.bindTToC» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CC.bad»);
    x2

def «Combinator.bindYToT» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CT.bad»);
    x2

def «Combinator.bindYToY» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CY.bad»);
    x2

def «Combinator.bindYToP» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CP.bad»);
    x2

def «Combinator.bindYToYs» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CYs.bad»);
    x2

def «Combinator.bindYToA» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CA.bad»);
    x2

def «Combinator.bindQToT» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CT.bad»);
    x2

def «Combinator.bindQToP» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CP.bad»);
    x2

def «Combinator.bindQToE» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CE.bad»);
    x2

def «Combinator.bindSToY» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CY.bad»);
    x2

def «Combinator.bindSToQ» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CQ.bad»);
    x2

def «Combinator.bindSToP» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CP.bad»);
    x2

def «Combinator.bindPToT» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CT.bad»);
    x2

def «Combinator.bindPToY» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CY.bad»);
    x2

def «Combinator.bindPToP» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CP.bad»);
    x2

def «Combinator.bindPToPs» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CPs.bad»);
    x2

def «Combinator.bindPToOP» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/COP.bad»);
    x2

def «Combinator.bindEToT» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CT.bad»);
    x2

def «Combinator.bindEToP» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CP.bad»);
    x2

def «Combinator.bindCToT» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CT.bad»);
    x2

def «Combinator.bindCToP» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CP.bad»);
    x2

def «Combinator.bindCToE» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CE.bad»);
    x2

def «Combinator.bindCToC» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CC.bad»);
    x2

def «Combinator.bindYsToY» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CY.bad»);
    x2

def «Combinator.bindYsToP» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CP.bad»);
    x2

def «Combinator.bindYsToE» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CE.bad»);
    x2

def «Combinator.bindYsToYs» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CYs.bad»);
    x2

def «Combinator.bindPsToP» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CP.bad»);
    x2

def «Combinator.bindPsToPs» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CPs.bad»);
    x2

def «Combinator.bindOYToY» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CY.bad»);
    x2

def «Combinator.bindOPToP» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CP.bad»);
    x2

def «Combinator.bindAToP» :=
  fun (x0 : T → T → T) (x1 : T → T → T → T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      let x4 : T := x0 x2 x3;
      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := x5;
        let x7 : T := Const.child x6 (leaf 0);
        let x8 : T := Const.child x6 (leaf 1); x1 x7 x2 x8
      else
        «Combinator/CP.bad»);
    x2

def «Combinator.pmGet» :=
  fun (_ : T) (x1 : T) =>
    let x2 : T := «Combinator/CS.ok» («Combinator/CS.res» x1 x1); x2

def «Combinator.pmGuard» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      if (x0).label ≠ 0 then
        «Combinator/CT.ok» («Combinator/CT.res» (leaf 0) x2)
      else
        «Combinator/CT.bad»);
    x1

def «Combinator.mapMEqC» :=
  fun (x0 : T → T → T → T) (x1 : List T) =>
    let x2 : T →
      T →
        T := Const.foldr
      (α := T)
      (β := T → T → T)
      (fun (x2 : T) (x3 : T → T → T) =>
        «Combinator.bindTToC»
          (x0 x2)
          (fun (x4 : T) =>
            «Combinator.bindCToC»
              x3
              (fun (x5 : T) =>
                «Combinator/CC.pure»
                  («Combinator.certs» (x4 :: («Combinator.certsOf» x5))))))
      («Combinator/CC.pure» («Combinator.certs» ([] : List T)))
      x1;
    x2

def «Combinator.mapMPairC» :=
  fun (x0 : T → T → T → T) (x1 : List T) =>
    let x2 : T →
      T →
        T := Const.foldr
      (α := T)
      (β := T → T → T)
      (fun (x2 : T) (x3 : T → T → T) =>
        «Combinator.bindTToC»
          (x0 x2)
          (fun (x4 : T) =>
            «Combinator.bindCToC»
              x3
              (fun (x5 : T) =>
                «Combinator/CC.pure»
                  («Combinator.certs» (x4 :: («Combinator.certsOf» x5))))))
      («Combinator/CC.pure» («Combinator.certs» ([] : List T)))
      x1;
    x2

def «Combinator.mapMTY» :=
  fun (x0 : T → T → T → T) (x1 : List T) =>
    let x2 : T →
      T →
        T := Const.foldr
      (α := T)
      (β := T → T → T)
      (fun (x2 : T) (x3 : T → T → T) =>
        «Combinator.bindYToYs»
          (x0 x2)
          (fun (x4 : T) =>
            «Combinator.bindYsToYs»
              x3
              (fun (x5 : T) =>
                «Combinator/CYs.pure»
                  («Combinator.ptys» (x4 :: («Combinator.ptysOf» x5))))))
      («Combinator/CYs.pure» («Combinator.ptys» ([] : List T)))
      x1;
    x2

def «Combinator.seqY» :=
  fun (x0 : List (T → T → T)) =>
    let x1 : T →
      T →
        T := Const.foldr
      (α := T → T → T)
      (β := T → T → T)
      (fun (x1 : T → T → T) (x2 : T → T → T) =>
        «Combinator.bindYToYs»
          x1
          (fun (x3 : T) =>
            «Combinator.bindYsToYs»
              x2
              (fun (x4 : T) =>
                «Combinator/CYs.pure»
                  («Combinator.ptys» (x3 :: («Combinator.ptysOf» x4))))))
      («Combinator/CYs.pure» («Combinator.ptys» ([] : List T)))
      x0;
    x1

def «Combinator.seqP» :=
  fun (x0 : List (T → T → T)) =>
    let x1 : T →
      T →
        T := Const.foldr
      (α := T → T → T)
      (β := T → T → T)
      (fun (x1 : T → T → T) (x2 : T → T → T) =>
        «Combinator.bindPToPs»
          x1
          (fun (x3 : T) =>
            «Combinator.bindPsToPs»
              x2
              (fun (x4 : T) =>
                «Combinator/CPs.pure»
                  («Combinator.pairs» (x3 :: («Combinator.pairsOf» x4))))))
      («Combinator/CPs.pure» («Combinator.pairs» ([] : List T)))
      x0;
    x1

def «Combinator.findIdx» :=
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
      («Combinator/Eqns.length» x1, «Prelude.none»)
      x1).2;
    x2

def «Combinator.seq0» :=
  «PartialHorn.mkSeq»
    ([] : List T)
    ([] : List T)
    («PartialHorn.eqn» (leaf 0) (leaf 0))

def «Combinator.pdefn0» :=
  «PartialHorn.pdefn»
    («PartialHorn.sorts» ([] : List T))
    (leaf 0)
    (leaf 0)

def «Combinator.axiomAt» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (if (Const.lt
      x0
      («Combinator/Seqs.length» «Theory.axioms»)).label ≠ 0 then
      «Combinator/CQ.pure»
        («Combinator/Seqs.atOr» «Combinator.seq0» «Theory.axioms» x0)
    else
      «Combinator.bindSToQ»
        «Combinator.pmGet»
        (fun (x1 : T) =>
          let x2 : T := Const.sub x0 («Combinator/Seqs.length» «Theory.axioms»);
          let x3 : T := «PartialHorn/OPDefn.nthOf»
            («Combinator.stDefs» x1)
            (Const.div x2 (leaf 2));
          if («PartialHorn/OPDefn.isJust» x3).label ≠ 0 then
            let x4 : T := «PartialHorn/OSequent.nthOf»
              («PartialHorn.pdAxioms»
                (Const.add
                  («Combinator/OpSigs.length» «Theory.sig»)
                  (Const.div x2 (leaf 2)))
                («PartialHorn/OPDefn.fromMaybe» «Combinator.pdefn0» x3))
              (Const.mod x2 (leaf 2));
            if («PartialHorn/OSequent.isJust» x4).label ≠ 0 then
              «Combinator/CQ.pure»
                («PartialHorn/OSequent.fromMaybe» «Combinator.seq0» x4)
            else
              «Combinator/CQ.fail»
          else
            «Combinator/CQ.fail»));
    x1

def «Combinator.addLemma» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      «Combinator/CT.ok»
        («Combinator/CT.res»
          («Combinator.scCite»
            x2
            («Combinator/DevL.length» («Combinator.stDev» x3)))
          («Combinator.withDev»
            x3
            («Combinator/DevL.append»
              («Combinator.stDev» x3)
              («Combinator/DevL.single»
                («Combinator.devEntry» («Combinator.scSeq» x2 x0) x1))))));
    x2

def «Combinator.lookup» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «Combinator/COY.ok»
        («Combinator/COY.res»
          («Combinator.memoFind» («Combinator.stMemo» x2) x0)
          x2));
    x1

def «Combinator.memoize» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «Combinator/CT.ok»
        («Combinator/CT.res»
          (leaf 0)
          («Combinator.withMemo»
            x2
            ((«Combinator.memoEntry» («Combinator.tyT» x0) x0) ::
              («Combinator.stMemo» x2)))));
    x1

def «Combinator.memoRet» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := «Combinator.bindTToY»
      («Combinator.memoize» x0)
      (fun (_ : T) => «Combinator/CY.pure» x0);
    x1

def «Combinator.dfdCert» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      if («Combinator.stInfer» x3).label ≠ 0 then
        «Combinator/CT.ok»
          («Combinator/CT.res» (Const.node (leaf 9) («Prelude.single» x0)) x3)
      else
        «Combinator.addLemma» («Theory.dfd» x0) x1 x2 x3);
    x2

def «Combinator.eqCert» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T →
      T →
        T := (fun (x2 : T) (x3 : T) =>
      if («Combinator.stInfer» x3).label ≠ 0 then
        «Combinator/CT.ok»
          («Combinator/CT.res»
            (Const.node
              (leaf 10)
              («Theory.l2» («PartialHorn.eqLhs» x0) («PartialHorn.eqRhs» x0)))
            x3)
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
        «Combinator/CT.ok»
          («Combinator/CT.res»
            (if («Combinator.stInfer» x3).label ≠ 0 then
              Const.node
                (leaf 10)
                («Theory.l2» («Combinator.tyT» x0) («Combinator.tyT» x1))
            else
              «Combinator.cTrans»
                («Combinator.tyLoC» x0)
                («Combinator.cSymm» («Combinator.tyLoC» x1)))
            x3)
      else
        «Combinator/CT.bad»);
    x2

def «Combinator.proveHyp» :=
  fun (x0 : List T → T → T → T → T) (x1 : List T) (x2 : T) =>
    let x3 : T →
      T →
        T := «Combinator.bindYToT»
      (x0 x1 («PartialHorn.eqLhs» x2))
      (fun (x3 : T) =>
        if (Const.equal
          («PartialHorn.eqLhs» x2)
          («PartialHorn.eqRhs» x2)).label ≠ 0 then
          «Combinator/CT.pure» («Combinator.tyDfd» x3)
        else
          «Combinator.bindYToT»
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
        T := «Combinator.bindQToP»
      («Combinator.axiomAt» x3)
      (fun (x5 : T) =>
        «Combinator.bindCToP»
          («Combinator.mapMEqC»
            (fun (x6 : T) =>
              if (Const.equal
                x6
                («Theory.dfd»
                  («PartialHorn.opVars»
                    x2
                    («Combinator/TyL.length» x1)))).label ≠ 0 then
                «Combinator/CT.pure» x4
              else
                «Combinator.proveHyp» x0 x1 x6)
            («PartialHorn.seqHyps» x5))
          (fun (x6 : T) =>
            let x7 : T := «Combinator.cAx»
              x3
              («Combinator/YT.map» «Combinator.tyT» x1)
              («Combinator/YT.map» «Combinator.tyDfd» x1)
              («Combinator.certsOf» x6);
            «Combinator.bindYToP»
              (x0 x1 («PartialHorn.eqRhs» («PartialHorn.seqConcl» x5)))
              (fun (x8 : T) =>
                «Combinator/CP.pure»
                  («Language.pr»
                    («Combinator.tyLo» x8)
                    («Combinator.cTrans» x7 («Combinator.tyLoC» x8))))));
    x5

def «Combinator.typeDefined» :=
  fun (x0 : List T → T → T → T → T) (x1 : T) (x2 : T) (x3 : List T) =>
    let x4 : T →
      T →
        T := «Combinator.bindSToY»
      «Combinator.pmGet»
      (fun (x4 : T) =>
        let x5 : T := «PartialHorn/OPDefn.nthOf» («Combinator.stDefs» x4) x1;
        if («PartialHorn/OPDefn.isJust» x5).label ≠ 0 then
          let x6 : List T := «Combinator/YT.map» «Combinator.tyT» x3;
          let x7 : T := «PartialHorn.phOp»
            (Const.add («Combinator/OpSigs.length» «Theory.sig») x1)
            x6;
          «Combinator.bindYToY»
            (x0
              x3
              («PartialHorn.pdBody»
                («PartialHorn/OPDefn.fromMaybe» «Combinator.pdefn0» x5)))
            (fun (x8 : T) =>
              «Combinator.bindSToY»
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
                    «Combinator.bindTToY»
                      («Combinator.addLemma»
                        («PartialHorn.eqn» x7 («Combinator.tyT» x8))
                        («Combinator.cAx»
                          («Infer.defAxIdx» x1)
                          x6
                          («Combinator/YT.map» «Combinator.tyDfd» x3)
                          («Prelude.single» («Combinator.tyDfd» x8))))
                      (fun (x10 : T) =>
                        «Combinator.bindTToY»
                          («Combinator.addLemma»
                            («Theory.dfd» x7)
                            («Combinator.cTrans» x10 («Combinator.cSymm» x10)))
                          (fun (x11 : T) =>
                            if (Const.eq x2 (leaf 0)).label ≠ 0 then
                              «Combinator.bindTToY»
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
                              «Combinator.bindTToY»
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
                                  «Combinator.bindTToY»
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
          «Combinator/CY.fail»);
    x4

def «Combinator.typeOpDfd» :=
  fun (x0 : List T → T → T → T → T) (x1 : T) (x2 : List T) =>
    let x3 : T →
      T →
        T := (let x3 : List T := «Combinator/YT.map» «Combinator.tyT» x2;
              let x4 : T := «Combinator/OODfd.nthOf» «Infer.dfdRules» x1;
              if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
                let x5 : T := Const.child x4 (leaf 0);
                let x6 : T := x5;
                if (Const.eq (Const.label x6) (leaf 1)).label ≠ 0 then
                  let x7 : T := Const.child x6 (leaf 0);
                  let x8 : T := x7;
                  if (Const.eq (Const.label x8) (leaf 0)).label ≠ 0 then
                    let x9 : T := Const.child x8 (leaf 0);
                    «Combinator.bindQToT»
                      («Combinator.axiomAt» x9)
                      (fun (x10 : T) =>
                        «Combinator.bindCToT»
                          («Combinator.mapMEqC»
                            («Combinator.proveHyp» x0 x2)
                            («PartialHorn.seqHyps» x10))
                          (fun (x11 : T) =>
                            «Combinator/CT.pure»
                              («Combinator.cAx»
                                x9
                                x3
                                («Combinator/YT.map» «Combinator.tyDfd» x2)
                                («Combinator.certsOf» x11))))
                  else
                    if (Const.eq (Const.label x8) (leaf 1)).label ≠ 0 then
                      let x9 : T := Const.child x8 (leaf 0);
                      «Combinator/CT.pure»
                        («Combinator.cStrict»
                          (leaf 0)
                          («Combinator.cAx»
                            x9
                            x3
                            («Combinator/YT.map» «Combinator.tyDfd» x2)
                            ([] : List T)))
                    else
                      let x9 : T := Const.child x8 (leaf 0);
                      let x10 : T := «Combinator.cAx»
                        x9
                        ([] : List T)
                        ([] : List T)
                        ([] : List T);
                      «Combinator/CT.pure»
                        («Combinator.cTrans» («Combinator.cSymm» x10) x10)
                else
                  «Combinator/CT.fail»
              else
                «Combinator/CT.fail»);
    x3

def «Combinator.typeOpObj» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List T) =>
    let x4 : T →
      T →
        T := (let x4 : T := «PartialHorn.phOp»
                x0
                («Combinator/YT.map»
                  (fun (x4 : T) =>
                    if (Const.eq («Combinator.tySort» x4) (leaf 0)).label ≠ 0 then
                      «Combinator.tyLo» x4
                    else
                      «Combinator.tyT» x4)
                  x3);
              if (Const.equal x4 x1).label ≠ 0 then
                «Combinator/CY.pure» («Combinator.pty» x1 (leaf 0) x2 x1 x2 x1 x2)
              else
                «Combinator.bindTToY»
                  («Combinator.eqCert»
                    («PartialHorn.eqn» x1 x4)
                    («Combinator.cCong»
                      x2
                      («Combinator/YT.map»
                        (fun (x5 : T) =>
                          if (Const.eq («Combinator.tySort» x5) (leaf 0)).label ≠ 0 then
                            «Combinator.tyLoC» x5
                          else
                            «Combinator.tyDfd» x5)
                        x3)))
                  (fun (x5 : T) =>
                    «Combinator/CY.pure» («Combinator.pty» x1 (leaf 0) x2 x4 x5 x4 x5)));
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
        (Const.eq («Combinator/TyL.length» x5) (leaf 1))).label ≠ 0 then
        let x6 : T := «Combinator/TyL.atOr» «Combinator.pty0» x5 (leaf 0);
        «Combinator/CY.pure»
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
          (Const.eq («Combinator/TyL.length» x5) (leaf 1))).label ≠ 0 then
          let x6 : T := «Combinator/TyL.atOr» «Combinator.pty0» x5 (leaf 0);
          «Combinator/CY.pure»
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
        «Combinator.bindPToY»
          («Combinator.pBound» x0 x5 x1 («Prelude.get» («Prelude.get» x6)) x4)
          (fun (x8 : T) =>
            «Combinator.bindPToY»
              («Combinator.pBound» x0 x5 x1 («Prelude.get» («Prelude.get» x7)) x4)
              (fun (x9 : T) =>
                «Combinator.bindTToY»
                  («Combinator.eqCert»
                    («PartialHorn.eqn» («Theory.dom» x3) («Language.p1» x8))
                    («Language.p2» x8))
                  (fun (x10 : T) =>
                    «Combinator.bindTToY»
                      («Combinator.eqCert»
                        («PartialHorn.eqn» («Theory.cod» x3) («Language.p1» x9))
                        («Language.p2» x9))
                      (fun (x11 : T) =>
                        «Combinator/CY.pure»
                          («Combinator.pty»
                            x3
                            (leaf 1)
                            x4
                            («Language.p1» x8)
                            x10
                            («Language.p1» x9)
                            x11)))))
      else
        «Combinator/CY.fail»);
    x6

def «Combinator.opSig0» :=
  «PartialHorn.opSig» («PartialHorn.sorts» ([] : List T)) (leaf 0)

def «Combinator.typeOp» :=
  fun (x0 : List T → T → T → T → T) (x1 : T) (x2 : List T) =>
    let x3 : T →
      T →
        T := «Combinator.bindSToY»
      «Combinator.pmGet»
      (fun (x3 : T) =>
        let x4 : T := «PartialHorn/OOpSig.nthOf» («Combinator.stSig» x3) x1;
        if («PartialHorn/OOpSig.isJust» x4).label ≠ 0 then
          let x5 : T := «PartialHorn/OOpSig.fromMaybe» «Combinator.opSig0» x4;
          if («Base.equalTs»
            («Combinator/YT.map» «Combinator.tySort» x2)
            («PartialHorn.opArgs» x5)).label ≠ 0 then
            if (Const.lt
              x1
              («Combinator/OpSigs.length» «Theory.sig»)).label ≠ 0 then
              let x6 : T := «PartialHorn.phOp»
                x1
                («Combinator/YT.map» «Combinator.tyT» x2);
              «Combinator.bindTToY»
                («Combinator.typeOpDfd» x0 x1 x2)
                (fun (x7 : T) =>
                  «Combinator.bindTToY»
                    («Combinator.dfdCert» x6 x7)
                    (fun (x8 : T) =>
                      «Combinator.bindYToY»
                        («Combinator.typeOpTy» x0 x1 («PartialHorn.opSort» x5) x6 x8 x2)
                        «Combinator.memoRet»))
            else
              «Combinator.typeDefined»
                x0
                (Const.sub x1 («Combinator/OpSigs.length» «Theory.sig»))
                («PartialHorn.opSort» x5)
                x2
          else
            «Combinator/CY.fail»
        else
          «Combinator/CY.fail»);
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
                  «Combinator/CY.fail»
              else
                «Combinator.bindOYToY»
                  («Combinator.lookup» (x2 x3))
                  (fun (x6 : T) =>
                    if («Combinator/OPTy.isJust» x6).label ≠ 0 then
                      «Combinator/CY.pure»
                        («Combinator/OPTy.fromMaybe» «Combinator.pty0» x6)
                    else
                      «Combinator.bindYsToY»
                        («Combinator.seqY» x4)
                        (fun (x7 : T) =>
                          «Combinator.typeOp»
                            x0
                            (Const.sub x5 (leaf 1))
                            («Combinator.ptysOf» x7))));
    x5

def «Combinator.eqn0» := «PartialHorn.eqn» (leaf 0) (leaf 0)

def «Combinator.varSide» :=
  fun (x0 : T → T → T → T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T →
      T →
        T := (fun (x5 : T) (x6 : T) =>
      let x7 : T := «PartialHorn.phOp»
        x3
        («Prelude.single» («PartialHorn.phVar» x1));
      let x8 : T := «Combinator.findIdx»
        (fun (x8 : T) => Const.equal («PartialHorn.eqLhs» x8) x7)
        («Combinator.scHyps» x5);
      if («Prelude.isSome» x8).label ≠ 0 then
        let x9 : T := «Prelude.get» x8;
        let x10 : T := «PartialHorn/OEqn.nthOf» («Combinator.scHyps» x5) x9;
        if («PartialHorn/OEqn.isJust» x10).label ≠ 0 then
          «Combinator.bindYToP»
            (x0
              («PartialHorn.eqRhs»
                («PartialHorn/OEqn.fromMaybe» «Combinator.eqn0» x10)))
            (fun (x11 : T) =>
              «Combinator/CP.pure»
                («Language.pr»
                  («Combinator.tyLo» x11)
                  (if (x2).label ≠ 0 then
                    Const.node (leaf 10) («Theory.l2» x7 («Combinator.tyLo» x11))
                  else
                    «Combinator.cTrans» («Combinator.cHyp» x9) («Combinator.tyLoC» x11))))
            x5
            x6
        else
          «Combinator/CP.bad»
      else
        «Combinator/CP.ok»
          («Combinator/CP.res»
            («Language.pr»
              x7
              («Combinator.cAx»
                x4
                («Prelude.single» («PartialHorn.phVar» x1))
                («Prelude.single» («Combinator.cRefl» x1))
                ([] : List T)))
            x6));
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
          «Combinator/CY.ok»
            («Combinator/CY.res»
              («Combinator.pty»
                («PartialHorn.phVar» x1)
                (leaf 0)
                («Combinator.cRefl» x1)
                («PartialHorn.phVar» x1)
                («Combinator.cRefl» x1)
                («PartialHorn.phVar» x1)
                («Combinator.cRefl» x1))
              x3)
        else
          if (Const.eq x5 (leaf 1)).label ≠ 0 then
            let x6 : T := «Combinator.stInfer» x3;
            «Combinator.bindPToY»
              («Combinator.varSide» x0 x1 x6 (leaf 0) (leaf 0))
              (fun (x7 : T) =>
                «Combinator.bindPToY»
                  («Combinator.varSide» x0 x1 x6 (leaf 1) (leaf 1))
                  (fun (x8 : T) =>
                    «Combinator/CY.pure»
                      («Combinator.pty»
                        («PartialHorn.phVar» x1)
                        (leaf 1)
                        («Combinator.cRefl» x1)
                        («Language.p1» x7)
                        («Language.p2» x7)
                        («Language.p1» x8)
                        («Language.p2» x8))))
              x2
              x3
          else
            «Combinator/CY.bad»
      else
        «Combinator/CY.bad»);
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
                let x5 : T := «Combinator/OPTy.nthOf» x2 x4;
                if («Combinator/OPTy.isJust» x5).label ≠ 0 then
                  «Combinator/CY.pure»
                    («Combinator/OPTy.fromMaybe» «Combinator.pty0» x5)
                else
                  «Combinator/CY.fail»)
              («PartialHorn.phSubst» («Combinator/YT.map» «Combinator.tyT» x2)))
            x3,
          fun (x2 : T) =>
            Const.para
              (α := T → T → T)
              («Combinator.typeStep»
                (x1).1
                («Combinator.typeVar» (x1).2)
                (fun (x3 : T) => x3))
              x2))
      (fun (_ : List T) (_ : T) => «Combinator/CY.fail»,
        fun (_ : T) => «Combinator/CY.fail»)
      x0;
    x1

def «Combinator.typeTerm» :=
  fun (x0 : T) =>
    let x1 : T → T → T := («Combinator.typers» (leaf 8)).2 x0; x1

def «Combinator.typePattern» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T → T → T := («Combinator.typers» (leaf 8)).1 x0 x1; x2

def «Combinator/DefSig.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Combinator.pmStart» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : T := «Combinator.pst»
      («Combinator.devs» x0)
      («Combinator.memos» ([] : List T))
      («Combinator.nfList» ([] : List T))
      («PartialHorn.pdefns» x1)
      («PartialHorn.opSigs»
        («Combinator/OpSigs.append»
          «Theory.sig»
          («Combinator/DefSig.map»
            (fun (x3 : T) =>
              «PartialHorn.opSig»
                («PartialHorn.sorts» («PartialHorn.pdCtx» x3))
                («PartialHorn.pdSort» x3))
            x1)))
      x2;
    x3

def «Combinator.srcAx» :=
  fun (x0 : T) => Const.node (leaf 0) (x0 :: ([] : List T))

def «Combinator.srcThm» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Combinator.dev0» :=
  «Combinator.devEntry» «Combinator.seq0» (leaf 0)

def «Combinator.srcSeq» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (let x1 : T := x0;
              if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
                let x2 : T := Const.child x1 (leaf 0); «Combinator.axiomAt» x2
              else
                let x2 : T := Const.child x1 (leaf 0);
                «Combinator.bindSToQ»
                  «Combinator.pmGet»
                  (fun (x3 : T) =>
                    let x4 : T := «Combinator/ODev.nthOf» («Combinator.stDev» x3) x2;
                    if («Combinator/ODev.isJust» x4).label ≠ 0 then
                      «Combinator/CQ.pure»
                        («Combinator.devSeq»
                          («Combinator/ODev.fromMaybe» «Combinator.dev0» x4))
                    else
                      «Combinator/CQ.fail»));
    x1

def «Combinator.srcCert» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : List T) =>
    let x4 : T := (let x4 : T := x0;
                   if (Const.eq (Const.label x4) (leaf 0)).label ≠ 0 then
                     let x5 : T := Const.child x4 (leaf 0); «Combinator.cAx» x5 x1 x2 x3
                   else
                     let x5 : T := Const.child x4 (leaf 0); «Combinator.cThm» x5 x1 x2 x3);
    x4

def «Combinator.labels» := fun (x0 : List T) => Const.node (leaf 0) x0

def «Combinator.rwRule» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «Combinator/RwRules.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Combinator/RwRules.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Combinator/RwRules.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Combinator/RwRules.reverse» :=
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

def «Combinator/RwRules.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Combinator/RwRules.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Combinator/RwRules.tail» x1 x0;
    x2

def «Combinator/RwRules.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Combinator/RwRules.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Combinator/RwL.l2» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List T := (x0 :: (x1 :: ([] : List T))); x2

def «Combinator/RwL.l3» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : List T := (x0 :: («Combinator/RwL.l2» x1 x2)); x3

def «Combinator/RwL.l4» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : List T := (x0 :: («Combinator/RwL.l3» x1 x2 x3)); x4

def «Combinator/RwL.l5» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : List T := (x0 :: («Combinator/RwL.l4» x1 x2 x3 x4)); x5

def «Combinator/RwL.l6» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : List T := (x0 :: («Combinator/RwL.l5» x1 x2 x3 x4 x5)); x6

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
            let x4 : T := Const.child x1 (leaf 2);
            let x5 : T := x4;
            let x6 : List
              T := Const.iter
              (α := List T)
              (fun (x6 : List T) =>
                Const.lcase
                  (α := T)
                  (β := List T)
                  x6
                  ([] : List T)
                  (fun (_ : T) (x8 : List T) => x8))
              (Const.children x5)
              (leaf 0);
            x6);
    x1

def «Combinator.opts» := fun (x0 : List T) => Const.node (leaf 0) x0

def «Combinator.matchSt» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator/OMatch.nothing» := Const.node (leaf 0) ([] : List T)

def «Combinator/OMatch.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Combinator/OMatch.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let _ : T := Const.child x1 (leaf 0); leaf 1
                   else
                     leaf 0);
    x1

def «Combinator/OMatch.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x3
                   else
                     x0);
    x2

def «Combinator/OMatch.nthOf» :=
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
      «Combinator/OMatch.nothing»
      (fun (x2 : T) (_ : List T) => «Combinator/OMatch.just» x2);
    x2

def «Combinator/OMatch.allJust» :=
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

def «Combinator.msSigma» :=
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

def «Combinator.msObjs» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let x3 : T := Const.child x1 (leaf 1); «Combinator.pairsOf» x3);
    x1

def «Combinator.msDefer» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Combinator.matchSt»
      («Combinator.opts» («Combinator.msSigma» x0))
      («Combinator.pairs»
        ((«Language.pr» x1 x2) :: («Combinator.msObjs» x0)));
    x3

def «Combinator.bindM» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x1 x3
                   else
                     «Combinator/OMatch.nothing»);
    x2

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
          («Combinator/OMatch.just» x6)
          (fun (x7 : T) (x8 : List T) =>
            «Combinator.bindM» (x3 x7 x6) (fun (x9 : T) => x4 x8 x9)))
      (fun (_ : List T) (x4 : T) => «Combinator/OMatch.just» x4)
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
                «Combinator/OMatch.just» x5
              else
                if (Const.equal
                  («Prelude.nth» x1 x7)
                  («Prelude.some» (leaf 0))).label ≠ 0 then
                  «Combinator/OMatch.just» («Combinator.msDefer» x5 x2 x4)
                else
                  «Combinator/OMatch.nothing»
            else
              «Combinator/OMatch.just»
                («Combinator.matchSt»
                  («Combinator.opts»
                    («Prover.setAt» («Combinator.msSigma» x5) x7 («Prelude.some» x4)))
                  («Combinator.pairs» («Combinator.msObjs» x5)))
          else
            «Combinator/OMatch.nothing»
        else
          «Combinator/OMatch.nothing»
      else
        if (Const.equal
          («PartialHorn.sortOf» x0 x1 x2)
          («Prelude.some» (leaf 0))).label ≠ 0 then
          «Combinator/OMatch.just» («Combinator.msDefer» x5 x2 x4)
        else
          if («Prelude.and»
            (Const.eq (Const.label x4) x6)
            (Const.eq
              («Prelude.length» (Const.children x4))
              («Prelude.length» (Const.children x2)))).label ≠ 0 then
            «Combinator.matchKids» x3 (Const.children x4) x5
          else
            «Combinator/OMatch.nothing»);
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
          («Combinator/CC.pure» («Combinator.certs» ([] : List T)))
          (fun (x5 : T) (x6 : List T) =>
            «Combinator.bindTToC»
              (x2 x5)
              (fun (x7 : T) =>
                «Combinator.bindCToC»
                  (x3 x6)
                  (fun (x8 : T) =>
                    «Combinator/CC.pure»
                      («Combinator.certs» (x7 :: («Combinator.certsOf» x8)))))))
      (fun (_ : List T) =>
        «Combinator/CC.pure» («Combinator.certs» ([] : List T)))
      x0
      x1;
    x2

def «Combinator.bridgeStep» :=
  fun (x0 : List T) (x1 : T) (x2 : List (T → T → T → T)) =>
    let x3 : T →
      T →
        T →
          T := (fun (x3 : T) =>
      «Combinator.bindYToT»
        («Combinator.typeTerm» x3)
        (fun (x4 : T) =>
          if (Const.equal
            («PartialHorn.phSubst» («Combinator/YT.map» «Combinator.tyT» x0) x1)
            x3).label ≠ 0 then
            «Combinator/CT.pure» («Combinator.tyDfd» x4)
          else
            if (Const.eq («Combinator.tySort» x4) (leaf 0)).label ≠ 0 then
              «Combinator.bindYToT»
                («Combinator.typePattern» x0 x1)
                (fun (x5 : T) => «Combinator.objEq» x4 x5)
            else
              if («Prelude.or»
                (Const.eq (Const.label x1) (leaf 0))
                («Base.not»
                  (Const.eq
                    («Prelude.length» (Const.children x3))
                    («Prelude.length» (Const.children x1))))).label ≠ 0 then
                «Combinator/CT.fail»
              else
                «Combinator.bindCToT»
                  («Combinator.bridgeKids» x2 (Const.children x3))
                  (fun (x5 : T) =>
                    «Combinator/CT.pure»
                      («Combinator.cCong»
                        («Combinator.tyDfd» x4)
                        («Combinator.certsOf» x5)))));
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

def «Combinator.ms0» :=
  «Combinator.matchSt»
    («Combinator.opts» ([] : List T))
    («Combinator.pairs» ([] : List T))

def «Combinator.applyRule» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T →
      T →
        T := «Combinator.bindTToP»
      («Combinator.pmGuard»
        («Base.not»
          («Base.anyT»
            (fun (x2 : T) => Const.eq (Const.label x1) x2)
            («Combinator.rwAvoid» x0))))
      (fun (_ : T) =>
        «Combinator.bindQToP»
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
            «Combinator.bindSToP»
              «Combinator.pmGet»
              (fun (x6 : T) =>
                let x7 : T := «Combinator.matchPat»
                  («Combinator.stSig» x6)
                  («PartialHorn.seqCtx» x3)
                  x4
                  x1
                  («Combinator.matchSt»
                    («Combinator.opts»
                      («Base.mapT»
                        (fun (_ : T) => «Prelude.none»)
                        («PartialHorn.seqCtx» x3)))
                    («Combinator.pairs» ([] : List T)));
                if («Combinator/OMatch.isJust» x7).label ≠ 0 then
                  let x8 : T := «Combinator/OMatch.fromMaybe» «Combinator.ms0» x7;
                  let x9 : T := «Base.allSomeT» («Combinator.msSigma» x8);
                  if («Prelude.isSome» x9).label ≠ 0 then
                    let x10 : List T := Const.children («Prelude.get» x9);
                    «Combinator.bindYsToP»
                      («Combinator.mapMTY» «Combinator.typeTerm» x10)
                      (fun (x11 : T) =>
                        let x12 : List T := «Combinator.ptysOf» x11;
                        «Combinator.bindCToP»
                          («Combinator.mapMPairC»
                            (fun (x13 : T) =>
                              «Combinator.bindYToT»
                                («Combinator.typePattern» x12 («Language.p1» x13))
                                (fun (x14 : T) =>
                                  «Combinator.bindYToT»
                                    («Combinator.typeTerm» («Language.p2» x13))
                                    (fun (x15 : T) => «Combinator.objEq» x14 x15)))
                            («Combinator.msObjs» x8))
                          (fun (_ : T) =>
                            «Combinator.bindTToP»
                              («Combinator.bridge» x12 x4 x1)
                              (fun (x14 : T) =>
                                «Combinator.bindCToP»
                                  («Combinator.mapMEqC»
                                    («Combinator.proveHyp» «Combinator.typePattern» x12)
                                    («PartialHorn.seqHyps» x3))
                                  (fun (x15 : T) =>
                                    let x16 : T := «Combinator.srcCert»
                                      («Combinator.rwSrc» x0)
                                      x10
                                      («Combinator/YT.map» «Combinator.tyDfd» x12)
                                      («Combinator.certsOf» x15);
                                    «Combinator/CP.pure»
                                      («Language.pr»
                                        («PartialHorn.phSubst» x10 x5)
                                        («Combinator.cTrans»
                                          x14
                                          (if («Combinator.rwFlip» x0).label ≠ 0 then
                                            «Combinator.cSymm» x16
                                          else
                                            x16)))))))
                  else
                    «Combinator/CP.fail»
                else
                  «Combinator/CP.fail»)));
    x2

def «Combinator.firstRule» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T →
      T →
        T := Const.foldr
      (α := T)
      (β := T → T → T)
      (fun (x2 : T) (x3 : T → T → T) =>
        «Combinator/CP.orElse» («Combinator.applyRule» x2 x1) x3)
      «Combinator/CP.fail»
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
        «Combinator.bindYToA»
          («Combinator.typeTerm» x0)
          (fun (x5 : T) =>
            «Combinator.bindYToA»
              («Combinator.typeTerm» x1)
              (fun (x6 : T) =>
                «Combinator.bindYToA»
                  («Combinator.typeTerm» x3)
                  (fun (x7 : T) =>
                    «Combinator.bindYToA»
                      («Combinator.typeTerm» x4)
                      (fun (x8 : T) =>
                        «Combinator/CA.pure»
                          («Combinator.assoc»
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
                              («Prelude.single» («Combinator.tyDfd» x5))))))))
      else
        «Combinator/CA.fail»
    else
      «Combinator/CA.fail»);
    x1

def «Combinator.rewriteRoot» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T →
      T →
        T := «Combinator/CP.orElse»
      («Combinator.firstRule» x0 x1)
      («Combinator.bindAToP»
        («Combinator.assocLeft» x1)
        (fun (x2 : T) =>
          let x3 : T := x2;
          let x4 : T := Const.child x3 (leaf 0);
          let x5 : T := Const.child x3 (leaf 1);
          let x6 : T := Const.child x3 (leaf 2);
          let x7 : T := Const.child x3 (leaf 3);
          «Combinator.bindPToP»
            («Combinator.firstRule» x0 («Theory.comp» x4 x5))
            (fun (x8 : T) =>
              «Combinator.bindYToP»
                («Combinator.typeTerm» («Theory.comp» («Theory.comp» x4 x5) x6))
                (fun (x9 : T) =>
                  «Combinator.bindYToP»
                    («Combinator.typeTerm» x6)
                    (fun (x10 : T) =>
                      «Combinator/CP.pure»
                        («Language.pr»
                          («Theory.comp» («Language.p1» x8) x6)
                          («Combinator.cTrans»
                            x7
                            («Combinator.cCong»
                              («Combinator.tyDfd» x9)
                              («Theory.l2» («Language.p2» x8) («Combinator.tyDfd» x10))))))))));
    x2

def «Combinator.lookupNf» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (fun (_ : T) (x2 : T) =>
      «Combinator/COP.ok»
        («Combinator/COP.res»
          («Combinator.nfFind» («Combinator.stNfs» x2) x0)
          x2));
    x1

def «Combinator.memoizeNf» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T →
      T →
        T := «Combinator.bindTToP»
      (if (Const.equal x0 x1).label ≠ 0 then
        «Combinator/CT.pure» x2
      else
        «Combinator.addLemma» («PartialHorn.eqn» x0 x1) x2)
      (fun (x3 : T) (_ : T) (x5 : T) =>
        «Combinator/CP.ok»
          («Combinator/CP.res»
            («Language.pr» x1 x3)
            («Combinator.withNfs»
              x5
              ((«Combinator.nfEntry» x0 («Language.pr» x1 x3)) ::
                («Combinator.stNfs» x5)))));
    x3

def «Combinator.pr0» := «Language.pr» (leaf 0) (leaf 0)

def «Combinator.normStepP» :=
  fun (x0 : List T)
    (x1 : T → T → T → T)
    (x2 : T)
    (x3 : List (T → T → T)) =>
    let x4 : T →
      T →
        T := «Combinator.bindOPToP»
      («Combinator.lookupNf» x2)
      (fun (x4 : T) =>
        if («Language/OTPair.isJust» x4).label ≠ 0 then
          «Combinator/CP.pure» («Language/OTPair.fromMaybe» «Combinator.pr0» x4)
        else
          «Combinator.bindYToP»
            («Combinator.typeTerm» x2)
            (fun (x5 : T) =>
              if (Const.eq («Combinator.tySort» x5) (leaf 0)).label ≠ 0 then
                «Combinator/CP.pure»
                  («Language.pr» («Combinator.tyLo» x5) («Combinator.tyLoC» x5))
              else
                if (Const.eq (Const.label x2) (leaf 0)).label ≠ 0 then
                  «Combinator/CP.pure» («Language.pr» x2 («Combinator.tyDfd» x5))
                else
                  «Combinator.bindPsToP»
                    («Combinator.seqP» x3)
                    (fun (x6 : T) =>
                      let x7 : List T := «Combinator.pairsOf» x6;
                      let x8 : T := Const.node
                        (Const.label x2)
                        («Combinator/PairT.map» «Language.p1» x7);
                      let x9 : T := (if (Const.equal x8 x2).label ≠ 0 then
                        «Combinator.tyDfd» x5
                      else
                        «Combinator.cCong»
                          («Combinator.tyDfd» x5)
                          («Combinator/PairT.map» «Language.p2» x7));
                      «Combinator.bindOPToP»
                        («Combinator/COP.orElse»
                          («Combinator.bindPToOP»
                            («Combinator.rewriteRoot» x0 x8)
                            (fun (x10 : T) => «Combinator/COP.pure» («Language/OTPair.just» x10)))
                          («Combinator/COP.pure» «Language/OTPair.nothing»))
                        (fun (x10 : T) =>
                          if («Language/OTPair.isJust» x10).label ≠ 0 then
                            let x11 : T := «Language/OTPair.fromMaybe» «Combinator.pr0» x10;
                            «Combinator.bindPToP»
                              (x1 («Language.p1» x11))
                              (fun (x12 : T) =>
                                «Combinator.memoizeNf»
                                  x2
                                  («Language.p1» x12)
                                  («Combinator.cTrans»
                                    x9
                                    («Combinator.cTrans» («Language.p2» x11) («Language.p2» x12))))
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
      (fun (_ : T) => «Combinator/CP.fail»)
      x1;
    x2

def «Combinator.pNormalize» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T → T → T := «Combinator.normalizers» x0 (leaf 64) x1; x2

def «Combinator.beforeTerminal» :=
  «Combinator/Seqs.length» «Theory.categoryAxioms»

def «Combinator.beforeProduct» :=
  Const.add
    «Combinator.beforeTerminal»
    («Combinator/Seqs.length» «Theory.terminalAxioms»)

def «Combinator.beforeExponential» :=
  Const.add
    «Combinator.beforeProduct»
    (Const.add
      («Combinator/Seqs.length» «Theory.productAxioms»)
      (Const.add
        («Combinator/Seqs.length» «Theory.equalizerAxioms»)
        (Const.add
          («Combinator/Seqs.length» «Theory.initialAxioms»)
          (Const.add
            («Combinator/Seqs.length» «Theory.coproductAxioms»)
            («Combinator/Seqs.length» «Theory.coequalizerAxioms»)))))

def «Combinator.beforeNat» :=
  Const.add
    «Combinator.beforeExponential»
    (Const.add
      («Combinator/Seqs.length» «Theory.exponentialAxioms»)
      («Combinator/Seqs.length» «Theory.classifierAxioms»))

def «Combinator.beforeList» :=
  Const.add
    «Combinator.beforeNat»
    («Combinator/Seqs.length» «Theory.natAxioms»)

def «Combinator.pInst» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T →
      T →
        T := «Combinator.bindQToE»
      («Combinator.srcSeq» x0)
      (fun (x2 : T) =>
        «Combinator.bindYsToE»
          («Combinator.mapMTY» «Combinator.typeTerm» x1)
          (fun (x3 : T) =>
            let x4 : List T := «Combinator.ptysOf» x3;
            «Combinator.bindCToE»
              («Combinator.mapMEqC»
                («Combinator.proveHyp» «Combinator.typePattern» x4)
                («PartialHorn.seqHyps» x2))
              (fun (x5 : T) =>
                «Combinator/CE.pure»
                  («Combinator.eqnCert»
                    («PartialHorn.eqSubst» x1 («PartialHorn.seqConcl» x2))
                    («Combinator.srcCert»
                      x0
                      x1
                      («Combinator/YT.map» «Combinator.tyDfd» x4)
                      («Combinator.certsOf» x5))))));
    x2

def «Combinator.etaExpand» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := «Combinator.bindYToP»
      («Combinator.typeTerm» x0)
      (fun (x1 : T) =>
        let x2 : T := «Combinator.tyHi» x1;
        if («Prelude.and»
          (Const.eq (Const.label x2) (leaf 7))
          (Const.eq
            («Prelude.length» (Const.children x2))
            (leaf 2))).label ≠ 0 then
          «Combinator.bindEToP»
            («Combinator.pInst»
              («Combinator.srcAx» (Const.add «Combinator.beforeProduct» (leaf 11)))
              («Theory.l3»
                x0
                («Prelude.at» (Const.children x2) (leaf 0))
                («Prelude.at» (Const.children x2) (leaf 1))))
            (fun (x3 : T) =>
              «Combinator/CP.pure»
                («Language.pr»
                  («PartialHorn.eqLhs» («Combinator.ecEqn» x3))
                  («Combinator.cSymm» («Combinator.ecCert» x3))))
        else
          «Combinator/CP.fail»);
    x1

def «Combinator.rwAx» :=
  fun (x0 : T) =>
    let x1 : T := «Combinator.rwRule»
      («Combinator.srcAx» x0)
      (leaf 0)
      («Combinator.labels» ([] : List T));
    x1

def «Combinator.rwThm» :=
  fun (x0 : T) =>
    let x1 : T := «Combinator.rwRule»
      («Combinator.srcThm» x0)
      (leaf 0)
      («Combinator.labels» ([] : List T));
    x1

def «Combinator.deltaRule» :=
  fun (x0 : T) =>
    let x1 : T := «Combinator.rwAx» («Infer.defAxIdx» x0); x1

def «Combinator.pByNorm» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T →
      T →
        T := «Combinator.bindPToT»
      («Combinator.pNormalize» x0 («PartialHorn.eqLhs» x1))
      (fun (x2 : T) =>
        «Combinator.bindPToT»
          («Combinator.pNormalize» x0 («PartialHorn.eqRhs» x1))
          (fun (x3 : T) =>
            «Combinator.bindTToT»
              («Combinator.pmGuard»
                (Const.equal («Language.p1» x2) («Language.p1» x3)))
              (fun (_ : T) =>
                «Combinator/CT.pure»
                  («Combinator.cTrans»
                    («Language.p2» x2)
                    («Combinator.cSymm» («Language.p2» x3))))));
    x2

def «Combinator.proved» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator/OProved.nothing» := Const.node (leaf 0) ([] : List T)

def «Combinator/OProved.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Combinator/OProved.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let _ : T := Const.child x1 (leaf 0); leaf 1
                   else
                     leaf 0);
    x1

def «Combinator/OProved.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x3
                   else
                     x0);
    x2

def «Combinator/OProved.nthOf» :=
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
      «Combinator/OProved.nothing»
      (fun (x2 : T) (_ : List T) => «Combinator/OProved.just» x2);
    x2

def «Combinator/OProved.allJust» :=
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

def «Combinator.provedIdx» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1); x2);
    x1

def «Combinator.provedDev» :=
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

def «Combinator.proveSeq» :=
  fun (x0 : T) (x1 : T → T → T) (x2 : List T) (x3 : T) (x4 : List T) =>
    let x5 : T := (let x5 : T := x1
                     («Combinator.scope»
                       («PartialHorn.sorts» («PartialHorn.seqCtx» x0))
                       («PartialHorn.eqns» («PartialHorn.seqHyps» x0)))
                     («Combinator.pmStart» x4 x2 x3);
                   if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
                     let x6 : T := Const.child x5 (leaf 0);
                     let x7 : T := x6;
                     let x8 : T := Const.child x7 (leaf 0);
                     let x9 : T := Const.child x7 (leaf 1);
                     let x10 : List T := «Combinator.stDev» x9;
                     «Combinator/OProved.just»
                       («Combinator.proved»
                         («Combinator/DevL.length» x10)
                         («Combinator.devs»
                           («Combinator/DevL.append»
                             x10
                             («Combinator/DevL.single» («Combinator.devEntry» x0 x8)))))
                   else
                     «Combinator/OProved.nothing»);
    x5

def «Combinator.normalizeThm» :=
  fun (x0 : List T) (x1 : T) (x2 : List T) (x3 : T) (x4 : List T) =>
    let x5 : T := (let x5 : T := «Combinator/ODev.nthOf» x4 x1;
                   if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
                     let x6 : T := Const.child x5 (leaf 0);
                     let x7 : T := «Combinator.devSeq» x6;
                     let x8 : T := «Combinator.scope»
                       («PartialHorn.sorts» («PartialHorn.seqCtx» x7))
                       («PartialHorn.eqns» («PartialHorn.seqHyps» x7));
                     let x9 : T := «Combinator.pNormalize»
                       x0
                       («PartialHorn.eqLhs» («PartialHorn.seqConcl» x7))
                       x8
                       («Combinator.pmStart» x4 x2 x3);
                     if (Const.eq (Const.label x9) (leaf 1)).label ≠ 0 then
                       let x10 : T := Const.child x9 (leaf 0);
                       let x11 : T := x10;
                       let x12 : T := Const.child x11 (leaf 0);
                       let x13 : T := Const.child x11 (leaf 1);
                       let x14 : List T := «Combinator.stDev» x13;
                       «Combinator/OProved.just»
                         («Combinator.proved»
                           («Combinator/DevL.length» x14)
                           («Combinator.devs»
                             («Combinator/DevL.append»
                               x14
                               («Combinator/DevL.single»
                                 («Combinator.devEntry»
                                   («Combinator.scSeq»
                                     x8
                                     («PartialHorn.eqn»
                                       («Language.p1» x12)
                                       («PartialHorn.eqRhs» («PartialHorn.seqConcl» x7))))
                                   («Combinator.cTrans»
                                     («Combinator.cSymm» («Language.p2» x12))
                                     («Combinator.scCite» x8 x1)))))))
                     else
                       «Combinator/OProved.nothing»
                   else
                     «Combinator/OProved.nothing»);
    x5

def «Combinator.instBy» :=
  fun (x0 : List T) (x1 : T) (x2 : List T) =>
    let x3 : T →
      T →
        T := «Combinator.bindQToE»
      («Combinator.srcSeq» x1)
      (fun (x3 : T) =>
        «Combinator.bindYsToE»
          («Combinator.mapMTY» «Combinator.typeTerm» x2)
          (fun (x4 : T) =>
            let x5 : List T := «Combinator.ptysOf» x4;
            «Combinator.bindCToE»
              («Combinator.mapMEqC»
                (fun (x6 : T) =>
                  «Combinator/CT.orElse»
                    («Combinator.proveHyp» «Combinator.typePattern» x5 x6)
                    («Combinator.pByNorm» x0 («PartialHorn.eqSubst» x2 x6)))
                («PartialHorn.seqHyps» x3))
              (fun (x6 : T) =>
                «Combinator/CE.pure»
                  («Combinator.eqnCert»
                    («PartialHorn.eqSubst» x2 («PartialHorn.seqConcl» x3))
                    («Combinator.srcCert»
                      x1
                      x2
                      («Combinator/YT.map» «Combinator.tyDfd» x5)
                      («Combinator.certsOf» x6))))));
    x3

def «Combinator.congStep» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List (T → T → T → T)) =>
    let x4 : T →
      T →
        T →
          T := (fun (x4 : T) =>
      «Combinator.bindYToT»
        («Combinator.typeTerm» x2)
        (fun (x5 : T) =>
          if (Const.equal x2 x4).label ≠ 0 then
            «Combinator/CT.pure» («Combinator.tyDfd» x5)
          else
            if («Prelude.and»
              (Const.equal x2 («PartialHorn.eqLhs» x0))
              (Const.equal x4 («PartialHorn.eqRhs» x0))).label ≠ 0 then
              «Combinator/CT.pure» x1
            else
              if (Const.eq («Combinator.tySort» x5) (leaf 0)).label ≠ 0 then
                «Combinator.bindYToT»
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
                  «Combinator/CT.fail»
                else
                  «Combinator.bindCToT»
                    («Combinator.bridgeKids» x3 (Const.children x4))
                    (fun (x6 : T) =>
                      «Combinator/CT.pure»
                        («Combinator.cCong»
                          («Combinator.tyDfd» x5)
                          («Combinator.certsOf» x6)))));
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
        T := «Combinator.bindEToT»
      («Combinator.instBy»
        x0
        («Combinator.srcAx» (Const.add «Combinator.beforeNat» (leaf 12)))
        («Theory.l3» x1 x2 x3))
      (fun (x4 : T) => «Combinator/CT.pure» («Combinator.ecCert» x4));
    x4

def «Combinator.listRecUniq» :=
  fun (x0 : List T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T →
      T →
        T := «Combinator.bindEToT»
      («Combinator.instBy»
        x0
        («Combinator.srcAx» (Const.add «Combinator.beforeList» (leaf 13)))
        («Theory.l4» x1 x2 x3 x4))
      (fun (x5 : T) => «Combinator/CT.pure» («Combinator.ecCert» x5));
    x5

def «Combinator.byNatInduction» :=
  fun (x0 : List T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T →
      T →
        T := «Combinator.bindTToT»
      («Combinator.natRecUniq» x0 x1 x2 («PartialHorn.eqLhs» x3))
      (fun (x4 : T) =>
        «Combinator.bindTToT»
          («Combinator.natRecUniq» x0 x1 x2 («PartialHorn.eqRhs» x3))
          (fun (x5 : T) =>
            «Combinator/CT.pure»
              («Combinator.cTrans» x4 («Combinator.cSymm» x5))));
    x4

def «Combinator.byListInduction» :=
  fun (x0 : List T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T →
      T →
        T := «Combinator.bindTToT»
      («Combinator.listRecUniq» x0 x1 x2 x3 («PartialHorn.eqLhs» x4))
      (fun (x5 : T) =>
        «Combinator.bindTToT»
          («Combinator.listRecUniq» x0 x1 x2 x3 («PartialHorn.eqRhs» x4))
          (fun (x6 : T) =>
            «Combinator/CT.pure»
              («Combinator.cTrans» x5 («Combinator.cSymm» x6))));
    x5

def «Combinator.byListParamInduction» :=
  fun (x0 : List T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T →
      T →
        T := «Combinator.bindYToT»
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
          «Combinator.bindTToT»
            («Combinator.byListInduction»
              x0
              x1
              x12
              x13
              («PartialHorn.eqn» x14 x15))
            (fun (x16 : T) =>
              «Combinator.bindEToT»
                («Combinator.pInst»
                  («Combinator.srcAx»
                    (Const.add «Combinator.beforeExponential» (leaf 7)))
                  («Theory.l3» x7 x8 («PartialHorn.eqLhs» x4)))
                (fun (x17 : T) =>
                  «Combinator.bindEToT»
                    («Combinator.pInst»
                      («Combinator.srcAx»
                        (Const.add «Combinator.beforeExponential» (leaf 7)))
                      («Theory.l3» x7 x8 («PartialHorn.eqRhs» x4)))
                    (fun (x18 : T) =>
                      «Combinator.bindTToT»
                        («Combinator.congBy»
                          («PartialHorn.eqn» x14 x15)
                          x16
                          («PartialHorn.eqLhs» («Combinator.ecEqn» x17))
                          («PartialHorn.eqLhs» («Combinator.ecEqn» x18)))
                        (fun (x19 : T) =>
                          «Combinator/CT.pure»
                            («Combinator.cTrans»
                              («Combinator.cSymm» («Combinator.ecCert» x17))
                              («Combinator.cTrans» x19 («Combinator.ecCert» x18)))))))
        else
          «Combinator/CT.fail»);
    x5

def «Combinator.baseRules» :=
  ((«Combinator.rwRule»
    («Combinator.srcAx» (leaf 7))
    (leaf 1)
    («Combinator.labels» ([] : List T))) ::
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
                («Combinator.labels» («Theory.l2» (leaf 3) (leaf 6)))) ::
                ((«Combinator.rwAx» (Const.add «Combinator.beforeNat» (leaf 10))) ::
                  ((«Combinator.rwAx» (Const.add «Combinator.beforeNat» (leaf 11))) ::
                    («Combinator/RwL.l2»
                      («Combinator.rwAx» (Const.add «Combinator.beforeList» (leaf 11)))
                      («Combinator.rwAx»
                        (Const.add «Combinator.beforeList» (leaf 12)))))))))))))

def «Combinator.compPairSeq» :=
  «PartialHorn.mkSeq»
    («Theory.l3» (leaf 1) (leaf 1) (leaf 1))
    («Combinator/EqnL.l2»
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
    («Combinator/EqnL.l4»
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
    («Combinator/EqnL.l3»
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
    («Combinator/EqnL.l2»
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
  «Combinator.bindPToT»
    («Combinator.etaExpand»
      («Combinator.seqLhs» «Combinator.compPairSeq»))
    (fun (x0 : T) =>
      «Combinator.bindPToT»
        («Combinator.pNormalize» «Combinator.baseRules» («Language.p1» x0))
        (fun (x1 : T) =>
          «Combinator.bindTToT»
            («Combinator.pmGuard»
              (Const.equal
                («Language.p1» x1)
                («Combinator.seqRhs» «Combinator.compPairSeq»)))
            (fun (_ : T) =>
              «Combinator/CT.pure»
                («Combinator.cTrans» («Language.p2» x0) («Language.p2» x1)))))

def «Combinator.pairFstSndProof» :=
  let x0 : T := «Theory.prod»
    («Theory.x» (leaf 0))
    («Theory.x» (leaf 1));
  «Combinator.bindEToT»
    («Combinator.pInst»
      («Combinator.srcAx» (Const.add «Combinator.beforeProduct» (leaf 11)))
      («Theory.l3»
        («Theory.idt» x0)
        («Theory.x» (leaf 0))
        («Theory.x» (leaf 1))))
    (fun (x1 : T) =>
      «Combinator.bindPToT»
        («Combinator.pNormalize»
          «Combinator.baseRules»
          («PartialHorn.eqLhs» («Combinator.ecEqn» x1)))
        (fun (x2 : T) =>
          «Combinator.bindTToT»
            («Combinator.pmGuard»
              (Const.equal
                («Language.p1» x2)
                («Combinator.seqLhs» «Combinator.pairFstSndSeq»)))
            (fun (_ : T) =>
              «Combinator/CT.pure»
                («Combinator.cTrans»
                  («Combinator.cSymm» («Language.p2» x2))
                  («Combinator.ecCert» x1)))))

def «Combinator.evCurryProof» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := (let x1 : List
                T := «Combinator/RwRules.append»
                «Combinator.baseRules»
                («Combinator/RwRules.single» («Combinator.rwThm» x0));
              «Combinator.bindEToT»
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
                    («PartialHorn.eqLhs» («Combinator.ecEqn» x2))
                    x3;
                  «Combinator.bindPToT»
                    («Combinator.pNormalize» x1 x4)
                    (fun (x5 : T) =>
                      «Combinator.bindPToT»
                        («Combinator.pNormalize»
                          x1
                          («Combinator.seqLhs» «Combinator.evCurrySeq»))
                        (fun (x6 : T) =>
                          «Combinator.bindTToT»
                            («Combinator.pmGuard»
                              (Const.equal («Language.p1» x5) («Language.p1» x6)))
                            (fun (_ : T) =>
                              «Combinator.bindYToT»
                                («Combinator.typeTerm» x4)
                                (fun (x8 : T) =>
                                  «Combinator.bindYToT»
                                    («Combinator.typeTerm» x3)
                                    (fun (x9 : T) =>
                                      «Combinator/CT.pure»
                                        («Combinator.cTrans»
                                          («Combinator.cTrans»
                                            («Language.p2» x6)
                                            («Combinator.cSymm» («Language.p2» x5)))
                                          («Combinator.cCong»
                                            («Combinator.tyDfd» x8)
                                            («Theory.l2»
                                              («Combinator.ecCert» x2)
                                              («Combinator.tyDfd» x9)))))))))));
    x1

def «Combinator.evCurry0Proof» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        T := «Combinator.bindEToT»
      («Combinator.pInst»
        («Combinator.srcThm» x0)
        («Theory.l5»
          («Theory.x» (leaf 0))
          («Theory.x» (leaf 1))
          («Theory.x» (leaf 2))
          («Theory.idt» («Theory.x» (leaf 0)))
          («Theory.x» (leaf 3))))
      (fun (x1 : T) =>
        let x2 : T := «Combinator.ecEqn» x1;
        «Combinator.bindPToT»
          («Combinator.pNormalize»
            «Combinator.baseRules»
            («PartialHorn.eqLhs» x2))
          (fun (x3 : T) =>
            «Combinator.bindTToT»
              («Combinator.pmGuard»
                («Prelude.and»
                  (Const.equal
                    («Language.p1» x3)
                    («Combinator.seqLhs» «Combinator.evCurry0Seq»))
                  (Const.equal
                    («PartialHorn.eqRhs» x2)
                    («Combinator.seqRhs» «Combinator.evCurry0Seq»))))
              (fun (_ : T) =>
                «Combinator/CT.pure»
                  («Combinator.cTrans»
                    («Combinator.cSymm» («Language.p2» x3))
                    («Combinator.ecCert» x1)))));
    x1

def «Combinator.curryNatProof» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T →
      T →
        T := (let x2 : List
                T := «Combinator/RwRules.append»
                «Combinator.baseRules»
                («Combinator/RwL.l2» («Combinator.rwThm» x0) («Combinator.rwThm» x1));
              let x3 : T := «Combinator.seqLhs» «Combinator.curryNatSeq»;
              «Combinator.bindEToT»
                («Combinator.pInst»
                  («Combinator.srcAx»
                    (Const.add «Combinator.beforeExponential» (leaf 8)))
                  («Theory.l4»
                    («Theory.dom» («Theory.x» (leaf 3)))
                    («Theory.x» (leaf 1))
                    («Theory.cod» («Theory.x» (leaf 2)))
                    x3))
                (fun (x4 : T) =>
                  «Combinator.bindPToT»
                    («Combinator.pNormalize»
                      x2
                      («PartialHorn.eqLhs» («Combinator.ecEqn» x4)))
                    (fun (x5 : T) =>
                      «Combinator.bindPToT»
                        («Combinator.pNormalize»
                          x2
                          («Combinator.seqRhs» «Combinator.curryNatSeq»))
                        (fun (x6 : T) =>
                          «Combinator.bindTToT»
                            («Combinator.pmGuard»
                              (Const.equal («Language.p1» x5) («Language.p1» x6)))
                            (fun (_ : T) =>
                              «Combinator/CT.pure»
                                («Combinator.cTrans»
                                  («Combinator.cSymm» («Combinator.ecCert» x4))
                                  («Combinator.cTrans»
                                    («Language.p2» x5)
                                    («Combinator.cSymm» («Language.p2» x6)))))))));
    x2

def «Combinator.bangOneProof» :=
  «Combinator.bindEToT»
    («Combinator.pInst»
      («Combinator.srcAx» (Const.add «Combinator.beforeTerminal» (leaf 3)))
      («Prelude.single» («Theory.idt» «Theory.one»)))
    (fun (x0 : T) =>
      «Combinator.bindPToT»
        («Combinator.pNormalize»
          «Combinator.baseRules»
          («PartialHorn.eqRhs» («Combinator.ecEqn» x0)))
        (fun (x1 : T) =>
          «Combinator.bindTToT»
            («Combinator.pmGuard»
              (Const.equal («Language.p1» x1) («Theory.bang» «Theory.one»)))
            (fun (_ : T) =>
              «Combinator/CT.pure»
                («Combinator.cSymm»
                  («Combinator.cTrans» («Combinator.ecCert» x0) («Language.p2» x1))))))

def «Combinator.indices» :=
  fun (x0 : List T) => Const.node (leaf 0) x0

def «Combinator.library» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Combinator/OLibrary.nothing» := Const.node (leaf 0) ([] : List T)

def «Combinator/OLibrary.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Combinator/OLibrary.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let _ : T := Const.child x1 (leaf 0); leaf 1
                   else
                     leaf 0);
    x1

def «Combinator/OLibrary.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x3
                   else
                     x0);
    x2

def «Combinator/OLibrary.nthOf» :=
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
      «Combinator/OLibrary.nothing»
      (fun (x2 : T) (_ : List T) => «Combinator/OLibrary.just» x2);
    x2

def «Combinator/OLibrary.allJust» :=
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

def «Combinator.bindPr» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x1 x3
                   else
                     «Combinator/OLibrary.nothing»);
    x2

def «Combinator.libraryWith» :=
  fun (x0 : T) =>
    let x1 : T := «Combinator.bindPr»
      («Combinator.proveSeq»
        «Combinator.compPairSeq»
        «Combinator.compPairProof»
        ([] : List T)
        x0
        ([] : List T))
      (fun (x1 : T) =>
        let x2 : T := «Combinator.provedIdx» x1;
        «Combinator.bindPr»
          («Combinator.proveSeq»
            «Combinator.pairFstSndSeq»
            «Combinator.pairFstSndProof»
            ([] : List T)
            x0
            («Combinator.provedDev» x1))
          (fun (x3 : T) =>
            let x4 : T := «Combinator.provedIdx» x3;
            «Combinator.bindPr»
              («Combinator.proveSeq»
                «Combinator.evCurrySeq»
                («Combinator.evCurryProof» x2)
                ([] : List T)
                x0
                («Combinator.provedDev» x3))
              (fun (x5 : T) =>
                let x6 : T := «Combinator.provedIdx» x5;
                «Combinator.bindPr»
                  («Combinator.proveSeq»
                    «Combinator.evCurry0Seq»
                    («Combinator.evCurry0Proof» x6)
                    ([] : List T)
                    x0
                    («Combinator.provedDev» x5))
                  (fun (x7 : T) =>
                    let x8 : T := «Combinator.provedIdx» x7;
                    «Combinator.bindPr»
                      («Combinator.proveSeq»
                        «Combinator.curryNatSeq»
                        («Combinator.curryNatProof» x2 x6)
                        ([] : List T)
                        x0
                        («Combinator.provedDev» x7))
                      (fun (x9 : T) =>
                        let x10 : T := «Combinator.provedIdx» x9;
                        «Combinator.bindPr»
                          («Combinator.proveSeq»
                            «Combinator.bangOneSeq»
                            «Combinator.bangOneProof»
                            ([] : List T)
                            x0
                            («Combinator.provedDev» x9))
                          (fun (x11 : T) =>
                            «Combinator/OLibrary.just»
                              («Combinator.library»
                                («Combinator.indices»
                                  («Theory.l6» x2 x4 x6 x8 x10 («Combinator.provedIdx» x11)))
                                («Combinator.devs» («Combinator.provedDev» x11)))))))));
    x1

def «Combinator.libRules» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : List
              T := (let x1 : T := x0;
                    let x2 : List
                      T := Const.iter
                      (α := List T)
                      (fun (x2 : List T) =>
                        Const.lcase
                          (α := T)
                          (β := List T)
                          x2
                          ([] : List T)
                          (fun (_ : T) (x4 : List T) => x4))
                      (Const.children x1)
                      (leaf 0);
                    x2);
            «Combinator/RwRules.append»
              «Combinator.baseRules»
              («Combinator/RwL.l5»
                («Combinator.rwThm» («Prelude.at» x1 (leaf 0)))
                («Combinator.rwThm» («Prelude.at» x1 (leaf 1)))
                («Combinator.rwThm» («Prelude.at» x1 (leaf 4)))
                («Combinator.rwThm» («Prelude.at» x1 (leaf 3)))
                («Combinator.rwThm» («Prelude.at» x1 (leaf 5)))));
    x1

end GebMirror.Metalogic

end
