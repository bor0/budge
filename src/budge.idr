data SignedNat = PosNat Nat | NegNat Nat

data BudgeCmd = CNum SignedNat | CCons BudgeCmd BudgeCmd | CSeq Nat BudgeCmd

Map : Type
Map = Nat -> Nat

EmptyMap : Map
EmptyMap _ = 0

UpdateMap : Map -> Nat -> Nat -> Map
UpdateMap m x v x' = if x == x' then v else m x'

data BudgeEval : Map -> BudgeCmd -> Map -> Type where
  BPos : BudgeEval i (CNum (PosNat x)) (UpdateMap i x (i x + 1))
  BNeg : BudgeEval i (CNum (NegNat x)) (UpdateMap i x (i x `minus` 1))
  BSeq : BudgeEval i c1 i'
    -> BudgeEval i' c2 i''
    -> BudgeEval i (CCons c1 c2) i''
  BWhileT : (i cond = 0 -> Void)
    -> BudgeEval i c i'
    -> BudgeEval i' (CSeq cond c) i''
    -> BudgeEval i (CSeq cond c) i''
  BWhileF : i cond = 0
    -> BudgeEval i (CSeq cond c) i

Composition : BudgeEval i c1 i' -> BudgeEval i' c2 i'' -> BudgeEval i (CCons c1 c2) i''
Composition hyp1 hyp2 = BSeq hyp1 hyp2
