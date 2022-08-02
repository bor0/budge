data SignedNat = PosNat Nat | NegNat Nat

data BudgeCmd = CNum SignedNat | CCons BudgeCmd BudgeCmd | CWhile Nat BudgeCmd

Map : Type
Map = Nat -> Nat

EmptyMap : Map
EmptyMap _ = 0

UpdateMap : Map -> Nat -> Nat -> Map
UpdateMap m x v x' = if x == x' then v else m x'

data BudgeEval : Map -> BudgeCmd -> Map -> Type where
  BPos : BudgeEval i (CNum (PosNat x)) (UpdateMap i x (i x + 1))
  BNeg : BudgeEval i (CNum (NegNat x)) (UpdateMap i x (i x `minus` 1))
  BCons : BudgeEval i c1 i'
    -> BudgeEval i' c2 i''
    -> BudgeEval i (CCons c1 c2) i''
  BWhileT : (i cond = 0 -> Void)
    -> BudgeEval i c i'
    -> BudgeEval i' (CWhile cond c) i''
    -> BudgeEval i (CWhile cond c) i''
  BWhileF : i cond = 0
    -> BudgeEval i (CWhile cond c) i

Addition : BudgeCmd
Addition = CWhile 2 (CCons (CNum (NegNat 2)) (CNum (PosNat 1)))

AddMap : Map
AddMap = UpdateMap EmptyMap 1 2
AddMap' : Map
AddMap' = UpdateMap AddMap 2 2
AddMap'' : Map
AddMap'' = UpdateMap AddMap' 2 (AddMap' 2 `minus` 1)
AddMap''' : Map
AddMap''' = UpdateMap AddMap'' 1 (AddMap'' 1 + 1)
AddMap'''' : Map
AddMap'''' = UpdateMap AddMap''' 2 (AddMap''' 2 `minus` 1)
AddMap''''' : Map
AddMap''''' = UpdateMap AddMap'''' 1 (AddMap'''' 1 + 1)

EgAdd : BudgeEval AddMap' Addition AddMap'''''
EgAdd = BWhileT
  (\case Refl impossible)
  (BCons BNeg BPos)
  (BWhileT (\case Refl impossible) (BCons BNeg BPos) (BWhileF Refl))

Composition : BudgeEval i c1 i' -> BudgeEval i' c2 i'' -> BudgeEval i (CCons c1 c2) i''
Composition hyp1 hyp2 = BCons hyp1 hyp2
