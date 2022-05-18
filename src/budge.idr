data SignedNat = PosNat Nat | NegNat Nat

data BudgeCmd = BNum SignedNat | BSeq Nat (List BudgeCmd)

Map : Type
Map = Nat -> Nat

EmptyMap : Map
EmptyMap _ = 0

UpdateMap : Map -> Nat -> Nat -> Map
UpdateMap m x v x' = if x == x' then v else m x'

data BudgeEval : Map -> List BudgeCmd -> Map -> Type where
  BId : BudgeEval i [] i
  BPos : BudgeEval i xs i'
    -> BudgeEval i (xs ++ [BNum (PosNat x)]) (UpdateMap i' x (i' x + 1))
  BNeg : BudgeEval i xs i'
    -> BudgeEval i (xs ++ [BNum (NegNat x)]) (UpdateMap i' x (i' x `minus` 1))
  BWhileT : (i x' = 0 -> Void)
    -> BudgeEval i x i'
    -> BudgeEval i' ((BSeq x' x)::xs) i''
    -> BudgeEval i ((BSeq x' x)::xs) i''
  BWhileF : i x' = 0
    -> BudgeEval i xs i'
    -> BudgeEval i ((BSeq x' x)::xs) i'

Addition : List BudgeCmd
Addition = [BSeq 2 [BNum (NegNat 2), BNum (PosNat 1)]]

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
  (BPos (BNeg BId))
  (BWhileT (\case Refl impossible) (BPos (BNeg BId)) (BWhileF Refl BId))
