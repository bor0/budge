data SignedNat = PosNat Nat | NegNat Nat

data BudgeData = BNum SignedNat | BSeq Nat (List BudgeData)

Map : Type
Map = Nat -> Nat

EmptyMap : Map
EmptyMap _ = 0

UpdateMap : Map -> Nat -> Nat -> Map
UpdateMap m x v x' = if x == x' then v else m x'

data Budge : Map -> List BudgeData -> Map -> Type where
  BId : Budge i [] i
  BPos : Budge (UpdateMap i' x (i' x + 1)) xs i''
    -> Budge i (BNum (PosNat x)::xs) (UpdateMap i' x (i' x + 1))
  BNeg : Budge (UpdateMap i' x (i' x `minus` 1)) xs i''
    -> Budge i (BNum (NegNat x)::xs) (UpdateMap i' x (i' x `minus` 1))
  BWhileT : (i x' = 0 -> Void)
    -> Budge i x i'
    -> Budge i' ((BSeq x' x)::xs) i''
    -> Budge i ((BSeq x' x)::xs) i''
  BWhileF : i x' = 0
    -> Budge i xs i'
    -> Budge i ((BSeq x' x)::xs) i'

Addition : List BudgeData
Addition = [BSeq 2 [BNum (NegNat 2), BNum (PosNat 1)]]

AddMap : Map
AddMap = UpdateMap EmptyMap 1 2
AddMap' : Map
AddMap' = UpdateMap AddMap 2 2
AddMap'' : Map
AddMap'' = UpdateMap AddMap' 1 (AddMap' 1 + 1)
AddMap''' : Map
AddMap''' = UpdateMap AddMap'' 2 (AddMap'' 2 `minus` 1)
AddMap'''' : Map
AddMap'''' = UpdateMap AddMap''' 1 (AddMap''' 1 + 1)
AddMap''''' : Map
AddMap''''' = UpdateMap AddMap'''' 2 (AddMap'''' 2 `minus` 1)

EgAdd : Budge AddMap' Addition AddMap'''''
EgAdd = BWhileT
  (\case Refl impossible)
  (BNeg {i' = AddMap'} (BPos {i' = AddMap''} BId))
  (BWhileT (\case Refl impossible) (BNeg (BPos {i' = AddMap'''''} BId)) (BWhileF Refl BId))
