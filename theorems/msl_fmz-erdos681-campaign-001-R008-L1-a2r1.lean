set_option autoImplicit false

def Nat.isPrime : Nat -> Bool
  | 0 => False | 1 => False
  | n => go 2 n
where
  go (d : Nat) (n : Nat) : Bool :=
    if d * d > n then True
    else if n % d == 0 then False else go (d+1) n

def witnessSucceeds (n : Nat) : Bool :=
  Nat.isPrime (n+1) == false && 1 < n+1

def failureSet : List Nat := [1, 2, 256, 276, 280, 292, 306]

def checkWindow (bound : Nat) : Bool :=
  (List.range bound).all fun i =>
    let n := i + 1
    witnessSucceeds n == !(failureSet.contains n)

theorem msl_fmz_erdos681_campaign_001_R008_L1_a2r1  : checkWindow 306 = true := by decide
