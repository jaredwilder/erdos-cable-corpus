set_option autoImplicit false

def isPrime : Nat -> Bool
  | 0 => False | 1 => False
  | n => go 2 n
where go : Nat -> Nat -> Bool
  | d, n => if d * d > n then True
            else if n % d == 0 then False else go (d+1) n

def witnessSucceeds (n : Nat) : Bool :=
  !isPrime (n+1) && 1 < n+1

def failureSet : List Nat := [1, 2, 256, 276, 280, 292, 306]

def failuresExact : Bool :=
  failureSet.all (fun n => witnessSucceeds n == false)

def noOtherFailures (bound : Nat) : Bool :=
  (List.range bound).all (fun i =>
    let n := i + 1
    witnessSucceeds n == !failureSet.contains n)

theorem msl_fmz_erdos681_campaign_001_R008_L1_a2r2  : failuresExact = true ∧ noOtherFailures 60 = true := by decide
