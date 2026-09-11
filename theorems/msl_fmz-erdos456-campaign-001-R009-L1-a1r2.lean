set_option autoImplicit false

def phi (m : Nat) : Nat := (List.range m).filter (fun k => Nat.gcd k m == 1) |>.length

def isPrime (n : Nat) : Bool :=
  n >= 2 && ((List.range n).drop 2).all (fun d => n % d != 0)

def dividesPhi (n m : Nat) : Bool := phi m % n == 0

def mOf (n : Nat) : Option Nat :=
  ((List.range 200).map (fun k => k + 1)).find? (dividesPhi n)

def pOf (n : Nat) : Option Nat :=
  ((List.range 2000).map (fun k => n * k + 1)).find? isPrime

def eqSet : List Nat := [2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19]

def leCheck : Bool :=
  ((List.range 20).map (fun k => k + 1)).all (fun n =>
    match mOf n, pOf n with
    | some m, some p => m <= p
    | _, _ => false)

def eqSetCheck : Bool :=
  ((List.range 19).map (fun k => k + 2)).all (fun n =>
    match mOf n, pOf n with
    | some m, some p =>
        (m == p) == (eqSet.contains n)
    | _, _ => false)

def strictWitnesses : Bool :=
  match mOf 8, pOf 8, mOf 20, pOf 20 with
  | some a, some b, some c, some d =>
      a == 15 && b == 17 && a < b && c == 25 && d == 41 && c < d
  | _, _, _, _ => false

def checkL1 : Bool := leCheck && eqSetCheck && strictWitnesses

theorem msl_fmz_erdos456_campaign_001_R009_L1_a1r2  : checkL1 = true := by native_decide
