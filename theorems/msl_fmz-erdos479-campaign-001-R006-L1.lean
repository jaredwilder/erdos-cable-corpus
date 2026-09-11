set_option autoImplicit false

def zmodCong : Int -> Int -> Int := fun a n => a % n

def witnessHolds (k n : Int) (s : Int) : Bool :=
  (2 ^ n.toNat) % n == (s * k) % n

-- L1 fragment: for odd k >= 3, every n in [1, Bound] with 2^n = s*k (mod n)
-- for s in {+1, -1} must satisfy: n is odd AND gcd(n, k) = 1 AND n not in {1 with k = ±1}.
def checkPair (k n : Nat) : Bool :=
  let K : Int := (k : Int) * 2 + 3   -- odd k >= 3
  let N : Int := (n : Int) + 1       -- n >= 1
  if witnessHolds K N 1 || witnessHolds K N (-1) then
    (N % 2 == 1) && (Int.gcd N K == 1)
  else true

def checkAll (bound : Nat) : Bool :=
  (List.range bound).all (fun k => (List.range bound).all (fun n => checkPair k n))

def check_witness : Bool := checkAll 60

theorem msl_fmz_erdos479_campaign_001_R006_L1  : check_witness = true := by decide
