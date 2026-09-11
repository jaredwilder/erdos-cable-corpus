set_option autoImplicit false

def gcdN : Nat -> Nat -> Nat
  | 0, m => m
  | n, m => gcdN (m % n) n

def tau (n : Nat) : Nat :=
  (List.range (n + 1)).filter (fun d => d > 0 && n % d == 0) |>.length

def pow2m1 (k : Nat) : Nat := 2 ^ k - 1

def checkGcdK (k : Nat) : Bool :=
  gcdN (pow2m1 k) (pow2m1 k + 2) == 1

def checkTauK (k : Nat) : Bool :=
  tau (pow2m1 (2*k)) == tau (pow2m1 k) * tau (pow2m1 k + 2)

def checkGcdRange (N : Nat) : Bool :=
  (List.range N).all (fun i => checkGcdK (i + 1))

def checkTauRange (N : Nat) : Bool :=
  (List.range N).all (fun i => checkTauK (i + 1))

theorem msl_fmz_erdos893_campaign_001_R009_L1_a1r2  : checkGcdRange 200 = true && checkTauRange 6 = true := by decide
