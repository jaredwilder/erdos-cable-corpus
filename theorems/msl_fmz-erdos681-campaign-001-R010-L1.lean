set_option autoImplicit false

-- Fuel-recursive, total, Nat/Bool only; fuel exhaustion returns false (fail-closed).
def lpfAux : Nat -> Nat -> Nat -> Nat
  | 0, _, m => m
  | (f+1), d, m => if d*d > m then m else if m % d == 0 then d else lpfAux f (d+1) m

def lpf (m : Nat) : Nat := lpfAux m 2 m

def isComposite (m : Nat) : Bool := m >= 4 && lpf m != m

-- L1 fragment (i): k^4 < n+k => k^4 < 2*n, for all n in [1,60], all k in the antecedent range.
def loopK : Nat -> Nat -> Nat -> Bool
  | 0, _, _ => false
  | (f+1), n, k => if k^4 >= n + k then true else if k^4 < 2*n then loopK f n (k+1) else false

def loopN : Nat -> Nat -> Bool
  | 0, _ => false
  | (f+1), n => if n > 60 then true else if loopK 200 n 1 then loopN f (n+1) else false

def reductionCheck : Bool := loopN 70 1

-- L1 fragment (ii): composite m in [4,2000] => (lpf m)^2 <= m.
def lpfLoop : Nat -> Nat -> Bool
  | 0, _ => false
  | (f+1), m => if m > 2000 then true else if !isComposite m || (lpf m)^2 <= m then lpfLoop f (m+1) else false

def lpfBoundCheck : Bool := lpfLoop 2100 4

def checkAll : Bool := reductionCheck && lpfBoundCheck

theorem msl_fmz_erdos681_campaign_001_R010_L1  : checkAll = true := by decide
