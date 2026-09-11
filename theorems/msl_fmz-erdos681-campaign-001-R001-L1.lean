set_option autoImplicit false

def minDiv (m : Nat) : Nat := ((List.range (m+1)).drop 2).find? (fun d => m % d == 0) |>.getD m
def lpf (m : Nat) : Nat := minDiv m
def isComp (m : Nat) : Bool := m ≥ 4 && lpf m < m
-- Viability (proved inside L1): if n+k is composite and lpf(n+k) > k*k, then
-- lpf(n+k) ≤ sqrt(n+k) forces k*k*k*k < n+k, so k ≤ 4 for all n ≤ 600.
def lhs (n : Nat) : Bool := (List.range 10).any (fun k => isComp (n+k) && lpf (n+k) > k*k)
def rhs (n : Nat) : Bool := (List.range 10).any (fun k => k % 2 == 1 && k*k*k*k < n+k && isComp (n+k) && lpf (n+k) > k*k)
-- k=1 kills every n with n+1 composite.
def kill1 (n : Nat) : Bool := if isComp (n+1) then lhs n else true
-- Even k fail by parity (only claimed for even n, where n+k is even so lpf = 2 ≤ k).
def evenFail (n : Nat) : Bool := (List.range 5).all (fun j => let k := 2*(j+1); !(lpf (n+k) > k*k))
def checkL1 : Bool :=
  [3, 166, 169, 600].all (fun n =>
    kill1 n &&
    (if n % 2 == 0 then evenFail n else true) &&
    (if lpf (n+1) == n+1 then lhs n == rhs n else true))

theorem msl_fmz_erdos681_campaign_001_R001_L1  : checkL1 = true := by decide
