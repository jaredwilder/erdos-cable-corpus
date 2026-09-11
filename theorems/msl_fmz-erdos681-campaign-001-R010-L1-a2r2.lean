set_option autoImplicit false

namespace R010

/-- Total, structurally recursive least-prime-factor-style divisor search:
    smallest divisor of m in [2, d0] (or m itself if none, i.e. m prime or m ≤ 3). -/
def divSearch : Nat → Nat → Nat → Nat
  | _, 0, _ => 0
  | m, k, acc =>
      if m ≤ 1 then 0
      else if k = 0 then acc
      else if m % k = 0 && k ≤ m then (if k < acc then k else acc)
      else divSearch m (k - 1) acc

def lpf (m : Nat) : Nat := divSearch m m m

def isComposite (m : Nat) : Bool :=
  m ≥ 4 && lpf m < m

/-- For all n ≤ bound, k with 2 ≤ k ≤ bound: k^4 < n+k → k^4 < 2n. -/
def checkWindow (bound : Nat) : Bool :=
  (List.range bound).all fun i =>
    let n := i + 1
    (List.range bound).all fun j =>
      let k := j + 2
      k^4 < n + k → k^4 < 2*n

/-- For all 1 ≤ m ≤ bound: composite m ⇒ (lpf m)^2 ≤ m. -/
def checkLpf (bound : Nat) : Bool :=
  (List.range bound).all fun i =>
    let m := i + 1
    isComposite m → (lpf m)^2 ≤ m

def check_all (bound : Nat) : Bool :=
  checkWindow bound && checkLpf bound

end R010

theorem msl_fmz_erdos681_campaign_001_R010_L1_a2r2  : R010.check_all 30 = true := by decide
