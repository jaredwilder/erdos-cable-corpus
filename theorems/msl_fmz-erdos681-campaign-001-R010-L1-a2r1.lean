set_option autoImplicit false

namespace R010

def lpfAux (m : Nat) (d : Nat) : Nat :=
  if m ≤ 1 then 0
  else if d * d > m then m
  else if d ∣ m then d else lpfAux m (d + 1)

def lpf (m : Nat) : Nat := lpfAux m 2

def isComposite (m : Nat) : Bool :=
  m ≥ 4 && lpf m < m

/-- For all n,k with 2 ≤ k, 1 ≤ n ≤ bound: if k^4 < n+k then k^4 < 2n. -/
def checkWindow (bound : Nat) : Bool :=
  (List.range bound).all fun i =>
    let n := i + 1
    (List.range bound).all fun j =>
      let k := j + 2
      k^4 < n + k → k^4 < 2*n

/-- For all m ≤ bound: if m is composite then lpf m ≤ sqrt m (integer form: (lpf m)^2 ≤ m). -/
def checkLpf (bound : Nat) : Bool :=
  (List.range (bound + 1)).all fun m =>
    isComposite m → (lpf m)^2 ≤ m

def check_all (bound : Nat) : Bool :=
  checkWindow bound && checkLpf bound

end R010

theorem msl_fmz_erdos681_campaign_001_R010_L1_a2r1  : R010.check_all 60 = true := by decide
