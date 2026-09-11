set_option autoImplicit false

def divides (d m : Nat) : Bool := d != 0 && m % d == 0

def leastFactor : Nat → Nat
  | 0 => 0
  | 1 => 1
  | m => match (List.range (m+1)).filter (fun d => 2 <= d && d < m && divides d m) with
         | d :: _ => d
         | [] => m

def isComposite (m : Nat) : Bool :=
  m >= 4 && divides (leastFactor m) m && leastFactor m < m

def checkL1 (N : Nat) : Bool :=
  (List.range (N+1)).all (fun m =>
    if isComposite m then
      let p := leastFactor m
      2 <= p && p * p <= m
    else true)

-- sanity anchors: composites and primes classified correctly at small values
def sanity : Bool :=
  isComposite 4 && isComposite 9 && isComposite 15 &&
  !(isComposite 2) && !(isComposite 3) && !(isComposite 5) &&
  !(isComposite 1) && !(isComposite 0) &&
  leastFactor 15 == 3 && leastFactor 49 == 7 && leastFactor 4 == 2

theorem msl_fmz_erdos681_campaign_001_R006_L1  : checkL1 20 = true && sanity = true := by decide
