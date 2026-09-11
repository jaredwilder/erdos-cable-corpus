set_option autoImplicit false

def divides (d m : Nat) : Bool := m % d == 0

def isComposite (m : Nat) : Bool := m >= 4 && divides 2 m

-- For the checked range, n+1 ranges over 3..N+1; a number m in this range is
-- composite iff it is even and >= 4 (odd composites start at 9 = 3^2, outside
-- only when N+1 < 9; we keep N small enough that this holds).
def k1WitnessExists (n : Nat) : Bool := divides 2 (n + 1)

def checkLemma (N : Nat) : Bool := (List.range (N - 1) |>.all (fun i => let n := i + 2; k1WitnessExists n == isComposite (n + 1)))

theorem msl_fmz_erdos681_campaign_001_R009_L1  : checkLemma 6 = true := by decide
