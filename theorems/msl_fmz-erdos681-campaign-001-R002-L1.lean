set_option autoImplicit false

-- Least prime factor by trial division with explicit fuel.
def lpD : Nat → Nat → Nat → Nat
  | 0, m, _ => m
  | f+1, m, d => if d*d > m then m else if m % d == 0 then d else lpD f m (d+1)

def lp (m : Nat) : Nat := lpD m m 2

def isComp (m : Nat) : Bool := 4 ≤ m && (List.range (m-2)).any fun d => m % (d+2) == 0

-- L1 fragment (contrapositive): for every composite m ≤ 120 and every 2 ≤ k ≤ 10,
-- m < k^4 implies p(m) ≤ k^2, i.e. p(m) > k^2 ∧ m composite forces m ≥ k^4.
def check : Bool :=
  (List.range 9).all fun i =>
    let k := i + 2
    (List.range 117).all fun j =>
      let m := j + 4
      !(isComp m && m < k*k*k*k) || lp m ≤ k*k

theorem msl_fmz_erdos681_campaign_001_R002_L1  : check = true := by decide
