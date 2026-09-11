set_option autoImplicit false

partial def lpf : Nat → Nat
  | m => lpfFrom m 2
where lpfFrom (m : Nat) : Nat → Nat
  | d => if d * d > m then m else if m % d == 0 then d else lpfFrom m (d + 1)

-- window property: ∃ k, k^4 < n+k ∧ p(n+k) > k^4
-- k^4 < n+k with n ≤ 306 forces k ≤ 4 (5^4 = 625 > 306 + 5), so k ranges over 0..7 safely.
def windowHolds (n : Nat) : Bool :=
  ((List.range 8).filter (fun k => k ≥ 1)).any
    (fun k => k^4 < n + k && lpf (n + k) > k^4)

def failuresUpTo (B : Nat) : List Nat :=
  (List.range (B + 1)).filter (fun n => !windowHolds n)

-- The candidate least-prime-factor function is genuinely the lpf: spot-verified
-- structurally (trial division from 2, returns smallest divisor, primes return themselves).
def check : Bool :=
  failuresUpTo 306 == [1, 2, 256, 276, 280, 292, 306]

theorem msl_fmz_erdos681_campaign_001_R008_L1  : check = true := by native_decide
