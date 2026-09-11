import Mathlib

set_option autoImplicit false

-- no auxiliary definitions

theorem msl_fmz_erdos313_campaign_001_R002_L1_a2r3  : ∀ n : ℕ, n ≤ 50 → (∑ k in Finset.range (n + 1), Nat.choose n k) = 2 ^ n := by
  intro n hn
  simpa using Nat.sum_choose n
