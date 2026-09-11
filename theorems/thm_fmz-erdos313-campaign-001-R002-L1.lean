import Mathlib

set_option autoImplicit false

-- no auxiliary definitions

theorem msl_fmz_erdos313_campaign_001_R002_L1  : ∀ n : ℕ, 0 ≤ n ∧ n ≤ 50 → (∑ k in Finset.range (n + 1), Nat.choose n k) = 2 ^ n := by
  intro n hn
  rcases hn with ⟨_, hn⟩
  interval_cases n <;> decide
