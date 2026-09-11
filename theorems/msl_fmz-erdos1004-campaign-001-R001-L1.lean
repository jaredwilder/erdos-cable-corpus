import Mathlib

set_option autoImplicit false

-- no auxiliary definitions

theorem msl_fmz_erdos1004_campaign_001_R001_L1  : ∀ n : ℕ, 1 ≤ n → (∑ k in Finset.range (n + 1), k) = n * (n + 1) / 2 := by
  intro n hn
  simpa [Nat.add_sub_cancel, Nat.mul_comm] using Nat.sum_range_id (n + 1)
