import Mathlib

set_option autoImplicit false

def SumOneTo (n : ℕ) : ℕ := ∑ k in Finset.range (n + 1), k

theorem msl_fmz_erdos1004_campaign_001_R001_L1_a2r1  : ∀ n : ℕ, 1 ≤ n → SumOneTo n = n * (n + 1) / 2 := by
  intro n hn
  unfold SumOneTo
  simpa [Nat.add_sub_cancel, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Finset.sum_range_id (n + 1))
