import Mathlib

set_option autoImplicit false

def SumOneTo (n : ℕ) : ℕ := ∑ k in Finset.range (n + 1), k

theorem msl_fmz_erdos1004_campaign_001_R001_L1_a2r4  : ∀ n : ℕ, 1 ≤ n → SumOneTo n = n * (n + 1) / 2 := by
  intro n _
  unfold SumOneTo
  rw [Nat.sum_range_id]
  simp only [Nat.add_sub_cancel]
  rw [Nat.mul_comm]
