import Mathlib

set_option autoImplicit false

-- no auxiliary definitions

theorem msl_fmz_erdos700_campaign_001_R002_L1_a2r1  : ∀ n : ℕ, (∑ i in Finset.range n, (((i + 1 : ℕ) : ℤ) - (i : ℤ))) = (n : ℤ) := by
  intro n
  have h : ∀ i : ℕ, (((i + 1 : ℕ) : ℤ) - (i : ℤ)) = 1 := by
    intro i
    rw [Nat.cast_add, Nat.cast_one]
    ring
  simp [h]
