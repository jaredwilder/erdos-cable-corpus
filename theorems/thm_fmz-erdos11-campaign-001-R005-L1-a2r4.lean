import Mathlib

set_option autoImplicit false

-- no auxiliary definitions

theorem msl_fmz_erdos11_campaign_001_R005_L1_a2r4  : ∀ n ∈ Finset.Icc 3 99, Odd n → ∃ k l : ℕ, 1 ≤ k ∧ Squarefree k ∧ n = k + 2 ^ l := by native_decide
