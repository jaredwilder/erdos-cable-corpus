import Mathlib

set_option autoImplicit false

-- no auxiliary definitions

theorem msl_fmz_erdos11_campaign_001_R005_L1_a2r5  : ∀ n : ℕ, 3 ≤ n → n ≤ 99 → Odd n → ∃ k ∈ Finset.range n, ∃ l ∈ Finset.range 7, Squarefree k ∧ n = k + 2 ^ l := by decide
