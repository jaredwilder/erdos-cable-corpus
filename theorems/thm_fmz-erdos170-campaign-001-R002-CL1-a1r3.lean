import Mathlib

set_option autoImplicit false

-- no auxiliary definitions

theorem msl_fmz_erdos170_campaign_001_R002_CL1_a1r3  : ((∀ d1 d2 d3 d4 : ℕ, Even (4 * d1 + 6 * d2 + 6 * d3 + 4 * d4)) ∧ Odd (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10)) := by
  constructor
  · intro d1 d2 d3 d4
    refine ⟨2 * d1 + 3 * d2 + 3 * d3 + 2 * d4, ?_⟩
    omega
  · norm_num
