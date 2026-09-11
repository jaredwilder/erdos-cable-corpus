import Mathlib

set_option autoImplicit false

-- no auxiliary definitions

theorem msl_fmz_erdos170_campaign_001_R012_L1_a1r3  : Nat.choose 0 2 < 1 ∧ Nat.choose 1 2 < 1 ∧ Nat.choose 2 2 ≥ 1 := by norm_num [Nat.choose]
