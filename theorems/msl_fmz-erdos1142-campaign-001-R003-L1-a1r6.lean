import Mathlib

set_option autoImplicit false

def Erdos1142Prop (n : ℕ) : Prop := 2 < n ∧ ∀ k, 0 < k → 2 ^ k < n → (n - 2 ^ k).Prime

theorem msl_fmz_erdos1142_campaign_001_R003_L1_a1r6  : Erdos1142Prop 4 := by
  norm_num [Erdos1142Prop]
  intro k hk hlt
  interval_cases k <;> norm_num at *
