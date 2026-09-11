import Mathlib

set_option autoImplicit false

-- no auxiliary definitions

theorem msl_fmz_erdos1142_campaign_001_R003_L1_a1r2  : (Erdos1142Prop 4 ∧ ¬ Erdos1142Prop 5) ∧ ∀ k : ℕ, 0 < k → 2 ^ k < 4 → k = 1 := by
  constructor
  · constructor
    · refine ⟨by omega, ?_⟩
      intro k hk hlt
      have hk_le : k ≤ 1 := by
        by_contra h
        have hk_ge : 2 ≤ k := by omega
        have hp : 2 ^ 2 ≤ 2 ^ k := by
          exact Nat.pow_le_pow_right (by omega : 1 ≤ 2) hk_ge
        omega
      interval_cases k <;> norm_num at *
    · intro h
      rcases h with ⟨_, hprop⟩
      have hbad : (5 - 2 ^ 2).Prime := hprop 2 (by omega) (by norm_num)
      norm_num at hbad
  · intro k hk hlt
    have hk_le : k ≤ 1 := by
      by_contra h
      have hk_ge : 2 ≤ k := by omega
      have hp : 2 ^ 2 ≤ 2 ^ k := by
        exact Nat.pow_le_pow_right (by omega : 1 ≤ 2) hk_ge
      omega
    omega
