import Mathlib

set_option autoImplicit false

def Erdos1142Prop (n : ℕ) : Prop := 2 < n ∧ ∀ k, 0 < k → 2 ^ k < n → (n - 2 ^ k).Prime

theorem msl_fmz_erdos1142_campaign_001_R003_L1_a1r1  : (Erdos1142Prop 4 ∧ ¬ Erdos1142Prop 5) ∧ ∀ k, 0 < k → 2 ^ k < 4 → k = 1 := by
  constructor
  · constructor
    · refine ⟨by norm_num, ?_⟩
      intro k hk hlt
      have hk' : k ≤ 1 := by
        by_contra! h
        exact absurd (Nat.pow_le_pow_right (by omega : 1 ≤ 2) h) (by omega)
      interval_cases k <;> norm_num at *
    · intro h
      rcases h with ⟨_, hprop⟩
      have hbad := hprop 2 (by omega) (by omega)
      revert hbad
      decide
  · intro k hk hlt
    have hk' : k ≤ 1 := by
      by_contra! h
      exact absurd (Nat.pow_le_pow_right (by omega : 1 ≤ 2) h) (by omega)
    omega
