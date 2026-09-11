import Mathlib

set_option autoImplicit false

def Erdos1142Prop (n : ℕ) : Prop := 2 < n ∧ ∀ k, 0 < k → 2 ^ k < n → (n - 2 ^ k).Prime

theorem msl_fmz_erdos1142_campaign_001_R003_L1_a1r4  : Erdos1142Prop 4 := by
  refine ⟨by norm_num, ?_⟩
  intro k hk hlt
  have hk_le : k ≤ 1 := by
    by_contra hnot
    have hk_ge : 2 ≤ k := by omega
    have hpow : 2 ^ 2 ≤ 2 ^ k := by
      exact Nat.pow_le_pow_right (by omega) hk_ge
    omega
  have hk_eq : k = 1 := by omega
  subst k
  norm_num
