import Mathlib

set_option autoImplicit false

def Erdos1142Prop (n : ℕ) : Prop := 2 < n ∧ ∀ k, 0 < k → 2 ^ k < n → (n - 2 ^ k).Prime

theorem msl_fmz_erdos1142_campaign_001_R003_L1_a1r3  : Erdos1142Prop 4 ∧ ¬ Erdos1142Prop 5 := by
  constructor
  · refine ⟨by norm_num, ?_⟩
    intro k hk hlt
    have hk1 : k = 1 := by omega
    subst k
    norm_num
  · intro h
    rcases h with ⟨_, hp⟩
    have h := hp 2 (by norm_num) (by norm_num)
    norm_num at h
