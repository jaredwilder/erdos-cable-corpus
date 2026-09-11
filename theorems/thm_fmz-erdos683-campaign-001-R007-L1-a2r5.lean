import Mathlib

set_option autoImplicit false

No auxiliary definitions; the proof uses the frozen Erdos683.P definition.

theorem msl_fmz_erdos683_campaign_001_R007_L1_a2r5  : ∀ c : ℝ, 0 < c → ∃ n k : ℕ, 1 ≤ k ∧ k ≤ n ∧ (Erdos683.P n k : ℝ) < min ((n - k + 1 : ℕ) : ℝ) ((k : ℝ) ^ (1 + c)) := by
  intro c hc
  refine ⟨2, 2, by norm_num, by norm_num, ?_⟩
  have hP : Erdos683.P 2 2 = 0 := by
    simp [Erdos683.P]
  rw [hP]
  have hpow : 0 < (2 : ℝ) ^ (1 + c) := by
    positivity
  exact lt_min (by norm_num) hpow
