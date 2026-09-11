import Mathlib

set_option autoImplicit false

def l1_statement : Prop := ∀ (R B : ℚ), 0 ≤ B → (R ^ 2 ≤ B ^ 2 ↔ |R| ≤ B)

theorem msl_fmz_erdos289_campaign_001_R006_L1_a2r5  : l1_statement := by
  intro R B hB
  rw [show R ^ 2 = |R| ^ 2 by exact sq_abs R]
  exact sq_le_sq₀ (abs_nonneg R) hB
