import Mathlib

set_option autoImplicit false

def l1_statement : Prop := ∀ (R B : ℚ), 0 ≤ B → (R ^ 2 ≤ B ^ 2 ↔ |R| ≤ B)

theorem msl_fmz_erdos289_campaign_001_R006_L1_a2r6  : l1_statement := by
  intro R B hB
  constructor
  · intro h
    have h' : |R| ^ 2 ≤ B ^ 2 := by
      simpa only [sq_abs] using h
    exact (sq_le_sq₀ (abs_nonneg R) hB).mp h'
  · intro h
    have h' : |R| ^ 2 ≤ B ^ 2 := (sq_le_sq₀ (abs_nonneg R) hB).mpr h
    simpa only [sq_abs] using h'
