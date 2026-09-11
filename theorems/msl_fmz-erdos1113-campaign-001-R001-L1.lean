import Mathlib

set_option autoImplicit false

-- no auxiliary definitions

theorem msl_fmz_erdos1113_campaign_001_R001_L1  : ∀ (verifier₁ verifier₂ : List Nat → Bool), verifier₁ [] = false → verifier₂ [] = false → ¬ (verifier₁ [] = true ∨ verifier₂ [] = true) := by
  intro verifier₁ verifier₂ h₁ h₂ h
  rcases h with h | h
  · have : false = true := h₁.symm.trans h
    cases this
  · have : false = true := h₂.symm.trans h
    cases this
