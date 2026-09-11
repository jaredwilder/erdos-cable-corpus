import Mathlib

set_option autoImplicit false

def artifactRegistry : List Nat := []
def certificateSoundlyIssuable (artifacts : List Nat) : Prop := artifacts ≠ []

theorem msl_fmz_erdos400_campaign_001_R002_L1_a2r3  : artifactRegistry = [] ∧ ¬ certificateSoundlyIssuable artifactRegistry := by
  constructor
  · rfl
  · simp [certificateSoundlyIssuable, artifactRegistry]
