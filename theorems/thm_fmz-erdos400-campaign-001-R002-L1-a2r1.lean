import Mathlib

set_option autoImplicit false

def artifactRegistry : List Nat := []
def soundlyIssuable (artifacts : List Nat) : Prop := artifacts ≠ []

theorem msl_fmz_erdos400_campaign_001_R002_L1_a2r1  : ¬ soundlyIssuable artifactRegistry := by simp [soundlyIssuable, artifactRegistry]
