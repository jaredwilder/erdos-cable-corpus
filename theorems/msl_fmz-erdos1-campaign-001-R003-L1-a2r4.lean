import Mathlib

set_option autoImplicit false

def exactLeCheck (a b c d : Nat) : Bool := decide (a * d ≤ c * b)
def exactLtCheck (a b c d : Nat) : Bool := decide (a * d < c * b)
def exactEqCheck (a b c d : Nat) : Bool := decide (a * d = c * b)

theorem msl_fmz_erdos1_campaign_001_R003_L1_a2r4  : ∀ a b c d : Nat, (exactLeCheck a b c d = true ↔ a * d ≤ c * b) ∧ (exactLtCheck a b c d = true ↔ a * d < c * b) ∧ (exactEqCheck a b c d = true ↔ a * d = c * b) := by
  intro a b c d
  simp [exactLeCheck, exactLtCheck, exactEqCheck]
