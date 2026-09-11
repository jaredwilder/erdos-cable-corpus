import Mathlib

set_option autoImplicit false

def VerifierAInput := Empty
def VerifierBInput := Empty
def HasNonemptyScopeCertificate (α : Type) := Nonempty α

theorem msl_fmz_erdos1113_campaign_001_R001_L1_a2r1  : (IsEmpty VerifierAInput ∧ IsEmpty VerifierBInput) ∧ ¬ HasNonemptyScopeCertificate VerifierAInput ∧ ¬ HasNonemptyScopeCertificate VerifierBInput := by
  simp [VerifierAInput, VerifierBInput, HasNonemptyScopeCertificate]
