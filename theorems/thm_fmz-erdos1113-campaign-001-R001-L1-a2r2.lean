import Mathlib

set_option autoImplicit false

def VerifierAInput : Type := Empty
def VerifierBInput : Type := Empty
def HasNonemptyScopeCertificate (α : Type) : Prop := Nonempty α

theorem msl_fmz_erdos1113_campaign_001_R001_L1_a2r2  : (IsEmpty VerifierAInput ∧ IsEmpty VerifierBInput) ∧ (¬ HasNonemptyScopeCertificate VerifierAInput ∧ ¬ HasNonemptyScopeCertificate VerifierBInput) := by
  constructor
  · constructor <;> exact ⟨fun x => nomatch x⟩
  · constructor <;> intro h
    · rcases h with ⟨x⟩
      exact nomatch x
    · rcases h with ⟨x⟩
      exact nomatch x
