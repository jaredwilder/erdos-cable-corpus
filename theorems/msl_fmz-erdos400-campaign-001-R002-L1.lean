import Mathlib

set_option autoImplicit false

def CertificateBytes := List Nat

def soundlyIssuable (artifacts : CertificateBytes) : Prop :=
  ∃ bytes, bytes ∈ artifacts

theorem L1_full :
    soundlyIssuable ([] : CertificateBytes) → False := by
  intro h
  rcases h with ⟨bytes, hbytes⟩
  simp at hbytes

theorem msl_fmz_erdos400_campaign_001_R002_L1  : soundlyIssuable ([] : CertificateBytes) → False := by
  intro h
  rcases h with ⟨bytes, hbytes⟩
  simp at hbytes
