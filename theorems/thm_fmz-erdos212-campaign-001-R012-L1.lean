set_option autoImplicit false

inductive ResidualSign | resolved (b : Bool) | unresolved

def verifierPass : ResidualSign → Bool
  | .resolved b => b
  | .unresolved => false

def r012_residual : ResidualSign := .unresolved

theorem msl_fmz_erdos212_campaign_001_R012_L1  : verifierPass r012_residual = false ∧ ∀ (cfg : ResidualSign), cfg = ResidualSign.unresolved → verifierPass cfg = false := by
  refine ⟨?_, ?_⟩
  · simp [verifierPass, r012_residual]
  · intro cfg h
    subst h
    rfl
