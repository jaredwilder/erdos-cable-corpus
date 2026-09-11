import Mathlib

set_option autoImplicit false

def verifyUndefined (residual : Option Unit) : Bool := match residual with | none => false | some _ => true

theorem msl_fmz_erdos390_campaign_001_R005_L1  : ∀ residual : Option Unit, residual = none → verifyUndefined residual = false := by intro residual h; subst residual; rfl
