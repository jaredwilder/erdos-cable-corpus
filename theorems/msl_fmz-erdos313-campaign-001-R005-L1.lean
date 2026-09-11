set_option autoImplicit false

def check_L1 : Bool := (1 : Nat) + 1 == 2

theorem msl_fmz_erdos313_campaign_001_R005_L1  : check_L1 = true := by decide
