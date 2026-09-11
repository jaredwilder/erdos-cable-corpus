set_option autoImplicit false

def l1Record : List String := ["residual_expression", "residual_bound", "residual_domain"]
def l1Supplied : List String := []
def degenerate (required supplied : List String) : Bool :=
  required.all (fun r => !(supplied.contains r))
def check_l1_degenerate : Bool := degenerate l1Record l1Supplied

theorem msl_fmz_erdos394_campaign_001_R005_L1  : check_l1_degenerate = true := by decide
