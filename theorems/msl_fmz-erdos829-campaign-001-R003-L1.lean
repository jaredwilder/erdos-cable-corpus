set_option autoImplicit false

def margin_num : Nat := 20000
def margin_den : Nat := 10000
def lhs_num : Nat := 19881
def lhs_den : Nat := 10000
def strict_lt : Bool := lhs_num * margin_den < margin_num * lhs_den

theorem msl_fmz_erdos829_campaign_001_R003_L1  : strict_lt = true := by decide
