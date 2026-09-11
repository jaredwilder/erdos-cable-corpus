set_option autoImplicit false

def verInput := { reduction : Option String, occurrences : Nat, hasSign : Bool, hasFloat : Bool }
-- Bool-valued, total, decidable: the deterministic verifier's abort branch logic
def abortBranch (v : verInput) : Bool :=
  (v.reduction == none) || (v.reduction == some "per contract") ||
  (v.occurrences == 0 && !v.hasSign && !v.hasFloat)
-- Concrete instance of L1's antecedent: null reduction, occurrence-count 0
-- for Good(n)/kernel-trace-7/B outside L1's own text, no sign, no float
def l1instance : verInput := { reduction := none, occurrences := 0, hasSign := false, hasFloat := false }

theorem msl_fmz_erdos1142_campaign_001_R002_L1  : abortBranch l1instance = true := by decide
