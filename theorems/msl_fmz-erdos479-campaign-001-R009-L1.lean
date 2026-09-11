set_option autoImplicit false

-- Mod-1 vacuity: for modulus n = 1, every integer is congruent to every integer.
-- 2^1 - k = 2 - k is divisible by 1 for every k; the witness carries no information.

def oneDivides (k : Int) : Bool := (2 - k) % 1 == 0

def check_fragment (maxAbs : Nat) : Bool :=
  (List.range (2 * maxAbs + 1)).all
    (fun i => oneDivides ((i : Int) - (maxAbs : Int)))

theorem msl_fmz_erdos479_campaign_001_R009_L1  : check_fragment 20 = true := by decide
