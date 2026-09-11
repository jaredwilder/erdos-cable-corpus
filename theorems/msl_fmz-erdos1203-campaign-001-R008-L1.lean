set_option autoImplicit false

def gauss : Nat → Nat
  | 0 => 0
  | (n+1) => gauss n + (n+1)

def checkSum : Nat → Bool
  | 0 => true
  | (n+1) => (gauss (n+1) == (n+1) * (n+2) / 2) && checkSum n

def checkRange (N : Nat) : Bool := checkSum N

theorem msl_fmz_erdos1203_campaign_001_R008_L1  : checkRange 20 = true := by decide
