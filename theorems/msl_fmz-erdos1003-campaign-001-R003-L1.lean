set_option autoImplicit false

def totient (n : Nat) : Nat :=
  (List.range n).filter (fun k => Nat.gcd (k+1) n == 1) |>.length

def checkWitnesses : Bool :=
  totient 1 == totient 2 && totient 3 == totient 4 && totient 15 == totient 16

theorem msl_fmz_erdos1003_campaign_001_R003_L1  : checkWitnesses = true := by decide
