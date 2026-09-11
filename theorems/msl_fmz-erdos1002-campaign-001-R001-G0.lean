set_option autoImplicit false

def residues (p q : Nat) : List Nat := (List.range' 1 q).map (fun k => (p * k) % q)

def check (p q : Nat) : Bool :=
  Nat.gcd p q == 1 ∧ (residues p q).sum == q * (q - 1) / 2

theorem msl_fmz_erdos1002_campaign_001_R001_G0  : check 1 2 = true ∧ check 1 3 = true ∧ check 2 3 = true ∧ check 1 4 = true ∧ check 3 4 = true := by decide
