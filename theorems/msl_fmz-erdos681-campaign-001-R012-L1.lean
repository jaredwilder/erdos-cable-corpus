set_option autoImplicit false

partial def lpfHelp (m d : Nat) : Nat :=
  if d * d > m then m
  else if m % d == 0 then d
  else lpfHelp m (d + 1)

def lpf (m : Nat) : Nat := lpfHelp m 2

def checkEvenClause (n k : Nat) : Bool :=
  k % 2 == 0 && k >= 2 && (n + k) % 2 == 0 && lpf (n + k) == 2 && lpf (n + k) < k * k

def sweep (n hi : Nat) : Bool :=
  (List.range ((hi / 2) + 1)).all (fun i => checkEvenClause n (2 * i))

def L1_check : Bool := sweep 100 20

theorem msl_fmz_erdos681_campaign_001_R012_L1  : L1_check = true := by decide
