set_option autoImplicit false

def lpf (m : Nat) : Nat :=
  match (List.range (m+1)).find? (fun d => d >= 2 && m % d == 0) with
  | some d => d
  | none => m

def evenClause (n k : Nat) : Bool :=
  let m := n + k
  k % 2 == 0 && k >= 2 && m >= 4 && m % 2 == 0 && k * k < lpf m

def checkRange : Bool :=
  (List.range 12).all (fun n =>
    (List.range 12).all (fun k => !(evenClause n k)))

theorem msl_fmz_erdos681_campaign_001_R012_L1_a1r2  : checkRange = true := by decide
