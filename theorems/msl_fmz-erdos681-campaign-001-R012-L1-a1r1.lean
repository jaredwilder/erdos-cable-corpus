set_option autoImplicit false

def lpFactor : Nat -> Nat
  | m => match m with
    | 0 => 0 | 1 => 1 | m =>
      let rec go (d : Nat) (m : Nat) : Nat :=
        if d * d > m then m
        else if m % d == 0 then d
        else go (d+1) m
      go 2 m

def evenClause (n k : Nat) : Bool :=
  let m := n + k
  k % 2 == 0 && k >= 2 && m >= 4 && m % 2 == 0 && k * k < lpFactor m

def checkRange (N : Nat) : Bool :=
  (List.range N).all (fun n => (List.range (N/2+1)).all (fun j => !(evenClause n (2*j))))

theorem msl_fmz_erdos681_campaign_001_R012_L1_a1r1  : checkRange 60 = true := by decide
