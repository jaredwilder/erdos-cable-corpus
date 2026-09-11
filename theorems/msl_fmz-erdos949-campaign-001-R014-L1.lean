set_option autoImplicit false

def inSet (x : Nat) (S : List Nat) : Bool := S.contains x

def sumFreeMod (S : List Nat) (n : Nat) : Bool :=
  S.all (fun a => S.all (fun b => !(inSet ((a + b) % n) S)))

def complementSize (S : List Nat) (n : Nat) : Nat :=
  (List.range n).filter (fun x => !(inSet x S)) |>.length

def S_witness : List Nat := [1, 3]
def modulus : Nat := 7

def check_witness : Bool :=
  sumFreeMod S_witness modulus && (complementSize S_witness modulus > modulus / 2)

theorem msl_fmz_erdos949_campaign_001_R014_L1  : check_witness = true := by decide
