set_option autoImplicit false

-- Rationals scaled by 2; S = {3/2, 5/2} encoded as {3, 5}; A = 2Z, A+A = 4Z.
def S : List Nat := [3, 5]

def sumFree : Bool :=
  S.all (fun a => S.all (fun b => S.all (fun c => a + b != c)))

def disjointFromA : Bool :=
  S.all (fun s => s % 2 != 0)

def sumAvoidsS : Bool :=
  S.all (fun s => s % 4 != 0)

def check_witness : Bool :=
  sumFree && disjointFromA && sumAvoidsS

theorem msl_fmz_erdos949_campaign_001_R007_L2  : check_witness = true := by decide
