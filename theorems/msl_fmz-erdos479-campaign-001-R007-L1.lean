set_option autoImplicit false

def v3 : Nat → Nat
  | 0 => 0
  | m => if m % 3 == 0 then 1 + v3 (m / 3) else 0

def val_a (a : Nat) : Nat := 2^(3^a) + 1

def check_a : Nat → Bool
  | 0 => v3 (val_a 0) == 1
  | 1 => v3 (val_a 1) == 2
  | 2 => v3 (val_a 2) == 3
  | 3 => v3 (val_a 3) == 4
  | _ => true

def check_witness : Bool :=
  List.all [0, 1, 2, 3] check_a && (2^4 % 4 == 0)

theorem msl_fmz_erdos479_campaign_001_R007_L1  : check_witness = true := by native_decide
