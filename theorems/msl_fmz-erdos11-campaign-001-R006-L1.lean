import Mathlib

set_option autoImplicit false

def sqfreeCheck : Nat → Bool
  | 0 => false
  | n => (List.range (n + 1)).all (fun d => if d * d ∣ n then Nat.ble 1 d else true)

def hasDecomp (n : Nat) : Bool :=
  (List.range (n + 1)).any (fun k =>
    sqfreeCheck k && (List.range 7).any (fun l => k + 2 ^ l = n))

def oddList : List Nat :=
  (List.range 64).filter (fun n => n % 2 = 1) |>.filter (fun n => 3 ≤ n)

def checkFinite : Bool :=
  oddList.length = 31 && oddList.all hasDecomp

theorem msl_fmz_erdos11_campaign_001_R006_L1  : checkFinite = true := by decide
