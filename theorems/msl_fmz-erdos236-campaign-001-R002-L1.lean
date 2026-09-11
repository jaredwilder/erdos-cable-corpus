import Mathlib

set_option autoImplicit false

def countRepr (n : Nat) : Nat :=
  (List.range (Nat.log2 n + 2)).filter
    (fun k => 2 ^ k < n && Nat.Prime (n - 2 ^ k)) |>.length

def checkLemma (N : Nat) : Bool :=
  (List.range (N + 1)).all
    (fun n => n < 2 || countRepr n <= Nat.log2 n + 1)

theorem msl_fmz_erdos236_campaign_001_R002_L1  : checkLemma 50 = true := by decide
