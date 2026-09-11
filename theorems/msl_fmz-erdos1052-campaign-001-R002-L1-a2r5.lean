import Mathlib

set_option autoImplicit false

def unitaryDivisors (n : Nat) : Finset Nat := {d ∈ Finset.Icc 1 n | d ∣ n ∧ Nat.Coprime d (n / d)}
def properUnitaryDivisors (n : Nat) : Finset Nat := {d ∈ Finset.Ico 1 n | d ∣ n ∧ Nat.Coprime d (n / d)}
def isUnitaryPerfect (n : Nat) : Prop := (∑ d in properUnitaryDivisors n, d) = n ∧ 0 < n

theorem msl_fmz_erdos1052_campaign_001_R002_L1_a2r5  : 6 = 2 * 3 ∧ unitaryDivisors 6 = ({1, 2, 3, 6} : Finset Nat) ∧ properUnitaryDivisors 6 = ({1, 2, 3} : Finset Nat) ∧ (∑ d in properUnitaryDivisors 6, d) = 6 ∧ isUnitaryPerfect 6 := by
  decide
