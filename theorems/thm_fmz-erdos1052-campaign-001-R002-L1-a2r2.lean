import Mathlib

set_option autoImplicit false

def unitaryDivisors (n : ℕ) : Finset ℕ := {d ∈ Finset.Icc 1 n | d ∣ n ∧ Nat.Coprime d (n / d)}
def properUnitaryDivisors (n : ℕ) : Finset ℕ := {d ∈ Finset.Ico 1 n | d ∣ n ∧ Nat.Coprime d (n / d)}

theorem msl_fmz_erdos1052_campaign_001_R002_L1_a2r2  : 6 = 2 * 3 ∧ unitaryDivisors 6 = ({1, 2, 3, 6} : Finset ℕ) ∧ properUnitaryDivisors 6 = ({1, 2, 3} : Finset ℕ) ∧ (∑ d in properUnitaryDivisors 6, d) = 6 := by
  decide
