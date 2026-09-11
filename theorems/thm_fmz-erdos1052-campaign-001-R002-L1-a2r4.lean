import Mathlib

set_option autoImplicit false

-- no auxiliary definitions

theorem msl_fmz_erdos1052_campaign_001_R002_L1_a2r4  : 6 = 2 * 3 ∧ ({d ∈ Finset.Icc 1 6 | d ∣ 6 ∧ d.Coprime (6 / d)} : Finset ℕ) = ({1, 2, 3, 6} : Finset ℕ) ∧ Erdos1052.properUnitaryDivisors 6 = ({1, 2, 3} : Finset ℕ) ∧ 1 + 2 + 3 = 6 ∧ Erdos1052.IsUnitaryPerfect 6 := by
  norm_num [Erdos1052.IsUnitaryPerfect, Erdos1052.properUnitaryDivisors] <;> decide
