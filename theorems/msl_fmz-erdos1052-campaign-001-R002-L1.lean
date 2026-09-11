import Mathlib

set_option autoImplicit false

namespace Erdos1052

def unitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ Finset.Icc 1 n | d ∣ n ∧ d.Coprime (n / d)}

def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ Finset.Ico 1 n | d ∣ n ∧ d.Coprime (n / d)}

def IsUnitaryPerfect (n : ℕ) : Prop :=
  ∑ i ∈ properUnitaryDivisors n, i = n ∧ 0 < n
end Erdos1052

theorem msl_fmz_erdos1052_campaign_001_R002_L1  : Erdos1052.unitaryDivisors 6 = ({1, 2, 3, 6} : Finset ℕ) ∧ Erdos1052.properUnitaryDivisors 6 = ({1, 2, 3} : Finset ℕ) ∧ Erdos1052.IsUnitaryPerfect 6 := by
  norm_num [Erdos1052.unitaryDivisors, Erdos1052.properUnitaryDivisors, Erdos1052.IsUnitaryPerfect]
  decide +kernel
