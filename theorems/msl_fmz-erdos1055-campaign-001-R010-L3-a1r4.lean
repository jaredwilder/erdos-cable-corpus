import Mathlib

set_option autoImplicit false

-- no auxiliary definitions

theorem msl_fmz_erdos1055_campaign_001_R010_L3_a1r4  : Nat.Prime 2 ∧ Nat.Prime 13 ∧ Nat.Prime 37 ∧ Nat.Prime 73 ∧ Nat.Prime 1021 := by
  constructor
  · norm_num
  constructor
  · norm_num [Nat.prime_def_lt]
  constructor
  · norm_num [Nat.prime_def_lt]
  constructor
  · norm_num [Nat.prime_def_lt]
  · norm_num [Nat.prime_def_lt]
