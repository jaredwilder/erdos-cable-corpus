import Mathlib

set_option autoImplicit false

theorem msl_o02_gap_above_pi_breaks_central_2026_09_05  : Real.arccos (Real.cos (3 * Real.pi / 2)) ≠ 3 * Real.pi / 2 := by
  have hc : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [show (3 * Real.pi / 2) = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi,
        Real.cos_pi_div_two, neg_zero]
  rw [hc, Real.arccos_zero]
  have hp := Real.pi_pos
  intro hEq
  linarith
