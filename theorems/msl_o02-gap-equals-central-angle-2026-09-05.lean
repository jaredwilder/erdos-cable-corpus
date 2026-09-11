import Mathlib

set_option autoImplicit false

theorem msl_o02_gap_equals_central_angle_2026_09_05 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ Real.pi) : Real.arccos (Real.cos t) = t := by exact Real.arccos_cos h0 h1
