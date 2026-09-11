import Mathlib

set_option autoImplicit false

theorem msl_o02_arg_injectivity_2026_09_05 (z w : ℂ) (hn : ‖z‖ = ‖w‖) (ha : z.arg = w.arg) : z = w := by exact Complex.ext_norm_arg hn ha
