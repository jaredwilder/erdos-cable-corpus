import Mathlib

set_option autoImplicit false

theorem msl_cut_150  : ((List.range 396).filter (fun m => m > 150 && [36, 40, 42, 45, 48, 50, 60, 64, 70, 72, 75, 80, 84, 90, 96, 100, 105, 108, 120, 125, 126, 128, 135, 140, 144, 147, 150].any (fun k => m % k == 0))).length < [36, 40, 42, 45, 48, 50, 60, 64, 70, 72, 75, 80, 84, 90, 96, 100, 105, 108, 120, 125, 126, 128, 135, 140, 144, 147, 150].length := by decide
