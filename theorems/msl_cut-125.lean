import Mathlib

set_option autoImplicit false

theorem msl_cut_125  : ((List.range 315).filter (fun m => m > 125 && [30, 36, 40, 48, 50, 56, 60, 72, 80, 84, 90, 96, 100, 105, 108, 112, 120, 125].any (fun k => m % k == 0))).length < [30, 36, 40, 48, 50, 56, 60, 72, 80, 84, 90, 96, 100, 105, 108, 112, 120, 125].length := by decide
