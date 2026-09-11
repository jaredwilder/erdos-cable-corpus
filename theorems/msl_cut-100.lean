import Mathlib

set_option autoImplicit false

theorem msl_cut_100  : ((List.range 260).filter (fun m => m > 100 && [20, 24, 27, 30, 36, 40, 42, 44, 45, 48, 54, 60, 63, 66, 70, 72, 75, 80, 81, 84, 88, 90, 96, 99, 100].any (fun k => m % k == 0))).length < [20, 24, 27, 30, 36, 40, 42, 44, 45, 48, 54, 60, 63, 66, 70, 72, 75, 80, 81, 84, 88, 90, 96, 99, 100].length := by decide
