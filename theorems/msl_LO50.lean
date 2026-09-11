import Mathlib

set_option autoImplicit false

theorem msl_LO50  : ((List.range (50+75)).filter (fun m => m > 50 && [12,20,24,30,36,40,42,45,48,50].any (fun k => m % k == 0))).length < [12,20,24,30,36,40,42,45,48,50].length := by decide
