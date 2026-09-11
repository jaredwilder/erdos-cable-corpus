import Mathlib

set_option autoImplicit false

theorem msl_LO100  : ((List.range (100+159)).filter (fun m => m > 100 && [20,24,27,30,36,42,44,45,63,66,70,75,99].any (fun k => m % k == 0))).length < [20,24,27,30,36,42,44,45,63,66,70,75,99].length := by decide
