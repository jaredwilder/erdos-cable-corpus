import Mathlib

set_option autoImplicit false

theorem msl_LO1  : ((List.range 125).filter (fun mm => mm > 50 && [12,20,24,30,36,40,42,45,48,50].any (fun k => mm % k == 0))).length < [12,20,24,30,36,40,42,45,48,50].length := by decide
