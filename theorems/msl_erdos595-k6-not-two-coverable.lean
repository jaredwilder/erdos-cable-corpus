import Mathlib

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

theorem msl_erdos595_k6_not_two_coverable  : ∀ f : Fin 15 → Bool, (f 0 = f 1 ∧ f 1 = f 5) ∨ (f 0 = f 2 ∧ f 2 = f 6) ∨ (f 0 = f 3 ∧ f 3 = f 7) ∨ (f 0 = f 4 ∧ f 4 = f 8) ∨ (f 1 = f 2 ∧ f 2 = f 9) ∨ (f 1 = f 3 ∧ f 3 = f 10) ∨ (f 1 = f 4 ∧ f 4 = f 11) ∨ (f 2 = f 3 ∧ f 3 = f 12) ∨ (f 2 = f 4 ∧ f 4 = f 13) ∨ (f 3 = f 4 ∧ f 4 = f 14) ∨ (f 5 = f 6 ∧ f 6 = f 9) ∨ (f 5 = f 7 ∧ f 7 = f 10) ∨ (f 5 = f 8 ∧ f 8 = f 11) ∨ (f 6 = f 7 ∧ f 7 = f 12) ∨ (f 6 = f 8 ∧ f 8 = f 13) ∨ (f 7 = f 8 ∧ f 8 = f 14) ∨ (f 9 = f 10 ∧ f 10 = f 12) ∨ (f 9 = f 11 ∧ f 11 = f 13) ∨ (f 10 = f 11 ∧ f 11 = f 14) ∨ (f 12 = f 13 ∧ f 13 = f 14) := by decide
