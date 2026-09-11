import Mathlib

set_option autoImplicit false
set_option maxRecDepth 100000

/-- The Paley-type split of the complete graph on five vertices: layer TRUE is the
difference class {1,4}, layer FALSE is {2,3}. Both layers are five-cycles. -/
def colK5 (a b : Fin 5) : Bool := (a - b = 1) || (a - b = 4)

theorem msl_erdos595_k5_two_cover  : ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c → ((colK5 a b == colK5 a c) && (colK5 a c == colK5 b c)) = false := by decide
