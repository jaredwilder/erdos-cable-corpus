import Mathlib

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 8000000

def adjC (a b : Fin 17) : Bool :=
  (a - b = 1) || (a - b = 2) || (a - b = 4) || (a - b = 8) ||
  (a - b = 9) || (a - b = 13) || (a - b = 15) || (a - b = 16)

def colC (a b : Fin 17) : Bool :=
  (a - b = 1) || (a - b = 4) || (a - b = 13) || (a - b = 16)

theorem msl_erdos595_c17_two_cover  : ∀ a b c : Fin 17, (adjC a b && adjC a c && adjC b c && (colC a b == colC a c) && (colC a c == colC b c)) = false := by decide
