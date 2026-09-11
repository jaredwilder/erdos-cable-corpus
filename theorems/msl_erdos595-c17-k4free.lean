import Mathlib

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 8000000

def adjC (a b : Fin 17) : Bool :=
  (a - b = 1) || (a - b = 2) || (a - b = 4) || (a - b = 8) ||
  (a - b = 9) || (a - b = 13) || (a - b = 15) || (a - b = 16)

def colC (a b : Fin 17) : Bool :=
  (a - b = 1) || (a - b = 4) || (a - b = 13) || (a - b = 16)

theorem msl_erdos595_c17_k4free  : ∀ a b c d : Fin 17, (adjC a b && adjC a c && adjC a d && adjC b c && adjC b d && adjC c d) = false := by decide
