import Mathlib

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 8000000

/-- The circulant on seventeen vertices with connection set {1,2,4,8} and its negatives. -/
def adjC (a b : Fin 17) : Bool :=
  let d := a - b
  d = 1 || d = 2 || d = 4 || d = 8 || d = 9 || d = 13 || d = 15 || d = 16

/-- The symmetric two-colouring: layer TRUE is the difference class {1,4} and its negatives. -/
def colC (a b : Fin 17) : Bool :=
  let d := a - b
  d = 1 || d = 4 || d = 13 || d = 16

theorem msl_erdos595_c17_k4free_two_cover  : (∀ a b c d : Fin 17, adjC a b = true → adjC a c = true → adjC a d = true → adjC b c = true → adjC b d = true → adjC c d = true → False) ∧ (∀ a b c : Fin 17, adjC a b = true → adjC a c = true → adjC b c = true → ¬ (colC a b = colC a c ∧ colC a c = colC b c)) := by decide
