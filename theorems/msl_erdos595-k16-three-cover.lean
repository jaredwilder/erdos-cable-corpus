import Mathlib

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The GF(16) coset table: index by the XOR difference, value is the colour class. -/
def cosetColour : Fin 16 → Fin 3 :=
  ![0, 0, 1, 1, 2, 2, 2, 1, 0, 2, 0, 1, 0, 1, 2, 0]

/-- Colour the pair {a,b} of vertices of the complete graph on sixteen vertices by the
coset of their difference in the field of order sixteen, where the difference is the
bitwise exclusive or. -/
def k16Colour (a b : Fin 16) : Fin 3 :=
  cosetColour ⟨Nat.xor a.val b.val % 16, Nat.mod_lt _ (by norm_num)⟩

theorem msl_erdos595_k16_three_cover  : ∀ a b c : Fin 16, a ≠ b → a ≠ c → b ≠ c → ¬ (k16Colour a b = k16Colour a c ∧ k16Colour a c = k16Colour b c) := by decide
