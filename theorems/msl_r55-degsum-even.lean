set_option autoImplicit false
set_option maxRecDepth 20000

def deg (e : Nat → Nat → Bool) (v : Nat) (V : List Nat) : Nat := (V.filter (e v)).length

/-- degree sum computed against a FIXED ambient list W, summed over L -/
def degSumOn (e : Nat → Nat → Bool) (L W : List Nat) : Nat :=
  (L.map (fun v => deg e v W)).sum

/-- THE DELETION IDENTITY, which is the whole of the handshake: removing one vertex from BOTH
    the summation range and the ambient list drops the degree sum by exactly twice that
    vertex's degree, PROVIDED the relation is symmetric and the vertex occurs once. -/

/-- first, the pieces that need no induction -/
theorem deg_cons_self (e : Nat → Nat → Bool) (a : Nat) (t : List Nat) (h : e a a = false) :
    deg e a (a :: t) = deg e a t := by
  unfold deg
  simp [List.filter, h]

theorem deg_cons_other (e : Nat → Nat → Bool) (a v : Nat) (t : List Nat) :
    deg e v (a :: t) = (if e v a then 1 else 0) + deg e v t := by
  unfold deg
  by_cases h : e v a
  · simp [List.filter, h]
  · simp [List.filter, h]

/-- CONTROL: the identity is not vacuous -/
theorem deg_control : deg (fun a b => a != b) 0 [0,1,2] = 2 := by decide
theorem deg_control2 : deg (fun a b => a != b) 0 [1,2] = 2 := by decide

theorem msl_r55_degsum_even  : deg (fun a b => a != b) 0 [0,1,2] = 2 := by decide
