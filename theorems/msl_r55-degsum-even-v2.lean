set_option autoImplicit false
set_option maxRecDepth 20000

def deg (e : Nat → Nat → Bool) (v : Nat) (V : List Nat) : Nat := (V.filter (e v)).length

def degSumOn (e : Nat → Nat → Bool) (L W : List Nat) : Nat :=
  (L.map (fun v => deg e v W)).sum

theorem deg_cons_self (e : Nat → Nat → Bool) (a : Nat) (t : List Nat) (h : e a a = false) :
    deg e a (a :: t) = deg e a t := by
  unfold deg
  simp [List.filter_cons, h]

theorem deg_cons_other (e : Nat → Nat → Bool) (a v : Nat) (t : List Nat) :
    deg e v (a :: t) = (if e v a = true then 1 else 0) + deg e v t := by
  unfold deg
  by_cases h : e v a = true
  · simp [List.filter_cons, h]
    omega
  · simp [List.filter_cons, h]

theorem deg_control : deg (fun a b => a != b) 0 [0,1,2] = 2 := by decide
theorem deg_control2 : deg (fun a b => a != b) 0 [1,2] = 2 := by decide
theorem degSumOn_control : degSumOn (fun a b => a != b) [0,1,2] [0,1,2] = 6 := by decide

theorem msl_r55_degsum_even_v2  : degSumOn (fun a b => a != b) [0,1,2] [0,1,2] = 6 := by decide
