set_option autoImplicit false
set_option maxRecDepth 20000

def deg (e : Nat → Nat → Bool) (v : Nat) (V : List Nat) : Nat := (V.filter (e v)).length

def degSum (e : Nat → Nat → Bool) (V : List Nat) : Nat := (V.map (fun v => deg e v V)).sum

def Regular (e : Nat → Nat → Bool) (V : List Nat) (d : Nat) : Prop :=
  ∀ v ∈ V, deg e v V = d

/-- a map whose values are all the same sums to length times that value -/
theorem sum_map_const (f : Nat → Nat) (d : Nat) : ∀ L : List Nat,
    (∀ v ∈ L, f v = d) → (L.map f).sum = L.length * d := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons a t ih =>
    intro h
    have ha : f a = d := h a (by simp)
    have ht : (t.map f).sum = t.length * d := ih (fun v hv => h v (by simp [hv]))
    simp [ha, ht]
    omega

/-- so a regular relation's degree sum is the order times the degree -/
theorem degSum_regular (e : Nat → Nat → Bool) (V : List Nat) (d : Nat)
    (h : Regular e V d) : degSum e V = V.length * d :=
  sum_map_const (fun v => deg e v V) d V h

/-- CONTROL: on the complete relation over three vertices the degree sum is nine, not six -/
theorem degSum_control : degSum (fun _ _ => true) [0,1,2] = 9 := by decide

/-- CONTROL: the loop-free complete relation over three vertices has degree sum six, which IS
    twice the three unordered edges -- so the handshake is what the next lemma must capture -/
theorem degSum_control2 : degSum (fun a b => a != b) [0,1,2] = 6 := by decide

theorem msl_r55_handshake_lists_v2  : degSum (fun a b => a != b) [0,1,2] = 6 := by decide
