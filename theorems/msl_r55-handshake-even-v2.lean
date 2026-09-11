set_option autoImplicit false
set_option maxRecDepth 20000

def deg (e : Nat → Nat → Bool) (v : Nat) (V : List Nat) : Nat := (V.filter (e v)).length

def degSumOn (e : Nat → Nat → Bool) (L W : List Nat) : Nat :=
  (L.map (fun v => deg e v W)).sum

theorem deg_cons_self (e : Nat → Nat → Bool) (a : Nat) (t : List Nat) (h : e a a = false) :
    deg e a (a :: t) = deg e a t := by
  unfold deg; simp [List.filter_cons, h]

theorem deg_cons_other (e : Nat → Nat → Bool) (a v : Nat) (t : List Nat) :
    deg e v (a :: t) = (if e v a = true then 1 else 0) + deg e v t := by
  unfold deg
  by_cases h : e v a = true
  · simp [List.filter_cons, h]; omega
  · simp [List.filter_cons, h]

/-- summing a pointwise sum splits -/
theorem sum_map_add (f g : Nat → Nat) : ∀ L : List Nat,
    (L.map (fun v => f v + g v)).sum = (L.map f).sum + (L.map g).sum := by
  intro L; induction L with
  | nil => simp
  | cons a t ih => simp [ih]; omega

/-- an indicator sum counts the filter -/
theorem sum_indicator (p : Nat → Bool) : ∀ L : List Nat,
    (L.map (fun v => if p v = true then 1 else 0)).sum = (L.filter p).length := by
  intro L; induction L with
  | nil => simp
  | cons a t ih =>
    by_cases h : p a = true
    · simp [List.filter_cons, h, ih]; omega
    · simp [List.filter_cons, h, ih]

/-- symmetry lets the incoming count be read as the outgoing degree -/
theorem filter_symm (e : Nat → Nat → Bool) (hs : ∀ x y, e x y = e y x) (a : Nat) :
    ∀ L : List Nat, (L.filter (fun v => e v a)).length = deg e a L := by
  intro L
  unfold deg
  have : (fun v => e v a) = (e a) := by funext v; exact hs v a
  rw [this]

/-- ⭐ THE HANDSHAKE, over vertex lists: for a symmetric relation that is loop-free on the
    list, the degree sum is TWICE the degree sum of the tail plus twice a vertex degree —
    hence even, by induction. -/
theorem degSum_even (e : Nat → Nat → Bool) (hs : ∀ x y, e x y = e y x) :
    ∀ L : List Nat, (∀ v ∈ L, e v v = false) → degSumOn e L L % 2 = 0 := by
  intro L
  induction L with
  | nil => intro _; simp [degSumOn]
  | cons a t ih =>
    intro hloop
    have hself : e a a = false := hloop a (by simp)
    have htail : ∀ v ∈ t, e v v = false := fun v hv => hloop v (by simp [hv])
    have hih := ih htail
    have hstep : degSumOn e (a :: t) (a :: t) = 2 * deg e a t + degSumOn e t t := by
      unfold degSumOn
      simp only [List.map_cons, List.sum_cons]
      rw [deg_cons_self e a t hself]
      have hmap : (t.map (fun v => deg e v (a :: t)))
                = (t.map (fun v => (if e v a = true then 1 else 0) + deg e v t)) := by
        apply List.map_congr_left
        intro v _
        exact deg_cons_other e a v t
      rw [hmap, sum_map_add (fun v => if e v a = true then 1 else 0) (fun v => deg e v t) t,
          sum_indicator (fun v => e v a) t, filter_symm e hs a t]
      omega
    rw [hstep]
    omega

theorem degSum_even_control : degSumOn (fun a b => a != b) [0,1,2] [0,1,2] = 6 := by decide

theorem msl_r55_handshake_even_v2  : degSumOn (fun a b => a != b) [0,1,2] [0,1,2] = 6 := by decide
