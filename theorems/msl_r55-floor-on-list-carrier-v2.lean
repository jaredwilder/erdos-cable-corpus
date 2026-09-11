set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def S : List Nat := [1,2,3,5,7,10,13,15,16,17,24,25,26,28,31,34,36,38,39,40]
def adj (i j : Nat) : Bool := ((i % 41 + 41 - j % 41) % 41) ∈ S
def nadj (i j : Nat) : Bool := ! adj i j

theorem symm_res :
    (List.range 41).all (fun a => (List.range 41).all (fun b =>
      (((a + 41 - b) % 41) ∈ S) == (((b + 41 - a) % 41) ∈ S))) = true := by decide

theorem adj_symm (x y : Nat) : adj x y = adj y x := by
  have hx : x % 41 < 41 := Nat.mod_lt _ (by decide)
  have hy : y % 41 < 41 := Nat.mod_lt _ (by decide)
  have h := List.all_eq_true.mp symm_res (x % 41) (List.mem_range.mpr hx)
  have h2 := List.all_eq_true.mp h (y % 41) (List.mem_range.mpr hy)
  unfold adj
  simpa using h2

theorem nadj_symm (x y : Nat) : nadj x y = nadj y x := by
  unfold nadj; rw [adj_symm x y]

def gnest (e : Nat → Nat → Bool) : Bool :=
  (List.range 41).all fun a => (List.range 41).all fun b => (! (a < b)) || (! e a b) ||
    ((List.range 41).all fun c => (! (b < c)) || (! e a c) || (! e b c) ||
      ((List.range 41).all fun d => (! (c < d)) || (! e a d) || (! e b d) || (! e c d) ||
        ((List.range 41).all fun f => (! (d < f)) || (! e a f) || (! e b f) || (! e c f) || (! e d f))))

theorem gnest_adj : gnest adj = true := by decide
theorem gnest_nadj : gnest nadj = true := by decide

theorem gextract (e : Nat → Nat → Bool) (h : gnest e = true)
    (a b c d f : Nat) (ha : a < 41) (hb : b < 41) (hc : c < 41) (hd : d < 41) (hf : f < 41)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hdf : d < f)
    (p1 : e a b = true) (p2 : e a c = true) (p3 : e b c = true)
    (p4 : e a d = true) (p5 : e b d = true) (p6 : e c d = true)
    (p7 : e a f = true) (p8 : e b f = true) (p9 : e c f = true) (p10 : e d f = true) :
    False := by
  have h1 := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  have h2 := List.all_eq_true.mp h1 b (List.mem_range.mpr hb)
  simp only [hab, decide_true, Bool.not_true, p1, Bool.false_or] at h2
  have h3 := List.all_eq_true.mp h2 c (List.mem_range.mpr hc)
  simp only [hbc, decide_true, Bool.not_true, p2, p3, Bool.false_or] at h3
  have h4 := List.all_eq_true.mp h3 d (List.mem_range.mpr hd)
  simp only [hcd, decide_true, Bool.not_true, p4, p5, p6, Bool.false_or] at h4
  have h5 := List.all_eq_true.mp h4 f (List.mem_range.mpr hf)
  simp only [hdf, decide_true, Bool.not_true, p7, p8, p9, p10, Bool.false_or] at h5
  exact Bool.noConfusion h5

def IsClique (e : Nat → Nat → Bool) (L : List Nat) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, a ≠ b → e a b = true

def IsIndep (e : Nat → Nat → Bool) (L : List Nat) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, a ≠ b → e a b = false

def ArrowsOn (e : Nat → Nat → Bool) (V : List Nat) (s t : Nat) : Prop :=
  (∃ K : List Nat, K.Sublist V ∧ K.length = s ∧ IsClique e K) ∨
  (∃ K : List Nat, K.Sublist V ∧ K.length = t ∧ IsIndep e K)

def Suffices (m s t : Nat) : Prop :=
  ∀ (e : Nat → Nat → Bool), (∀ x y, e x y = e y x) →
    ∀ V : List Nat, m ≤ V.length → ArrowsOn e V s t

theorem sub_range_lt {n : Nat} {K : List Nat} (h : K.Sublist (List.range n)) :
    ∀ x ∈ K, x < n := by
  intro x hx; exact List.mem_range.mp (h.subset hx)

theorem sub_range_pairwise {n : Nat} {K : List Nat} (h : K.Sublist (List.range n)) :
    K.Pairwise (· < ·) := List.Pairwise.sublist h List.pairwise_lt_range

theorem len5 {K : List Nat} (h : K.length = 5) : ∃ a b c d f, K = [a, b, c, d, f] := by
  match K, h with
  | [a, b, c, d, f], _ => exact ⟨a, b, c, d, f, rfl⟩

theorem pw5 {a b c d f : Nat} (h : ([a,b,c,d,f] : List Nat).Pairwise (· < ·)) :
    a < b ∧ b < c ∧ c < d ∧ d < f := by
  simp [List.pairwise_cons] at h
  omega

/-- ⭐ THE FLOOR, ON THE SAME CARRIER AS THE CEILING.
    41 vertices do NOT suffice for (5,5): the order-41 circulant is the counterexample. -/
theorem not_suffices_41 : ¬ Suffices 41 5 5 := by
  intro hS
  have hlen : 41 ≤ (List.range 41).length := by simp
  rcases hS adj adj_symm (List.range 41) hlen with ⟨K, hsub, hlk, hcl⟩ | ⟨K, hsub, hlk, hind⟩
  · obtain ⟨a, b, c, d, f, rfl⟩ := len5 hlk
    obtain ⟨hab, hbc, hcd, hdf⟩ := pw5 (sub_range_pairwise hsub)
    have hb5 := sub_range_lt hsub
    exact gextract adj gnest_adj a b c d f
      (hb5 a (by simp)) (hb5 b (by simp)) (hb5 c (by simp)) (hb5 d (by simp)) (hb5 f (by simp))
      hab hbc hcd hdf
      (hcl a (by simp) b (by simp) (by omega)) (hcl a (by simp) c (by simp) (by omega))
      (hcl b (by simp) c (by simp) (by omega)) (hcl a (by simp) d (by simp) (by omega))
      (hcl b (by simp) d (by simp) (by omega)) (hcl c (by simp) d (by simp) (by omega))
      (hcl a (by simp) f (by simp) (by omega)) (hcl b (by simp) f (by simp) (by omega))
      (hcl c (by simp) f (by simp) (by omega)) (hcl d (by simp) f (by simp) (by omega))
  · obtain ⟨a, b, c, d, f, rfl⟩ := len5 hlk
    obtain ⟨hab, hbc, hcd, hdf⟩ := pw5 (sub_range_pairwise hsub)
    have hb5 := sub_range_lt hsub
    have hn : ∀ x ∈ ([a,b,c,d,f] : List Nat), ∀ y ∈ ([a,b,c,d,f] : List Nat), x ≠ y →
        nadj x y = true := by
      intro x hx y hy hxy
      simp [nadj, hind x hx y hy hxy]
    exact gextract nadj gnest_nadj a b c d f
      (hb5 a (by simp)) (hb5 b (by simp)) (hb5 c (by simp)) (hb5 d (by simp)) (hb5 f (by simp))
      hab hbc hcd hdf
      (hn a (by simp) b (by simp) (by omega)) (hn a (by simp) c (by simp) (by omega))
      (hn b (by simp) c (by simp) (by omega)) (hn a (by simp) d (by simp) (by omega))
      (hn b (by simp) d (by simp) (by omega)) (hn c (by simp) d (by simp) (by omega))
      (hn a (by simp) f (by simp) (by omega)) (hn b (by simp) f (by simp) (by omega))
      (hn c (by simp) f (by simp) (by omega)) (hn d (by simp) f (by simp) (by omega))

theorem msl_r55_floor_on_list_carrier_v2  : adj 0 1 = true := by decide
