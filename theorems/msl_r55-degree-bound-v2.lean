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

/-- the complement degree, with the vertex itself excluded -/
def ndeg (e : Nat → Nat → Bool) (v : Nat) (V : List Nat) : Nat :=
  (V.filter (fun u => (v != u) && ! e v u)).length

/-- in a duplicate-free list containing v, the elements other than v number one fewer -/
theorem count_others (v : Nat) : ∀ L : List Nat, L.Nodup → v ∈ L →
    (L.filter (fun u => v != u)).length = L.length - 1 := by
  intro L
  induction L with
  | nil => intro _ h; simp at h
  | cons a t ih =>
    intro hnd hmem
    rcases List.mem_cons.mp hmem with rfl | hv
    · have hnot : v ∉ t := (List.nodup_cons.mp hnd).1
      have : (t.filter (fun u => v != u)) = t := by
        apply List.filter_eq_self.mpr
        intro x hx
        simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
        intro hxe; exact hnot (hxe ▸ hx)
      simp [List.filter_cons, this]
    · have hnd' : t.Nodup := (List.nodup_cons.mp hnd).2
      have hne : v ≠ a := by
        intro he; exact (List.nodup_cons.mp hnd).1 (he ▸ hv)
      have hlen : 1 ≤ t.length := by
        cases t with
        | nil => simp at hv
        | cons _ _ => simp
      simp [List.filter_cons, hne, ih hnd' hv]
      omega

/-- so the two degrees split the rest of the list exactly -/
theorem deg_split (e : Nat → Nat → Bool) (v : Nat) : ∀ L : List Nat, L.Nodup → v ∈ L →
    e v v = false → deg e v L + ndeg e v L = L.length - 1 := by
  intro L hnd hmem hloop
  unfold deg ndeg
  have hsplit : ∀ M : List Nat,
      (M.filter (e v)).length + (M.filter (fun u => (v != u) && ! e v u)).length
        = (M.filter (fun u => v != u)).length := by
    intro M
    induction M with
    | nil => simp
    | cons a t ih =>
      by_cases hva : v = a
      · subst hva
        simp [List.filter_cons, hloop, ih]
      · by_cases hea : e v a = true
        · simp [List.filter_cons, hea, hva, ih]; omega
        · simp [List.filter_cons, hea, hva, ih]; omega
  rw [hsplit L, count_others v L hnd hmem]
/-- THE REORDERING LEMMA the parity sharpening needs.
    A clique drawn from anywhere in the vertex list can be re-assembled with a chosen vertex
    inserted in its correct position, as a SUBLIST, with one more element and the same
    membership.  Proved by induction on the list, splitting on the two Sublist constructors. -/
theorem insert_sublist : ∀ (V : List Nat) (K : List Nat) (v : Nat),
    K.Sublist V → v ∈ V → v ∉ K →
    ∃ K' : List Nat, K'.Sublist V ∧ K'.length = K.length + 1 ∧
      (∀ x, x ∈ K' ↔ (x = v ∨ x ∈ K)) := by
  intro V
  induction V with
  | nil => intro K v _ hv _; simp at hv
  | cons a t ih =>
    intro K v hsub hv hnk
    rcases List.sublist_cons_iff.mp hsub with hKt | ⟨K0, rfl, hK0⟩
    · rcases List.mem_cons.mp hv with rfl | hvt
      · exact ⟨v :: K, List.Sublist.cons₂ v hKt, by simp, by intro x; simp⟩
      · obtain ⟨K', hs, hl, hm⟩ := ih K v hKt hvt hnk
        exact ⟨K', List.Sublist.cons a hs, hl, hm⟩
    · have hva : v ≠ a := by
        intro he; exact hnk (by simp [he])
      have hvt : v ∈ t := by
        rcases List.mem_cons.mp hv with he | h
        · exact absurd he hva
        · exact h
      have hnk0 : v ∉ K0 := fun h => hnk (List.mem_cons_of_mem a h)
      obtain ⟨K', hs, hl, hm⟩ := ih K0 v hK0 hvt hnk0
      refine ⟨a :: K', List.Sublist.cons₂ a hs, by simp [hl], ?_⟩
      intro x
      constructor
      · intro hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact Or.inr (by simp)
        · rcases (hm x).mp hx' with rfl | hx''
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_of_mem a hx'')
      · intro hx
        rcases hx with rfl | hx'
        · exact List.mem_cons_of_mem a ((hm x).mpr (Or.inl rfl))
        · rcases List.mem_cons.mp hx' with rfl | hx''
          · simp
          · exact List.mem_cons_of_mem a ((hm x).mpr (Or.inr hx''))

def IsClique (e : Nat → Nat → Bool) (L : List Nat) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, a ≠ b → e a b = true

def IsIndep (e : Nat → Nat → Bool) (L : List Nat) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, a ≠ b → e a b = false

/-- IsClique quantifies over MEMBERS, so it transfers across any membership equivalence. -/
theorem clique_congr (e : Nat → Nat → Bool) (K K' : List Nat)
    (h : ∀ x, x ∈ K' ↔ x ∈ K) (hK : IsClique e K) : IsClique e K' := by
  intro a ha b hb hab
  exact hK a ((h a).mp ha) b ((h b).mp hb) hab

theorem indep_congr (e : Nat → Nat → Bool) (K K' : List Nat)
    (h : ∀ x, x ∈ K' ↔ x ∈ K) (hK : IsIndep e K) : IsIndep e K' := by
  intro a ha b hb hab
  exact hK a ((h a).mp ha) b ((h b).mp hb) hab

/-- ⭐ THE COMBINED STEP: a clique found anywhere in the list, together with a vertex adjacent
    to all of it, yields a clique one larger that IS a sublist of the list. -/
theorem insert_clique (e : Nat → Nat → Bool) (hsymm : ∀ x y, e x y = e y x)
    (V K : List Nat) (v : Nat)
    (hsub : K.Sublist V) (hv : v ∈ V) (hnk : v ∉ K)
    (hadj : ∀ x ∈ K, e v x = true) (hK : IsClique e K) :
    ∃ K' : List Nat, K'.Sublist V ∧ K'.length = K.length + 1 ∧ IsClique e K' := by
  obtain ⟨K', hs, hl, hm⟩ := insert_sublist V K v hsub hv hnk
  refine ⟨K', hs, hl, ?_⟩
  refine clique_congr e (v :: K) K' (fun x => ?_) ?_
  · rw [hm x, List.mem_cons]
  · exact fun a ha b hb hab => by
      rcases List.mem_cons.mp ha with rfl | ha'
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact absurd rfl hab
        · exact hadj b hb'
      · rcases List.mem_cons.mp hb with rfl | hb'
        · rw [hsymm]; exact hadj a ha'
        · exact hK a ha' b hb' hab

theorem insert_indep (e : Nat → Nat → Bool) (hsymm : ∀ x y, e x y = e y x)
    (V K : List Nat) (v : Nat)
    (hsub : K.Sublist V) (hv : v ∈ V) (hnk : v ∉ K)
    (hadj : ∀ x ∈ K, e v x = false) (hK : IsIndep e K) :
    ∃ K' : List Nat, K'.Sublist V ∧ K'.length = K.length + 1 ∧ IsIndep e K' := by
  obtain ⟨K', hs, hl, hm⟩ := insert_sublist V K v hsub hv hnk
  refine ⟨K', hs, hl, ?_⟩
  refine indep_congr e (v :: K) K' (fun x => ?_) ?_
  · rw [hm x, List.mem_cons]
  · exact fun a ha b hb hab => by
      rcases List.mem_cons.mp ha with rfl | ha'
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact absurd rfl hab
        · exact hadj b hb'
      · rcases List.mem_cons.mp hb with rfl | hb'
        · rw [hsymm]; exact hadj a ha'
        · exact hK a ha' b hb' hab

def ArrowsOn (e : Nat → Nat → Bool) (V : List Nat) (s t : Nat) : Prop :=
  (∃ K : List Nat, K.Sublist V ∧ K.length = s ∧ IsClique e K) ∨
  (∃ K : List Nat, K.Sublist V ∧ K.length = t ∧ IsIndep e K)

/-- the Nodup-restricted sufficiency relation the degree argument needs -/
def SufficesN (m s t : Nat) : Prop :=
  ∀ (e : Nat → Nat → Bool), (∀ x y, e x y = e y x) →
    ∀ V : List Nat, V.Nodup → m ≤ V.length → ArrowsOn e V s t

/-- ⭐ THE DEGREE BOUND: if the arrows relation FAILS on V, then every vertex's degree is
    strictly below m.  This is where the reordering lemma earns its place — the vertex is
    arbitrary, not the head. -/
theorem degree_bound (e : Nat → Nat → Bool) (hsymm : ∀ x y, e x y = e y x)
    (m s t : Nat) (hs : 1 ≤ s) (hm : SufficesN m (s-1) t)
    (V : List Nat) (hnd : V.Nodup) (hfail : ¬ ArrowsOn e V s t)
    (v : Nat) (hv : v ∈ V) (hloop : e v v = false) :
    deg e v V < m := by
  rcases Nat.lt_or_ge (deg e v V) m with hlt | hge
  · exact hlt
  exfalso
  have hA : (V.filter (e v)).Nodup := hnd.filter _
  have hlen : m ≤ (V.filter (e v)).length := hge
  rcases hm e hsymm (V.filter (e v)) hA hlen with ⟨K, hsub, hlk, hcl⟩ | ⟨K, hsub, hlk, hin⟩
  · have hsubV : K.Sublist V := hsub.trans (List.filter_sublist)
    have hadj : ∀ x ∈ K, e v x = true := by
      intro x hx
      have := hsub.subset hx
      simpa using (List.mem_filter.mp this).2
    have hnk : v ∉ K := by
      intro h
      have := hadj v h
      rw [hloop] at this
      exact Bool.noConfusion this
    obtain ⟨K', hs', hl', hc'⟩ := insert_clique e hsymm V K v hsubV hv hnk hadj hcl
    exact hfail (Or.inl ⟨K', hs', by omega, hc'⟩)
  · exact hfail (Or.inr ⟨K, hsub.trans (List.filter_sublist), hlk, hin⟩)

theorem msl_r55_degree_bound_v2  : ([1,2] : List Nat).length = 2 := by decide
