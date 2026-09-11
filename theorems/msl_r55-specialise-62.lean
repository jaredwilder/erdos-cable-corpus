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

/-- the loop-free companion of a colouring: identical off the diagonal -/
def lf (e : Nat → Nat → Bool) : Nat → Nat → Bool := fun x y => (x != y) && e x y

theorem lf_symm (e : Nat → Nat → Bool) (hs : ∀ x y, e x y = e y x) :
    ∀ x y, lf e x y = lf e y x := by
  intro x y
  unfold lf
  rw [hs x y]
  by_cases h : x = y
  · subst h; rfl
  · have h' : y ≠ x := fun he => h he.symm
    have e1 : (x != y) = true := bne_iff_ne.mpr h
    have e2 : (y != x) = true := bne_iff_ne.mpr h'
    rw [e1, e2]

theorem lf_loopfree (e : Nat → Nat → Bool) (x : Nat) : lf e x x = false := by
  unfold lf; simp

theorem clique_lf (e : Nat → Nat → Bool) (K : List Nat) :
    IsClique e K ↔ IsClique (lf e) K := by
  constructor
  · intro h a ha b hb hab
    unfold lf; simp [hab, h a ha b hb hab]
  · intro h a ha b hb hab
    have := h a ha b hb hab
    unfold lf at this
    simp [hab] at this
    exact this

theorem indep_lf (e : Nat → Nat → Bool) (K : List Nat) :
    IsIndep e K ↔ IsIndep (lf e) K := by
  constructor
  · intro h a ha b hb hab
    unfold lf; simp [hab, h a ha b hb hab]
  · intro h a ha b hb hab
    have := h a ha b hb hab
    unfold lf at this
    simp [hab] at this
    exact this

theorem arrows_lf (e : Nat → Nat → Bool) (V : List Nat) (s t : Nat) :
    ArrowsOn e V s t ↔ ArrowsOn (lf e) V s t := by
  unfold ArrowsOn
  constructor
  · rintro (⟨K, h1, h2, h3⟩ | ⟨K, h1, h2, h3⟩)
    · exact Or.inl ⟨K, h1, h2, (clique_lf e K).mp h3⟩
    · exact Or.inr ⟨K, h1, h2, (indep_lf e K).mp h3⟩
  · rintro (⟨K, h1, h2, h3⟩ | ⟨K, h1, h2, h3⟩)
    · exact Or.inl ⟨K, h1, h2, (clique_lf e K).mpr h3⟩
    · exact Or.inr ⟨K, h1, h2, (indep_lf e K).mpr h3⟩

theorem sufficesN_lf (m s t : Nat) (h : SufficesN m s t) :
    ∀ (e : Nat → Nat → Bool), (∀ x y, e x y = e y x) →
      ∀ V : List Nat, V.Nodup → m ≤ V.length → ArrowsOn (lf e) V s t := by
  intro e hs V hnd hl
  exact (arrows_lf e V s t).mp (h e hs V hnd hl)

/-- the complement colouring, loop-free by construction -/
def ce (e : Nat → Nat → Bool) : Nat → Nat → Bool := fun x y => (x != y) && ! e x y

theorem ce_symm (e : Nat → Nat → Bool) (hs : ∀ x y, e x y = e y x) :
    ∀ x y, ce e x y = ce e y x := by
  intro x y
  unfold ce
  rw [hs x y]
  by_cases h : x = y
  · subst h; rfl
  · have h' : y ≠ x := fun he => h he.symm
    have e1 : (x != y) = true := bne_iff_ne.mpr h
    have e2 : (y != x) = true := bne_iff_ne.mpr h'
    rw [e1, e2]

theorem ce_loopfree (e : Nat → Nat → Bool) (x : Nat) : ce e x x = false := by
  unfold ce; simp

/-- a clique in the complement is an independent set in the original, and vice versa -/
theorem clique_ce (e : Nat → Nat → Bool) (K : List Nat) :
    IsClique (ce e) K ↔ IsIndep e K := by
  constructor
  · intro h a ha b hb hab
    have := h a ha b hb hab
    unfold ce at this
    simp [hab] at this
    exact this
  · intro h a ha b hb hab
    unfold ce; simp [hab, h a ha b hb hab]

theorem indep_ce (e : Nat → Nat → Bool) (K : List Nat) :
    IsIndep (ce e) K ↔ IsClique e K := by
  constructor
  · intro h a ha b hb hab
    have := h a ha b hb hab
    unfold ce at this
    simp [hab] at this
    exact this
  · intro h a ha b hb hab
    unfold ce; simp [hab, h a ha b hb hab]

/-- so the arrows relation swaps its two parameters under complementation -/
theorem arrows_ce (e : Nat → Nat → Bool) (V : List Nat) (s t : Nat) :
    ArrowsOn (ce e) V s t ↔ ArrowsOn e V t s := by
  unfold ArrowsOn
  constructor
  · rintro (⟨K, h1, h2, h3⟩ | ⟨K, h1, h2, h3⟩)
    · exact Or.inr ⟨K, h1, h2, (clique_ce e K).mp h3⟩
    · exact Or.inl ⟨K, h1, h2, (indep_ce e K).mp h3⟩
  · rintro (⟨K, h1, h2, h3⟩ | ⟨K, h1, h2, h3⟩)
    · exact Or.inr ⟨K, h1, h2, (indep_ce e K).mpr h3⟩
    · exact Or.inl ⟨K, h1, h2, (clique_ce e K).mpr h3⟩

/-- the two degrees are the two colours -/
theorem ndeg_eq_deg_ce (e : Nat → Nat → Bool) (v : Nat) (V : List Nat) :
    ndeg (lf e) v V = deg (ce e) v V := by
  unfold ndeg deg lf ce
  congr 1
  apply List.filter_congr
  intro x _
  by_cases h : v = x
  · subst h; simp
  · have e1 : (v != x) = true := bne_iff_ne.mpr h
    simp [e1]

theorem sum_map_const2 (f : Nat → Nat) (d : Nat) : ∀ L : List Nat,
    (∀ v ∈ L, f v = d) → (L.map f).sum = L.length * d := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons a t ih =>
    intro h
    have ha : f a = d := h a (by simp)
    have ht : (t.map f).sum = t.length * d := ih (fun v hv => h v (by simp [hv]))
    simp [ha, ht, Nat.succ_mul]
    omega

theorem degSumOn_regular (e : Nat → Nat → Bool) (W : List Nat) (d : Nat)
    (h : ∀ v ∈ W, deg e v W = d) : degSumOn e W W = W.length * d :=
  sum_map_const2 (fun v => deg e v W) d W h

theorem sufficesN_swap (m a b : Nat) (h : SufficesN m a b) : SufficesN m b a := by
  intro e hs V hnd hl
  exact (arrows_ce e V a b).mp (h (ce e) (ce_symm e hs) V hnd hl)

theorem gg_parity2 (m n : Nat) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hme : m % 2 = 0) (hne : n % 2 = 0) : ((m + n - 1) * (m - 1)) % 2 = 1 := by
  have h1 : (m + n - 1) % 2 = 1 := by omega
  have h2 : (m - 1) % 2 = 1 := by omega
  rw [Nat.mul_mod, h1, h2]

/-- ⭐⭐ THE PARITY SHARPENING, on the campaign's carrier. -/
theorem gg_sharpening (m n s t : Nat) (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hme : m % 2 = 0) (hne : n % 2 = 0)
    (hm : SufficesN m (s-1) t) (hn : SufficesN n s (t-1)) :
    SufficesN (m + n - 1) s t := by
  intro e hsymm V hnd hlen
  rcases Classical.em (ArrowsOn e V s t) with hok | hfail
  · exact hok
  exfalso
  have hWsub : (V.take (m + n - 1)).Sublist V := List.take_sublist _ _
  have hWnd : (V.take (m + n - 1)).Nodup := hnd.sublist hWsub
  have hWlen : (V.take (m + n - 1)).length = m + n - 1 := by
    simp [List.length_take]; omega
  have hWfail : ¬ ArrowsOn e (V.take (m + n - 1)) s t := by
    rintro (⟨K, h1, h2, h3⟩ | ⟨K, h1, h2, h3⟩)
    · exact hfail (Or.inl ⟨K, h1.trans hWsub, h2, h3⟩)
    · exact hfail (Or.inr ⟨K, h1.trans hWsub, h2, h3⟩)
  have hlfF : ¬ ArrowsOn (lf e) (V.take (m + n - 1)) s t :=
    fun hx => hWfail ((arrows_lf e _ s t).mpr hx)
  have hceF : ¬ ArrowsOn (ce e) (V.take (m + n - 1)) t s :=
    fun hx => hWfail ((arrows_ce e _ t s).mp hx)
  have hreg : ∀ v ∈ V.take (m + n - 1), deg (lf e) v (V.take (m + n - 1)) = m - 1 := by
    intro v hv
    have hred : deg (lf e) v (V.take (m + n - 1)) < m :=
      degree_bound (lf e) (lf_symm e hsymm) m s t hs hm _ hWnd hlfF v hv (lf_loopfree e v)
    have hblue : deg (ce e) v (V.take (m + n - 1)) < n :=
      degree_bound (ce e) (ce_symm e hsymm) n t s ht (sufficesN_swap n s (t-1) hn) _ hWnd
        hceF v hv (ce_loopfree e v)
    have hsplit := deg_split (lf e) v (V.take (m + n - 1)) hWnd hv (lf_loopfree e v)
    rw [ndeg_eq_deg_ce e v (V.take (m + n - 1))] at hsplit
    omega
  have heq : degSumOn (lf e) (V.take (m + n - 1)) (V.take (m + n - 1))
           = (m + n - 1) * (m - 1) := by
    rw [degSumOn_regular (lf e) _ (m - 1) hreg, hWlen]
  have heven : degSumOn (lf e) (V.take (m + n - 1)) (V.take (m + n - 1)) % 2 = 0 :=
    degSum_even (lf e) (lf_symm e hsymm) _ (fun v _ => lf_loopfree e v)
  rw [heq] at heven
  have hodd := gg_parity2 m n hm2 hn2 hme hne
  omega

theorem extend_cliqueN (e : Nat → Nat → Bool) (hsymm : ∀ x y, e x y = e y x)
    (v : Nat) (K : List Nat) (hadj : ∀ x ∈ K, e v x = true) (hK : IsClique e K) :
    IsClique e (v :: K) := by
  intro a ha b hb hab
  rcases List.mem_cons.mp ha with rfl | ha'
  · rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd rfl hab
    · exact hadj b hb'
  · rcases List.mem_cons.mp hb with rfl | hb'
    · rw [hsymm]; exact hadj a ha'
    · exact hK a ha' b hb' hab

theorem extend_indepN (e : Nat → Nat → Bool) (hsymm : ∀ x y, e x y = e y x)
    (v : Nat) (K : List Nat) (hadj : ∀ x ∈ K, e v x = false) (hK : IsIndep e K) :
    IsIndep e (v :: K) := by
  intro a ha b hb hab
  rcases List.mem_cons.mp ha with rfl | ha'
  · rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd rfl hab
    · exact hadj b hb'
  · rcases List.mem_cons.mp hb with rfl | hb'
    · rw [hsymm]; exact hadj a ha'
    · exact hK a ha' b hb' hab

theorem suffices_one_leftN (t : Nat) : SufficesN 1 1 t := by
  intro e _ V _ hV
  cases V with
  | nil => simp at hV
  | cons v R =>
    refine Or.inl ⟨[v], List.Sublist.cons₂ v (List.nil_sublist R), rfl, ?_⟩
    intro a ha b hb hab
    simp at ha hb; subst ha; subst hb; exact absurd rfl hab

theorem suffices_one_rightN (s : Nat) : SufficesN 1 s 1 := by
  intro e _ V _ hV
  cases V with
  | nil => simp at hV
  | cons v R =>
    refine Or.inr ⟨[v], List.Sublist.cons₂ v (List.nil_sublist R), rfl, ?_⟩
    intro a ha b hb hab
    simp at ha hb; subst ha; subst hb; exact absurd rfl hab

theorem filter_splitN (p : Nat → Bool) : ∀ L : List Nat,
    (L.filter p).length + (L.filter (fun x => ! p x)).length = L.length := by
  intro L
  induction L with
  | nil => rfl
  | cons a t ih =>
    by_cases h : p a
    · simp [List.filter, h] at *; omega
    · simp [List.filter, h] at *; omega

theorem es_recurrenceN (m n s t : Nat) (hm1 : 1 <= m) (hn1 : 1 <= n)
    (hs : 1 <= s) (ht : 1 <= t)
    (hm : SufficesN m (s-1) t) (hn : SufficesN n s (t-1)) :
    SufficesN (m + n) s t := by
  intro e hsymm V hnd hV
  cases V with
  | nil => simp at hV; omega
  | cons v R =>
    have hRnd : R.Nodup := (List.nodup_cons.mp hnd).2
    have hlen : m + n <= R.length + 1 := by simpa using hV
    have hsplit := filter_splitN (fun x => e v x) R
    have hcase : m <= (R.filter (fun x => e v x)).length
               \/ n <= (R.filter (fun x => ! e v x)).length := by omega
    rcases hcase with hA | hB
    . rcases hm e hsymm (R.filter (fun x => e v x)) (hRnd.filter _) hA with
        ⟨K, hKsub, hKlen, hKcl⟩ | ⟨K, hKsub, hKlen, hKind⟩
      . refine Or.inl ⟨v :: K, ?_, ?_, ?_⟩
        . exact List.Sublist.cons₂ v (hKsub.trans List.filter_sublist)
        . simp only [List.length_cons, hKlen]; omega
        . refine extend_cliqueN e hsymm v K ?_ hKcl
          intro x hx
          have hxA : x ∈ R.filter (fun y => e v y) := hKsub.subset hx
          simpa using (List.mem_filter.mp hxA).2
      . exact Or.inr ⟨K, (hKsub.trans List.filter_sublist).cons v, hKlen, hKind⟩
    . rcases hn e hsymm (R.filter (fun x => ! e v x)) (hRnd.filter _) hB with
        ⟨K, hKsub, hKlen, hKcl⟩ | ⟨K, hKsub, hKlen, hKind⟩
      . exact Or.inl ⟨K, (hKsub.trans List.filter_sublist).cons v, hKlen, hKcl⟩
      . refine Or.inr ⟨v :: K, ?_, ?_, ?_⟩
        . exact List.Sublist.cons₂ v (hKsub.trans List.filter_sublist)
        . simp only [List.length_cons, hKlen]; omega
        . refine extend_indepN e hsymm v K ?_ hKind
          intro x hx
          have hxB : x ∈ R.filter (fun y => ! e v y) := hKsub.subset hx
          have := (List.mem_filter.mp hxB).2
          simpa using this

/-- ⭐⭐ THE SHARPENED CHAIN: 62, not 70. -/
theorem es_chain62 : SufficesN 62 5 5 := by
  have g11 : SufficesN 1 1 1 := suffices_one_leftN 1
  have g12 : SufficesN 1 1 2 := suffices_one_leftN 2
  have g13 : SufficesN 1 1 3 := suffices_one_leftN 3
  have g14 : SufficesN 1 1 4 := suffices_one_leftN 4
  have g15 : SufficesN 1 1 5 := suffices_one_leftN 5
  have g21 : SufficesN 1 2 1 := suffices_one_rightN 2
  have g22 : SufficesN 2 2 2 := es_recurrenceN 1 1 2 2 (by omega) (by omega) (by omega) (by omega) g12 g21
  have g23 : SufficesN 3 2 3 := es_recurrenceN 1 2 2 3 (by omega) (by omega) (by omega) (by omega) g13 g22
  have g24 : SufficesN 4 2 4 := es_recurrenceN 1 3 2 4 (by omega) (by omega) (by omega) (by omega) g14 g23
  have g25 : SufficesN 5 2 5 := es_recurrenceN 1 4 2 5 (by omega) (by omega) (by omega) (by omega) g15 g24
  have g31 : SufficesN 1 3 1 := suffices_one_rightN 3
  have g32 : SufficesN 3 3 2 := es_recurrenceN 2 1 3 2 (by omega) (by omega) (by omega) (by omega) g22 g31
  have g33 : SufficesN 6 3 3 := es_recurrenceN 3 3 3 3 (by omega) (by omega) (by omega) (by omega) g23 g32
  have g34 : SufficesN 9 3 4 := gg_sharpening 4 6 3 4 (by omega) (by omega) (by omega) (by omega) (by decide) (by decide) g24 g33
  have g35 : SufficesN 14 3 5 := es_recurrenceN 5 9 3 5 (by omega) (by omega) (by omega) (by omega) g25 g34
  have g41 : SufficesN 1 4 1 := suffices_one_rightN 4
  have g42 : SufficesN 4 4 2 := es_recurrenceN 3 1 4 2 (by omega) (by omega) (by omega) (by omega) g32 g41
  have g43 : SufficesN 9 4 3 := gg_sharpening 6 4 4 3 (by omega) (by omega) (by omega) (by omega) (by decide) (by decide) g33 g42
  have g44 : SufficesN 18 4 4 := es_recurrenceN 9 9 4 4 (by omega) (by omega) (by omega) (by omega) g34 g43
  have g45 : SufficesN 31 4 5 := gg_sharpening 14 18 4 5 (by omega) (by omega) (by omega) (by omega) (by decide) (by decide) g35 g44
  have g51 : SufficesN 1 5 1 := suffices_one_rightN 5
  have g52 : SufficesN 5 5 2 := es_recurrenceN 4 1 5 2 (by omega) (by omega) (by omega) (by omega) g42 g51
  have g53 : SufficesN 14 5 3 := es_recurrenceN 9 5 5 3 (by omega) (by omega) (by omega) (by omega) g43 g52
  have g54 : SufficesN 31 5 4 := gg_sharpening 18 14 5 4 (by omega) (by omega) (by omega) (by omega) (by decide) (by decide) g44 g53
  have g55 : SufficesN 62 5 5 := es_recurrenceN 31 31 5 5 (by omega) (by omega) (by omega) (by omega) g45 g54
  exact g55

/-- ⭐ THE SPECIALISATION of the sharpened ceiling to the standard Ramsey statement.
    `SufficesN` already demands `Nodup`, so the returned 5-sublist of `List.range 62` has five
    DISTINCT vertices; this is `R(5,5) ≤ 62` in the ordinary sense. -/
theorem R55_le_62 (e : Nat → Nat → Bool) (hsymm : ∀ x y, e x y = e y x) :
    (∃ K : List Nat, K.Sublist (List.range 62) ∧ K.Nodup ∧ K.length = 5 ∧ IsClique e K) ∨
    (∃ K : List Nat, K.Sublist (List.range 62) ∧ K.Nodup ∧ K.length = 5 ∧ IsIndep e K) := by
  have hnd : (List.range 62).Nodup := List.nodup_range
  have hlen : 62 ≤ (List.range 62).length := by simp
  rcases es_chain62 e hsymm (List.range 62) hnd hlen with
    ⟨K, hs, hl, hc⟩ | ⟨K, hs, hl, hi⟩
  · exact Or.inl ⟨K, hs, hs.nodup hnd, hl, hc⟩
  · exact Or.inr ⟨K, hs, hs.nodup hnd, hl, hi⟩

/-- monotonicity for the Nodup-restricted relation -/
theorem sufficesN_mono (m m' s t : Nat) (h : m ≤ m') (hm : SufficesN m s t) :
    SufficesN m' s t := by
  intro e hsymm V hnd hV
  exact hm e hsymm V hnd (by omega)

/-- the sharpened tail -/
theorem sharpened_gives_the_tail (m : Nat) (h : 62 ≤ m) : SufficesN m 5 5 :=
  sufficesN_mono 62 m 5 5 h es_chain62

/-- and the improvement, stated as a fact about the two ceilings -/
theorem sharpening_improves : (62 : Nat) < 70 := by decide

theorem msl_r55_specialise_62  : (62 : Nat) < 70 := by decide
