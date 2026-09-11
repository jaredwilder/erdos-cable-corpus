set_option autoImplicit false
set_option maxRecDepth 20000

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

theorem msl_r55_insert_clique  : ([1,2] : List Nat).length = 2 := by decide
