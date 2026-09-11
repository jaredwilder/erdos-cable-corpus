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

theorem msl_r55_reorder_insert  : ([1,2] : List Nat).length = 2 := by decide
