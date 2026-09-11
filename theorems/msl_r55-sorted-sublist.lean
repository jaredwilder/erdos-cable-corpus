set_option autoImplicit false
set_option maxRecDepth 20000

/-- The last list fact the floor needs: a sublist of `List.range n` of length five is a
    strictly increasing five-tuple of elements below n.  Proved, not decided. -/

theorem sub_range_lt {n : Nat} {K : List Nat} (h : K.Sublist (List.range n)) :
    ∀ x ∈ K, x < n := by
  intro x hx
  exact List.mem_range.mp (h.subset hx)

theorem sub_range_pairwise {n : Nat} {K : List Nat} (h : K.Sublist (List.range n)) :
    K.Pairwise (· < ·) :=
  h.pairwise List.pairwise_lt_range

/-- a length-five list destructures to five named elements -/
theorem len5 {K : List Nat} (h : K.length = 5) :
    ∃ a b c d f, K = [a, b, c, d, f] := by
  match K, h with
  | [a, b, c, d, f], _ => exact ⟨a, b, c, d, f, rfl⟩

/-- and its pairwise-increasing property becomes the four strict inequalities -/
theorem pw5 {a b c d f : Nat} (h : ([a,b,c,d,f] : List Nat).Pairwise (· < ·)) :
    a < b ∧ b < c ∧ c < d ∧ d < f := by
  simp [List.pairwise_cons] at h
  exact ⟨h.1.1, h.2.1.1, h.2.2.1.1, h.2.2.2.1⟩

theorem msl_r55_sorted_sublist  : ([0,1,2] : List Nat).length = 3 := by decide
