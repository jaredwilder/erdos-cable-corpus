import Mathlib

set_option autoImplicit false

open SimpleGraph Set in
def GoodOn {V : Type} (G : SimpleGraph V) (k : ℕ) (S : Set V) (f : Sym2 V → Fin k) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, G.Adj a b → G.Adj a c → G.Adj b c →
    ¬ (f s(a, b) = f s(a, c) ∧ f s(a, c) = f s(b, c))

theorem msl_erdos595_compactness_T26 {V : Type} (G : SimpleGraph V) (k : ℕ) (h : ∀ S : Finset V, ∃ f : Sym2 V → Fin k, GoodOn G k (S : Set V) f) : ∃ f : Sym2 V → Fin k, GoodOn G k Set.univ f := by
  classical
  letI : TopologicalSpace (Fin k) := ⊥
  haveI : DiscreteTopology (Fin k) := ⟨rfl⟩
  haveI : CompactSpace (Fin k) := Finite.compactSpace
  haveI : CompactSpace (Sym2 V → Fin k) := Pi.compactSpace
  let T := {p : V × V × V // G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2}
  let C : T → Set (Sym2 V → Fin k) := fun t =>
    {f | ¬ (f s(t.1.1, t.1.2.1) = f s(t.1.1, t.1.2.2) ∧
            f s(t.1.1, t.1.2.2) = f s(t.1.2.1, t.1.2.2))}
  have hclosed : ∀ t : T, IsClosed (C t) := by
    intro t
    have hcont : Continuous (fun f : Sym2 V → Fin k =>
        (f s(t.1.1, t.1.2.1), f s(t.1.1, t.1.2.2), f s(t.1.2.1, t.1.2.2))) :=
      by fun_prop
    have heq : C t = (fun f : Sym2 V → Fin k =>
        (f s(t.1.1, t.1.2.1), f s(t.1.1, t.1.2.2), f s(t.1.2.1, t.1.2.2))) ⁻¹'
        {p : Fin k × Fin k × Fin k | ¬ (p.1 = p.2.1 ∧ p.2.1 = p.2.2)} := rfl
    rw [heq]
    exact (isClosed_discrete _).preimage hcont
  have hne : (⋂ t : T, C t).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    obtain ⟨u, hu⟩ := (isCompact_univ (X := Sym2 V → Fin k)).elim_finite_subfamily_closed
      C hclosed (by rw [Set.univ_inter, hcon])
    let S : Finset V := u.biUnion (fun t => {t.1.1, t.1.2.1, t.1.2.2})
    obtain ⟨f, hf⟩ := h S
    have hmem : f ∈ ⋂ t ∈ u, C t := by
      refine Set.mem_iInter₂.2 (fun t ht => ?_)
      have h1 : t.1.1 ∈ S := Finset.mem_biUnion.2 ⟨t, ht, by simp⟩
      have h2 : t.1.2.1 ∈ S := Finset.mem_biUnion.2 ⟨t, ht, by simp⟩
      have h3 : t.1.2.2 ∈ S := Finset.mem_biUnion.2 ⟨t, ht, by simp⟩
      exact hf _ h1 _ h2 _ h3 t.2.1 t.2.2.1 t.2.2.2
    have hmem2 : f ∈ (Set.univ : Set (Sym2 V → Fin k)) ∩ ⋂ t ∈ u, C t := ⟨trivial, hmem⟩
    rw [hu] at hmem2
    exact hmem2.elim
  obtain ⟨f, hf⟩ := hne
  refine ⟨f, ?_⟩
  intro a _ b _ c _ hab hac hbc
  exact (Set.mem_iInter.1 hf ⟨(a, b, c), ⟨hab, hac, hbc⟩⟩)
