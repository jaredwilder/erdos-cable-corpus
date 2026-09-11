import Mathlib

set_option autoImplicit false

open SimpleGraph in
def IsCUTF {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

theorem msl_erdos595_cone_two_layers {V : Type} (G : SimpleGraph V) (v : V) : (∀ a b c : V, a ≠ v → b ≠ v → c ≠ v → G.Adj a b → G.Adj a c → G.Adj b c → False) → G.CliqueFree 4 ∧ IsCUTF G := by
  classical
  intro hT
  constructor
  · intro t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hteq⟩ := Finset.card_eq_four.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hc : c ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    by_cases hav : a = v
    · subst hav
      exact hT b c d (fun h => hab h.symm) (fun h => hac h.symm) (fun h => had h.symm)
        (hcl hb hc hbc) (hcl hb hd hbd) (hcl hc hd hcd)
    · by_cases hbv : b = v
      · subst hbv
        exact hT a c d hav (fun h => hbc h.symm) (fun h => hbd h.symm)
          (hcl ha hc hac) (hcl ha hd had) (hcl hc hd hcd)
      · by_cases hcv : c = v
        · subst hcv
          exact hT a b d hav hbv (fun h => hcd h.symm)
            (hcl ha hb hab) (hcl ha hd had) (hcl hb hd hbd)
        · exact hT a b c hav hbv hcv (hcl ha hb hab) (hcl ha hc hac) (hcl hb hc hbc)
  · set L0 : SimpleGraph V := SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ v ∉ e} with hL0
    set L1 : SimpleGraph V := SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ v ∈ e} with hL1
    have h0free : L0.CliqueFree 3 := by
      intro t ht
      obtain ⟨hcl, hcard⟩ := ht
      obtain ⟨a, b, c, hab, hac, hbc, hteq⟩ := Finset.card_eq_three.mp hcard
      have ha : a ∈ t := by rw [hteq]; simp
      have hb : b ∈ t := by rw [hteq]; simp
      have hc : c ∈ t := by rw [hteq]; simp
      have e1 := hcl ha hb hab
      have e2 := hcl ha hc hac
      have e3 := hcl hb hc hbc
      rw [hL0, SimpleGraph.fromEdgeSet_adj] at e1 e2 e3
      have hav : a ≠ v := fun h => e1.1.2 (by rw [← h]; exact Sym2.mem_mk_left a b)
      have hbv : b ≠ v := fun h => e1.1.2 (by rw [← h]; exact Sym2.mem_mk_right a b)
      have hcv : c ≠ v := fun h => e2.1.2 (by rw [← h]; exact Sym2.mem_mk_right a c)
      exact hT a b c hav hbv hcv e1.1.1 e2.1.1 e3.1.1
    have h1free : L1.CliqueFree 3 := by
      intro t ht
      obtain ⟨hcl, hcard⟩ := ht
      obtain ⟨a, b, c, hab, hac, hbc, hteq⟩ := Finset.card_eq_three.mp hcard
      have ha : a ∈ t := by rw [hteq]; simp
      have hb : b ∈ t := by rw [hteq]; simp
      have hc : c ∈ t := by rw [hteq]; simp
      have e1 := hcl ha hb hab
      have e2 := hcl ha hc hac
      have e3 := hcl hb hc hbc
      rw [hL1, SimpleGraph.fromEdgeSet_adj] at e1 e2 e3
      have m1 : v = a ∨ v = b := by simpa [Sym2.mem_iff] using e1.1.2
      have m2 : v = a ∨ v = c := by simpa [Sym2.mem_iff] using e2.1.2
      have m3 : v = b ∨ v = c := by simpa [Sym2.mem_iff] using e3.1.2
      rcases m1 with rfl | rfl
      · rcases m3 with rfl | rfl
        · exact hab rfl
        · exact hac rfl
      · rcases m2 with rfl | rfl
        · exact hab rfl
        · exact hbc rfl
    refine ⟨fun n => Nat.casesOn n L0 (fun _ => L1), ?_, ?_⟩
    · rintro (_ | k)
      · exact h0free
      · exact h1free
    · ext a b
      rw [SimpleGraph.iSup_adj]
      constructor
      · intro hab
        by_cases hv : v ∈ s(a, b)
        · refine ⟨1, ?_⟩
          show L1.Adj a b
          rw [hL1, SimpleGraph.fromEdgeSet_adj]
          exact ⟨⟨hab, hv⟩, G.ne_of_adj hab⟩
        · refine ⟨0, ?_⟩
          show L0.Adj a b
          rw [hL0, SimpleGraph.fromEdgeSet_adj]
          exact ⟨⟨hab, hv⟩, G.ne_of_adj hab⟩
      · rintro ⟨n, hn⟩
        rcases n with _ | k
        · have : L0.Adj a b := hn
          rw [hL0, SimpleGraph.fromEdgeSet_adj] at this
          exact this.1.1
        · have : L1.Adj a b := hn
          rw [hL1, SimpleGraph.fromEdgeSet_adj] at this
          exact this.1.1
