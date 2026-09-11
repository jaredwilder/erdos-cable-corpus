import Mathlib

set_option autoImplicit false

open SimpleGraph in
def IsCUTF {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

theorem msl_erdos595_arrow_form {V : Type} (G : SimpleGraph V) : ¬ IsCUTF G ↔ ∀ f : Sym2 V → ℕ, ∃ a b c : V, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧ f s(a, b) = f s(a, c) ∧ f s(a, c) = f s(b, c) := by
  classical
  constructor
  · intro hw f
    by_contra hcon
    push_neg at hcon
    refine hw ⟨fun n => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ f e = n}, ?_, ?_⟩
    · intro n t ht
      obtain ⟨hcl, hcard⟩ := ht
      obtain ⟨a, b, c, hab, hac, hbc, hteq⟩ := Finset.card_eq_three.mp hcard
      have ha : a ∈ t := by rw [hteq]; simp
      have hb : b ∈ t := by rw [hteq]; simp
      have hc : c ∈ t := by rw [hteq]; simp
      have e1 := hcl ha hb hab
      have e2 := hcl ha hc hac
      have e3 := hcl hb hc hbc
      rw [SimpleGraph.fromEdgeSet_adj] at e1 e2 e3
      exact hcon a b c e1.1.1 e2.1.1 e3.1.1 (by rw [e1.1.2, e2.1.2]) (by rw [e2.1.2, e3.1.2])
    · ext a b
      rw [SimpleGraph.iSup_adj]
      constructor
      · intro hab
        exact ⟨f s(a, b), by
          rw [SimpleGraph.fromEdgeSet_adj]
          exact ⟨⟨hab, rfl⟩, G.ne_of_adj hab⟩⟩
      · rintro ⟨n, hn⟩
        rw [SimpleGraph.fromEdgeSet_adj] at hn
        exact hn.1.1
  · rintro harr ⟨H, hfree, hEq⟩
    have hex : ∀ e : Sym2 V, ∃ n : ℕ, e ∈ G.edgeSet → e ∈ (H n).edgeSet := by
      intro e
      by_cases he : e ∈ G.edgeSet
      · revert he
        refine Sym2.ind (fun a b he => ?_) e
        rw [SimpleGraph.mem_edgeSet, hEq, SimpleGraph.iSup_adj] at he
        obtain ⟨n, hn⟩ := he
        exact ⟨n, fun _ => hn⟩
      · exact ⟨0, fun hc => absurd hc he⟩
    obtain ⟨a, b, c, hab, hac, hbc, h1, h2⟩ :=
      harr (fun e => Nat.find (hex e))
    have m1 : s(a, b) ∈ (H (Nat.find (hex s(a, b)))).edgeSet := Nat.find_spec (hex s(a, b)) hab
    have m2 : s(a, c) ∈ (H (Nat.find (hex s(a, c)))).edgeSet := Nat.find_spec (hex s(a, c)) hac
    have m3 : s(b, c) ∈ (H (Nat.find (hex s(b, c)))).edgeSet := Nat.find_spec (hex s(b, c)) hbc
    rw [← h1] at m2
    rw [← h2, ← h1] at m3
    exact hfree (Nat.find (hex s(a, b))) {a, b, c}
      (SimpleGraph.is3Clique_triple_iff.mpr ⟨m1, m2, m3⟩)
