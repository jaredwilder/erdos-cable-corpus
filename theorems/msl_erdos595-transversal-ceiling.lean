import Mathlib

set_option autoImplicit false

open SimpleGraph in
def IsProperC {V : Type} (G : SimpleGraph V) {C : Type} (f : V → C) : Prop :=
  ∀ a b : V, G.Adj a b → f a ≠ f b

open SimpleGraph in
def IsTransversal {V : Type} (G : SimpleGraph V) (D : Set (Sym2 V)) : Prop :=
  ∀ a b c : V, G.Adj a b → G.Adj a c → G.Adj b c →
    s(a, b) ∈ D ∨ s(a, c) ∈ D ∨ s(b, c) ∈ D

theorem msl_erdos595_transversal_ceiling {V C : Type} (G : SimpleGraph V) : (∀ D : Set (Sym2 V), IsTransversal G D → ∃ f : V → C, IsProperC (G.deleteEdges D) f) ↔ (∀ H : SimpleGraph V, H ≤ G → H.CliqueFree 3 → ∃ f : V → C, IsProperC H f) := by
  classical
  constructor
  · intro hD H hHle hHfree
    obtain ⟨f, hf⟩ := hD {e | e ∈ G.edgeSet ∧ e ∉ H.edgeSet} (by
      intro a b c hab hac hbc
      by_contra hcon
      push_neg at hcon
      obtain ⟨h1, h2, h3⟩ := hcon
      have m1 : H.Adj a b := by
        by_contra hx
        exact h1 ⟨hab, fun hy => hx hy⟩
      have m2 : H.Adj a c := by
        by_contra hx
        exact h2 ⟨hac, fun hy => hx hy⟩
      have m3 : H.Adj b c := by
        by_contra hx
        exact h3 ⟨hbc, fun hy => hx hy⟩
      exact hHfree {a, b, c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨m1, m2, m3⟩))
    refine ⟨f, fun a b hab => hf a b ?_⟩
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨hHle hab, fun hmem => hmem.2 hab⟩
  · intro hH D hDtr
    refine hH (G.deleteEdges D) (SimpleGraph.deleteEdges_le D) ?_
    intro t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, c, hab, hac, hbc, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hc : c ∈ t := by rw [hteq]; simp
    have e1 := hcl ha hb hab
    have e2 := hcl ha hc hac
    have e3 := hcl hb hc hbc
    rw [SimpleGraph.deleteEdges_adj] at e1 e2 e3
    rcases hDtr a b c e1.1 e2.1 e3.1 with h | h | h
    · exact e1.2 h
    · exact e2.2 h
    · exact e3.2 h
