import Mathlib

set_option autoImplicit false

open SimpleGraph in
/-- The link of an edge: the apexes completing it to a triangle. -/
def Link {V : Type} (G : SimpleGraph V) (a b : V) : Set V := {v | G.Adj a v ∧ G.Adj b v}

theorem msl_erdos595_link_independence {V : Type} (G : SimpleGraph V) : G.CliqueFree 4 ↔ ∀ a b : V, G.Adj a b → ∀ x ∈ Link G a b, ∀ y ∈ Link G a b, x ≠ y → ¬ G.Adj x y := by
  classical
  constructor
  · intro hK4 a b hab x hx y hy hxy hxyadj
    obtain ⟨hax, hbx⟩ := hx
    obtain ⟨hay, hby⟩ := hy
    have h3 : G.IsNClique 3 {a, x, y} :=
      SimpleGraph.is3Clique_triple_iff.mpr ⟨hax, hay, hxyadj⟩
    refine hK4 (insert b {a, x, y}) (h3.insert ?_)
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hab.symm
    · exact hbx
    · exact hby
  · intro hlink t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, x, y, hab, hax, hay, hbx, hby, hxy, hteq⟩ := Finset.card_eq_four.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hx : x ∈ t := by rw [hteq]; simp
    have hy : y ∈ t := by rw [hteq]; simp
    exact hlink a b (hcl ha hb hab) x ⟨hcl ha hx hax, hcl hb hx hbx⟩
      y ⟨hcl ha hy hay, hcl hb hy hby⟩ hxy (hcl hx hy hxy)
