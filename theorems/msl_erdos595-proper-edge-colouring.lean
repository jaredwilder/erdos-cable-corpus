import Mathlib

set_option autoImplicit false

open SimpleGraph in
def IsCUTF {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

open SimpleGraph in
def IsProperEdgeColouring {V : Type} (G : SimpleGraph V) (c : Sym2 V → ℕ) : Prop :=
  ∀ a b d : V, G.Adj a b → G.Adj a d → b ≠ d → c s(a, b) ≠ c s(a, d)

theorem msl_erdos595_proper_edge_colouring {V : Type} (G : SimpleGraph V) : (∃ c : Sym2 V → ℕ, IsProperEdgeColouring G c) → IsCUTF G := by
  classical
  rintro ⟨c, hc⟩
  refine ⟨fun n => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ c e = n}, ?_, ?_⟩
  · intro n t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    have e1 := hcl ha hb hab
    have e2 := hcl ha hd had
    rw [SimpleGraph.fromEdgeSet_adj] at e1 e2
    exact hc a b d e1.1.1 e2.1.1 hbd (by rw [e1.1.2, e2.1.2])
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      exact ⟨c s(a, b), by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨hab, rfl⟩, G.ne_of_adj hab⟩⟩
    · rintro ⟨n, hn⟩
      rw [SimpleGraph.fromEdgeSet_adj] at hn
      exact hn.1.1
