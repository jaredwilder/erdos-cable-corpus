import Mathlib

set_option autoImplicit false

open SimpleGraph in
def IsUTF {V : Type} (I : Type) (G : SimpleGraph V) : Prop :=
  ∃ H : I → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

theorem triAdjGen {V I : Type} (G : SimpleGraph V) :
    (∃ c : Sym2 V → I, ∀ a b d : V, G.Adj a b → G.Adj a d → G.Adj b d → c s(a, b) ≠ c s(a, d)) → IsUTF I G := by
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
    have e3 := hcl hb hd hbd
    rw [SimpleGraph.fromEdgeSet_adj] at e1 e2 e3
    exact hc a b d e1.1.1 e2.1.1 e3.1.1 (by rw [e1.1.2, e2.1.2])
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

theorem msl_erdos595_pair_colouring_criterion {V I : Type} (G : SimpleGraph V) (c : V → V → I) : (∀ a b : V, c a b = c b a) → (∀ a b d : V, G.Adj a b → G.Adj a d → G.Adj b d → c a b ≠ c a d) → IsUTF I G := by
  intro hsymm h
  refine triAdjGen G ⟨Sym2.lift ⟨c, hsymm⟩, ?_⟩
  intro a b d h1 h2 h3
  exact h a b d h1 h2 h3
