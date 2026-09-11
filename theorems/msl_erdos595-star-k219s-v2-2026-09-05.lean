import Mathlib

set_option autoImplicit false

namespace Erdos595Star

variable {V : Type*}

def star (G : SimpleGraph V) (v : V) : SimpleGraph V where
  Adj x y := (x = v ∧ G.Adj v y) ∨ (y = v ∧ G.Adj x v)
  symm := fun x y h => by
    rcases h with ⟨hx, ha⟩ | ⟨hy, ha⟩
    · exact Or.inr ⟨hx, ha.symm⟩
    · exact Or.inl ⟨hy, ha.symm⟩
  loopless := fun x h => by
    rcases h with ⟨hx, ha⟩ | ⟨hx, ha⟩ <;> subst hx <;> exact G.irrefl ha

theorem star_le (G : SimpleGraph V) (v : V) : star G v ≤ G := by
  intro x y h
  rcases h with ⟨hx, ha⟩ | ⟨hy, ha⟩
  · subst hx; exact ha
  · subst hy; exact ha

theorem star_cliqueFree (G : SimpleGraph V) (v : V) : (star G v).CliqueFree 3 := by
  classical
  intro s hs
  have h3 : s.card = 3 := hs.2
  have hle : s.card - 1 ≤ (s.erase v).card := Finset.pred_card_le_card_erase (a := v) (s := s)
  have h2 : 1 < (s.erase v).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
  have hav : a ≠ v := (Finset.mem_erase.mp ha).1
  have hbv : b ≠ v := (Finset.mem_erase.mp hb).1
  have hclique := SimpleGraph.isClique_iff.mp hs.1
  have hadj : (star G v).Adj a b :=
    hclique (Finset.mem_coe.mpr (Finset.mem_of_mem_erase ha))
            (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hb)) hab
  rcases hadj with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact hav h1
  · exact hbv h1

theorem star_edgeSet_uncountable (G : SimpleGraph V) (v : V)
    (h : ¬ (G.neighborSet v).Countable) : ¬ (star G v).edgeSet.Countable := by
  intro hc
  apply h
  have hinj : Function.Injective (fun u : V => s(v, u)) := fun u u' he => Sym2.congr_right.mp he
  have hpre : G.neighborSet v ⊆ (fun u : V => s(v, u)) ⁻¹' (star G v).edgeSet := by
    intro u hu
    exact (star G v).mem_edgeSet.mpr (Or.inl ⟨rfl, hu⟩)
  exact (hc.preimage hinj).mono hpre

end Erdos595Star

theorem msl_erdos595_star_k219s_v2_2026_09_05 {V : Type*} (G : SimpleGraph V) (v : V) (h : ¬ (G.neighborSet v).Countable) : ∃ H : SimpleGraph V, H ≤ G ∧ H.CliqueFree 3 ∧ ¬ H.edgeSet.Countable := by exact ⟨Erdos595Star.star G v, Erdos595Star.star_le G v, Erdos595Star.star_cliqueFree G v, Erdos595Star.star_edgeSet_uncountable G v h⟩
