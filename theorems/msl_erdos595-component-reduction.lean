import Mathlib

set_option autoImplicit false

open SimpleGraph in
def IsUTF {V : Type} (I : Type) (G : SimpleGraph V) : Prop :=
  ∃ H : I → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

theorem msl_erdos595_component_reduction {V I K : Type} (G : SimpleGraph V) (part : V → K) (H : K → I → SimpleGraph V) : (∀ a b : V, G.Adj a b → part a = part b) → (∀ k i, (H k i).CliqueFree 3) → (∀ k i a b, (H k i).Adj a b → part a = k) → (∀ a b : V, G.Adj a b → ∃ i, (H (part a) i).Adj a b) → (∀ k i, H k i ≤ G) → IsUTF I G := by
  classical
  intro hsep hfree hin hcov hle
  refine ⟨fun i => ⨆ k : K, H k i, ?_, ?_⟩
  · intro i t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    obtain ⟨k1, e1⟩ := SimpleGraph.iSup_adj.mp (hcl ha hb hab)
    obtain ⟨k2, e2⟩ := SimpleGraph.iSup_adj.mp (hcl ha hd had)
    obtain ⟨k3, e3⟩ := SimpleGraph.iSup_adj.mp (hcl hb hd hbd)
    have p1 : part a = k1 := hin k1 i a b e1
    have p2 : part a = k2 := hin k2 i a d e2
    have p3 : part b = k3 := hin k3 i b d e3
    have pb : part b = k1 := hin k1 i b a e1.symm
    have hk12 : k1 = k2 := p1.symm.trans p2
    have hk13 : k1 = k3 := pb.symm.trans p3
    subst hk12
    subst hk13
    exact hfree k1 i {a, b, d} (SimpleGraph.is3Clique_triple_iff.mpr ⟨e1, e2, e3⟩)
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      obtain ⟨i, hi⟩ := hcov a b hab
      exact ⟨i, SimpleGraph.iSup_adj.mpr ⟨part a, hi⟩⟩
    · rintro ⟨i, hi⟩
      obtain ⟨k, hk⟩ := SimpleGraph.iSup_adj.mp hi
      exact hle k i hk
