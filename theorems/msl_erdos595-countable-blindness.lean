import Mathlib

set_option autoImplicit false

open SimpleGraph Set in
def IsCUTF {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

theorem cliqueFreeSubsingleton {V : Type} (H : SimpleGraph V)
    (h : ∀ e₁ ∈ H.edgeSet, ∀ e₂ ∈ H.edgeSet, e₁ = e₂) : H.CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨hcl, hcard⟩ := ht
  obtain ⟨a, b, c, hab, hac, hbc, hteq⟩ := Finset.card_eq_three.mp hcard
  have ha : a ∈ t := by rw [hteq]; simp
  have hb : b ∈ t := by rw [hteq]; simp
  have hc : c ∈ t := by rw [hteq]; simp
  have e1 : s(a, b) ∈ H.edgeSet := hcl ha hb hab
  have e2 : s(a, c) ∈ H.edgeSet := hcl ha hc hac
  have hEq := h _ e1 _ e2
  rw [Sym2.eq_iff] at hEq
  rcases hEq with ⟨-, hbc'⟩ | ⟨h1, -⟩
  · exact hbc hbc'
  · exact hac h1

theorem countableEdgesCUTF {V : Type} (G : SimpleGraph V) (hG : Countable G.edgeSet) :
    IsCUTF G := by
  classical
  obtain ⟨cc, hcc⟩ := Countable.exists_injective_nat G.edgeSet
  refine ⟨fun n => SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ G.edgeSet, cc ⟨e, h⟩ = n}, ?_, ?_⟩
  · intro n
    refine cliqueFreeSubsingleton _ ?_
    intro e₁ h₁ e₂ h₂
    revert h₁ h₂
    refine Sym2.ind (fun a b => ?_) e₁
    refine Sym2.ind (fun x y => ?_) e₂
    intro h₁ h₂
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromEdgeSet_adj] at h₁ h₂
    obtain ⟨⟨hm₁, hv₁⟩, -⟩ := h₁
    obtain ⟨⟨hm₂, hv₂⟩, -⟩ := h₂
    exact congrArg Subtype.val (hcc (hv₁.trans hv₂.symm))
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      have hm : s(a, b) ∈ G.edgeSet := hab
      exact ⟨cc ⟨s(a, b), hm⟩, by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨hm, rfl⟩, G.ne_of_adj hab⟩⟩
    · rintro ⟨n, hn⟩
      rw [SimpleGraph.fromEdgeSet_adj] at hn
      exact hn.1.1

theorem msl_erdos595_countable_blindness {V : Type} (G : SimpleGraph V) : ∀ W : Set V, W.Countable → IsCUTF (G.induce W) := by
  classical
  intro W hW
  have hsub : Countable ((G.induce W).edgeSet) := by
    haveI : Countable W := hW.to_subtype
    haveI : Countable (Sym2 W) := inferInstance
    exact Subtype.countable
  exact countableEdgesCUTF _ hsub
