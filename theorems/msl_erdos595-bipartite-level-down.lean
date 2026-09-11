import Mathlib

set_option autoImplicit false

open SimpleGraph in
def IsProperC {V : Type} (G : SimpleGraph V) {C : Type} (f : V → C) : Prop :=
  ∀ a b : V, G.Adj a b → f a ≠ f b

open SimpleGraph in
def IsCUB {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, ∃ f : V → Bool, IsProperC (H i) f) ∧ G = ⨆ i, H i

theorem msl_erdos595_bipartite_level_down {V : Type} (G : SimpleGraph V) : IsCUB G ↔ ∃ f : V → (ℕ → Bool), IsProperC G f := by
  constructor
  · rintro ⟨H, hbip, hEq⟩
    choose f hf using hbip
    refine ⟨fun v => fun i => f i v, ?_⟩
    intro a b hab hcon
    rw [hEq, SimpleGraph.iSup_adj] at hab
    obtain ⟨i, hi⟩ := hab
    exact hf i a b hi (congrFun hcon i)
  · rintro ⟨g, hg⟩
    refine ⟨fun i => SimpleGraph.fromRel (fun a b => G.Adj a b ∧ g a i ≠ g b i), ?_, ?_⟩
    · intro i
      refine ⟨fun v => g v i, ?_⟩
      intro a b hab
      rw [SimpleGraph.fromRel_adj] at hab
      rcases hab.2 with h | h
      · exact h.2
      · exact fun hc => h.2 hc.symm
    · ext a b
      rw [SimpleGraph.iSup_adj]
      constructor
      · intro hab
        obtain ⟨i, hi⟩ := Function.ne_iff.mp (hg a b hab)
        exact ⟨i, by rw [SimpleGraph.fromRel_adj]; exact ⟨G.ne_of_adj hab, Or.inl ⟨hab, hi⟩⟩⟩
      · rintro ⟨i, hi⟩
        rw [SimpleGraph.fromRel_adj] at hi
        rcases hi.2 with h | h
        · exact h.1
        · exact h.1.symm
