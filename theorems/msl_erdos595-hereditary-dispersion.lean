import Mathlib

set_option autoImplicit false

open SimpleGraph in
def IsProperC {V : Type} (G : SimpleGraph V) {C : Type} (f : V → C) : Prop :=
  ∀ a b : V, G.Adj a b → f a ≠ f b

theorem msl_erdos595_hereditary_dispersion {V C I : Type} (P : SimpleGraph V → Prop) (G : SimpleGraph V) : (∀ H₁ H₂ : SimpleGraph V, H₁ ≤ H₂ → P H₂ → P H₁) → (∀ H : SimpleGraph V, H ≤ G → P H → ∃ f : V → C, IsProperC H f) → (∀ f : V → (I → C), ¬ IsProperC G f) → ¬ ∃ H : I → SimpleGraph V, (∀ i, P (H i)) ∧ G = ⨆ i, H i := by
  classical
  intro hP htau hchi
  rintro ⟨H, hHP, hEq⟩
  have hle : ∀ i, H i ≤ G := by
    intro i
    rw [hEq]
    exact le_iSup H i
  choose f hf using fun i => htau (H i) (hle i) (hHP i)
  refine hchi (fun v => fun i => f i v) ?_
  intro a b hab hcon
  rw [hEq, SimpleGraph.iSup_adj] at hab
  obtain ⟨i, hi⟩ := hab
  exact hf i a b hi (congrFun hcon i)
