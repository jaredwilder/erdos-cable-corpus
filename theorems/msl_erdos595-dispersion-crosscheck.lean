import Mathlib

set_option autoImplicit false

open SimpleGraph in
def IsCUTF {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

def IsProp' {V : Type} (G : SimpleGraph V) {C : Type} (f : V → C) : Prop :=
  ∀ a b : V, G.Adj a b → f a ≠ f b

theorem msl_erdos595_dispersion_crosscheck {V : Type} {C : Type} (G : SimpleGraph V) (htau : ∀ H : SimpleGraph V, H ≤ G → H.CliqueFree 3 → ∃ f : V → C, IsProp' H f) (hchi : ∀ f : V → (ℕ → C), ¬ IsProp' G f) : ¬ IsCUTF G := by
  classical
  rintro ⟨H, hfree, hEq⟩
  have hle : ∀ i, H i ≤ G := by
    intro i; rw [hEq]; exact le_iSup H i
  choose f hf using fun i => htau (H i) (hle i) (hfree i)
  refine hchi (fun v => fun i => f i v) ?_
  rw [hEq]
  intro a b hab hcon
  rw [SimpleGraph.iSup_adj] at hab
  obtain ⟨i, hi⟩ := hab
  exact hf i a b hi (congrFun hcon i)
