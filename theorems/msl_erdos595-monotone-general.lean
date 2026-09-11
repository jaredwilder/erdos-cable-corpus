import Mathlib

set_option autoImplicit false

open SimpleGraph in
def IsUTF {V : Type} (I : Type) (G : SimpleGraph V) : Prop :=
  ∃ H : I → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

theorem msl_erdos595_monotone_general {V I : Type} (G H : SimpleGraph V) : H ≤ G → IsUTF I G → IsUTF I H := by
  classical
  rintro hle ⟨L, hfree, hEq⟩
  refine ⟨fun i => H ⊓ L i, fun i => (hfree i).anti inf_le_right, ?_⟩
  ext a b
  rw [SimpleGraph.iSup_adj]
  constructor
  · intro hab
    have hG : G.Adj a b := hle hab
    rw [hEq, SimpleGraph.iSup_adj] at hG
    obtain ⟨i, hi⟩ := hG
    exact ⟨i, ⟨hab, hi⟩⟩
  · rintro ⟨i, hi⟩
    exact hi.1
