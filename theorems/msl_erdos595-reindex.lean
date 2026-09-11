import Mathlib

set_option autoImplicit false

open SimpleGraph in
def IsUTF {V : Type} (I : Type) (G : SimpleGraph V) : Prop :=
  ∃ H : I → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

theorem msl_erdos595_reindex {V I J : Type} (G : SimpleGraph V) (s : J → I) : Function.Surjective s → IsUTF I G → IsUTF J G := by
  rintro hs ⟨L, hfree, hEq⟩
  refine ⟨fun j => L (s j), fun j => hfree _, ?_⟩
  ext a b
  rw [hEq, SimpleGraph.iSup_adj, SimpleGraph.iSup_adj]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := hs i
    exact ⟨j, hi⟩
  · rintro ⟨j, hj⟩
    exact ⟨s j, hj⟩
