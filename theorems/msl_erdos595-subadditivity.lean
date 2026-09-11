import Mathlib

set_option autoImplicit false

open SimpleGraph in
def IsUTF {V : Type} (I : Type) (G : SimpleGraph V) : Prop :=
  ∃ H : I → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

theorem msl_erdos595_subadditivity {V : Type} {I J : Type} (G : SimpleGraph V) (F : I → SimpleGraph V) (hG : G = ⨆ i, F i) : (∀ i, IsUTF J (F i)) → IsUTF (I × J) G := by
  classical
  intro hsub
  choose H hfree hEq using hsub
  refine ⟨fun p => H p.1 p.2, fun p => hfree p.1 p.2, ?_⟩
  ext a b
  rw [SimpleGraph.iSup_adj]
  constructor
  · intro hab
    rw [hG, SimpleGraph.iSup_adj] at hab
    obtain ⟨i, hi⟩ := hab
    rw [hEq i, SimpleGraph.iSup_adj] at hi
    obtain ⟨j, hj⟩ := hi
    exact ⟨(i, j), hj⟩
  · rintro ⟨p, hp⟩
    rw [hG, SimpleGraph.iSup_adj]
    refine ⟨p.1, ?_⟩
    rw [hEq p.1, SimpleGraph.iSup_adj]
    exact ⟨p.2, hp⟩
