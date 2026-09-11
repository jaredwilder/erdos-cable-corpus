import Mathlib

set_option autoImplicit false

theorem msl_erdos595_locally_countable_component {W : Type} (T : SimpleGraph W) : (∀ v : W, (T.neighborSet v).Countable) → ∀ w : W, {x : W | T.Reachable w x}.Countable := by
  classical
  intro h w
  set B : ℕ → Set W := fun n => Nat.rec ({w} : Set W)
    (fun _ prev => prev ∪ ⋃ v ∈ prev, T.neighborSet v) n with hB
  have hBc : ∀ n, (B n).Countable := by
    intro n
    induction n with
    | zero => exact Set.countable_singleton w
    | succ k ih => exact ih.union (ih.biUnion (fun v _ => h v))
  have hstep : ∀ (c x : W), T.Adj c x → (∃ n, c ∈ B n) → ∃ n, x ∈ B n := by
    rintro c x hcx ⟨n, hn⟩
    exact ⟨n + 1, Or.inr (Set.mem_biUnion hn hcx)⟩
  have hrtg : ∀ x : W, Relation.ReflTransGen T.Adj w x → ∃ n, x ∈ B n := by
    intro x hx
    induction hx with
    | refl => exact ⟨0, rfl⟩
    | tail hprev hadj ih => exact hstep _ _ hadj ih
  refine Set.Countable.mono (fun x hx => ?_) (Set.countable_iUnion hBc)
  obtain ⟨n, hn⟩ := hrtg x ((SimpleGraph.reachable_iff_reflTransGen w x).mp hx)
  exact Set.mem_iUnion.2 ⟨n, hn⟩
