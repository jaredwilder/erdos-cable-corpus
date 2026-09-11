import Mathlib

set_option autoImplicit false

def ValidAssignment (n : Nat) (a : Nat → Nat) : Prop :=
  Set.InjOn a (Set.Icc 1 n) ∧ (∀ k : Nat, k ∈ Set.Icc 1 n → k ∣ a k)

theorem msl_endpoint_fix  : ∀ (n : Nat) (a : Nat → Nat), ValidAssignment (n + 1) a → ValidAssignment n a := by
  intro n a h
  obtain ⟨hinj, hdiv⟩ := h
  constructor
  · intro x hx y hy hxy
    simp only [Set.mem_Icc] at hx hy
    exact hinj (by simp only [Set.mem_Icc]; omega) (by simp only [Set.mem_Icc]; omega) hxy
  · intro k hk
    simp only [Set.mem_Icc] at hk
    exact hdiv k (by simp only [Set.mem_Icc]; omega)
