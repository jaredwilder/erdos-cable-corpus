import Mathlib

set_option autoImplicit false

def IsLucasSequence (L : ℕ → ℕ) : Prop := ∀ n, L (n + 2) = L (n + 1) + L n

def NecessaryConditions (a : ℕ → ℕ) : Prop :=
  IsLucasSequence a ∧
  (∀ k, (a k).Composite) ∧
  (∀ n > 1, ∃ k, Nat.gcd n (a k) = 1)

theorem msl_fmz_erdos276_campaign_001_R004_L1_a1r6  : ∀ (a : ℕ → ℕ), NecessaryConditions a → (a 0).Composite ∧ (a 1).Composite := by
  intro a h
  exact ⟨h.2.1 0, h.2.1 1⟩
