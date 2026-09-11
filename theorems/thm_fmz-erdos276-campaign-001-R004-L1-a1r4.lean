import Mathlib

set_option autoImplicit false

def IsLucasSequence (L : ℕ → ℕ) : Prop := ∀ n, L (n + 2) = L (n + 1) + L n

theorem msl_fmz_erdos276_campaign_001_R004_L1_a1r4  : ∀ (a : ℕ → ℕ), IsLucasSequence a → (∀ k, (a k).Composite) → (∀ n > 1, ∃ k, Nat.gcd n (a k) = 1) → (a 0).Composite ∧ (a 1).Composite := by
  intro a hLucas hComposite hCoprime
  exact ⟨hComposite 0, hComposite 1⟩
