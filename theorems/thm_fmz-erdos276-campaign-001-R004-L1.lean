import Mathlib

set_option autoImplicit false

def CommonDivisor (a : ℕ → ℕ) (d : ℕ) : Prop := ∀ n, d ∣ a n

theorem msl_fmz_erdos276_campaign_001_R004_L1  : ∀ (a : ℕ → ℕ), (∀ n : ℕ, a (n + 2) = a (n + 1) + a n) → ∀ d : ℕ, CommonDivisor a d ↔ d ∣ Nat.gcd (a 0) (a 1) := by
  intro a hrec d
  constructor
  · intro hd
    exact Nat.dvd_gcd (hd 0) (hd 1)
  · intro hg n
    have h0 : d ∣ a 0 := dvd_trans hg (Nat.gcd_dvd_left (a 0) (a 1))
    have h1 : d ∣ a 1 := dvd_trans hg (Nat.gcd_dvd_right (a 0) (a 1))
    induction n using Nat.twoStepInduction with
    | zero => exact h0
    | one => exact h1
    | more n ih0 ih1 =>
        rw [hrec n]
        exact dvd_add ih1 ih0
