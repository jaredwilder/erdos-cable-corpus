import Mathlib

set_option autoImplicit false

-- no auxiliary definitions

theorem msl_fmz_erdos1142_campaign_001_R005_L1_a1r6  : ∀ n : ℕ, 4 < n → Even n → ¬ Nat.Prime (n - 2) := by
  intro n hn hEven
  rcases hEven with ⟨k, hk⟩
  intro hprime
  have hn_eq : n = 2 * k := by
    omega
  have hk_ge : 2 ≤ k := by
    omega
  have hsub : n - 2 = 2 * (k - 1) := by
    omega
  have hdiv : 2 ∣ n - 2 := by
    rw [hsub]
    exact ⟨k - 1, by omega⟩
  have hgt : 2 < n - 2 := by
    omega
  have hprime_two : Nat.Prime 2 := by decide
  have htwo_dvd : 2 ∣ n - 2 := hdiv
  have h_eq : n - 2 = 2 := by
    exact (Nat.dvd_prime hprime).mp htwo_dvd |>.resolve_left (by omega)
  omega
