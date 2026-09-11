import Mathlib

set_option autoImplicit false

def even_n_minus_two_composite (n : ℕ) : Prop := 4 < n ∧ Even n → ¬Nat.Prime (n - 2)

theorem msl_fmz_erdos1142_campaign_001_R005_L1_a1r1  : ∀ n : ℕ, 4 < n → Even n → ¬Nat.Prime (n - 2) := by
  intro n hn hEven hprime
  obtain ⟨k, rfl⟩ := hEven
  have hk : 2 < k := by omega
  have hsub : 2 * (k - 1) = 2 * k - 2 := by omega
  have hprime_eq : (2 * k - 2).Prime := by simpa [hsub] using hprime
  have hfactor : 2 ∣ 2 * k - 2 := by
    refine ⟨k - 1, ?_⟩
    omega
  have hlt : 2 < 2 * k - 2 := by omega
  exact (Nat.Prime.not_dvd_one hprime_eq) (by
    have hdiv : 2 ∣ 2 * k - 2 := hfactor
    exact hdiv)
