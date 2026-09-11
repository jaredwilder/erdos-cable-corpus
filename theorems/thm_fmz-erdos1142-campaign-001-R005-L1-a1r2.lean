import Mathlib

set_option autoImplicit false

def even_n_minus_two_composite (n : ℕ) : Prop := 4 < n ∧ Even n → ¬Nat.Prime (n - 2)

theorem msl_fmz_erdos1142_campaign_001_R005_L1_a1r2  : ∀ n : ℕ, 4 < n → Even n → ¬Nat.Prime (n - 2) := by
  intro n hn hEven hprime
  rcases hEven with ⟨k, hk⟩
  have hk' : 2 ≤ k := by
    omega
  have hnk : n = 2 * k := by
    simpa [Even] using hk
  have hsub : n - 2 = 2 * (k - 1) := by
    rw [hnk]
    omega
  rw [hsub] at hprime
  have hfactor : 2 ∣ 2 * (k - 1) := by
    exact dvd_mul_right 2 (k - 1)
  have hfactor_lt : 2 < 2 * (k - 1) := by
    omega
  exact (Nat.Prime.not_dvd hprime (by norm_num)) (by simpa using hfactor)
