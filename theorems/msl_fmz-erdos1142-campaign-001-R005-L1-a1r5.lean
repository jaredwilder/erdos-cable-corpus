import Mathlib

set_option autoImplicit false

-- no auxiliary definitions

theorem msl_fmz_erdos1142_campaign_001_R005_L1_a1r5  : ∀ n : ℕ, 4 < n → Even n → ¬ Nat.Prime (n - 2) := by
  intro n hn hev hprime
  obtain ⟨k, rfl⟩ := hev
  have hk : 2 < k := by omega
  have hprime' : Nat.Prime (2 * k - 2) := by
    simpa using hprime
  have hdiv : 2 ∣ 2 * k - 2 := by
    exact ⟨k - 1, by omega⟩
  have htwo : 2 < 2 * k - 2 := by omega
  have hnot : ¬ Nat.Prime (2 * k - 2) := by
    intro hp
    obtain ⟨q, hqprime, hqdiv⟩ := (Nat.prime_iff.mp hp).2 2 (by norm_num) hdiv
    have : q = 2 := by omega
    subst q
    exact (Nat.Prime.not_dvd_one hqprime) (by simpa using hqdiv)
  exact hnot hprime'
