import Mathlib

set_option autoImplicit false

def sumFromOne (n : Nat) : Nat := ∑ k in Finset.Icc 1 n, k

theorem msl_fmz_erdos1004_campaign_001_R001_L1_a2r3  : ∀ n : Nat, 1 ≤ n → sumFromOne n = n * (n + 1) / 2 := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : n = 0
      · subst h
        decide
      · have hn' : 1 ≤ n := by omega
        rw [sumFromOne, Finset.sum_Icc_succ_top hn']
        rw [ih hn']
        omega
