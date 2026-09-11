import Mathlib

set_option autoImplicit false

namespace Erdos276L1
def IsLucas (a : ℕ → ℕ) : Prop := ∀ n, a (n + 2) = a (n + 1) + a n
theorem dvd_step (a : ℕ → ℕ) (h : IsLucas a) (d : ℕ) (h0 : d ∣ a 0) (h1 : d ∣ a 1) : ∀ n, d ∣ a n := by
  have Q : ∀ n, d ∣ a n ∧ d ∣ a (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [h n]
      exact dvd_add ih.2 ih.1
  exact fun n => (Q n).1
theorem gcd_invariance (a : ℕ → ℕ) (h : IsLucas a) (d : ℕ) (hd : 0 < d) : ((∀ k, d ∣ a k) ↔ d ∣ Nat.gcd (a 0) (a 1)) := by
  constructor
  · exact fun hall => Nat.dvd_gcd (hall 0) (hall 1)
  · exact fun hg => dvd_step a h d (hg.trans (Nat.gcd_dvd_left _ _)) (hg.trans (Nat.gcd_dvd_right _ _))
theorem coprime_seeds_no_common_divisor (a : ℕ → ℕ) (h : IsLucas a) (hc : Nat.gcd (a 0) (a 1) = 1) (d : ℕ) (hd : 1 < d) : ∃ k, ¬ (d ∣ a k) := by
  refine ⟨0, fun hdv => ?_⟩
  have hall : ∀ k, d ∣ a k := by
    intro k
    cases k with
    | zero => exact hdv
    | succ m => exact dvd_step a h d hdv hdv (m + 1)
  have hg : d ∣ Nat.gcd (a 0) (a 1) := (gcd_invariance a h d hd).1 hall
  rw [hc] at hg
  have h1 : d = 1 := Nat.dvd_one.mp hg
  omega
end Erdos276L1

theorem msl_fmz_erdos276_campaign_001_R001_L1  : ∀ (a : ℕ → ℕ), (∀ n, a (n + 2) = a (n + 1) + a n) →
  ((∀ k, Nat.gcd (a 0) (a 1) ∣ a k) ∧
   (∀ d > 0, ((∀ k, d ∣ a k) ↔ d ∣ Nat.gcd (a 0) (a 1))) ∧
   (Nat.gcd (a 0) (a 1) = 1 → ∀ d > 1, ∃ k, ¬ (d ∣ a k))) := by
  intro a h
  refine ⟨Erdos276L1.dvd_step a h (Nat.gcd (a 0) (a 1)) (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _), fun d hd => Erdos276L1.gcd_invariance a h d hd, fun hc d hd => Erdos276L1.coprime_seeds_no_common_divisor a h hc d hd⟩
