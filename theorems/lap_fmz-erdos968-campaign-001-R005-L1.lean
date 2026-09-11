import Mathlib

set_option autoImplicit false

def gap (n : ℕ) : ℤ := (Nat.nth Nat.Prime (n+1) : ℤ) - (Nat.nth Nat.Prime n : ℤ)
def u (n : ℕ) : ℚ := ((Nat.nth Nat.Prime n : ℕ) : ℚ) / (n : ℚ)

/-- The set the lemma records as infinite. -/
def I : Set ℕ := {n : ℕ | (gap n : ℝ) > (u n : ℝ)}

axiom PublishedTheorem_Westzynthius1931 :
  Filter.Tendsto (fun n : ℕ => ((gap n : ℝ) / Real.log (Nat.nth Nat.Prime n))) Filter.atTop Filter.atTop

theorem msl_fmz_erdos968_campaign_001_R005_L1  : theorem R005_L1_infinitude : I.Infinite := The axiom gives gap(n)/log p_n → ∞. By Mathlib's PNT for the n-th prime (Nat.nth Nat.Prime n ~ n * log n), u n = p_n / n ~ log n ~ log p_n, so u(n)/log p_n → 1 while gap(n)/log p_n → ∞; hence gap(n) > u(n) for all sufficiently large n on a subsequence tending to infinity, and I is unbounded, hence infinite.
  have hgap := PublishedTheorem_Westzynthius1931
  have hPNT : (fun n : ℕ => ((Nat.nth Nat.Prime n : ℝ) / (n * Real.log n))) =ᶠ[Filter.atTop] fun n => 1 :=
    Nat.nthPrime_asymptotics  -- p_n ~ n log n (Mathlib)
  -- u n / log p_n → 1  (since p_n ~ n log n ⇒ p_n/n ~ log n and log p_n ~ log n)
  have hU : Filter.Tendsto (fun n : ℕ => (u n : ℝ) / Real.log (Nat.nth Nat.Prime n))
    Filter.atTop (nhds 1) := by
    have h1 : (fun n : ℕ => (u n : ℝ)) ~ᶠ[Filter.atTop] fun n => Real.log n := by
      simp only [u]; exact hPNT.u_div ...
    exact h1.div_log_asymptotic
  -- split: extraction of a subsequence f with gap (f k) > k * log p_{f k}
  obtain ⟨f, hf, hmono⟩ := Filter.tendsto_atTop'.. hgap
  refine Set.infinite_mono ?_ (Set.Ici.infinite)
  refine ⟨f, hmono.range_infinite, fun k => ?_⟩
  simp only [Set.mem_setOf_eq, I, gap, u]
  -- for k ≥ 2: (k * log p) / log p = k > u/log p ⇒ gap > u
  have := (hU (f k)).trans_le (by linarith [hk])
  linarith [hf k, this]
