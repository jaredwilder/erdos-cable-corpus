import Mathlib

set_option autoImplicit false
set_option maxRecDepth 20000

-- THE COUNTING CORE OF ERDOS-SZEKERES.
-- In the derivation, v has m+n-1 other vertices; A is its red neighbourhood and B its blue.
-- The claim is that A and B cannot BOTH fall short.
theorem es_pigeonhole (m n a b : Nat) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hsplit : a + b = m + n - 1) (ha : a ≤ m - 1) (hb : b ≤ n - 1) : False := by
  omega

-- THE COUNTING CORE OF THE GREENWOOD-GLEASON PARITY SHARPENING.
-- Both one-sided bounds are tight at every vertex, so the red graph is (m-1)-regular
-- on N = m+n-1 vertices; with m and n even that degree sum is odd.
theorem gg_forced_tight (m n a b : Nat) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hsplit : a + b = m + n - 2) (ha : a ≤ m - 1) (hb : b ≤ n - 1) :
    a = m - 1 ∧ b = n - 1 := by
  omega

theorem gg_parity (m n : Nat) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hme : m % 2 = 0) (hne : n % 2 = 0) :
    ((m + n - 1) * (m - 1)) % 2 = 1 := by
  obtain ⟨p, rfl⟩ : ∃ p, m = 2 * p := ⟨m / 2, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, n = 2 * q := ⟨n / 2, by omega⟩
  have h1 : 2 * p + 2 * q - 1 = 2 * (p + q - 1) + 1 := by omega
  have h2 : 2 * p - 1 = 2 * (p - 1) + 1 := by omega
  rw [h1, h2]
  omega

-- HANDSHAKE, as the parity argument uses it: a degree sum is even.
theorem handshake_even (N d : Nat) (h : ∃ E : Nat, N * d = 2 * E) : (N * d) % 2 = 0 := by
  obtain ⟨E, hE⟩ := h; omega

theorem msl_r55_es_arith_core  : (41 * 20) % 2 = 0 := by decide
