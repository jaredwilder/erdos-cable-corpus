set_option autoImplicit false
set_option maxRecDepth 20000

-- THE COUNTING CORE OF ERDOS-SZEKERES. v has m+n-1 other vertices; A is its red
-- neighbourhood and B its blue. They cannot BOTH fall short.
theorem es_pigeonhole (m n a b : Nat) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hsplit : a + b = m + n - 1) (ha : a ≤ m - 1) (hb : b ≤ n - 1) : False := by
  omega

-- THE COUNTING CORE OF THE PARITY SHARPENING, step one: at one lower total both
-- one-sided bounds are forced EXACTLY tight, at every vertex.
theorem gg_forced_tight (m n a b : Nat) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hsplit : a + b = m + n - 2) (ha : a ≤ m - 1) (hb : b ≤ n - 1) :
    a = m - 1 ∧ b = n - 1 := by
  omega

-- step two: with both neighbours EVEN, the order is odd and the degree is odd, so the
-- degree sum is odd. This is the contradiction the sharpening rests on.
theorem gg_parity (m n : Nat) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hme : m % 2 = 0) (hne : n % 2 = 0) :
    ((m + n - 1) * (m - 1)) % 2 = 1 := by
  have h1 : (m + n - 1) % 2 = 1 := by omega
  have h2 : (m - 1) % 2 = 1 := by omega
  rw [Nat.mul_mod, h1, h2]

-- step three: HANDSHAKE. any degree sum that is twice an edge count is even.
theorem handshake_even (N d E : Nat) (h : N * d = 2 * E) : (N * d) % 2 = 0 := by
  omega

-- the two together: under the parity hypothesis no such regular graph can exist.
theorem gg_contradiction (m n E : Nat) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hme : m % 2 = 0) (hne : n % 2 = 0)
    (hshake : (m + n - 1) * (m - 1) = 2 * E) : False := by
  have hodd := gg_parity m n hm hn hme hne
  omega

theorem msl_r55_es_arith_core_v2  : (41 * 20) % 2 = 0 := by decide
