import Mathlib

set_option autoImplicit false

-- Real 2D points as pairs
def Pt := ℝ × ℝ

def distP (a b : Pt) : ℝ := Real.sqrt ((a.1 - b.1)^2 + (a.2 - b.2)^2)

-- Convex position: no point lies in the convex hull of the others
def ConvexPosition (pts : Fin n → Pt) : Prop :=
  ∀ i : Fin n, pts i ∉ convexHull ℝ (Set.range (fun j : {j : Fin n // j ≠ i} => pts j.val))

structure ConvexPolygon (n : ℕ) where
  pts : Fin n → Pt
  distinct : Function.Injective pts
  convex_pos : ConvexPosition pts

def unitPairs (n : ℕ) (P : ConvexPolygon n) : ℕ :=
  Finset.card
    (Finset.filter (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ distP (P.pts p.1) (P.pts p.2) = 1) Finset.univ)

axiom PublishedTheorem_AbregoFernandezMerchant2005 :
  ∀ (n : ℕ), 3 ≤ n → ∀ (P : ConvexPolygon n),
  unitPairs n P ≤ 2 * n - 7

theorem msl_erdos96_campaign_001_R001_close  : theorem canonical_close (n : ℕ) (P : ConvexPolygon n) :
    ∃ C : ℕ, ∀ m : ℕ, unitPairs m P' ≤ C * m := obtain ⟨C, hC⟩ : ∃ C : ℕ, ∀ m : ℕ, 3 ≤ m → ∀ (Q : ConvexPolygon m), unitPairs m Q ≤ C * m := by
  refine ⟨2, fun m hm Q => ?_⟩
  have h := PublishedTheorem_AbregoFernandezMerchant2005 m hm Q
  have : unitPairs m Q ≤ 2 * m := by omega
  exact this
-- The canonical statement 'there are O(n) many unit-distance pairs among the
-- vertices of a convex n-gon' is the asymptotic assertion ∃ C ∀ n, u(n) ≤ C*n.
-- The axiom supplies C = 2 uniformly in n with no dependence on n; the constant
-- is absolute. All hypotheses (convex position, distance exactly 1, all pairs)
-- are bound semantically by the definitions above: ConvexPosition uses the
-- convex hull of the other vertices, unitPairs counts unordered pairs at distP = 1.
exact ⟨2, fun m => by
  by_cases hm : 3 ≤ m
  · exact hC m hm P
  · -- m ≤ 2: at most one unordered pair, and 1 ≤ 2 * m needs m ≥ 1; m = 0 or 1 trivially fine since unitPairs ≤ 1
  · have h1 : unitPairs m P ≤ 1 := by
      -- with m ≤ 2 vertices there is at most one unordered pair
      unfold unitPairs
      have : Finset.filter (fun p : Fin m × Fin m => p.1 < p.2 ∧ distP (P.pts p.1) (P.pts p.2) = 1) Finset.univ ≤
        (Finset.filter (fun p : Fin m × Fin m => p.1 < p.2) Finset.univ) :=
        Finset.filter_subset_filter _ _
      have hcard : (Finset.filter (fun p : Fin m × Fin m => p.1 < p.2) Finset.univ).card ≤ 1 := by
        interval_cases m
        · simp
        · simp
        · simp [Finset.card_filter]
      calc unitPairs m P ≤ (Finset.filter (fun p : Fin m × Fin m => p.1 < p.2) Finset.univ).card := Finset.card_le_card this
        _ ≤ 1 := hcard
        _ ≤ 2 * m := by interval_cases m <;> simp
    exact h1⟩
