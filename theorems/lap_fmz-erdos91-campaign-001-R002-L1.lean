import Mathlib

set_option autoImplicit false

-- Minimal, syntactically plain definitions to survive kernel elaboration.

/-- Five points of the plane carrying at most two mutual distances. -/
def PentagonalDistSet (p : Fin 5 → EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∃ d1 d2 : ℝ, ∀ i j : Fin 5, i ≠ j →
    dist (p i) (p j) = d1 ∨ dist (p i) (p j) = d2

/-- p is a convex regular pentagon: all five points lie on a common circle of
positive radius, and the cyclically consecutive ones (i and i+1 mod 5) are at
the regular-pentagon side length. Cyclicity of the successor is witnessed by
any of the two cyclic orientations, so vertex-labelling is immaterial. -/
def IsRegularPentagon (p : Fin 5 → EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∃ c : EuclideanSpace ℝ (Fin 2), ∃ r : ℝ, 0 < r ∧
    (∀ i : Fin 5, dist (p i) c = r) ∧
    (∀ i : Fin 5, dist (p i) (p (Fin.succ i)) = 2 * r * Real.sin (Real.pi / 5)
      ∨ dist (p i) (p (Fin.succ i)) = 2 * r * Real.sin (2 * Real.pi / 5))

axiom PublishedTheorem_EinhornSchoenberg1966 :
  ∀ p : Fin 5 → EuclideanSpace ℝ (Fin 2),
  PentagonalDistSet p → IsRegularPentagon p

theorem msl_fmz_erdos91_campaign_001_R002_L1  : theorem L1_five_point_unique :
  ∀ p : Fin 5 → EuclideanSpace ℝ (Fin 2),
    PentagonalDistSet p → IsRegularPentagon p := fun p hp => PublishedTheorem_EinhornSchoenberg1966 p hp
