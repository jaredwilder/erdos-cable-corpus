import Mathlib

set_option autoImplicit false

def exactSign (x : Int) : Option Int :=
  if x = 0 then none else some (if x < 0 then -1 else 1)

def verifier (xs : List Int) : Option (List Int) :=
  xs.mapM exactSign

theorem msl_fmz_erdos1_campaign_001_R002_L1_rechk_20260902T130754Z_1  : ∀ xs : List Int, verifier xs = none ↔ ∃ x : Int, x ∈ xs ∧ x = 0 := by
  intro xs
  induction xs with
  | nil =>
      simp [verifier]
  | cons x xs ih =>
      by_cases hx : x = 0
      · simp [verifier, exactSign, hx]
      · simp only [verifier, List.mapM_cons, exactSign, hx, if_false,
          Option.some_bind]
        by_cases hxs : verifier xs = none
        · simp [hxs, ih]
        · simp [hxs, ih]
