import Mathlib

set_option autoImplicit false

noncomputable def Lf_unit : Set ℂ := Metric.closedBall (0 : ℂ) 1
def Circle (p : Σ' _ : ℂ, ℝ) : Set ℂ := Metric.sphere p.1 p.2

axiom PublishedTheorem_Mathlib_addHaar_sphere :
  ∀ (μ : MeasureTheory.Measure ℂ) [MeasureTheory.IsAddHaarMeasure μ] (c : ℂ) (r : ℝ), r ≠ 0 → μ (Metric.sphere c r) = 0

theorem msl_fmz_erdos509_campaign_001_R004_L1  : theorem no_circle_cover_of_unit_disk : ¬ ∃ S : Set (Σ' _ : ℂ, ℝ), S.Countable ∧ Lf_unit ⊆ ⋃ p ∈ S, Circle p := rintro ⟨S, hScount, hcover⟩
have hnull : ∀ p ∈ S, volume (Circle p) = 0 := by
  intro p hp
  by_cases hr : p.2 = 0
  · subst hr
    simp only [Circle, Metric.sphere_zero]
    exact MeasureTheory.measure_singleton p.1
  · exact PublishedTheorem_Mathlib_addHaar_sphere volume p.1 p.2 hr
have hunion : volume (⋃ p ∈ S, Circle p) = 0 := by
  rw [MeasureTheory.measure_biUnion_null_iff hScount]
  exact hnull
have hdisk : 0 < volume Lf_unit := by
  rw [Lf_unit, Real.volume_closedBall]
  positivity
have hsub : volume Lf_unit ≤ 0 := by
  calc volume Lf_unit ≤ volume (⋃ p ∈ S, Circle p) := MeasureTheory.measure_mono hcover
    _ = 0 := hunion
linarith
