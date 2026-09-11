set_option autoImplicit false
set_option maxRecDepth 20000

/-- TOY RIG: the SAME nest shape at order 7 instead of 41, so the extraction TACTIC SCRIPT
    can be validated in seconds before it is aimed at the real nest.  Nothing here is about
    R(5,5); it exists only to de-risk the script. -/
def T : List Nat := [1,6]
def e7 (i j : Nat) : Bool := ((i % 7 + 7 - j % 7) % 7) ∈ T

def nest7 (e : Nat → Nat → Bool) : Bool :=
  (List.range 7).all fun a => (List.range 7).all fun b => (! (a < b)) ||
    ((List.range 7).all fun c => (! (b < c)) ||
      (! (e a b && e a c && e b c)))

theorem nest7_holds : nest7 e7 = true := by decide

/-- THE EXTRACTION SCRIPT UNDER TEST: one instance at an increasing triple below 7. -/
theorem extract7 (e : Nat → Nat → Bool) (h : nest7 e = true)
    (a b c : Nat) (ha : a < 7) (hb : b < 7) (hc : c < 7)
    (hab : a < b) (hbc : b < c) :
    ¬ (e a b = true ∧ e a c = true ∧ e b c = true) := by
  have h1 := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  have h2 := List.all_eq_true.mp h1 b (List.mem_range.mpr hb)
  simp only [hab, decide_true, Bool.not_true, Bool.false_or] at h2
  have h3 := List.all_eq_true.mp h2 c (List.mem_range.mpr hc)
  simp only [hbc, decide_true, Bool.not_true, Bool.false_or] at h3
  rintro ⟨p1, p2, p3⟩
  simp [p1, p2, p3] at h3

/-- and the script APPLIED, so the rig is not merely well typed -/
theorem toy_no_triangle : ¬ (e7 0 1 = true ∧ e7 0 2 = true ∧ e7 1 2 = true) :=
  extract7 e7 nest7_holds 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)

theorem msl_r55_extract_toy7_v2  : e7 0 1 = true := by decide
