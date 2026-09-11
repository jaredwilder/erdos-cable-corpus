import Mathlib

set_option autoImplicit false

def TotalOn400 (f : ℕ → ℕ) : Prop := ∀ q, q.Prime → q ≤ 400 → ∃ n, f q = n

def MatchesAnchors (f : ℕ → ℕ) : Prop := f 13 = 2 ∧ f 37 = 3 ∧ f 73 = 4

def L1Statement : Prop := ∃ f1 f2 : ℕ → ℕ, TotalOn400 f1 ∧ TotalOn400 f2 ∧ MatchesAnchors f1 ∧ MatchesAnchors f2 ∧ f1 2 ≠ f2 2

theorem msl_fmz_erdos1055_campaign_001_R011_L1_a1r1  : L1Statement := by
  let f1 : ℕ → ℕ := fun p => if p = 13 then 2 else if p = 37 then 3 else if p = 73 then 4 else 0
  let f2 : ℕ → ℕ := fun p => if p = 13 then 2 else if p = 37 then 3 else if p = 73 then 4 else 500 + p
  refine ⟨f1, f2, ?_⟩
  have htotal1 : TotalOn400 f1 := by
    intro q hq hq400
    exact ⟨f1 q, rfl⟩
  have htotal2 : TotalOn400 f2 := by
    intro q hq hq400
    exact ⟨f2 q, rfl⟩
  have hmatch1 : MatchesAnchors f1 := by
    dsimp [MatchesAnchors, f1]
    norm_num
  have hmatch2 : MatchesAnchors f2 := by
    dsimp [MatchesAnchors, f2]
    norm_num
  have hdiff : f1 2 ≠ f2 2 := by
    dsimp [f1, f2]
    norm_num
  exact ⟨htotal1, htotal2, hmatch1, hmatch2, hdiff⟩
