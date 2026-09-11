import Mathlib

set_option autoImplicit false

def Valid (p : ℕ × ℕ) : Prop :=
  1 < p.1 ∧ 1 < p.2 ∧ Nat.gcd p.1 p.2 = 1 ∧
    (¬ p.1.Prime ∨ ¬ p.2.Prime)

def Adj (p q : ℕ × ℕ) : Prop :=
  (p.1 = q.1 ∧ (p.2 = q.2 + 1 ∨ q.2 = p.2 + 1)) ∨
  (p.2 = q.2 ∧ (p.1 = q.1 + 1 ∨ q.1 = p.1 + 1))

theorem msl_fmz_erdos1212_campaign_001_R006_L1  : Valid (2, 9) ∧ ∀ q : ℕ × ℕ, Adj (2, 9) q → ¬ Valid q := by
  constructor
  · norm_num [Valid]
  · intro q hq
    rcases hq with ⟨h₁, h₂ | h₂⟩ | ⟨h₁, h₂ | h₂⟩
    · have hq' : q = (2, 8) := by
        apply Prod.ext <;> omega
      subst q
      norm_num [Valid]
    · have hq' : q = (2, 10) := by
        apply Prod.ext <;> omega
      subst q
      norm_num [Valid]
    · have hq' : q = (1, 9) := by
        apply Prod.ext <;> omega
      subst q
      norm_num [Valid]
    · have hq' : q = (3, 9) := by
        apply Prod.ext <;> omega
      subst q
      norm_num [Valid]
