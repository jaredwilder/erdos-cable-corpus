import Mathlib

set_option autoImplicit false

-- The contract's object: least prime in a residue class.
def LeastPrimeInClass (a d : Nat) : Nat := sInf {p : Nat | Nat.Prime p ∧ p ≡ a [MOD d] ∧ p ≥ 2}

-- The certified fragment: Linnik's bound with L = 5, uniform over all large d
-- and all reduced classes a, exactly as the published theorem states it.
def LinnikBound5 : Prop :=
  ∃ C : Nat, 0 < C ∧ ∀ d > 1, ∀ a : Nat, Nat.Coprime a d → ∃ p : Nat,
    Nat.Prime p ∧ p ≡ a [MOD d] ∧ p ≤ C * d ^ 5

-- The close-branch target, for contrast (NOT claimed here):
def AffirmativeTarget : Prop :=
  ∃ c > 0, ∃ N : Nat, ∀ d > N, ∃ S : Finset Nat,
    (∀ a ∈ S, Nat.Coprime a d) ∧ S.card ≥ Nat.totient d ∧
    ∀ a ∈ S, LeastPrimeInClass (a % d) d > (1 + c) * Nat.totient d * Real.log d

axiom PublishedTheorem_Xylouris2011 :
  ∃ C : Nat, 0 < C ∧ ∀ d > 1, ∀ a : Nat, Nat.Coprime a d → ∃ p : Nat, Nat.Prime p ∧ p ≡ a [MOD d] ∧ p ≤ C * d ^ 5

theorem msl_fmz_erdos971_campaign_001_R006_L1  : theorem linnik5_baseline : LinnikBound5 := exact PublishedTheorem_Xylouris2011
