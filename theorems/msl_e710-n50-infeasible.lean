import Mathlib

set_option autoImplicit false

def Deficient {iota alpha : Type*} [DecidableEq alpha] (tt : iota → Finset alpha)
    (S : Finset iota) : Prop := (S.biUnion tt).card < S.card

theorem hall_deficiency_blocks {iota alpha : Type*} [DecidableEq alpha]
    (tt : iota → Finset alpha) (S : Finset iota) (hdef : Deficient tt S) :
    ¬ (∃ f : iota → alpha, Set.InjOn f (S : Set iota)
        ∧ (∀ i, i ∈ S → f i ∈ tt i)) := by
  rintro ⟨f, hinj, hmem⟩
  have hsub : S.image f ⊆ S.biUnion tt := by
    intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    exact Finset.mem_biUnion.mpr ⟨i, hi, hmem i hi⟩
  have hcard : (S.image f).card = S.card := Finset.card_image_of_injOn hinj
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  exact absurd hle (Nat.not_le.mpr hdef)

/-- The divisibility neighborhood: integers ∈ the open interval (n, n+L) that k divides. -/
def divNbhd (n L k : Nat) : Finset Nat := (Finset.Ioo n (n + L)).filter (fun v => k ∣ v)

/-- Corollary about Erdos 710: a deficient index set blocks every valid assignment
    (each index k mapped injectively to a multiple of k inside the open interval). -/
theorem e710_infeasible (n L : Nat) (S : Finset Nat) (hdef : Deficient (divNbhd n L) S) :
    ¬ (∃ a : Nat → Nat, Set.InjOn a (S : Set Nat)
        ∧ (∀ k, k ∈ S → a k ∈ divNbhd n L k)) :=
  hall_deficiency_blocks (divNbhd n L) S hdef

theorem msl_e710_n50_infeasible  : ¬ (∃ a : Nat → Nat, Set.InjOn a (({12, 20, 24, 30, 36, 40, 42, 45, 48, 50} : Finset Nat) : Set Nat) ∧ (∀ k, k ∈ ({12, 20, 24, 30, 36, 40, 42, 45, 48, 50} : Finset Nat) → a k ∈ divNbhd 50 75 k)) := by
  apply e710_infeasible
  unfold Deficient divNbhd
  decide
