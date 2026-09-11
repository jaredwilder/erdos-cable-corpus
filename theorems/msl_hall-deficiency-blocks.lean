import Mathlib

set_option autoImplicit false

/-- A witness set `S` is *deficient* for neighborhood map `t` when the union of
    neighborhoods of `S` is strictly smaller than `S` itself. -/
def Deficient {ι α : Type*} [DecidableEq α] (t : ι → Finset α) (S : Finset ι) : Prop :=
  (S.biUnion t).card < S.card

theorem msl_hall_deficiency_blocks  : ∀ {iota : Type*} {alpha : Type*}, ∀ [inst : DecidableEq alpha],
  ∀ (t : iota → Finset alpha) (S : Finset iota),
    Deficient t S →
    ¬ (∃ f : iota → alpha, Set.InjOn f (S : Set iota) ∧ (∀ i, i ∈ S → f i ∈ t i)) := by
  intro iota alpha inst t S hdef
  rintro ⟨f, hinj, hmem⟩
  have hsub : S.image f ⊆ S.biUnion t := by
    intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    exact Finset.mem_biUnion.mpr ⟨i, hi, hmem i hi⟩
  have hcard : (S.image f).card = S.card := Finset.card_image_of_injOn hinj
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  exact absurd hle (Nat.not_le.mpr hdef)
