import Mathlib

set_option autoImplicit false

open SimpleGraph in
def IsCUTF {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

theorem msl_erdos595_continuum_blindness {V : Type} (G : SimpleGraph V) (e : V → (ℕ → Bool)) : Function.Injective e → IsCUTF G := by
  classical
  intro he
  have hdiff : ∀ a b : V, G.Adj a b → ∃ n : ℕ, e a n ≠ e b n := by
    intro a b hab
    by_contra hcon
    push_neg at hcon
    exact (G.ne_of_adj hab) (he (funext hcon))
  refine ⟨fun n => SimpleGraph.fromRel (fun a b => ∃ h : G.Adj a b, Nat.find (hdiff a b h) = n), ?_, ?_⟩
  · intro n t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    have get : ∀ x y : V, (SimpleGraph.fromRel (fun a b => ∃ h : G.Adj a b, Nat.find (hdiff a b h) = n)).Adj x y →
        e x n ≠ e y n := by
      intro x y hxy
      rw [SimpleGraph.fromRel_adj] at hxy
      rcases hxy.2 with ⟨h, hn⟩ | ⟨h, hn⟩
      · have := Nat.find_spec (hdiff x y h)
        rw [hn] at this; exact this
      · have := Nat.find_spec (hdiff y x h)
        rw [hn] at this; exact fun hc => this hc.symm
    have d1 := get a b (hcl ha hb hab)
    have d2 := get a d (hcl ha hd had)
    have d3 := get b d (hcl hb hd hbd)
    rcases Bool.eq_false_or_eq_true (e a n) with h | h <;>
      rcases Bool.eq_false_or_eq_true (e b n) with h' | h' <;>
      rcases Bool.eq_false_or_eq_true (e d n) with h'' | h'' <;>
      simp_all
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      refine ⟨Nat.find (hdiff a b hab), ?_⟩
      rw [SimpleGraph.fromRel_adj]
      exact ⟨G.ne_of_adj hab, Or.inl ⟨hab, rfl⟩⟩
    · rintro ⟨n, hn⟩
      rw [SimpleGraph.fromRel_adj] at hn
      rcases hn.2 with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact h.symm
