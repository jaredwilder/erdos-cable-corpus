import Mathlib

set_option autoImplicit false

open SimpleGraph in
def IsUTF {V : Type} (I : Type) (G : SimpleGraph V) : Prop :=
  ∃ H : I → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

theorem properBinary {V I : Type} (G : SimpleGraph V) (e : V → (I → Bool)) :
    (∀ a b : V, G.Adj a b → e a ≠ e b) → IsUTF I G := by
  classical
  intro he
  have hdiff : ∀ a b : V, G.Adj a b → ∃ i : I, e a i ≠ e b i := by
    intro a b hab
    by_contra hcon
    push_neg at hcon
    exact he a b hab (funext hcon)
  choose ch hch using hdiff
  refine ⟨fun i => SimpleGraph.fromRel (fun a b => ∃ h : G.Adj a b, ch a b h = i), ?_, ?_⟩
  · intro i t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    have get : ∀ x y : V,
        (SimpleGraph.fromRel (fun a b => ∃ h : G.Adj a b, ch a b h = i)).Adj x y →
        e x i ≠ e y i := by
      intro x y hxy
      rw [SimpleGraph.fromRel_adj] at hxy
      rcases hxy.2 with ⟨h, hn⟩ | ⟨h, hn⟩
      · have hs := hch x y h
        rw [hn] at hs
        exact hs
      · have hs := hch y x h
        rw [hn] at hs
        exact fun hc => hs hc.symm
    have d1 := get a b (hcl ha hb hab)
    have d2 := get a d (hcl ha hd had)
    have d3 := get b d (hcl hb hd hbd)
    rcases Bool.eq_false_or_eq_true (e a i) with h | h <;>
      rcases Bool.eq_false_or_eq_true (e b i) with h' | h' <;>
      rcases Bool.eq_false_or_eq_true (e d i) with h'' | h'' <;>
      simp_all
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      refine ⟨ch a b hab, ?_⟩
      rw [SimpleGraph.fromRel_adj]
      exact ⟨G.ne_of_adj hab, Or.inl ⟨hab, rfl⟩⟩
    · rintro ⟨i, hi⟩
      rw [SimpleGraph.fromRel_adj] at hi
      rcases hi.2 with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact h.symm

theorem msl_erdos595_colour_interface {V I C : Type} (G : SimpleGraph V) (f : V → C) (g : C → (I → Bool)) : (∀ a b : V, G.Adj a b → f a ≠ f b) → Function.Injective g → IsUTF I G := by
  intro hf hg
  refine properBinary G (fun v => g (f v)) ?_
  intro a b hab hcon
  exact hf a b hab (hg hcon)
