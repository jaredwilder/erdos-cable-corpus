import Mathlib

set_option autoImplicit false

open SimpleGraph in
/-- `G` is a union of triangle-free subgraphs indexed by `I`. -/
def IsUTF {V : Type} (I : Type) (G : SimpleGraph V) : Prop :=
  ∃ H : I → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

theorem msl_erdos595_ordering_bound_general {V : Type} {I : Type} [LinearOrder V] (G : SimpleGraph V) : (∀ u : V, ∃ g : V → I, ∀ a b : V, u < a → u < b → G.Adj u a → G.Adj u b → G.Adj a b → g a ≠ g b) → IsUTF I G := by
  classical
  intro hnb
  choose g hg using hnb
  set F : V → V → I := fun a b => if a ≤ b then g a b else g b a with hF
  have hsymm : ∀ a b : V, F a b = F b a := by
    intro a b
    rcases eq_or_ne a b with rfl | hne
    · rfl
    · rcases le_total a b with h | h
      · have h2 : ¬ b ≤ a := fun hc => hne (le_antisymm h hc)
        simp [hF, h, h2]
      · have h2 : ¬ a ≤ b := fun hc => hne (le_antisymm hc h)
        simp [hF, h, h2]
  set c : Sym2 V → I := Sym2.lift ⟨F, hsymm⟩ with hc
  have hcval : ∀ a b : V, c s(a, b) = F a b := by intro a b; rfl
  have key : ∀ u x y : V, u ≤ x → u ≤ y → G.Adj u x → G.Adj u y → G.Adj x y →
      c s(u, x) = c s(u, y) → False := by
    intro u x y hux huy h1 h2 h3 heq
    rw [hcval, hcval, hF] at heq
    simp only [if_pos hux, if_pos huy] at heq
    have hlx : u < x := lt_of_le_of_ne hux (G.ne_of_adj h1)
    have hly : u < y := lt_of_le_of_ne huy (G.ne_of_adj h2)
    exact hg u x y hlx hly h1 h2 h3 heq
  refine ⟨fun n => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ c e = n}, ?_, ?_⟩
  · intro n t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    have e1 := hcl ha hb hab
    have e2 := hcl ha hd had
    have e3 := hcl hb hd hbd
    rw [SimpleGraph.fromEdgeSet_adj] at e1 e2 e3
    have g1 : G.Adj a b := e1.1.1
    have g2 : G.Adj a d := e2.1.1
    have g3 : G.Adj b d := e3.1.1
    have c1 : c s(a, b) = n := e1.1.2
    have c2 : c s(a, d) = n := e2.1.2
    have c3 : c s(b, d) = n := e3.1.2
    have swapDA : s(d, a) = s(a, d) := Sym2.eq_swap
    have swapDB : s(d, b) = s(b, d) := Sym2.eq_swap
    have swapBA : s(b, a) = s(a, b) := Sym2.eq_swap
    have kmin_a : a ≤ b → a ≤ d → False := fun h1' h2' =>
      key a b d h1' h2' g1 g2 g3 (by rw [c1, c2])
    have kmin_b : b ≤ a → b ≤ d → False := fun h1' h2' =>
      key b a d h1' h2' g1.symm g3 g2 (by rw [swapBA, c1, c3])
    have kmin_d : d ≤ a → d ≤ b → False := fun h1' h2' =>
      key d a b h1' h2' g2.symm g3.symm g1 (by rw [swapDA, swapDB, c2, c3])
    rcases le_total a b with hab' | hab'
    · rcases le_total a d with had' | had'
      · exact kmin_a hab' had'
      · exact kmin_d had' (le_trans had' hab')
    · rcases le_total b d with hbd' | hbd'
      · exact kmin_b hab' hbd'
      · exact kmin_d (le_trans hbd' hab') hbd'
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      exact ⟨c s(a, b), by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨hab, rfl⟩, G.ne_of_adj hab⟩⟩
    · rintro ⟨n, hn⟩
      rw [SimpleGraph.fromEdgeSet_adj] at hn
      exact hn.1.1
