import Mathlib

set_option autoImplicit false

open SimpleGraph in
def IsUTF {V : Type} (I : Type) (G : SimpleGraph V) : Prop :=
  ∃ H : I → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

theorem msl_erdos595_top_vertex_bound {V I : Type} [LinearOrder V] (G : SimpleGraph V) (f : V → I) : (∀ x y z : V, x < y → y < z → G.Adj x y → G.Adj x z → G.Adj y z → f y ≠ f z) → IsUTF I G := by
  classical
  intro htop
  set F : V → V → I := fun a b => if a ≤ b then f b else f a with hF
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
  refine ⟨fun p => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ c e = p}, ?_, ?_⟩
  · intro p t ht
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
    have c1 : c s(a, b) = p := e1.1.2
    have c2 : c s(a, d) = p := e2.1.2
    have c3 : c s(b, d) = p := e3.1.2
    have key : ∀ x y z : V, x ≤ y → y ≤ z → G.Adj x y → G.Adj x z → G.Adj y z →
        c s(x, z) = c s(y, z) → c s(x, y) = c s(x, z) → False := by
      intro x y z hxy hyz gxy gxz gyz h1 h2
      have hxz : x ≤ z := le_trans hxy hyz
      have v1 : c s(x, y) = f y := by rw [hcval, hF]; simp [hxy]
      have v2 : c s(x, z) = f z := by rw [hcval, hF]; simp [hxz]
      have hne : y ≠ z := G.ne_of_adj gyz
      have hlt : y < z := lt_of_le_of_ne hyz hne
      have hltx : x < y := lt_of_le_of_ne hxy (G.ne_of_adj gxy)
      exact htop x y z hltx hlt gxy gxz gyz (by rw [← v1, ← v2, h2])
    rcases le_total a b with hab' | hab'
    · rcases le_total b d with hbd' | hbd'
      · exact key a b d hab' hbd' g1 g2 g3 (by rw [c2, c3]) (by rw [c1, c2])
      · rcases le_total a d with had' | had'
        · exact key a d b had' hbd' g2 g1 g3.symm (by rw [c1, Sym2.eq_swap (a := d), c3]) (by rw [c2, c1])
        · exact key d a b had' hab' g2.symm g3.symm g1
            (by rw [Sym2.eq_swap (a := d), c3, c1]) (by rw [Sym2.eq_swap (a := d), c2, Sym2.eq_swap (a := d), c3])
    · rcases le_total a d with had' | had'
      · exact key b a d hab' had' g1.symm g3 g2 (by rw [c3, c2]) (by rw [Sym2.eq_swap (a := b), c1, c3])
      · rcases le_total b d with hbd' | hbd'
        · exact key b d a hbd' had' g3 g1.symm g2.symm
            (by rw [Sym2.eq_swap (a := b), c1, Sym2.eq_swap (a := d), c2]) (by rw [c3, Sym2.eq_swap (a := b), c1])
        · exact key d b a hbd' hab' g3.symm g2.symm g1.symm
            (by rw [Sym2.eq_swap (a := d), c2, Sym2.eq_swap (a := b), c1]) (by rw [Sym2.eq_swap (a := d), c3, Sym2.eq_swap (a := d), c2])
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      exact ⟨c s(a, b), by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨hab, rfl⟩, G.ne_of_adj hab⟩⟩
    · rintro ⟨p, hp⟩
      rw [SimpleGraph.fromEdgeSet_adj] at hp
      exact hp.1.1
