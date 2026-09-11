import Mathlib

set_option autoImplicit false

open SimpleGraph in
def IsCUTF {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

theorem msl_erdos595_countable_lower_neighbourhood {V : Type} [LinearOrder V] (G : SimpleGraph V) : (∀ u : V, Set.Countable {w : V | G.Adj u w ∧ w < u}) → IsCUTF G := by
  classical
  intro hcount
  have hcol : ∀ u : V, ∃ g : V → ℕ, ∀ a b : V, a < u → b < u → G.Adj u a → G.Adj u b →
      G.Adj a b → g a ≠ g b := by
    intro u
    haveI : Countable {w : V // G.Adj u w ∧ w < u} := (hcount u).to_subtype
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat {w : V // G.Adj u w ∧ w < u}
    refine ⟨fun x => if hx : G.Adj u x ∧ x < u then f ⟨x, hx⟩ else 0, ?_⟩
    intro a b hau hbu hua hub hab
    simp only [dif_pos (⟨hua, hau⟩ : G.Adj u a ∧ a < u),
      dif_pos (⟨hub, hbu⟩ : G.Adj u b ∧ b < u)]
    exact fun hc => G.ne_of_adj hab (congrArg Subtype.val (hf hc))
  choose g hg using hcol
  set F : V → V → ℕ := fun a b => if a ≤ b then g b a else g a b with hF
  have hsymm : ∀ a b : V, F a b = F b a := by
    intro a b
    rcases eq_or_ne a b with rfl | hne
    · rfl
    · rcases le_total a b with h | h
      · have h2 : ¬ b ≤ a := fun hc => hne (le_antisymm h hc)
        simp [hF, h, h2]
      · have h2 : ¬ a ≤ b := fun hc => hne (le_antisymm hc h)
        simp [hF, h, h2]
  set c : Sym2 V → ℕ := Sym2.lift ⟨F, hsymm⟩ with hc
  have hcval : ∀ a b : V, c s(a, b) = F a b := by intro a b; rfl
  have key : ∀ u x y : V, x ≤ u → y ≤ u → G.Adj u x → G.Adj u y → G.Adj x y →
      c s(x, u) = c s(y, u) → False := by
    intro u x y hxu hyu h1 h2 h3 heq
    rw [hcval, hcval, hF] at heq
    simp only [if_pos hxu, if_pos hyu] at heq
    exact hg u x y (lt_of_le_of_ne hxu (G.ne_of_adj h1).symm)
      (lt_of_le_of_ne hyu (G.ne_of_adj h2).symm) h1 h2 h3 heq
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
    have swapAB : s(a, b) = s(b, a) := Sym2.eq_swap
    have swapAD : s(a, d) = s(d, a) := Sym2.eq_swap
    have swapBD : s(b, d) = s(d, b) := Sym2.eq_swap
    have kmax_a : b ≤ a → d ≤ a → False := fun h1' h2' =>
      key a b d h1' h2' g1 g2 g3 (by rw [← swapAB, c1, ← swapAD, c2])
    have kmax_b : a ≤ b → d ≤ b → False := fun h1' h2' =>
      key b a d h1' h2' g1.symm g3 g2 (by rw [c1, ← swapBD, c3])
    have kmax_d : a ≤ d → b ≤ d → False := fun h1' h2' =>
      key d a b h1' h2' g2.symm g3.symm g1 (by rw [c2, c3])
    rcases le_total a b with hab' | hab'
    · rcases le_total b d with hbd' | hbd'
      · exact kmax_d (le_trans hab' hbd') hbd'
      · exact kmax_b hab' hbd'
    · rcases le_total a d with had' | had'
      · exact kmax_d had' (le_trans hab' had')
      · exact kmax_a hab' had'
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
