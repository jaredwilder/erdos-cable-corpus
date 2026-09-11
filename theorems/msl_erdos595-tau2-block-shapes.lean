import Mathlib

set_option autoImplicit false

open SimpleGraph in
def IsUTF' {V : Type} (I : Type) (G : SimpleGraph V) : Prop :=
  ∃ H : I → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

open SimpleGraph in
def starAt {V : Type} (G : SimpleGraph V) (v : V) : SimpleGraph V :=
  G ⊓ SimpleGraph.fromRel (fun x y => x = v ∨ y = v)

open SimpleGraph in
theorem starAt_cliqueFree {V : Type} (G : SimpleGraph V) (v : V) :
    (starAt G v).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨hcl, hcard⟩ := ht
  obtain ⟨x, y, z, hxy, hxz, hyz, hteq⟩ := Finset.card_eq_three.mp hcard
  have hx : x ∈ t := by rw [hteq]; simp
  have hy : y ∈ t := by rw [hteq]; simp
  have hz : z ∈ t := by rw [hteq]; simp
  have mem : ∀ p q : V, p ∈ t → q ∈ t → p ≠ q → p = v ∨ q = v := by
    intro p q hp hq hpq
    have hadj := hcl hp hq hpq
    rw [starAt, SimpleGraph.inf_adj, SimpleGraph.fromRel_adj] at hadj
    exact hadj.2.2.elim id Or.symm
  have h1 := mem x y hx hy hxy
  have h2 := mem x z hx hz hxz
  have h3 := mem y z hy hz hyz
  rcases h1 with e1 | e1
  · rcases h3 with e3 | e3
    · exact hxy (e1.trans e3.symm)
    · exact hxz (e1.trans e3.symm)
  · rcases h2 with e2 | e2
    · exact hxy (e2.trans e1.symm)
    · exact hyz (e1.trans e2.symm)

open SimpleGraph in
theorem bool_proper_cliqueFree {V : Type} (G : SimpleGraph V) (f : V → Bool)
    (hf : ∀ x y : V, G.Adj x y → f x ≠ f y) : G.CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨hcl, hcard⟩ := ht
  obtain ⟨x, y, z, hxy, hxz, hyz, hteq⟩ := Finset.card_eq_three.mp hcard
  have hx : x ∈ t := by rw [hteq]; simp
  have hy : y ∈ t := by rw [hteq]; simp
  have hz : z ∈ t := by rw [hteq]; simp
  have a1 := hf x y (hcl hx hy hxy)
  have a2 := hf x z (hcl hx hz hxz)
  have a3 := hf y z (hcl hy hz hyz)
  cases hfx : f x <;> cases hfy : f y <;> cases hfz : f z <;> simp_all

theorem msl_erdos595_tau2_block_shapes {V : Type} (G : SimpleGraph V) (h : (∃ f : V → Bool, ∀ x y : V, G.Adj x y → f x ≠ f y) ∨ (∃ a b : V, ∀ x y : V, G.Adj x y → x = a ∨ y = a ∨ x = b ∨ y = b)) : IsUTF' Bool G := by
  classical
  rcases h with ⟨f, hf⟩ | ⟨a, b, hab⟩
  · refine ⟨fun _ => G, fun _ => bool_proper_cliqueFree G f hf, ?_⟩
    simp
  · refine ⟨fun i : Bool => starAt G (cond i a b), fun i => starAt_cliqueFree G _, ?_⟩
    ext x y
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hxy
      have hne : x ≠ y := G.ne_of_adj hxy
      rcases hab x y hxy with e | e | e | e
      · refine ⟨true, ?_⟩
        show (starAt G a).Adj x y
        rw [starAt, SimpleGraph.inf_adj, SimpleGraph.fromRel_adj]
        exact ⟨hxy, hne, by tauto⟩
      · refine ⟨true, ?_⟩
        show (starAt G a).Adj x y
        rw [starAt, SimpleGraph.inf_adj, SimpleGraph.fromRel_adj]
        exact ⟨hxy, hne, by tauto⟩
      · refine ⟨false, ?_⟩
        show (starAt G b).Adj x y
        rw [starAt, SimpleGraph.inf_adj, SimpleGraph.fromRel_adj]
        exact ⟨hxy, hne, by tauto⟩
      · refine ⟨false, ?_⟩
        show (starAt G b).Adj x y
        rw [starAt, SimpleGraph.inf_adj, SimpleGraph.fromRel_adj]
        exact ⟨hxy, hne, by tauto⟩
    · rintro ⟨i, hi⟩
      have hh : (starAt G (cond i a b)).Adj x y := hi
      rw [starAt, SimpleGraph.inf_adj] at hh
      exact hh.1
