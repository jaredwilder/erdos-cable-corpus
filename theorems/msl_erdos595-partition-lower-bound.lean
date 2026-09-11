import Mathlib

set_option autoImplicit false

open SimpleGraph in
def IsUTF {V : Type} (I : Type) (G : SimpleGraph V) : Prop :=
  ∃ H : I → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

theorem partitionBound {V I : Type} (G : SimpleGraph V) (rho : V → I) :
    (∀ a b d : V, rho a = rho b → rho b = rho d → G.Adj a b → G.Adj a d → G.Adj b d → False) → IsUTF (Sym2 I) G := by
  classical
  intro h
  have key : ∀ x y z : I, s(x, y) = s(x, z) → s(x, z) = s(y, z) → x = y ∧ y = z := by
    intro x y z h1 h2
    rcases Sym2.eq_iff.mp h1 with ⟨-, hyz⟩ | ⟨hxz, hyx⟩
    · rcases Sym2.eq_iff.mp h2 with ⟨hxy, -⟩ | ⟨hxz', hzy⟩
      · exact ⟨hxy, hyz⟩
      · exact ⟨hxz'.trans hzy, hyz⟩
    · exact ⟨hyx.symm, hyx.trans hxz⟩
  refine ⟨fun p => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ Sym2.map rho e = p}, ?_, ?_⟩
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
    have q1 : s(rho a, rho b) = s(rho a, rho d) := by
      have t1 : Sym2.map rho s(a, b) = p := e1.1.2
      have t2 : Sym2.map rho s(a, d) = p := e2.1.2
      simpa [Sym2.map_pair_eq] using t1.trans t2.symm
    have q2 : s(rho a, rho d) = s(rho b, rho d) := by
      have t2 : Sym2.map rho s(a, d) = p := e2.1.2
      have t3 : Sym2.map rho s(b, d) = p := e3.1.2
      simpa [Sym2.map_pair_eq] using t2.trans t3.symm
    obtain ⟨hx, hy⟩ := key (rho a) (rho b) (rho d) q1 q2
    exact h a b d hx hy e1.1.1 e2.1.1 e3.1.1
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      exact ⟨Sym2.map rho s(a, b), by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨hab, rfl⟩, G.ne_of_adj hab⟩⟩
    · rintro ⟨p, hp⟩
      rw [SimpleGraph.fromEdgeSet_adj] at hp
      exact hp.1.1

theorem msl_erdos595_partition_lower_bound {V I : Type} (G : SimpleGraph V) : ¬ IsUTF (Sym2 I) G → ¬ ∃ rho : V → I, ∀ a b d : V, rho a = rho b → rho b = rho d → G.Adj a b → G.Adj a d → G.Adj b d → False := by
  intro hnot hex
  obtain ⟨rho, hrho⟩ := hex
  exact hnot (partitionBound G rho hrho)
