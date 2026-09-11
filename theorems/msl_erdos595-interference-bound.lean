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

theorem msl_erdos595_interference_bound {V I J : Type} (G : SimpleGraph V) (D : I → V) (col : I → J) : G.CliqueFree 4 → (∀ x : V, ∃ i : I, x = D i ∨ G.Adj (D i) x) → (∀ i j : I, col i = col j → i ≠ j → ∀ x y : V, (x = D i ∨ G.Adj (D i) x) → (y = D j ∨ G.Adj (D j) y) → ¬ G.Adj x y) → IsUTF (Sym2 (J × Bool)) G := by
  classical
  intro hK4 hdom hsep
  choose n hspec using hdom
  refine partitionBound G (fun x => (col (n x), decide (x = D (n x)))) ?_
  intro a b d h1 h2 g1 g2 g3
  have hc1 : col (n a) = col (n b) := congrArg Prod.fst h1
  have hc2 : col (n b) = col (n d) := congrArg Prod.fst h2
  have hnab : n a = n b := by
    by_contra hne
    exact hsep (n a) (n b) hc1 hne a b (hspec a) (hspec b) g1
  have hnbd : n b = n d := by
    by_contra hne
    exact hsep (n b) (n d) hc2 hne b d (hspec b) (hspec d) g3
  have hnad : n a = n d := hnab.trans hnbd
  have hb1 : decide (a = D (n a)) = decide (b = D (n b)) := congrArg Prod.snd h1
  have hb2 : decide (b = D (n b)) = decide (d = D (n d)) := congrArg Prod.snd h2
  by_cases ha : a = D (n a)
  · have hb : b = D (n b) := by
      by_contra hbb
      rw [decide_eq_true ha, decide_eq_false hbb] at hb1
      exact Bool.noConfusion hb1
    exact (G.ne_of_adj g1) (ha.trans (by rw [hnab]; exact hb.symm))
  · have hb : ¬ b = D (n b) := by
      intro hbb
      have := hb1.symm
      rw [decide_eq_true hbb, decide_eq_false ha] at this
      exact Bool.noConfusion this
    have hd : ¬ d = D (n d) := by
      intro hdd
      rw [decide_eq_true hdd, decide_eq_false hb] at hb2
      exact Bool.noConfusion hb2
    have ea : G.Adj (D (n a)) a := (hspec a).resolve_left ha
    have eb : G.Adj (D (n a)) b := by rw [hnab]; exact (hspec b).resolve_left hb
    have ed : G.Adj (D (n a)) d := by rw [hnad]; exact (hspec d).resolve_left hd
    refine hK4 (insert (D (n a)) {a, b, d})
      ((SimpleGraph.is3Clique_triple_iff.mpr ⟨g1, g2, g3⟩).insert ?_)
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ea
    · exact eb
    · exact ed
