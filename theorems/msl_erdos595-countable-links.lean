import Mathlib

set_option autoImplicit false

open SimpleGraph in
def IsCUTF {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

theorem compCountable {W : Type} (T : SimpleGraph W) :
    (∀ v : W, (T.neighborSet v).Countable) → ∀ w : W, {x : W | T.Reachable w x}.Countable := by
  classical
  intro h w
  set B : ℕ → Set W := fun n => Nat.rec ({w} : Set W)
    (fun _ prev => prev ∪ ⋃ v ∈ prev, T.neighborSet v) n with hB
  have hBc : ∀ n, (B n).Countable := by
    intro n
    induction n with
    | zero => exact Set.countable_singleton w
    | succ k ih => exact ih.union (ih.biUnion (fun v _ => h v))
  have hstep : ∀ (c x : W), T.Adj c x → (∃ n, c ∈ B n) → ∃ n, x ∈ B n := by
    rintro c x hcx ⟨n, hn⟩
    exact ⟨n + 1, Or.inr (Set.mem_biUnion hn hcx)⟩
  have hrtg : ∀ x : W, Relation.ReflTransGen T.Adj w x → ∃ n, x ∈ B n := by
    intro x hx
    induction hx with
    | refl => exact ⟨0, rfl⟩
    | tail hprev hadj ih => exact hstep _ _ hadj ih
  refine Set.Countable.mono (fun x hx => ?_) (Set.countable_iUnion hBc)
  obtain ⟨n, hn⟩ := hrtg x ((SimpleGraph.reachable_iff_reflTransGen w x).mp hx)
  exact Set.mem_iUnion.2 ⟨n, hn⟩

theorem triAdj {V : Type} (G : SimpleGraph V) :
    (∃ c : Sym2 V → ℕ, ∀ a b d : V, G.Adj a b → G.Adj a d → G.Adj b d → c s(a, b) ≠ c s(a, d)) → IsCUTF G := by
  classical
  rintro ⟨c, hc⟩
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
    exact hc a b d e1.1.1 e2.1.1 e3.1.1 (by rw [e1.1.2, e2.1.2])
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

theorem msl_erdos595_countable_links {V : Type} (G : SimpleGraph V) (T : SimpleGraph (Sym2 V)) : (∀ a b d : V, G.Adj a b → G.Adj a d → G.Adj b d → s(a, b) ≠ s(a, d) → T.Adj s(a, b) s(a, d)) → (∀ e : Sym2 V, (T.neighborSet e).Countable) → IsCUTF G := by
  classical
  intro hT hloc
  have hcomp : ∀ q : T.ConnectedComponent,
      {x : Sym2 V | T.connectedComponentMk x = q}.Countable := by
    intro q
    obtain ⟨r, hr⟩ := Quot.exists_rep q
    have hset : {x : Sym2 V | T.connectedComponentMk x = q} = {x | T.Reachable r x} := by
      ext x
      constructor
      · intro hx
        have hxr : T.connectedComponentMk x = T.connectedComponentMk r := hx.trans hr.symm
        exact (SimpleGraph.ConnectedComponent.exact hxr).symm
      · intro hx
        have hxr : T.connectedComponentMk x = T.connectedComponentMk r :=
          SimpleGraph.ConnectedComponent.sound hx.symm
        exact hxr.trans hr
    rw [hset]
    exact compCountable T hloc r
  have hinj : ∀ q : T.ConnectedComponent,
      ∃ g : Sym2 V → ℕ, ∀ x y : Sym2 V, T.connectedComponentMk x = q →
        T.connectedComponentMk y = q → g x = g y → x = y := by
    intro q
    haveI : Countable {x : Sym2 V // T.connectedComponentMk x = q} := (hcomp q).to_subtype
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat {x : Sym2 V // T.connectedComponentMk x = q}
    refine ⟨fun x => if hx : T.connectedComponentMk x = q then f ⟨x, hx⟩ else 0, ?_⟩
    intro x y hx hy hxy
    simp only [dif_pos hx, dif_pos hy] at hxy
    exact congrArg Subtype.val (hf hxy)
  choose g hg using hinj
  refine triAdj G ⟨fun e => g (T.connectedComponentMk e) e, ?_⟩
  intro a b d hab had hbd hcon
  have hne : s(a, b) ≠ s(a, d) := by
    intro hEq
    rw [Sym2.eq_iff] at hEq
    rcases hEq with ⟨-, h2⟩ | ⟨h1, h2⟩
    · exact (G.ne_of_adj hbd) h2
    · exact (G.ne_of_adj hab) h2.symm
  have hadj : T.Adj s(a, b) s(a, d) := hT a b d hab had hbd hne
  have hsame : T.connectedComponentMk s(a, b) = T.connectedComponentMk s(a, d) :=
    SimpleGraph.ConnectedComponent.sound hadj.reachable
  refine hne (hg (T.connectedComponentMk s(a, b)) s(a, b) s(a, d) rfl hsame.symm ?_)
  simpa [hsame] using hcon
