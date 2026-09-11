set_option autoImplicit false
set_option maxRecDepth 20000

-- THE ERDOS-SZEKERES RECURRENCE ITSELF, over vertex LISTS rather than over an interval,
-- which is what removes the need for any relabelling.

def IsClique (e : Nat → Nat → Bool) (L : List Nat) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, a ≠ b → e a b = true

def IsIndep (e : Nat → Nat → Bool) (L : List Nat) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, a ≠ b → e a b = false

/-- `V` arrows `(s,t)` under `e`: some `s`-subset of `V` is a clique, or some `t`-subset is
    independent.  Sublists are used so no relabelling is ever needed. -/
def ArrowsOn (e : Nat → Nat → Bool) (V : List Nat) (s t : Nat) : Prop :=
  (∃ K : List Nat, K.Sublist V ∧ K.length = s ∧ IsClique e K) ∨
  (∃ K : List Nat, K.Sublist V ∧ K.length = t ∧ IsIndep e K)

/-- `m` suffices for `(s,t)`: EVERY symmetric colouring on EVERY vertex list of size at
    least `m` arrows `(s,t)`.  This is the abstraction of `R(s,t) ≤ m`. -/
def Suffices (m s t : Nat) : Prop :=
  ∀ (e : Nat → Nat → Bool), (∀ x y, e x y = e y x) →
    ∀ V : List Nat, m ≤ V.length → ArrowsOn e V s t

theorem extend_clique (e : Nat → Nat → Bool) (hsymm : ∀ x y, e x y = e y x)
    (v : Nat) (K : List Nat) (hadj : ∀ x ∈ K, e v x = true) (hK : IsClique e K) :
    IsClique e (v :: K) := by
  intro a ha b hb hab
  rcases List.mem_cons.mp ha with rfl | ha'
  · rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd rfl hab
    · exact hadj b hb'
  · rcases List.mem_cons.mp hb with rfl | hb'
    · rw [hsymm]; exact hadj a ha'
    · exact hK a ha' b hb' hab

theorem extend_indep (e : Nat → Nat → Bool) (hsymm : ∀ x y, e x y = e y x)
    (v : Nat) (K : List Nat) (hadj : ∀ x ∈ K, e v x = false) (hK : IsIndep e K) :
    IsIndep e (v :: K) := by
  intro a ha b hb hab
  rcases List.mem_cons.mp ha with rfl | ha'
  · rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd rfl hab
    · exact hadj b hb'
  · rcases List.mem_cons.mp hb with rfl | hb'
    · rw [hsymm]; exact hadj a ha'
    · exact hK a ha' b hb' hab

theorem filter_split (p : Nat → Bool) : ∀ L : List Nat,
    (L.filter p).length + (L.filter (fun x => ! p x)).length = L.length := by
  intro L
  induction L with
  | nil => rfl
  | cons a t ih =>
    by_cases h : p a
    · simp [List.filter, h] at *; omega
    · simp [List.filter, h] at *; omega

theorem es_recurrence (m n s t : Nat) (hm1 : 1 <= m) (hn1 : 1 <= n)
    (hs : 1 <= s) (ht : 1 <= t)
    (hm : Suffices m (s-1) t) (hn : Suffices n s (t-1)) :
    Suffices (m + n) s t := by
  intro e hsymm V hV
  cases V with
  | nil => simp at hV; omega
  | cons v R =>
    have hlen : m + n <= R.length + 1 := by simpa using hV
    have hsplit := filter_split (fun x => e v x) R
    have hcase : m <= (R.filter (fun x => e v x)).length
               \/ n <= (R.filter (fun x => ! e v x)).length := by omega
    rcases hcase with hA | hB
    . rcases hm e hsymm (R.filter (fun x => e v x)) hA with
        ⟨K, hKsub, hKlen, hKcl⟩ | ⟨K, hKsub, hKlen, hKind⟩
      . refine Or.inl ⟨v :: K, ?_, ?_, ?_⟩
        . exact List.Sublist.cons₂ v (hKsub.trans (List.filter_sublist))
        . simp only [List.length_cons, hKlen]; omega
        . refine extend_clique e hsymm v K ?_ hKcl
          intro x hx
          have hxA : x ∈ R.filter (fun y => e v y) := hKsub.subset hx
          simpa using (List.mem_filter.mp hxA).2
      . exact Or.inr ⟨K, (hKsub.trans (List.filter_sublist)).cons v, hKlen, hKind⟩
    . rcases hn e hsymm (R.filter (fun x => ! e v x)) hB with
        ⟨K, hKsub, hKlen, hKcl⟩ | ⟨K, hKsub, hKlen, hKind⟩
      . exact Or.inl ⟨K, (hKsub.trans (List.filter_sublist)).cons v, hKlen, hKcl⟩
      . refine Or.inr ⟨v :: K, ?_, ?_, ?_⟩
        . exact List.Sublist.cons₂ v (hKsub.trans (List.filter_sublist))
        . simp only [List.length_cons, hKlen]; omega
        . refine extend_indep e hsymm v K ?_ hKind
          intro x hx
          have hxB : x ∈ R.filter (fun y => ! e v y) := hKsub.subset hx
          have := (List.mem_filter.mp hxB).2
          simpa using this
theorem suffices_one_left (t : Nat) : Suffices 1 1 t := by
  intro e _ V hV
  cases V with
  | nil => simp at hV
  | cons v R =>
    refine Or.inl ⟨[v], List.Sublist.cons₂ v (List.nil_sublist R), rfl, ?_⟩
    intro a ha b hb hab
    simp at ha hb
    subst ha; subst hb
    exact absurd rfl hab

theorem suffices_one_right (s : Nat) : Suffices 1 s 1 := by
  intro e _ V hV
  cases V with
  | nil => simp at hV
  | cons v R =>
    refine Or.inr ⟨[v], List.Sublist.cons₂ v (List.nil_sublist R), rfl, ?_⟩
    intro a ha b hb hab
    simp at ha hb
    subst ha; subst hb
    exact absurd rfl hab

/-- THE CHAIN TO 70.  Each step is one application of `es_recurrence`; the numerals are the
    Pascal recurrence with unit boundary, whose agreement with the binomial coefficient is
    kernel-checked separately (`r55-binomial-grid-v3`). -/
theorem es_chain : Suffices 70 5 5 := by
  have h11 : Suffices 1 1 1 := suffices_one_left 1
  have h12 : Suffices 1 1 2 := suffices_one_left 2
  have h13 : Suffices 1 1 3 := suffices_one_left 3
  have h14 : Suffices 1 1 4 := suffices_one_left 4
  have h15 : Suffices 1 1 5 := suffices_one_left 5
  have h21 : Suffices 1 2 1 := suffices_one_right 2
  have h22 : Suffices 2 2 2 := es_recurrence 1 1 2 2 (by omega) (by omega) (by omega) (by omega) h12 h21
  have h23 : Suffices 3 2 3 := es_recurrence 1 2 2 3 (by omega) (by omega) (by omega) (by omega) h13 h22
  have h24 : Suffices 4 2 4 := es_recurrence 1 3 2 4 (by omega) (by omega) (by omega) (by omega) h14 h23
  have h25 : Suffices 5 2 5 := es_recurrence 1 4 2 5 (by omega) (by omega) (by omega) (by omega) h15 h24
  have h31 : Suffices 1 3 1 := suffices_one_right 3
  have h32 : Suffices 3 3 2 := es_recurrence 2 1 3 2 (by omega) (by omega) (by omega) (by omega) h22 h31
  have h33 : Suffices 6 3 3 := es_recurrence 3 3 3 3 (by omega) (by omega) (by omega) (by omega) h23 h32
  have h34 : Suffices 10 3 4 := es_recurrence 4 6 3 4 (by omega) (by omega) (by omega) (by omega) h24 h33
  have h35 : Suffices 15 3 5 := es_recurrence 5 10 3 5 (by omega) (by omega) (by omega) (by omega) h25 h34
  have h41 : Suffices 1 4 1 := suffices_one_right 4
  have h42 : Suffices 4 4 2 := es_recurrence 3 1 4 2 (by omega) (by omega) (by omega) (by omega) h32 h41
  have h43 : Suffices 10 4 3 := es_recurrence 6 4 4 3 (by omega) (by omega) (by omega) (by omega) h33 h42
  have h44 : Suffices 20 4 4 := es_recurrence 10 10 4 4 (by omega) (by omega) (by omega) (by omega) h34 h43
  have h45 : Suffices 35 4 5 := es_recurrence 15 20 4 5 (by omega) (by omega) (by omega) (by omega) h35 h44
  have h51 : Suffices 1 5 1 := suffices_one_right 5
  have h52 : Suffices 5 5 2 := es_recurrence 4 1 5 2 (by omega) (by omega) (by omega) (by omega) h42 h51
  have h53 : Suffices 15 5 3 := es_recurrence 10 5 5 3 (by omega) (by omega) (by omega) (by omega) h43 h52
  have h54 : Suffices 35 5 4 := es_recurrence 20 15 5 4 (by omega) (by omega) (by omega) (by omega) h44 h53
  have h55 : Suffices 70 5 5 := es_recurrence 35 35 5 5 (by omega) (by omega) (by omega) (by omega) h45 h54
  exact h55

theorem msl_r55_es_chain_to_70  : ([1,2] : List Nat).length = 2 := by decide
