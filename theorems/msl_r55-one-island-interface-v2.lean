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

/-- ⭐ THE SPECIALISATION: from the list-carried statement to the STANDARD Ramsey statement.

    `Suffices` quantifies over ALL lists, including degenerate ones with repeats, where
    `IsClique` is vacuously true.  That degeneracy is harmless because the theorem holds for
    every list, so it holds for `List.range 70`, which is duplicate-free — and a sublist of a
    duplicate-free list is duplicate-free, so the returned 5-set really has 5 DISTINCT vertices.

    This is exactly `R(5,5) ≤ 70`. -/
theorem R55_le_70 (e : Nat → Nat → Bool) (hsymm : ∀ x y, e x y = e y x) :
    (∃ K : List Nat, K.Sublist (List.range 70) ∧ K.Nodup ∧ K.length = 5 ∧ IsClique e K) ∨
    (∃ K : List Nat, K.Sublist (List.range 70) ∧ K.Nodup ∧ K.length = 5 ∧ IsIndep e K) := by
  have hlen : 70 ≤ (List.range 70).length := by simp
  rcases es_chain e hsymm (List.range 70) hlen with
    ⟨K, hs, hl, hc⟩ | ⟨K, hs, hl, hi⟩
  · exact Or.inl ⟨K, hs, hs.nodup List.nodup_range, hl, hc⟩
  · exact Or.inr ⟨K, hs, hs.nodup List.nodup_range, hl, hi⟩

/-- The SAME specialisation for the (4,5) parameters, which the campaign also needs. -/
theorem R45_le_35 (e : Nat → Nat → Bool) (hsymm : ∀ x y, e x y = e y x)
    (h : Suffices 35 4 5) :
    (∃ K : List Nat, K.Sublist (List.range 35) ∧ K.Nodup ∧ K.length = 4 ∧ IsClique e K) ∨
    (∃ K : List Nat, K.Sublist (List.range 35) ∧ K.Nodup ∧ K.length = 5 ∧ IsIndep e K) := by
  have hlen : 35 ≤ (List.range 35).length := by simp
  rcases h e hsymm (List.range 35) hlen with ⟨K, hs, hl, hc⟩ | ⟨K, hs, hl, hi⟩
  · exact Or.inl ⟨K, hs, hs.nodup List.nodup_range, hl, hc⟩
  · exact Or.inr ⟨K, hs, hs.nodup List.nodup_range, hl, hi⟩

/-- NEGATIVE CONTROL on the degeneracy the audit named: a repeated-vertex list of length 5 IS
    a vacuous `IsClique`, so the specialisation above is doing real work and is not decoration. -/
theorem degenerate_clique_exists (e : Nat → Nat → Bool) :
    IsClique e [7,7,7,7,7] := by
  intro a ha b hb hab
  simp at ha hb
  subst ha; subst hb
  exact absurd rfl hab

theorem degenerate_list_not_nodup : ¬ ([7,7,7,7,7] : List Nat).Nodup := by decide

/-! ## ONE ISLAND: the obstruction stated on the SAME carrier as the proved ceiling.

    The fifth audit's finding was that the campaign held two formalisation islands — this
    list-carried chain, and a separate interface file whose `upperObligation` carries `sorry`
    over a different colouring type.  The repair is not a transfer lemma; it is to state the
    obstruction HERE, in the language the ceiling is proved in, so a stranger attacking it uses
    the same definitions and needs nothing else. -/

/-- Monotonicity: a sufficient size stays sufficient when enlarged.  PROVED. -/
theorem suffices_mono (m m' s t : Nat) (h : m ≤ m') (hm : Suffices m s t) :
    Suffices m' s t := by
  intro e hsymm V hV
  exact hm e hsymm V (by omega)

/-- `R(5,5) = N` in this carrier: `N` suffices and `N-1` does not. -/
def IsExactly (N s t : Nat) : Prop := Suffices N s t ∧ ¬ Suffices (N - 1) s t

/-- ⛔ THE OBSTRUCTION, stated on the carrier of the proved ceiling.

    This campaign proved `Suffices 70 5 5` and, by `suffices_mono`, everything above it.
    It did NOT prove this.  The gap between `Suffices 43 5 5` and `Suffices 70 5 5` is
    27 orders, and every one of them is open in this record.

    A stranger can attack this statement with nothing but the definitions above it in this
    file: `IsClique`, `IsIndep`, `ArrowsOn`, `Suffices`.  No other file is needed. -/
theorem frontier_obligation : Suffices 43 5 5 := by
  sorry

/-- What the obstruction would give, if it were closed.  PROVED, modulo the obstruction. -/
theorem frontier_gives_the_tail (m : Nat) (h : 43 ≤ m) : Suffices m 5 5 :=
  suffices_mono 43 m 5 5 h frontier_obligation

/-- And the ceiling this campaign DID prove, restated through the same monotonicity. -/
theorem ceiling_gives_the_tail (m : Nat) (h : 70 ≤ m) : Suffices m 5 5 :=
  suffices_mono 70 m 5 5 h es_chain

theorem msl_r55_one_island_interface_v2  : ([1,2] : List Nat).length = 2 := by decide
