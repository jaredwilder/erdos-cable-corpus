set_option autoImplicit false
set_option maxRecDepth 20000

-- THE CONSTRUCTIVE HALF OF THE CLIQUE-EXTRACTION.
-- "a red K_(s-1) inside A together with v is a red K_s": the derivation's own words.
-- Everything in A is red-adjacent to v by construction of A, so prepending v to a red
-- clique of A yields a red clique one larger.

def IsClique (e : Nat → Nat → Bool) (L : List Nat) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, a ≠ b → e a b = true

theorem extend_clique (e : Nat → Nat → Bool)
    (hsymm : ∀ x y, e x y = e y x)
    (v : Nat) (K : List Nat)
    (hadj : ∀ x ∈ K, e v x = true)
    (hK : IsClique e K) :
    IsClique e (v :: K) := by
  intro a ha b hb hab
  rcases List.mem_cons.mp ha with rfl | ha'
  · rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd rfl hab
    · exact hadj b hb'
  · rcases List.mem_cons.mp hb with rfl | hb'
    · rw [hsymm]; exact hadj a ha'
    · exact hK a ha' b hb' hab

theorem extend_clique_length (v : Nat) (K : List Nat) :
    (v :: K).length = K.length + 1 := rfl

-- the same statement on the OTHER colour, which is what makes the argument symmetric
theorem extend_indep (e : Nat → Nat → Bool)
    (hsymm : ∀ x y, e x y = e y x)
    (v : Nat) (K : List Nat)
    (hadj : ∀ x ∈ K, e v x = false)
    (hK : ∀ a ∈ K, ∀ b ∈ K, a ≠ b → e a b = false) :
    ∀ a ∈ (v :: K), ∀ b ∈ (v :: K), a ≠ b → e a b = false := by
  intro a ha b hb hab
  rcases List.mem_cons.mp ha with rfl | ha'
  · rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd rfl hab
    · exact hadj b hb'
  · rcases List.mem_cons.mp hb with rfl | hb'
    · rw [hsymm]; exact hadj a ha'
    · exact hK a ha' b hb' hab

theorem msl_r55_extend_clique  : ([7,1,2] : List Nat).length = 3 := by decide
