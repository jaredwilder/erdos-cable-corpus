set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def S : List Nat := [1,2,3,5,7,10,13,15,16,17,24,25,26,28,31,34,36,38,39,40]

/-- the circulant adjacency, normalised so it depends only on residues and is therefore
    total on the naturals -/
def adj (i j : Nat) : Bool := ((i % 41 + 41 - j % 41) % 41) ∈ S

/-- symmetry on RESIDUES, decided over all 1681 pairs -/
theorem symm_res :
    (List.range 41).all (fun a => (List.range 41).all (fun b =>
      (((a + 41 - b) % 41) ∈ S) == (((b + 41 - a) % 41) ∈ S))) = true := by decide

/-- lifting that to a statement about every pair of naturals -/
theorem adj_symm (x y : Nat) : adj x y = adj y x := by
  have hx : x % 41 < 41 := Nat.mod_lt _ (by decide)
  have hy : y % 41 < 41 := Nat.mod_lt _ (by decide)
  have h := List.all_eq_true.mp symm_res (x % 41) (List.mem_range.mpr hx)
  have h2 := List.all_eq_true.mp h (y % 41) (List.mem_range.mpr hy)
  unfold adj
  simpa using h2

/-- and the reflexive case, which the campaign's witness needs to be loop-free -/
theorem adj_irrefl (x : Nat) : adj x x = false := by
  unfold adj
  have : (x % 41 + 41 - x % 41) % 41 = 0 := by
    have hx : x % 41 < 41 := Nat.mod_lt _ (by decide)
    omega
  rw [this]
  decide

def IsClique (e : Nat → Nat → Bool) (L : List Nat) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, a ≠ b → e a b = true

def IsIndep (e : Nat → Nat → Bool) (L : List Nat) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, a ≠ b → e a b = false

def nadj (i j : Nat) : Bool := (i % 41 != j % 41) && (! adj i j)

/-- the global Ramsey property of the order-41 witness, as a guarded nest.  KERNEL-CHECKED
    separately as `r55-global-ramsey-41`; restated here over the residue-normalised adjacency. -/
def noMono5 (e : Nat → Nat → Bool) : Bool :=
  (List.range 41).all fun a => (List.range 41).all fun b => (! (a < b)) || (! e a b) ||
    ((List.range 41).all fun c => (! (b < c)) || (! e a c) || (! e b c) ||
      ((List.range 41).all fun d => (! (c < d)) || (! e a d) || (! e b d) || (! e c d) ||
        ((List.range 41).all fun f => (! (d < f)) || (! e a f) || (! e b f) || (! e c f) || (! e d f))))

theorem witness_noMono5 : noMono5 adj = true := by decide
theorem witness_noMono5_c : noMono5 nadj = true := by decide

/-- extracting one instance of the nest at a strictly increasing 5-tuple below 41 -/
theorem nest_at (e : Nat → Nat → Bool) (h : noMono5 e = true)
    (a b c d f : Nat) (ha : a < 41) (hb : b < 41) (hc : c < 41) (hd : d < 41) (hf : f < 41)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hdf : d < f) :
    ! (e a b && e a c && e b c && e a d && e b d && e c d && e a f && e b f && e c f && e d f) = true := by
  have h1 := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  have h2 := List.all_eq_true.mp (by simpa [hab] using h1) b (List.mem_range.mpr hb)
  by_cases hEab : e a b = true
  · have h3 := List.all_eq_true.mp (by simpa [hab, hEab] using h2) c (List.mem_range.mpr hc)
    by_cases hEac : e a c = true
    · by_cases hEbc : e b c = true
      · have h4 := List.all_eq_true.mp (by simpa [hbc, hEac, hEbc] using h3) d (List.mem_range.mpr hd)
        by_cases hEad : e a d = true
        · by_cases hEbd : e b d = true
          · by_cases hEcd : e c d = true
            · have h5 := List.all_eq_true.mp
                (by simpa [hcd, hEad, hEbd, hEcd] using h4) f (List.mem_range.mpr hf)
              simp [hdf, hEab, hEac, hEbc, hEad, hEbd, hEcd] at h5 ⊢
              simp [h5]
            · simp [hEcd]
          · simp [hEbd]
        · simp [hEad]
      · simp [hEbc]
    · simp [hEac]
  · simp [hEab]

theorem msl_r55_nest_extract  : adj 0 1 = true := by decide
