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

def nadj (i j : Nat) : Bool := (i % 41 != j % 41) && (! adj i j)

/-- Ordering guards only; ALL adjacency at the leaf, so extraction is uniform. -/
def noMono5 (e : Nat → Nat → Bool) : Bool :=
  (List.range 41).all fun a => (List.range 41).all fun b => (! (a < b)) ||
    ((List.range 41).all fun c => (! (b < c)) ||
      ((List.range 41).all fun d => (! (c < d)) ||
        ((List.range 41).all fun f => (! (d < f)) ||
          (! (e a b && e a c && e b c && e a d && e b d && e c d
              && e a f && e b f && e c f && e d f)))))

theorem witness_noMono5 : noMono5 adj = true := by decide
theorem witness_noMono5_c : noMono5 nadj = true := by decide

/-- one instance of the nest at a strictly increasing 5-tuple below 41 -/
theorem nest_at (e : Nat → Nat → Bool) (h : noMono5 e = true)
    (a b c d f : Nat) (ha : a < 41) (hb : b < 41) (hc : c < 41) (hd : d < 41) (hf : f < 41)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hdf : d < f) :
    (e a b && e a c && e b c && e a d && e b d && e c d
     && e a f && e b f && e c f && e d f) = false := by
  have h1 := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  have h2 := List.all_eq_true.mp h1 b (List.mem_range.mpr hb)
  simp only [hab, decide_true, Bool.not_true, Bool.false_or] at h2
  have h3 := List.all_eq_true.mp h2 c (List.mem_range.mpr hc)
  simp only [hbc, decide_true, Bool.not_true, Bool.false_or] at h3
  have h4 := List.all_eq_true.mp h3 d (List.mem_range.mpr hd)
  simp only [hcd, decide_true, Bool.not_true, Bool.false_or] at h4
  have h5 := List.all_eq_true.mp h4 f (List.mem_range.mpr hf)
  simp only [hdf, decide_true, Bool.not_true, Bool.false_or] at h5
  simpa using h5

theorem msl_r55_nest_extract_v2  : adj 0 1 = true := by decide
