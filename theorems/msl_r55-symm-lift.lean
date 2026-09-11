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

theorem msl_r55_symm_lift  : adj 0 1 = true := by decide
