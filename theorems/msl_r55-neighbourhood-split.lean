set_option autoImplicit false
set_option maxRecDepth 20000

-- THE GRAPH STEP OF ERDOS-SZEKERES, its formalizable core.
-- In the derivation, L is the list of the other N-1 vertices and p says the edge to v is red.
-- The two neighbourhoods partition L, and at length m+n-1 one of them must reach its threshold.

theorem filter_split (p : Nat → Bool) : ∀ L : List Nat,
    (L.filter p).length + (L.filter (fun x => ! p x)).length = L.length := by
  intro L
  induction L with
  | nil => rfl
  | cons a t ih =>
    by_cases h : p a
    · simp [List.filter, h] at *; omega
    · simp [List.filter, h] at *; omega

/-- THE NEIGHBOURHOOD SPLIT. With m+n-1 other vertices, the red neighbourhood reaches m or
    the blue neighbourhood reaches n. This is the step the recurrence turns on. -/
theorem nbr_split (p : Nat → Bool) (L : List Nat) (m n : Nat)
    (hlen : L.length = m + n - 1) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    m ≤ (L.filter p).length ∨ n ≤ (L.filter (fun x => ! p x)).length := by
  have h := filter_split p L
  omega

/-- THE PARITY VARIANT. At m+n-2 the two neighbourhoods are forced EXACTLY tight, which is
    what makes the red graph regular in the Greenwood-Gleason sharpening. -/
theorem nbr_split_tight (p : Nat → Bool) (L : List Nat) (m n : Nat)
    (hlen : L.length = m + n - 2) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (ha : (L.filter p).length ≤ m - 1)
    (hb : (L.filter (fun x => ! p x)).length ≤ n - 1) :
    (L.filter p).length = m - 1 ∧ (L.filter (fun x => ! p x)).length = n - 1 := by
  have h := filter_split p L
  omega

theorem msl_r55_neighbourhood_split  : (([0,1,2,3,4] : List Nat).filter (fun x => x % 2 == 0)).length = 3 := by decide
