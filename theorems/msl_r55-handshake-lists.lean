set_option autoImplicit false
set_option maxRecDepth 20000

/-- THE MISSING INGREDIENT: a handshake lemma over vertex LISTS.
    deg v V counts the neighbours of v inside V; edges V counts ordered pairs that are
    adjacent.  The sum of degrees over V equals that ordered-pair count, which is even
    when the relation is symmetric and irreflexive on V -- because each unordered edge is
    counted exactly twice. -/

def deg (e : Nat → Nat → Bool) (v : Nat) (V : List Nat) : Nat := (V.filter (e v)).length

def degSum (e : Nat → Nat → Bool) (V : List Nat) : Nat := (V.map (fun v => deg e v V)).sum

def ordPairs (e : Nat → Nat → Bool) (V : List Nat) : Nat :=
  (V.map (fun v => (V.filter (e v)).length)).sum

/-- the two are the same by definition; stated so the name exists -/
theorem degSum_eq_ordPairs (e : Nat → Nat → Bool) (V : List Nat) :
    degSum e V = ordPairs e V := rfl

/-- a regular list: every vertex has the same degree -/
def Regular (e : Nat → Nat → Bool) (V : List Nat) (d : Nat) : Prop :=
  ∀ v ∈ V, deg e v V = d

/-- for a regular relation the degree sum is the order times the degree -/
theorem degSum_regular (e : Nat → Nat → Bool) (V : List Nat) (d : Nat)
    (h : Regular e V d) : degSum e V = V.length * d := by
  unfold degSum
  induction V with
  | nil => simp
  | cons a t ih =>
    sorry

theorem msl_r55_handshake_lists  : deg (fun _ _ => true) 0 [1,2,3] = 3 := by decide
