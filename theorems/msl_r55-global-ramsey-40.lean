set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def S : List Nat := [1,2,4,5,7,12,16,17,18,22,23,24,28,33,35,36,38,39]
def adj (i j : Nat) : Bool := ((i + 40 - j) % 40) ∈ S
def nadj (i j : Nat) : Bool := (i != j) && (! adj i j)
def V : List Nat := List.range 40
def noMono4 (e : Nat → Nat → Bool) : Bool :=
  V.all fun a => V.all fun b => (! (a < b)) || (! e a b) ||
    (V.all fun c => (! (b < c)) || (! e a c) || (! e b c) ||
      (V.all fun d => (! (c < d)) || (! e a d) || (! e b d) || (! e c d)))
def noMono5 (e : Nat → Nat → Bool) : Bool :=
  V.all fun a => V.all fun b => (! (a < b)) || (! e a b) ||
    (V.all fun c => (! (b < c)) || (! e a c) || (! e b c) ||
      (V.all fun d => (! (c < d)) || (! e a d) || (! e b d) || (! e c d) ||
        (V.all fun f => (! (d < f)) || (! e a f) || (! e b f) || (! e c f) || (! e d f))))
def globalOK : Bool := noMono5 adj && noMono5 nadj

theorem msl_r55_global_ramsey_40  : globalOK = true := by decide
