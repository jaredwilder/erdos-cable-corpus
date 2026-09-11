set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def S : List Nat := [1,2,4,8,9,15,16,20,22,23]
def adj (i j : Nat) : Bool := ((i + 24 - j) % 24) ∈ S
def nadj (i j : Nat) : Bool := (i != j) && (! adj i j)
def V : List Nat := List.range 24
def noMono4 (e : Nat → Nat → Bool) : Bool :=
  V.all fun a => V.all fun b => (! (a < b)) || (! e a b) ||
    (V.all fun c => (! (b < c)) || (! e a c) || (! e b c) ||
      (V.all fun d => (! (c < d)) || (! e a d) || (! e b d) || (! e c d)))
def noMono5 (e : Nat → Nat → Bool) : Bool :=
  V.all fun a => V.all fun b => (! (a < b)) || (! e a b) ||
    (V.all fun c => (! (b < c)) || (! e a c) || (! e b c) ||
      (V.all fun d => (! (c < d)) || (! e a d) || (! e b d) || (! e c d) ||
        (V.all fun f => (! (d < f)) || (! e a f) || (! e b f) || (! e c f) || (! e d f))))
def globalOK : Bool := noMono4 adj && noMono5 nadj

theorem msl_r45_global_ramsey_24  : globalOK = true := by decide
