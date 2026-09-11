set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def P : List Nat := [1,2,4,5,8,9,10,16,18,20,21,23,25,31,32,33,36,37,39,40]
def padj (i j : Nat) : Bool := ((i + 41 - j) % 41) ∈ P
def V : List Nat := List.range 41
def noMono5 (e : Nat → Nat → Bool) : Bool :=
  V.all fun a => V.all fun b => (! (a < b)) || (! e a b) ||
    (V.all fun c => (! (b < c)) || (! e a c) || (! e b c) ||
      (V.all fun d => (! (c < d)) || (! e a d) || (! e b d) || (! e c d) ||
        (V.all fun f => (! (d < f)) || (! e a f) || (! e b f) || (! e c f) || (! e d f))))
def controlOK : Bool := (P.length == 20) && (noMono5 padj == false)

theorem msl_r55_control_paley_41  : controlOK = true := by decide
