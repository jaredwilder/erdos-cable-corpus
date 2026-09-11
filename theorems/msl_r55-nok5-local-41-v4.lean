set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def S : List Nat := [1,2,3,5,7,10,13,15,16,17,24,25,26,28,31,34,36,38,39,40]
def adj (i j : Nat) : Bool := ((i + 41 - j) % 41) ∈ S
def comp : List Nat := [4,6,8,9,11,12,14,18,19,20,21,22,23,27,29,30,32,33,35,37]
def nadj (i j : Nat) : Bool := (i != j) && (! adj i j)
def noK4in (L : List Nat) (e : Nat → Nat → Bool) : Bool :=
  L.all fun a => L.all fun b => (! (a < b)) ||
    (L.all fun c => (! (b < c)) || (! e a b) || (! e a c) || (! e b c) ||
      (L.all fun d => (! (c < d)) || (! e a d) || (! e b d) || (! e c d)))
def localOK : Bool :=
  (S.length == 20) && (comp.length == 20)
  && (comp.all fun u => ! (u ∈ S)) && (S.all fun u => ! (u ∈ comp))
  && noK4in S adj && noK4in comp nadj

theorem msl_r55_nok5_local_41_v4  : localOK = true := by decide
