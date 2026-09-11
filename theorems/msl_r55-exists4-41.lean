set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def S : List Nat := [1,2,3,5,7,10,13,15,16,17,24,25,26,28,31,34,36,38,39,40]
def adj (i j : Nat) : Bool := ((i + 41 - j) % 41) ∈ S
def pairsOf (L : List Nat) : List (Nat × Nat) :=
  L.flatMap fun a => L.filterMap fun b => if a < b then some (a,b) else none
def isClique (L : List Nat) : Bool := (pairsOf L).all fun p => adj p.1 p.2
def isIndep (L : List Nat) : Bool := (pairsOf L).all fun p => ! adj p.1 p.2
def K : List Nat := [0,1,2,3]
def I : List Nat := [0,4,8,12]
def existsOK : Bool :=
  (K.length == 4) && (I.length == 4)
  && ((pairsOf K).length == 6) && ((pairsOf I).length == 6)
  && isClique K && isIndep I
  && (! isIndep K) && (! isClique I)

theorem msl_r55_exists4_41  : existsOK = true := by decide
