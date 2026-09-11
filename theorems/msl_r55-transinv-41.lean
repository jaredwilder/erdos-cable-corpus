set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def S : List Nat := [1,2,3,5,7,10,13,15,16,17,24,25,26,28,31,34,36,38,39,40]
def adj (i j : Nat) : Bool := ((i + 41 - j) % 41) ∈ S
def V : List Nat := List.range 41
def transInv : Bool :=
  V.all fun t => V.all fun i => V.all fun j =>
    adj ((i + t) % 41) ((j + t) % 41) == adj i j
def symmetric : Bool := V.all fun i => V.all fun j => adj i j == adj j i
def loopfree : Bool := V.all fun i => ! adj i i
def regular20 : Bool := V.all fun i => (V.filter (fun j => adj i j)).length == 20
def shapeOK : Bool := transInv && symmetric && loopfree && regular20

theorem msl_r55_transinv_41  : shapeOK = true := by decide
