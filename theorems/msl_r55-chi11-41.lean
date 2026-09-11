set_option autoImplicit false

def S : List Nat := [1,2,3,5,7,10,13,15,16,17,24,25,26,28,31,34,36,38,39,40]
def adj (i j : Nat) : Bool := ((i + 41 - j) % 41) ∈ S
def cls (k : Nat) : List Nat := [ (4*(4*k+1)) % 41, (4*(4*k+2)) % 41, (4*(4*k+3)) % 41, (4*(4*k+4)) % 41 ]
def classes : List (List Nat) := (List.range 10).map cls
def allCells : List Nat := classes.flatten
def indepClass (c : List Nat) : Bool := c.all fun a => c.all fun b => (a == b) || (! adj a b)
def chiOK : Bool :=
  (allCells.length == 40)
  && ((List.range 41).all fun v => (v == 0) || allCells.contains v)
  && (allCells.all fun v => v != 0)
  && ((List.range 41).all fun v => (v == 0) || (allCells.count v == 1))
  && (classes.all indepClass)

theorem msl_r55_chi11_41  : chiOK = true := by decide
