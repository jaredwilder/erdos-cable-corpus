set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def S : List Nat := [1,2,3,5,7,10,13,15,16,17,24,25,26,28,31,34,36,38,39,40]
def adj (i j : Nat) : Bool := ((i + 41 - j) % 41) ∈ S
def V : List Nat := List.range 41
def cls (k : Nat) : List Nat := [ (4*(4*k+1)) % 41, (4*(4*k+2)) % 41, (4*(4*k+3)) % 41, (4*(4*k+4)) % 41 ]
def shift (v : Nat) (l : List Nat) : List Nat := l.map (fun x => (x + v) % 41)
def indep (c : List Nat) : Bool := c.all fun a => c.all fun b => (a == b) || (! adj a b)
def classesAt (v : Nat) : List (List Nat) := (List.range 10).map (fun k => shift v (cls k))
def cellsAt (v : Nat) : List Nat := (classesAt v).flatten
def okAt (v : Nat) : Bool :=
  ((cellsAt v).length == 40)
  && ((classesAt v).all indep)
  && ((classesAt v).all (fun c => c.length == 4))
  && ((cellsAt v).all (fun x => x != v))
  && (V.all fun x => (x == v) || ((cellsAt v).count x == 1))
def chiMinusOK : Bool := V.all okAt
def ctrlArm : Bool := ((classesAt 0).length == 10) && (! (indep [0,1,2,3]))
def allOK : Bool := chiMinusOK && ctrlArm

theorem msl_r55_chi_minus_v_41  : allOK = true := by decide
