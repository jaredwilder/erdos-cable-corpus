set_option autoImplicit false

def S : List Nat := [1,2,3,5,7,10,13,15,16,17,24,25,26,28,31,34,36,38,39,40]
def units : List Nat := (List.range 40).map (fun k => k+1)
def comp : List Nat := units.filter (fun u => ! (u ∈ S))
def img (a : Nat) : List Nat := S.map (fun s => (a*s) % 41)
def sameSet (x y : List Nat) : Bool := x.all (fun v => y.contains v) && y.all (fun v => x.contains v)
def preserve : List Nat := units.filter (fun a => sameSet (img a) S)
def swap : List Nat := units.filter (fun a => sameSet (img a) comp)
def multOK : Bool := (preserve == [1,40]) && (swap == [9,32]) && ((9*9) % 41 == 40)

theorem msl_r55_multgroup_41  : multOK = true := by decide
