set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

def S : List Nat := [1,2,3,5,7,10,13,15,16,17,24,25,26,28,31,34,36,38,39,40]
def adj (i j : Nat) : Bool := ((i + 41 - j) % 41) ∈ S
def quads : List (Nat × Nat × Nat × Nat) :=
  S.flatMap fun a => S.flatMap fun b => S.flatMap fun c => S.filterMap fun d =>
    if a < b && b < c && c < d then some (a,b,c,d) else none
def comp : List Nat := ((List.range 40).map (fun k => k+1)).filter (fun u => ! (u ∈ S))
def nadj (i j : Nat) : Bool := (i != j) && (! adj i j)
def cquads : List (Nat × Nat × Nat × Nat) :=
  comp.flatMap fun a => comp.flatMap fun b => comp.flatMap fun c => comp.filterMap fun d =>
    if a < b && b < c && c < d then some (a,b,c,d) else none
def localOK : Bool :=
  (S.length == 20) && (comp.length == 20)
  && (quads.length == 4845) && (cquads.length == 4845)
  && (quads.all fun q => ! (adj q.1 q.2.1 && adj q.1 q.2.2.1 && adj q.1 q.2.2.2 && adj q.2.1 q.2.2.1 && adj q.2.1 q.2.2.2 && adj q.2.2.1 q.2.2.2))
  && (cquads.all fun q => ! (nadj q.1 q.2.1 && nadj q.1 q.2.2.1 && nadj q.1 q.2.2.2 && nadj q.2.1 q.2.2.1 && nadj q.2.1 q.2.2.2 && nadj q.2.2.1 q.2.2.2))

theorem msl_r55_nok5_local_41_v3  : localOK = true := by decide
