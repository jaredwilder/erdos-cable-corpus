set_option autoImplicit false

def S : List Nat := [1,2,3,5,7,10,13,15,16,17,24,25,26,28,31,34,36,38,39,40]
def adj (i j : Nat) : Bool := ((i + 41 - j) % 41) ∈ S
def selfComp : Bool :=
  (List.range 41).all fun i =>
    (List.range 41).all fun j =>
      (i == j) || (adj i j != adj ((9*i) % 41) ((9*j) % 41))

theorem msl_r55_selfcomp_41  : selfComp = true := by decide
