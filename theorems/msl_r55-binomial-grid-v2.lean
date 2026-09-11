set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def B : Nat → Nat → Nat
  | 0, _ => 1
  | _, 0 => 1
  | (s+1), (t+1) => B s (t+1) + B (s+1) t
def C : Nat → Nat → Nat
  | _, 0 => 1
  | 0, (_+1) => 0
  | (n+1), (k+1) => C n k + C n (k+1)
def grid : List Nat := List.range 12
def identityHolds : Bool :=
  grid.all fun s => grid.all fun t => B s t == C (s + t) s
def anchors : Bool :=
  (B 4 4 == 70) && (C 8 4 == 70) && (B 3 4 == 35) && (2 * B 3 4 == 70)
  && (B 0 7 == 1) && (B 7 0 == 1)
def ctrlArm : Bool := (B 4 4 != 69) && (C 8 4 != 71) && (C 8 3 == 56)
def binomialOK : Bool := identityHolds && anchors && ctrlArm

theorem msl_r55_binomial_grid_v2  : binomialOK = true := by decide
