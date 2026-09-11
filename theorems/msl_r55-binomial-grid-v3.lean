set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def prow : Nat → List Nat
  | 0 => [1]
  | (n+1) => List.zipWith (· + ·) (0 :: prow n) (prow n ++ [0])
def brow : Nat → List Nat
  | 0 => List.replicate 12 1
  | (s+1) => List.scanl (· + ·) 1 ((brow s).drop 1)
def Bv (s t : Nat) : Nat := (brow s).getD t 0
def Cv (n k : Nat) : Nat := (prow n).getD k 0
def grid : List Nat := List.range 12
def identityHolds : Bool := grid.all fun s => grid.all fun t => Bv s t == Cv (s + t) s
def anchors : Bool :=
  (Bv 4 4 == 70) && (Cv 8 4 == 70) && (Bv 3 4 == 35) && (2 * Bv 3 4 == 70)
  && (Bv 0 7 == 1) && (Bv 7 0 == 1)
def ctrlArm : Bool :=
  (Bv 4 4 != 69) && (Cv 8 4 != 71) && (Cv 8 3 == 56)
  && ((brow 0).length == 12) && ((brow 5).length == 12) && ((prow 8).length == 9)
def binomialOK : Bool := identityHolds && anchors && ctrlArm

theorem msl_r55_binomial_grid_v3  : binomialOK = true := by decide
