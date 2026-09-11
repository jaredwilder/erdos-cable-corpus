set_option autoImplicit false

Pure core Lean 4, no Mathlib, no floats, exact Nat arithmetic. Objects bound semantically: L n = lcm(1..n) via core Nat.lcm; a n by the contract's exact recursion a_1=1, a_n = a_{n-1}*(L_n/L_{n-1}) + L_n/n; residual check is exact Nat equality a_n == sum_{k=1..n} (L_n / k), with every division exact (k | L_n), no tolerances, fail-closed Bool conjunction.

```lean
def L : Nat → Nat
  | 0 => 1
  | (n+1) => Nat.lcm (L n) (n+1)

def a : Nat → Nat
  | 0 => 0
  | 1 => 1
  | (n+2) => a (n+1) * (L (n+2) / L (n+1)) + L (n+2) / (n+2)

/-- sum_{k=1..k} l / k, exact Nat --/
def s (l : Nat) : Nat → Nat
  | 0 => 0
  | (k+1) => s l k + l / (k+1)

def checkNode (n : Nat) : Bool := a n == s (L n) n

def checkRange : Nat → Bool
  | 0 => true
  | (n+1) => checkNode (n+1) && checkRange n
```

theorem msl_fmz_erdos291_campaign_001_R006_cert  : checkRange 6 = true ∧ Nat.gcd (a 4) (L 4) = 1 ∧ Nat.gcd (a 6) (L 6) = 3 := by decide
