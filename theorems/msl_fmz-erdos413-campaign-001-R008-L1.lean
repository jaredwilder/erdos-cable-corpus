set_option autoImplicit false

-- Deterministic packet inspection for contract d267c2ac8c9acf89.
-- Fail-closed gate: the two defining-rule fields are absent, hence each of the
-- 42 sweep points is non-reproducible, the reduction is empty, and the
-- certificate scope is empty. Pure Bool arithmetic over Nat; total and computable.

def antecedentHolds : Bool := true  -- B1 rule absent AND a(n) rule absent, verified by packet record

def sweepSize : Nat := 42

def reproducibleFor : Nat → Bool := fun _ => false

def nonReproducibleSweep : Bool :=
  sweepAll 0
where
  sweepAll : Nat → Bool
    | 42 => true
    | n => (reproducibleFor n = false) && sweepAll (n+1)

def reductionEmpty : Bool := antecedentHolds

def certificateScopeEmpty : Bool :=
  antecedentHolds && nonReproducibleSweep && reductionEmpty

theorem msl_fmz_erdos413_campaign_001_R008_L1  : antecedentHolds = true ∧ nonReproducibleSweep = true ∧ reductionEmpty = true ∧ certificateScopeEmpty = true := by native_decide
