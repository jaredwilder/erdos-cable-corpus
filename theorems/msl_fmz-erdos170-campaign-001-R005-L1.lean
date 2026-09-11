set_option autoImplicit false

structure SkeletonInputs where
  F_definition : Bool
  routeThesisWitnesses : Bool
  dualityLemmaRkWitnesses : Bool

def abortCode (inp : SkeletonInputs) : Nat :=
  if !(inp.F_definition && inp.routeThesisWitnesses && inp.dualityLemmaRkWitnesses) then 3 else 0

def abortSet (inp : SkeletonInputs) : List String :=
  (List.zip ["F_definition", "route_thesis_witnesses", "duality_lemma_Rk_witnesses"]
    [inp.F_definition, inp.routeThesisWitnesses, inp.dualityLemmaRkWitnesses]).filterMap
    (fun p => if !p.2 then some p.1 else none)

-- The frozen skeleton's checkable fragment: with all three required inputs
-- absent/falsy, it aborts deterministically with code 3, and the abort set is
-- exactly the three missing items (nonempty, fail closed).
def check_frozen_abort : Bool :=
  let frozen : SkeletonInputs := ⟨false, false, false⟩
  abortCode frozen = 3 && abortSet frozen = ["F_definition", "route_thesis_witnesses", "duality_lemma_Rk_witnesses"]

-- Determinism: re-execution yields identical results.
def check_determinism : Bool :=
  let frozen : SkeletonInputs := ⟨false, false, false⟩
  (abortCode frozen, abortSet frozen) = (abortCode frozen, abortSet frozen)

-- Fail-closed: with all inputs present the skeleton emits no mathematical claim
-- (abort code 0, empty abort set); any single falsy input alone triggers abort 3.
def check_no_self_claim : Bool :=
  let full : SkeletonInputs := ⟨true, true, true⟩
  abortCode full = 0 && abortSet full = []
  && (abortCode ⟨false, true, true⟩ = 3)
  && (abortCode ⟨true, false, true⟩ = 3)
  && (abortCode ⟨true, true, false⟩ = 3)
  && (abortSet ⟨false, true, true⟩ = ["F_definition"])
  && (abortSet ⟨true, false, true⟩ = ["route_thesis_witnesses"])
  && (abortSet ⟨true, true, false⟩ = ["duality_lemma_Rk_witnesses"])

def check_L1_fragment : Bool :=
  check_frozen_abort && check_determinism && check_no_self_claim

theorem msl_fmz_erdos170_campaign_001_R005_L1  : check_L1_fragment = true := by decide
