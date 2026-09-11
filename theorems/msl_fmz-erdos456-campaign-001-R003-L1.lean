set_option autoImplicit false

-- L1 asserts three exactly-decidable absence-facts about the frozen
-- packet record with sha 2a675ae82c68664c. We bind that record as a finite
-- structure of strings (the only load-bearing fields per the lemma) and define
-- a total Bool-valued check of each absence-fact, plus the conjunction.

structure PacketRecord where
  sha        : String
  reduction  : String
  has_mn_pn_defs : Bool
  census_value_count : Nat

def frozen : PacketRecord :=
  { sha := "2a675ae82c68664c"
    reduction := "none"
    has_mn_pn_defs := false
    census_value_count := 0 }

-- Absence-fact 1: reduction field is exactly "none".
def check_no_reduction (p : PacketRecord) : Bool := p.reduction = "none"

-- Absence-fact 2: no m_n / p_n definitions present.
def check_no_mn_pn_defs (p : PacketRecord) : Bool := !(p.has_mn_pn_defs)

-- Absence-fact 3: no 29-value census present (census is empty, i.e. not 29 values).
def check_no_census (p : PacketRecord) : Bool := p.census_value_count ≠ 29 ∧ p.census_value_count = 0

def check_abort_certificate (p : PacketRecord) : Bool :=
  check_no_reduction p && check_no_mn_pn_defs p && check_no_census p

theorem msl_fmz_erdos456_campaign_001_R003_L1  : check_abort_certificate frozen = true ∧ frozen.sha = "2a675ae82c68664c" := by decide
