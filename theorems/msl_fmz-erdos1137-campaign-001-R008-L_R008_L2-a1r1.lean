set_option autoImplicit false

-- Checkable fragment of L_R008_L2: the contract-as-delivered record
-- (CONTRACT_SHA 2f925e97a84d83a2) is exhaustively inspected as a finite object.
-- The lemma's finite, decidable core: the delivered contract carries
--   (a) residual = bare pointer 'per contract' (no materialized residual object),
--   (b) analytic reduction = literal 'none',
--   (c) zero other attachments,
-- hence no exact closed form, recurrence, or finite procedure for R(x) is
-- delivered by the contract itself. This is decidable by direct inspection of
-- the finite contract record; the full non-existence claim over all possible
-- derivations is NOT covered (covers = fragment).

structure ContractRecord where
  sha           : String
  residual      : String
  analyticRed   : String
  attachments   : List String

def delivered : ContractRecord :=
  { sha := "2f925e97a84d83a2"
    residual := "per contract"
    analyticRed := "none"
    attachments := [] }

def isBarePointer (r : String) : Bool := r == "per contract"
def isLiteralNone (r : String) : Bool := r == "none"

def absence_check (c : ContractRecord) : Bool :=
  c.sha == "2f925e97a84d83a2"
  && isBarePointer c.residual
  && isLiteralNone c.analyticRed
  && c.attachments = []

theorem msl_fmz_erdos1137_campaign_001_R008_L_R008_L2_a1r1  : absence_check delivered = true := by decide
