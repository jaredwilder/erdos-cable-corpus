import Mathlib

set_option autoImplicit false

inductive GateInput where
  | absent
  | present (value : Bool)

def gate : GateInput → GateInput → Option Bool
  | GateInput.absent, GateInput.absent => none
  | GateInput.absent, GateInput.present _ => some false
  | GateInput.present _, GateInput.absent => some false
  | GateInput.present _, GateInput.present _ => some true

theorem msl_fmz_erdos25_campaign_001_R003_L1  : ∀ reduction residual : GateInput,
    gate reduction residual = none ↔
      reduction = GateInput.absent ∧ residual = GateInput.absent := by
  intro reduction residual
  cases reduction <;> cases residual <;> simp [gate]
