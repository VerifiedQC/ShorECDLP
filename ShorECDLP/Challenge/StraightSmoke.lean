import ShorECDLP.Challenge.StraightLine
open ShorECDLP ShorECDLP.Quantum ShorECDLP.Challenge
-- Empty history cannot name a record: recordGate requires Fin 0.
-- A measurement makes record zero available to the fixed suffix.
def sample : Straight 0 0 1 :=
  .measure 0 (.recordGate ⟨0, by decide⟩ true (.X 1) .done)
example : sample.gateSlots = 1 := rfl
example (read : ConstantBit 0 → Bool) :
    (sample.instantiate read Fin.elim0).measurementCount = 1 :=
  sample.measurementCount read Fin.elim0
#print axioms Straight.instantiate_wellFormed
#print axioms Straight.measurementCount
#print axioms Straight.allGateCount_le
#print axioms Straight.gateSlots_append
