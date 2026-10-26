import ShorECDLP.Challenge.Template
open ShorECDLP ShorECDLP.Quantum ShorECDLP.Challenge

-- Count both CCXs; branch counters take max, not sum.
example : toffoliCount (.unitary [.CCX 0 1 2, .CCX 0 1 2] .done) = 2 := rfl
example : toffoliCount (.xMeasureReset 0
  (.unitary [.CCX 0 1 2] .done) (.unitary [.CCX 0 1 2] .done)) = 1 := rfl
example : nonCliffordCount (.unitary [.P .forward 2 0, .P .inverse 3 0] .done) = 1 := rfl
-- Seven T gates do not disappear when no CCX constructors remain.
example : (resources (.unitary (List.replicate 7 (.P .forward 3 0)) .done)).tModel = 7 := rfl
-- Public-point callbacks, counters and decoders are not Entry fields.
#check Entry.mk
#check Entry.program_wellFormed
#check Template.instantiate_seq
#print axioms Entry.program_wellFormed
#print axioms Template.instantiate_seq
