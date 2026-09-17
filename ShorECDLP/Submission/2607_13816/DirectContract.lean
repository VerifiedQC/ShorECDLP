import ShorECDLP.Submission.«2607_13816».Window.DirectTCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section

open ShorECDLP.Secp256k1
/-- A closed certificate for the concrete 33-addition direct-load algorithm, its physical reset,
and its fixed 26-run repetition. Phase gates retain the unit-cost-P convention;
the classical candidate is a mathematical specification. -/
structure DirectSecpWindowContract (Q : Point) (hrQ : ShorECDLP.order • Q=0) : Prop where
  sampling : ∀ out : Fin (2^257) × Fin (2^257),
    Instrument.bornMass ((resetDirectWindowTrial Q hrQ).run.filter
      (fun b => resetDirectWindowDecode Q hrQ b.history==
        some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2))) (ket zeroBasisState)=
      secpWindowOutputMass Q hrQ out
  ideal_sampling : Q≠0 → ∀ d : Nat, Q=d • G →
    ∀ out : Fin (2^257) × Fin (2^257),
      secpWindowOutputMass Q hrQ out=paperPairMass ShorECDLP.order 257 d out
  single_total : ∀ d : Nat, Q=d • G → Instrument.bornMass (resetDirectWindowTrial Q hrQ).run (ket zeroBasisState)=1
  single_sound : ∀ d : Nat, Q=d • G → ∀ hist c,
    resetDirectWindowCandidate Q hrQ hist=some c → c=(d:ZMod ShorECDLP.order)
  single_success : ∀ d : Nat, Q=d • G → (163:ℝ)/1000 ≤
    Instrument.bornMass ((resetDirectWindowTrial Q hrQ).run.filter
      (fun b => (resetDirectWindowCandidate Q hrQ b.history).isSome)) (ket zeroBasisState)
  single_clean : ∀ b∈(resetDirectWindowTrial Q hrQ).run,
    b.kraus (ket zeroBasisState)=(b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState
  single_resources : primitiveResources (resetDirectWindowTrial Q hrQ)=
    (directSecpWindowPrimitives Q hrQ).add ⟨0,0,0,0,0,1383⟩
  single_T : (resetDirectWindowTrial Q hrQ).tCount=
    7*(directSecpWindowPrimitives Q hrQ).toffoli+(directSecpWindowPrimitives Q hrQ).phase
  single_qubits : (resetDirectWindowTrial Q hrQ).qubitCount≤1383
  repeated_sound : ∀ d : Nat, Q=d • G → ∀ hist c,
    directSecpWindowRepeatedCandidate Q hrQ hist=some c → c=(d:ZMod ShorECDLP.order)
  repeated_success : ∀ d : Nat, Q=d • G → (99:ℝ)/100 ≤
    Instrument.bornMass ((directSecpWindowRepeatedProgram Q hrQ).run.filter
      (fun b => (directSecpWindowRepeatedCandidate Q hrQ b.history).isSome)) (ket zeroBasisState)
  repeated_clean : ∀ b∈(directSecpWindowRepeatedProgram Q hrQ).run,
    b.kraus (ket zeroBasisState)=(b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState
  repeated_resources : primitiveResources (directSecpWindowRepeatedProgram Q hrQ)=directRepeatedWindowPrimitives Q hrQ
  repeated_T : (directSecpWindowRepeatedProgram Q hrQ).tCount=
    7*(directRepeatedWindowPrimitives Q hrQ).toffoli+(directRepeatedWindowPrimitives Q hrQ).phase
  repeated_qubits : (directSecpWindowRepeatedProgram Q hrQ).qubitCount≤1383

theorem directSecpWindowContract (Q : Point) (hrQ : ShorECDLP.order • Q=0) : DirectSecpWindowContract Q hrQ where
  sampling := resetDirectWindowOutputMass_physical Q hrQ
  ideal_sampling := by
    intro hQ d hd out
    unfold secpWindowOutputMass
    rw [dif_neg hQ]
    exact windowTrialFiniteOutputMass_eq order_prime G Q _ _ _ _ generator_order d hd out
  single_total := resetDirectWindowTrial_total Q hrQ
  single_sound := resetDirectWindowCandidate_sound Q hrQ
  single_success := by
    intro d hd
    rw [resetDirectWindowCandidate_mass Q hrQ d hd]
    exact secpWindowSuccessMass_numeric Q hrQ d hd
  single_clean := resetDirectWindowTrial_zero_branch Q hrQ
  single_resources := by
    rw [resetDirectWindowTrial,primitiveResources_seq,directSecpWindowProgram_primitive,windowResetProgram_primitive]
  single_T := (resetDirectWindowTrial_resources Q hrQ).1.trans (directSecpWindowProgram_tCount_exact Q hrQ)
  single_qubits := resetDirectWindowTrial_qubitCount Q hrQ
  repeated_sound := directSecpWindowRepeatedCandidate_sound Q hrQ
  repeated_success := directSecpWindowRepeatedCandidate_success Q hrQ
  repeated_clean := directSecpWindowRepeatedProgram_clean Q hrQ
  repeated_resources := directSecpWindowRepeatedProgram_primitive Q hrQ
  repeated_T := directSecpWindowRepeatedProgram_tCount_exact Q hrQ
  repeated_qubits := directSecpWindowRepeatedProgram_qubitCount Q hrQ

end
end ShorECDLP.Paper2607_13816
