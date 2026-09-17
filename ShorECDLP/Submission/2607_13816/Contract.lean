import ShorECDLP.Submission.«2607_13816».Window.TrialTCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section

open ShorECDLP.Secp256k1
/-- A closed certificate for the concrete 34-window algorithm, its physical reset,
and its fixed 26-run repetition. Phase gates retain the unit-cost-P convention;
the classical candidate is a mathematical specification. -/
structure SecpWindowContract (Q : Point) (hrQ : ShorECDLP.order • Q=0) : Prop where
  sampling : ∀ out : Fin (2^257) × Fin (2^257),
    Instrument.bornMass ((resetWindowTrial Q hrQ).run.filter
      (fun b => resetWindowDecode Q hrQ b.history==
        some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2))) (ket zeroBasisState)=
      secpWindowOutputMass Q hrQ out
  ideal_sampling : Q≠0 → ∀ d : Nat, Q=d • G →
    ∀ out : Fin (2^257) × Fin (2^257),
      secpWindowOutputMass Q hrQ out=paperPairMass ShorECDLP.order 257 d out
  single_total : ∀ d : Nat, Q=d • G → Instrument.bornMass (resetWindowTrial Q hrQ).run (ket zeroBasisState)=1
  single_sound : ∀ d : Nat, Q=d • G → ∀ hist c,
    resetWindowCandidate Q hrQ hist=some c → c=(d:ZMod ShorECDLP.order)
  single_success : ∀ d : Nat, Q=d • G → (163:ℝ)/1000 ≤
    Instrument.bornMass ((resetWindowTrial Q hrQ).run.filter
      (fun b => (resetWindowCandidate Q hrQ b.history).isSome)) (ket zeroBasisState)
  single_clean : ∀ b∈(resetWindowTrial Q hrQ).run,
    b.kraus (ket zeroBasisState)=(b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState
  single_resources : primitiveResources (resetWindowTrial Q hrQ)=
    (secpWindowPrimitives Q hrQ).add ⟨0,0,0,0,0,1383⟩
  single_T : (resetWindowTrial Q hrQ).tCount=
    7*(secpWindowPrimitives Q hrQ).toffoli+(secpWindowPrimitives Q hrQ).phase
  single_qubits : (resetWindowTrial Q hrQ).qubitCount≤1383
  repeated_sound : ∀ d : Nat, Q=d • G → ∀ hist c,
    secpWindowRepeatedCandidate Q hrQ hist=some c → c=(d:ZMod ShorECDLP.order)
  repeated_success : ∀ d : Nat, Q=d • G → (99:ℝ)/100 ≤
    Instrument.bornMass ((secpWindowRepeatedProgram Q hrQ).run.filter
      (fun b => (secpWindowRepeatedCandidate Q hrQ b.history).isSome)) (ket zeroBasisState)
  repeated_clean : ∀ b∈(secpWindowRepeatedProgram Q hrQ).run,
    b.kraus (ket zeroBasisState)=(b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState
  repeated_resources : primitiveResources (secpWindowRepeatedProgram Q hrQ)=repeatedWindowPrimitives Q hrQ
  repeated_T : (secpWindowRepeatedProgram Q hrQ).tCount=
    7*(repeatedWindowPrimitives Q hrQ).toffoli+(repeatedWindowPrimitives Q hrQ).phase
  repeated_qubits : (secpWindowRepeatedProgram Q hrQ).qubitCount≤1383

theorem secpWindowContract (Q : Point) (hrQ : ShorECDLP.order • Q=0) : SecpWindowContract Q hrQ where
  sampling := resetWindowOutputMass_physical Q hrQ
  ideal_sampling := by
    intro hQ d hd out
    unfold secpWindowOutputMass
    rw [dif_neg hQ]
    exact windowTrialFiniteOutputMass_eq order_prime G Q _ _ _ _ generator_order d hd out
  single_total := resetWindowTrial_total Q hrQ
  single_sound := resetWindowCandidate_sound Q hrQ
  single_success := by
    intro d hd
    rw [resetWindowCandidate_mass Q hrQ d hd]
    exact secpWindowSuccessMass_numeric Q hrQ d hd
  single_clean := resetWindowTrial_zero_branch Q hrQ
  single_resources := by
    rw [resetWindowTrial,primitiveResources_seq,secpWindowProgram_primitive,windowResetProgram_primitive]
  single_T := (resetWindowTrial_resources Q hrQ).1.trans (secpWindowProgram_tCount_exact Q hrQ)
  single_qubits := resetWindowTrial_qubitCount Q hrQ
  repeated_sound := secpWindowRepeatedCandidate_sound Q hrQ
  repeated_success := secpWindowRepeatedCandidate_success Q hrQ
  repeated_clean := secpWindowRepeatedProgram_clean Q hrQ
  repeated_resources := secpWindowRepeatedProgram_primitive Q hrQ
  repeated_T := secpWindowRepeatedProgram_tCount_exact Q hrQ
  repeated_qubits := secpWindowRepeatedProgram_qubitCount Q hrQ

end
end ShorECDLP.Paper2607_13816
