import ShorECDLP.Submission.«2607_13816».Window.ReducedTCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section

open ShorECDLP.Secp256k1
/-- A closed certificate for the concrete 28-addition reduced-load algorithm, its physical reset,
and its fixed 26-run repetition. Phase gates retain the unit-cost-P convention;
the classical candidate is a mathematical specification. -/
structure ReducedSecpWindowContract (Q : Point) (hrQ : ShorECDLP.order • Q=0) : Prop where
  sampling : ∀ out : Fin (2^256) × Fin (2^208),
    Instrument.bornMass ((resetReducedWindowTrial Q hrQ).run.filter
      (fun b => resetReducedWindowDecode Q hrQ b.history==
        some (paperOutcomeBits 256 out.1,paperOutcomeBits 208 out.2))) (ket zeroBasisState)=
      reducedSecpWindowOutputMass Q hrQ out
  ideal_sampling : Q≠0 → ∀ d : Nat, Q=d • G →
    ∀ out : Fin (2^256) × Fin (2^208),
      reducedSecpWindowOutputMass Q hrQ out=asymmetricPairMass ShorECDLP.order 256 208 d out
  single_total : ∀ d : Nat, Q=d • G → Instrument.bornMass (resetReducedWindowTrial Q hrQ).run (ket zeroBasisState)=1
  single_sound : ∀ d : Nat, Q=d • G → ∀ hist c,
    resetReducedWindowCandidate Q hrQ hist=some c → c=(d:ZMod ShorECDLP.order)
  single_success : ∀ d : Nat, Q=d • G → (163:ℝ)/1000 ≤
    Instrument.bornMass ((resetReducedWindowTrial Q hrQ).run.filter
      (fun b => (resetReducedWindowCandidate Q hrQ b.history).isSome)) (ket zeroBasisState)
  single_clean : ∀ b∈(resetReducedWindowTrial Q hrQ).run,
    b.kraus (ket zeroBasisState)=(b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState
  single_resources : primitiveResources (resetReducedWindowTrial Q hrQ)=
    (reducedSecpWindowPrimitives Q hrQ).add ⟨0,0,0,0,0,1303⟩
  single_T : (resetReducedWindowTrial Q hrQ).tCount=
    7*(reducedSecpWindowPrimitives Q hrQ).toffoli+(reducedSecpWindowPrimitives Q hrQ).phase
  single_qubits : (resetReducedWindowTrial Q hrQ).qubitCount≤1303
  repeated_sound : ∀ d : Nat, Q=d • G → ∀ hist c,
    reducedSecpWindowRepeatedCandidate Q hrQ hist=some c → c=(d:ZMod ShorECDLP.order)
  repeated_success : ∀ d : Nat, Q=d • G → (99:ℝ)/100 ≤
    Instrument.bornMass ((reducedSecpWindowRepeatedProgram Q hrQ).run.filter
      (fun b => (reducedSecpWindowRepeatedCandidate Q hrQ b.history).isSome)) (ket zeroBasisState)
  repeated_clean : ∀ b∈(reducedSecpWindowRepeatedProgram Q hrQ).run,
    b.kraus (ket zeroBasisState)=(b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState
  repeated_resources : primitiveResources (reducedSecpWindowRepeatedProgram Q hrQ)=reducedRepeatedWindowPrimitives Q hrQ
  repeated_T : (reducedSecpWindowRepeatedProgram Q hrQ).tCount=
    7*(reducedRepeatedWindowPrimitives Q hrQ).toffoli+(reducedRepeatedWindowPrimitives Q hrQ).phase
  repeated_qubits : (reducedSecpWindowRepeatedProgram Q hrQ).qubitCount≤1303

theorem reducedSecpWindowContract (Q : Point) (hrQ : ShorECDLP.order • Q=0) : ReducedSecpWindowContract Q hrQ where
  sampling := resetReducedWindowOutputMass_physical Q hrQ
  ideal_sampling := by
    intro hQ d hd out
    unfold reducedSecpWindowOutputMass
    rw [dif_neg hQ]
    exact reducedWindowTrialFiniteOutputMass_eq order_prime G Q _ _ _ _ generator_order d hd out
  single_total := resetReducedWindowTrial_total Q hrQ
  single_sound := resetReducedWindowCandidate_sound Q hrQ
  single_success := by
    intro d hd
    rw [resetReducedWindowCandidate_mass Q hrQ d hd]
    exact reducedSecpWindowSuccessMass_numeric Q hrQ d hd
  single_clean := resetReducedWindowTrial_zero_branch Q hrQ
  single_resources := by
    rw [resetReducedWindowTrial,primitiveResources_seq,reducedSecpWindowProgram_primitive,reducedResetProgram_primitive]
  single_T := (resetReducedWindowTrial_resources Q hrQ).1.trans (reducedSecpWindowProgram_tCount_exact Q hrQ)
  single_qubits := resetReducedWindowTrial_qubitCount Q hrQ
  repeated_sound := reducedSecpWindowRepeatedCandidate_sound Q hrQ
  repeated_success := reducedSecpWindowRepeatedCandidate_success Q hrQ
  repeated_clean := reducedSecpWindowRepeatedProgram_clean Q hrQ
  repeated_resources := reducedSecpWindowRepeatedProgram_primitive Q hrQ
  repeated_T := reducedSecpWindowRepeatedProgram_tCount_exact Q hrQ
  repeated_qubits := reducedSecpWindowRepeatedProgram_qubitCount Q hrQ

end
end ShorECDLP.Paper2607_13816
