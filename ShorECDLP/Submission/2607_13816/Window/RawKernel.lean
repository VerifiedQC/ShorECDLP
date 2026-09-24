import ShorECDLP.Submission.«2607_13816».Window.StreamTwoKernel
namespace ShorECDLP.Paper2607_13816
open Quantum ShorECDLP.Secp256k1
noncomputable section
/-- Actual arithmetic paths followed by the 256- and 208-bit mathematical
Fourier rows, retaining each original complete transcript. -/
def streamRawKernelBody (P Q : Point) : Instrument :=
  streamTwoKernelBody (indexedStreamCalls 1 (streamRawLeftCalls P Q))
    (indexedStreamCalls 17 (streamRawRightCalls Q)) (.unitary [.X 836] .done)

theorem streamRawDeferredBody_kernel (P Q : Point) :
    streamRawDeferredBody P Q = streamRawKernelBody P Q := by
  unfold streamRawDeferredBody streamRawKernelBody
  apply deferredTwoAxis_kernel
  · simp only [indexedStreamCalls, List.map_map, Function.comp_def, Prod.fst_swap, List.zipIdx_map_snd]
    exact List.nodup_range'
  · simp only [indexedStreamCalls, List.map_map, Function.comp_def, Prod.fst_swap, List.zipIdx_map_snd]
    exact List.nodup_range'
  · intro c hc d hd
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hd
    have hai := List.mem_zipIdx ha
    have hbi := List.mem_zipIdx hb
    have hl : (streamRawLeftCalls P Q).length = 16 := by
      simp [streamRawLeftCalls]
    dsimp
    omega
  · intro c hc
    have hh := List.mem_map_of_mem (f:=Prod.snd) hc
    rw [indexedStreamCalls_calls] at hh
    obtain ⟨j, hj, he⟩ := List.mem_map.mp hh
    rw [← he]
    exact streamRawCall_support _ _
  · intro w hw
    obtain ⟨c, hc, hw⟩ := List.mem_flatMap.mp hw
    have hn : w ≠ 836 := by
      simp only [List.mem_reverse, List.mem_range'_1, windowBankStart] at hw
      dsimp only [Wire] at *
      omega
    simpa only [AdaptiveCircuit.wires, circuitWires, List.flatMap_cons, List.flatMap_nil,
      gateWires, List.append_nil, List.mem_singleton] using hn

/-- Both Fourier rows now act after all actual arithmetic. Amplitudes are
preserved before probabilities, including all internal arithmetic outcomes. -/
theorem streamRawTrial_kernel (P Q : Point) :
    (streamRawTrial P Q).run.map (fun b => (b.history, b.kraus (ket zeroBasisState))) =
    (streamRawKernelBody P Q).map (fun b => (b.history, b.kraus
      (Quantum.run (streamRawPreparation P Q) (ket (scalarRootFlip zeroBasisState))))) := by
  rw [streamRawTrial_deferred, streamRawDeferredBody_kernel]

theorem streamFourierWires_length (calls : List (Nat × AdaptiveCircuit)) :
    (streamFourierWires calls).length = 16 * calls.length := by
  induction calls with
  | nil => rfl
  | cons c calls ih =>
    simpa only [streamFourierWires, List.flatMap_cons, List.length_append,
      List.length_reverse, List.length_range', List.length_cons, Nat.mul_add,
      Nat.mul_one, Nat.add_comm] using congrArg (16+·) ih

theorem streamRawKernel_precisions (P Q : Point) :
    (streamFourierWires (indexedStreamCalls 1 (streamRawLeftCalls P Q))).length = 256 ∧
    (streamFourierWires (indexedStreamCalls 17 (streamRawRightCalls Q))).length = 208 := by
  simp only [streamFourierWires_length, indexedStreamCalls, List.length_map,
    List.length_zipIdx, streamRawLeftCalls, streamRawRightCalls, List.length_cons,
    List.length_reverse, List.length_range]
  decide
end
end ShorECDLP.Paper2607_13816
