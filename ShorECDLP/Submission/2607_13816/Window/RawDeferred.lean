import ShorECDLP.Submission.«2607_13816».Window.StreamDeferred
namespace ShorECDLP.Paper2607_13816
open Quantum ShorECDLP.Secp256k1
noncomputable section
/-- Both axes with Fourier maps deferred within each axis. Histories retain their
original order; the axes still have independent feedback. -/
def streamRawDeferredBody (P Q : Point) : Instrument :=
  (deferredStreamAxis (indexedStreamCalls 1 (streamRawLeftCalls P Q)) List.nil .done).seq
    (deferredStreamAxis (indexedStreamCalls 17 (streamRawRightCalls Q)) List.nil
      (.unitary [.X 836] .done))

private theorem indexed_nodup (start : Nat) (calls : List AdaptiveCircuit) :
    ((indexedStreamCalls start calls).map Prod.fst).Nodup := by
  simpa only [indexedStreamCalls, List.map_map, Function.comp_def, Prod.fst_swap,
    List.zipIdx_map_snd] using (List.nodup_range' (s:=start) (n:=calls.length))
private theorem indexed_support (start : Nat) (calls : List AdaptiveCircuit)
    (hc : ∀ c ∈ calls, c.wires ⊆ streamAllocation) :
    ∀ c ∈ indexedStreamCalls start calls, c.2.wires ⊆ streamAllocation := by
  intro c hm
  have hh := List.mem_map_of_mem (f:=Prod.snd) hm
  rw [indexedStreamCalls_calls] at hh
  exact hc c.2 hh

theorem streamRawPreparedBody_deferred (P Q : Point) :
    streamRawPreparedBody P Q = streamRawDeferredBody P Q := by
  have hl : ∀ c ∈ streamRawLeftCalls P Q, c.wires ⊆ streamAllocation := by
    intro c hc
    simp only [streamRawLeftCalls, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨j, hj, rfl⟩
    · exact streamPointLookup_support _
    · exact streamRawCall_support _ _
  have hr : ∀ c ∈ streamRawRightCalls Q, c.wires ⊆ streamAllocation := by
    intro c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    exact streamRawCall_support _ _
  unfold streamRawPreparedBody streamRawDeferredBody
  rw [unpreparedStreamAxis_deferred _ _ .done (indexed_nodup _ _)
    (indexed_support _ _ hl) (by simp [AdaptiveCircuit.wires])]
  rw [unpreparedStreamAxis_deferred _ _ (.unitary [.X 836] .done) (indexed_nodup _ _)
    (indexed_support _ _ hr)]
  intro c hc w hw
  have hn : w ≠ 836 := by
    simp only [List.mem_range'_1, windowBankStart] at hw
    dsimp only [Wire] at *
    omega
  simpa only [AdaptiveCircuit.wires, circuitWires, List.flatMap_cons, List.flatMap_nil,
    gateWires, List.append_nil, List.mem_singleton] using hn

/-- Exact actual-trial correspondence with deferred Fourier maps. This keeps
all arithmetic and Fourier records; no decoder success claim is inferred. -/
theorem streamRawTrial_deferred (P Q : Point) :
    (streamRawTrial P Q).run.map (fun b => (b.history, b.kraus (ket zeroBasisState))) =
    (streamRawDeferredBody P Q).map (fun b => (b.history, b.kraus
      (Quantum.run (streamRawPreparation P Q) (ket (scalarRootFlip zeroBasisState))))) := by
  rw [streamRawTrial_prepared, streamRawPreparedBody_deferred]
end
end ShorECDLP.Paper2607_13816
