import ShorECDLP.Submission.«2607_13816».Window.TwoAxisReuse
namespace ShorECDLP.Paper2607_13816
open Quantum ShorECDLP.Secp256k1
noncomputable section
/-- The actual two-axis arithmetic/Fourier instrument after moving preparation
out of every block. Each axis starts with empty Fourier feedback. -/
def streamRawPreparedBody (P Q : Point) : Instrument :=
  (unpreparedStreamAxis (indexedStreamCalls 1 (streamRawLeftCalls P Q)) List.nil .done).seq
    (unpreparedStreamAxis (indexedStreamCalls 17 (streamRawRightCalls Q)) List.nil
      (.unitary [.X 836] .done))
def streamRawPreparation (P Q : Point) : Circuit :=
  ((streamPreparationWires (indexedStreamCalls 1 (streamRawLeftCalls P Q))) ++
    streamPreparationWires (indexedStreamCalls 17 (streamRawRightCalls Q))).map Gate.H

/-- The same 855-wire physical trial has exactly the histories and branch states
of the two-axis body on a fully prepared logical input (banks 1..29).
This does not yet identify its sampling with the mathematical reference. -/
theorem streamRawTrial_prepared (P Q : Point) :
    (streamRawTrial P Q).run.map (fun b => (b.history, b.kraus (ket zeroBasisState))) =
    (streamRawPreparedBody P Q).map (fun b => (b.history, b.kraus
      (Quantum.run (streamRawPreparation P Q) (ket (scalarRootFlip zeroBasisState))))) := by
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
  have hs : SupportedOn (Clean streamAddress) (ket (scalarRootFlip zeroBasisState)) := by
    apply supportedOn_ket
    intro w hw
    have hn : w ≠ 836 := by
      simp only [streamAddress, List.mem_range'_1] at hw
      dsimp only [Wire] at *
      omega
    simp only [scalarRootFlip, upd, if_neg hn, zeroBasisState]
  have hb : ∀ k, SupportedOn (Clean (List.range' (windowBankStart k) 16))
      (ket (scalarRootFlip zeroBasisState)) := by
    intro k
    apply supportedOn_ket
    intro w hw
    have hn : w ≠ 836 := by
      simp only [windowBankStart, List.mem_range'_1] at hw
      dsimp only [Wire] at *
      omega
    simp only [scalarRootFlip, upd, if_neg hn, zeroBasisState]
  have h := indexedTwoAxis_prepared (streamRawLeftCalls P Q) (streamRawRightCalls Q)
    List.nil List.nil (.unitary [.X 836] .done) 1 17 (by decide) (by decide)
    (by simp only [streamRawLeftCalls, List.length_cons, List.length_map,
          List.length_reverse, List.length_range]; decide)
    hl hr (ket (scalarRootFlip zeroBasisState)) hs
    (fun k _ _ => hb k) (fun k _ _ => hb k)
  rw [streamRawTrial, AdaptiveCircuit.run_seq, AdaptiveCircuit.run_unitary_done]
  simp only [Instrument.seq, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    InstrumentBranch.seq, List.nil_append, List.map_map, Function.comp_def, LinearMap.comp_apply]
  have hx : Quantum.run [Gate.X 836] (ket zeroBasisState) = ket (scalarRootFlip zeroBasisState) := by
    simp only [run_cons, run_nil, applyGate_X_ket, scalarRootFlip]
  rw [hx]
  exact h
end
end ShorECDLP.Paper2607_13816
