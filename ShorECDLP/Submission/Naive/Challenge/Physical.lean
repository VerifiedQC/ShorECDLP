import ShorECDLP.Submission.Naive.Challenge.Probability
import ShorECDLP.Submission.Naive.Challenge.ResetRepeat
import ShorECDLP.Submission.Naive.Submission

namespace ShorECDLP.NaiveChallenge
open Classical Quantum Secp256k1
open scoped BigOperators
noncomputable section

theorem naive_bound_value : bitcoinECDLPSubmission.singleRunSuccessLowerBound = 41 / 250 := by
  unfold bitcoinECDLPSubmission
  rcases bitcoinWireLayout with ⟨ha, hb, hp, hn, hf⟩
  rfl

theorem naive_trialCount_value : bitcoinECDLPSubmission.trialCount = 26 := by
  unfold bitcoinECDLPSubmission
  rcases bitcoinWireLayout with ⟨ha, hb, hp, hn, hf⟩
  rfl

def naiveObserved (Q : Point) : AdaptiveCircuit :=
  observedTrial (bitcoinECDLPSubmission.program Q) bitcoinAReg bitcoinBReg

def naiveRepeated (Q : Point) : AdaptiveCircuit := repeatFixed (resetTrial (naiveObserved Q)) 26

/-- Success is specified using the secret, but neither the physical program nor
its public postprocessing receives it as input. -/
def recoveredPair (d a b : Nat) : Bool :=
  decide (Quantum.OrderFinding.orderFindingPostprocess order 256 order_prime
    (Fin.ofNat (2^256) a, Fin.ofNat (2^256) b) = some (d : ZMod order))

def naiveEvent (d : Nat) : List Bool → Bool := pairEvent 256 (recoveredPair d)

def naiveRepeatedSuccess (Q : Point) (d : Nat) (history : List Bool) : Bool :=
  !repeatFailed (512 + (naiveObserved Q).wires.dedup.length)
    (fun bits => naiveEvent d (bits.take 512)) 26 history

theorem naiveObserved_length (Q : Point) (b : InstrumentBranch)
    (hb : b ∈ (naiveObserved Q).run) : b.history.length = 512 := by
  simpa [naiveObserved, bitcoinWireLayout.1, bitcoinWireLayout.2.1] using
    observedTrial_history_length (bitcoinECDLPSubmission.program Q) bitcoinAReg bitcoinBReg b hb

theorem naiveObserved_probability (Q : Point) (d : Nat) :
    recordMass (naiveObserved Q).run (naiveEvent d) (ket zeroBasisState) =
      ∑ a : Fin (2^256), ∑ b : Fin (2^256),
        if Quantum.OrderFinding.orderFindingPostprocess order 256 order_prime (a, b) = some (d : ZMod order)
        then Quantum.OrderFinding.jointRegisterProbability bitcoinAReg bitcoinBReg a.val b.val
          (Quantum.run (bitcoinECDLPSubmission.program Q) (ket zeroBasisState)) else 0 := by
  unfold naiveObserved naiveEvent
  rw [observedTrial_recordMass]
  have h := zObserve_eventProbability bitcoinAReg bitcoinBReg 256
    bitcoinWireLayout.1 bitcoinWireLayout.2.1 (recoveredPair d)
    (Quantum.run (bitcoinECDLPSubmission.program Q) (ket zeroBasisState))
  simpa [bitcoinWireLayout.1, recoveredPair, Fin.ofNat_eq_cast] using h

theorem naiveObserved_total (Q : Point) (d : Nat) (hQ : Q = d • G) (hn : Q ≠ 0) :
    (naiveObserved Q).run.bornMass (ket zeroBasisState) = 1 := by
  rw [naiveObserved, observedTrial_total]
  exact (bitcoinECDLPSubmission.correct Q d hQ hn).2.2.1

theorem naiveObserved_success (Q : Point) (d : Nat) (hQ : Q = d • G) (hn : Q ≠ 0) :
    (41 / 250 : ℝ) ≤ recordMass (naiveObserved Q).run (naiveEvent d) (ket zeroBasisState) ∧
    recordMass (naiveObserved Q).run (naiveEvent d) (ket zeroBasisState) ≤ 1 := by
  rw [naiveObserved_probability]
  have hlo := (bitcoinECDLPSubmission.correct Q d hQ hn).2.2.2
  rw [naive_bound_value] at hlo
  refine ⟨hlo, ?_⟩
  have hm := Quantum.OrderFinding.jointRegisterProbability_sum_eq_normSq
    bitcoinAReg bitcoinBReg 256 bitcoinWireLayout.1 bitcoinWireLayout.2.1
    (Quantum.run (bitcoinECDLPSubmission.program Q) (ket zeroBasisState))
  rw [(bitcoinECDLPSubmission.correct Q d hQ hn).2.2.1] at hm
  rw [← hm]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  split_ifs
  · exact le_rfl
  · exact Quantum.OrderFinding.jointRegisterProbability_nonneg _ _ _ _ _

/-- Actual 26-run probability, with all reset outcomes retained. -/
theorem naiveRepeated_probability (Q : Point) (d : Nat) (hQ : Q = d • G) (hn : Q ≠ 0) :
    Instrument.bornMass ((naiveRepeated Q).run.filter
      (fun b => naiveRepeatedSuccess Q d b.history)) (ket zeroBasisState) =
      independentRetrySuccessProbability
        (recordMass (naiveObserved Q).run (naiveEvent d) (ket zeroBasisState)) 26 := by
  unfold naiveRepeated naiveRepeatedSuccess
  rw [resetTrial_twentySix _ _ (naiveObserved_length Q) (naiveObserved_total Q d hQ hn)]
  rw [recordMass_filter]

/-- The old numerical guarantee now applies to an explicit sequential instrument. -/
theorem naiveRepeated_success (Q : Point) (d : Nat) (hQ : Q = d • G) (hn : Q ≠ 0) :
    (99 / 100 : ℝ) ≤ Instrument.bornMass ((naiveRepeated Q).run.filter
      (fun b => naiveRepeatedSuccess Q d b.history)) (ket zeroBasisState) := by
  rw [naiveRepeated_probability Q d hQ hn]
  have hp := naiveObserved_success Q d hQ hn
  calc
    (99 / 100 : ℝ) ≤ independentRetrySuccessProbability (41 / 250) 26 :=
      by simpa [independentRetrySuccessProbability, naive_bound_value, naive_trialCount_value] using
        bitcoinECDLPSubmission.trialCount_correct
    _ ≤ _ := independentRetrySuccessProbability_mono 26 hp.2 hp.1

end
end ShorECDLP.NaiveChallenge
