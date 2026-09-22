import ShorECDLP.Submission.«2607_13816».EEA.MeasuredEndIteration
import ShorECDLP.Submission.«2607_13816».EEA.IndexedStep
/-! # Measured scheduled endpoint refresh
The existing source prefix computes the enable flags; only the endpoint refresh
is replaced. The parity CNOT and source flag cleanup retain their literal order.
-/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
private theorem h_seq
    {a b : AdaptiveCircuit} {u v : Circuit} {P Q : BasisState → Prop}
    (ha : CoherentlyImplementsOn a (Quantum.run u) P)
    (hb : CoherentlyImplementsOn b (Quantum.run v) Q)
    (hu : HPFree u) (hp : ∀ s, P s → Q (Classical.run u s)) :
    CoherentlyImplementsOn (a.seq b) (Quantum.run (u ++ v)) P := by
  have h := ha.seq hb (by
    intro s hs
    rw [run_ket_agrees_classical u s hu]
    exact supportedOn_ket Q _ (hp s hs))
  apply h.congrIdeal
  intro s _
  exact (Quantum.run_append u v (ket s)).symm

/-- Actual every-fourth-step forward H block with measured length refresh. -/
def measuredBlockHForward (r : IndexedStepRegisters) (n T : Nat) : AdaptiveCircuit :=
  if T%4=0 then
    .unitary (blockHPrefix r)
      ((measuredEndIteration (r.endIteration n T) n (endIterationWindowsAt n T)).seq
        (.unitary ([.CX r.control r.iter] ++ blockHSuffix r) .done))
  else .done

/-- Actual inverse H block retains parity update before its measured inverse refresh. -/
def measuredBlockHInverse (r : IndexedStepRegisters) (n T : Nat) : AdaptiveCircuit :=
  if T%4=0 then
    .unitary (blockHPrefix r ++ [.CX r.control r.iter])
      ((measuredEndIterationInverse (r.endIteration n T) n (endIterationWindowsAt n T)).seq
        (.unitary (blockHSuffix r) .done))
  else .done

private theorem forward_split (r : IndexedStepRegisters) (n T : Nat) (ht : T%4=0) :
    blockHForward r n T = blockHPrefix r ++
      (swapWorkAndLengthUnaryShared (r.endIteration n T) n (endIterationWindowsAt n T) ++
        ([.CX r.control r.iter] ++ blockHSuffix r)) := by
  simp [blockHForward,ht,blockHPrefix,blockHSuffix,List.append_assoc]

private theorem inverse_split (r : IndexedStepRegisters) (n T : Nat) (ht : T%4=0) :
    blockHInverse r n T = (blockHPrefix r ++ [.CX r.control r.iter]) ++
      (swapWorkAndLengthUnarySharedInverse (r.endIteration n T) n (endIterationWindowsAt n T) ++
        blockHSuffix r) := by
  simp [blockHInverse,ht,blockHPrefix,blockHSuffix,List.append_assoc]

/-- The measured forward H block coherently implements the same literal source block. -/
theorem measuredBlockHForward_coherent (r : IndexedStepRegisters) (n T : Nat)
    (h : IndexedStepLayout r n T) :
    CoherentlyImplementsOn (measuredBlockHForward r n T) (Quantum.run (blockHForward r n T))
      (IndexedStepReady r) := by
  by_cases ht : T%4=0
  · have hm := measuredEndIteration_coherent (r.endIteration n T) n (endIterationWindowsAt n T) (h.endIteration ht)
    have hb := h_seq hm (CoherentlyImplementsOn.unitary ([.CX r.control r.iter] ++ blockHSuffix r) (fun _ => True))
      (by simp) (by intros; trivial)
    have ha := h_seq (CoherentlyImplementsOn.unitary (blockHPrefix r) (IndexedStepReady r)) hb
      (by simp [blockHPrefix]) (fun s hs => (blockHPrefix_run r n T s h hs).2)
    rw [measuredBlockHForward,if_pos ht,forward_split r n T ht]
    exact ha
  · simpa [measuredBlockHForward,blockHForward,ht] using
      (CoherentlyImplementsOn.unitary ([] : Circuit) (IndexedStepReady r))

/-- The measured inverse H block has the same coherent contract and restored scratch boundary. -/
theorem measuredBlockHInverse_coherent (r : IndexedStepRegisters) (n T : Nat)
    (h : IndexedStepLayout r n T) :
    CoherentlyImplementsOn (measuredBlockHInverse r n T) (Quantum.run (blockHInverse r n T))
      (IndexedStepReady r) := by
  by_cases ht : T%4=0
  · have hm := measuredEndIterationInverse_coherent (r.endIteration n T) n (endIterationWindowsAt n T) (h.endIteration ht)
    have hb := h_seq hm (CoherentlyImplementsOn.unitary (blockHSuffix r) (fun _ => True))
      (by simp) (by intros; trivial)
    have ha := h_seq (CoherentlyImplementsOn.unitary (blockHPrefix r ++ [.CX r.control r.iter]) (IndexedStepReady r)) hb
      (by simp [blockHPrefix]) (fun s hs => by
        rw [Classical.run_append]
        exact blockHIter_ready r n T h _ (blockHPrefix_run r n T s h hs).2)
    rw [measuredBlockHInverse,if_pos ht,inverse_split r n T ht]
    exact ha
  · simpa [measuredBlockHInverse,blockHInverse,ht] using
      (CoherentlyImplementsOn.unitary ([] : Circuit) (IndexedStepReady r))

/-- All scheduled branches are physically well formed. -/
theorem measuredBlockHForward_wellFormed (r : IndexedStepRegisters) (n T : Nat)
    (h : IndexedStepLayout r n T) : (measuredBlockHForward r n T).WellFormed := by
  by_cases ht : T%4=0
  · have hs := blockHForward_wellFormed r n T h
    rw [forward_split r n T ht] at hs
    simp only [circuitWellFormed_append] at hs
    rw [measuredBlockHForward,if_pos ht]
    exact ⟨hs.1,(measuredEndIteration_wellFormed _ _ _ (h.endIteration ht)).seq ⟨(circuitWellFormed_append _ _).mpr hs.2.2,trivial⟩⟩
  · simp [measuredBlockHForward,ht,AdaptiveCircuit.WellFormed]

/-- All inverse scheduled branches are physically well formed. -/
theorem measuredBlockHInverse_wellFormed (r : IndexedStepRegisters) (n T : Nat)
    (h : IndexedStepLayout r n T) : (measuredBlockHInverse r n T).WellFormed := by
  by_cases ht : T%4=0
  · have hs := blockHInverse_wellFormed r n T h
    rw [inverse_split r n T ht] at hs
    simp only [circuitWellFormed_append] at hs
    rw [measuredBlockHInverse,if_pos ht]
    exact ⟨(circuitWellFormed_append _ _).mpr hs.1,(measuredEndIterationInverse_wellFormed _ _ _ (h.endIteration ht)).seq ⟨hs.2.2,trivial⟩⟩
  · simp [measuredBlockHInverse,ht,AdaptiveCircuit.WellFormed]

/-- Exact savings only on indices where the source schedules a refresh. -/
def measuredBlockHSavings (n T : Nat) : Nat :=
  let w := endIterationWindowsAt n T
  if T%4=0 then (16*(w.K4+1-w.k4)-12)+(16*(w.K5Decode n+1-w.k5)-12) else 0

/-- Actual scheduled forward savings, with the flag and parity circuits counted unchanged. -/
theorem measuredBlockHForward_toffoli (r : IndexedStepRegisters) (n T : Nat)
    (h : IndexedStepLayout r n T) (hw : 2 ≤ r.lengthT.length) :
    (primitiveResources (measuredBlockHForward r n T)).toffoli + measuredBlockHSavings n T =
      eeaToffoliCount (blockHForward r n T) := by
  by_cases ht : T%4=0
  · let e := r.endIteration n T
    let w := endIterationWindowsAt n T
    have he := h.endIteration ht
    have hw' : 2 ≤ e.width := hw
    have hc := (swapWorkAndLengthUnaryShared_resourceCounts e n w hw' he).1
    have hd := measuredEndIteration_savings e.work1.length e.width n w he.k4_le_K4 he.k5_le_decode
    rw [measuredBlockHForward,if_pos ht,primitiveResources_unitary_HPFree _ _ (by simp [blockHPrefix]),
      primitiveResources_seq,primitiveResources_unitary_HPFree _ _ (by simp [blockHSuffix])]
    simp only [PrimitiveResources.add]
    rw [measuredEndIteration_toffoli _ _ _ he]
    rw [forward_split r n T ht]
    simp only [eeaToffoliCount_append]
    change _ + measuredBlockHSavings n T = _ + (eeaToffoliCount (swapWorkAndLengthUnaryShared e n w) + _)
    rw [hc]
    simp only [measuredBlockHSavings,ht,if_true]
    simp only [primitiveResources,gidneyToffoliCount,gidneyGateCount]
    dsimp only [e,w] at hd ⊢
    omega
  · simp [measuredBlockHForward,blockHForward,measuredBlockHSavings,ht,
      primitiveResources,gidneyToffoliCount,gidneyGateCount,eeaToffoliCount]

/-- Actual scheduled inverse savings, with the flag and parity circuits counted unchanged. -/
theorem measuredBlockHInverse_toffoli (r : IndexedStepRegisters) (n T : Nat)
    (h : IndexedStepLayout r n T) (hw : 2 ≤ r.lengthT.length) :
    (primitiveResources (measuredBlockHInverse r n T)).toffoli + measuredBlockHSavings n T =
      eeaToffoliCount (blockHInverse r n T) := by
  by_cases ht : T%4=0
  · let e := r.endIteration n T
    let w := endIterationWindowsAt n T
    have he := h.endIteration ht
    have hw' : 2 ≤ e.width := hw
    have hc := (swapWorkAndLengthUnaryShared_resourceCounts e n w hw' he).1
    have hd := measuredEndIteration_savings e.work1.length e.width n w he.k4_le_K4 he.k5_le_decode
    have hi := swapWorkAndLengthUnarySharedInverse_toffoliCount e n w
      (he.work1_length.trans he.work2_length.symm)
    rw [measuredBlockHInverse,if_pos ht,primitiveResources_unitary_HPFree _ _ (by simp [blockHPrefix]),
      primitiveResources_seq,primitiveResources_unitary_HPFree _ _ (by simp [blockHSuffix])]
    simp only [PrimitiveResources.add]
    rw [measuredEndIterationInverse_toffoli _ _ _ he]
    rw [inverse_split r n T ht]
    simp only [eeaToffoliCount_append]
    change _ + measuredBlockHSavings n T = _ + (eeaToffoliCount (swapWorkAndLengthUnarySharedInverse e n w) + _)
    rw [hi,hc]
    simp only [measuredBlockHSavings,ht,if_true]
    simp only [primitiveResources,gidneyToffoliCount,gidneyGateCount]
    dsimp only [e,w] at hd ⊢
    omega
  · simp [measuredBlockHInverse,blockHInverse,measuredBlockHSavings,ht,
      primitiveResources,gidneyToffoliCount,gidneyGateCount,eeaToffoliCount]
end
end ShorECDLP.Paper2607_13816
