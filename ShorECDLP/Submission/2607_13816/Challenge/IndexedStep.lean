import ShorECDLP.Submission.«2607_13816».Challenge.Phase
import ShorECDLP.Submission.«2607_13816».Challenge.IntervalWhole
import ShorECDLP.Submission.«2607_13816».Challenge.Coefficient
import ShorECDLP.Submission.«2607_13816».EEA.IndexedStep
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
attribute [local irreducible] intervalProgram coefficientProgram phaseProgram
def remainderBlockSources (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow) : List AdaptiveCircuit :=
  ([.unitary (rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch) .done,
    intervalAddSub (r.remainder w) width w.start w.stop .sub true .work1,
    .unitary (rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch) .done,
    .unitary (blockB2 r) .done,
    .unitary (([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal]) .done,
    intervalAddSub (r.remainder w) width w.start w.stop .add false .work1,
    .unitary (([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal]) .done] : List AdaptiveCircuit)
def remainderBlockSegments (n : Nat) (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow) : List (FixedSegment n) :=
  ([(fun _ => ⟨0, literalProgram (rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch)⟩),
    (fun cursor => intervalProgram n cursor (r.remainder w) width w.start w.stop .sub true .work1),
    (fun _ => ⟨0, literalProgram (rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch)⟩),
    (fun _ => ⟨0, literalProgram (blockB2 r)⟩),
    (fun _ => ⟨0, literalProgram (([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal])⟩),
    (fun cursor => intervalProgram n cursor (r.remainder w) width w.start w.stop .add false .work1),
    (fun _ => ⟨0, literalProgram (([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal])⟩)] : List (FixedSegment n))
theorem remainderBlockSources_eq (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow) :
    sequenceCircuit (remainderBlockSources r width w) = blockBAdaptive r width w := by
  rw [blockBAdaptive_eq_parts]
  simp only [remainderBlockSources, sequenceCircuit, adaptive_seq_assoc, adaptive_seq_done]

def remainderBlockProgram (n start : Nat) (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow) : (count : Nat) × Straight n start (start+count) :=
  sequenceProgram n (remainderBlockSegments n r width w) start
attribute [local irreducible] remainderBlockProgram
theorem remainderBlockProgram_run (n start : Nat) (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (remainderBlockProgram n start r width w) read history = (blockBAdaptive r width w).run := by
  unfold remainderBlockProgram
  rw [← remainderBlockSources_eq r width w]
  apply sequenceProgram_run
  unfold remainderBlockSegments remainderBlockSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))
  · intro cursor h
    exact literalProgram_run _ read h
  · intro cursor h
    exact intervalProgram_run n cursor (r.remainder w) width w.start w.stop .sub true .work1 read h
  · intro cursor h
    exact literalProgram_run _ read h
  · intro cursor h
    exact literalProgram_run _ read h
  · intro cursor h
    exact literalProgram_run _ read h
  · intro cursor h
    exact intervalProgram_run n cursor (r.remainder w) width w.start w.stop .add false .work1 read h
  · intro cursor h
    exact literalProgram_run _ read h

theorem remainderBlockProgram_tCount (n start : Nat) (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (remainderBlockProgram n start r width w) read history = (blockBAdaptive r width w).tCount := by
  unfold remainderBlockProgram
  rw [← remainderBlockSources_eq r width w]
  apply sequenceProgram_tCount
  unfold remainderBlockSegments remainderBlockSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))
  · intro cursor h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]
  · intro cursor h
    exact intervalProgram_tCount n cursor (r.remainder w) width w.start w.stop .sub true .work1 read h
  · intro cursor h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]
  · intro cursor h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]
  · intro cursor h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]
  · intro cursor h
    exact intervalProgram_tCount n cursor (r.remainder w) width w.start w.stop .add false .work1 read h
  · intro cursor h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]

def coefficientBlockSources (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow) : List AdaptiveCircuit :=
  ([.unitary (((computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch) ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch) ++ prepareLatestPaperTBoundary r.tBoundary width) .done,
    coefficientPrefixAdaptive (r.coefficient w) w.start w.stop .sub false .work2,
    .unitary ((((computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch) ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch) ++ [.CX r.phase1 r.sign]) ++ computeControl [r.phase1] 1 r.control r.blockScratch) .done,
    coefficientPrefixAdaptive (r.coefficient w) w.start w.stop .add true .work2,
    .unitary (computeControl [r.phase1] 1 r.control r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary width) .done] : List AdaptiveCircuit)
def coefficientBlockSegments (n : Nat) (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow) : List (FixedSegment n) :=
  ([(fun _ => ⟨0, literalProgram (((computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch) ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch) ++ prepareLatestPaperTBoundary r.tBoundary width)⟩),
    (fun cursor => coefficientProgram n cursor (r.coefficient w) w.start w.stop .sub false .work2),
    (fun _ => ⟨0, literalProgram ((((computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch) ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch) ++ [.CX r.phase1 r.sign]) ++ computeControl [r.phase1] 1 r.control r.blockScratch)⟩),
    (fun cursor => coefficientProgram n cursor (r.coefficient w) w.start w.stop .add true .work2),
    (fun _ => ⟨0, literalProgram (computeControl [r.phase1] 1 r.control r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary width)⟩)] : List (FixedSegment n))
theorem coefficientBlockSources_eq (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow) :
    sequenceCircuit (coefficientBlockSources r width w) = blockEAdaptive r width w := by
  rw [blockEAdaptive_eq_parts]
  simp only [coefficientBlockSources, sequenceCircuit, adaptive_seq_assoc, adaptive_seq_done]

def coefficientBlockProgram (n start : Nat) (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow) : (count : Nat) × Straight n start (start+count) :=
  sequenceProgram n (coefficientBlockSegments n r width w) start
attribute [local irreducible] coefficientBlockProgram
theorem coefficientBlockProgram_run (n start : Nat) (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (coefficientBlockProgram n start r width w) read history = (blockEAdaptive r width w).run := by
  unfold coefficientBlockProgram
  rw [← coefficientBlockSources_eq r width w]
  apply sequenceProgram_run
  unfold coefficientBlockSegments coefficientBlockSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor h
    exact literalProgram_run _ read h
  · intro cursor h
    exact coefficientProgram_run n cursor (r.coefficient w) w.start w.stop .sub false .work2 read h
  · intro cursor h
    exact literalProgram_run _ read h
  · intro cursor h
    exact coefficientProgram_run n cursor (r.coefficient w) w.start w.stop .add true .work2 read h
  · intro cursor h
    exact literalProgram_run _ read h

theorem coefficientBlockProgram_tCount (n start : Nat) (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (coefficientBlockProgram n start r width w) read history = (blockEAdaptive r width w).tCount := by
  unfold coefficientBlockProgram
  rw [← coefficientBlockSources_eq r width w]
  apply sequenceProgram_tCount
  unfold coefficientBlockSegments coefficientBlockSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]
  · intro cursor h
    exact coefficientProgram_tCount n cursor (r.coefficient w) w.start w.stop .sub false .work2 read h
  · intro cursor h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]
  · intro cursor h
    exact coefficientProgram_tCount n cursor (r.coefficient w) w.start w.stop .add true .work2 read h
  · intro cursor h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]

def indexedStepSources (r : IndexedStepRegisters) (width T : Nat) : List AdaptiveCircuit :=
  ([.unitary (blockAForward r) .done,
    blockBAdaptive r width (certifiedActiveWindows width T).remainder,
    .unitary (blockCForward r ++ blockDForward r (certifiedActiveWindows width T).quotientSwap) .done,
    blockEAdaptive r width (certifiedActiveWindows width T).coefficient,
    .unitary (blockFForward r) .done,
    phaseUpdateEpochAdaptive r.phaseUpdate r.shiftEpoch,
    .unitary (blockHForward r width T) .done] : List AdaptiveCircuit)
def indexedStepSegments (n : Nat) (r : IndexedStepRegisters) (width T : Nat) : List (FixedSegment n) :=
  ([(fun _ => ⟨0, literalProgram (blockAForward r)⟩),
    (fun cursor => remainderBlockProgram n cursor r width (certifiedActiveWindows width T).remainder),
    (fun _ => ⟨0, literalProgram (blockCForward r ++ blockDForward r (certifiedActiveWindows width T).quotientSwap)⟩),
    (fun cursor => coefficientBlockProgram n cursor r width (certifiedActiveWindows width T).coefficient),
    (fun _ => ⟨0, literalProgram (blockFForward r)⟩),
    (fun cursor => phaseProgram n cursor r.phaseUpdate r.shiftEpoch),
    (fun _ => ⟨0, literalProgram (blockHForward r width T)⟩)] : List (FixedSegment n))
theorem indexedStepSources_eq (r : IndexedStepRegisters) (width T : Nat) :
    sequenceCircuit (indexedStepSources r width T) = indexedStepAdaptive r width T := by
  simp only [indexedStepSources, sequenceCircuit, indexedStepAdaptive, adaptive_seq_done]
  rfl

def indexedStepProgram (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) : (count : Nat) × Straight n start (start+count) :=
  sequenceProgram n (indexedStepSegments n r width T) start
attribute [local irreducible] indexedStepProgram
theorem indexedStepProgram_run (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (indexedStepProgram n start r width T) read history = (indexedStepAdaptive r width T).run := by
  unfold indexedStepProgram
  rw [← indexedStepSources_eq r width T]
  apply sequenceProgram_run
  unfold indexedStepSegments indexedStepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))
  · intro cursor h
    exact literalProgram_run _ read h
  · intro cursor h
    exact remainderBlockProgram_run n cursor r width (certifiedActiveWindows width T).remainder read h
  · intro cursor h
    exact literalProgram_run _ read h
  · intro cursor h
    exact coefficientBlockProgram_run n cursor r width (certifiedActiveWindows width T).coefficient read h
  · intro cursor h
    exact literalProgram_run _ read h
  · intro cursor h
    exact phaseProgram_run n cursor r.phaseUpdate r.shiftEpoch read h
  · intro cursor h
    exact literalProgram_run _ read h

theorem indexedStepProgram_tCount (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (indexedStepProgram n start r width T) read history = (indexedStepAdaptive r width T).tCount := by
  unfold indexedStepProgram
  rw [← indexedStepSources_eq r width T]
  apply sequenceProgram_tCount
  unfold indexedStepSegments indexedStepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))
  · intro cursor h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]
  · intro cursor h
    exact remainderBlockProgram_tCount n cursor r width (certifiedActiveWindows width T).remainder read h
  · intro cursor h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]
  · intro cursor h
    exact coefficientBlockProgram_tCount n cursor r width (certifiedActiveWindows width T).coefficient read h
  · intro cursor h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]
  · intro cursor h
    exact phaseProgram_tCount n cursor r.phaseUpdate r.shiftEpoch read h
  · intro cursor h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]

def indexedInverseStepSources (r : IndexedStepRegisters) (T : Nat) : List AdaptiveCircuit :=
  ([.unitary (blockHInverse r 256 T) .done,
    phaseUpdateEpochInverseAdaptive r.phaseUpdate r.shiftEpoch,
    .unitary ((blockFForward r).adjoint ++ prepareLatestPaperTBoundary r.tBoundary 256 ++ computeControl [r.phase1] 1 r.control r.blockScratch) .done,
    coefficientPrefixInverseAdaptive (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .add true .work2,
    .unitary (computeControl [r.phase1] 1 r.control r.blockScratch ++ [.CX r.phase1 r.sign] ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch) .done,
    coefficientPrefixInverseAdaptive (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .sub false .work2,
    .unitary (computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256 ++ blockDInverse r (certifiedActiveWindows 256 T).quotientSwap ++ blockCInverse r ++ (([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal])) .done,
    intervalAddSubInverse (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .add false .work1,
    .unitary ((([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal]) ++ blockB2 r ++ rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch) .done,
    intervalAddSubInverse (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .sub true .work1,
    .unitary (rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch ++ blockAInverse r) .done] : List AdaptiveCircuit)
def indexedInverseStepSegments (n : Nat) (r : IndexedStepRegisters) (T : Nat) : List (FixedSegment n) :=
  ([(fun _ => ⟨0, literalProgram (blockHInverse r 256 T)⟩),
    (fun cursor => phaseInverseProgram n cursor r.phaseUpdate r.shiftEpoch),
    (fun _ => ⟨0, literalProgram ((blockFForward r).adjoint ++ prepareLatestPaperTBoundary r.tBoundary 256 ++ computeControl [r.phase1] 1 r.control r.blockScratch)⟩),
    (fun cursor => coefficientInverseProgram n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .add true .work2),
    (fun _ => ⟨0, literalProgram (computeControl [r.phase1] 1 r.control r.blockScratch ++ [.CX r.phase1 r.sign] ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch)⟩),
    (fun cursor => coefficientInverseProgram n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .sub false .work2),
    (fun _ => ⟨0, literalProgram (computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256 ++ blockDInverse r (certifiedActiveWindows 256 T).quotientSwap ++ blockCInverse r ++ (([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal]))⟩),
    (fun cursor => intervalInverseProgram n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .add false .work1),
    (fun _ => ⟨0, literalProgram ((([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal]) ++ blockB2 r ++ rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch)⟩),
    (fun cursor => intervalInverseProgram n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .sub true .work1),
    (fun _ => ⟨0, literalProgram (rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch ++ blockAInverse r)⟩)] : List (FixedSegment n))
theorem indexedInverseStepSources_eq (r : IndexedStepRegisters) (T : Nat) :
    sequenceCircuit (indexedInverseStepSources r T) = indexedStepInverseAdaptive r 256 T := by
  rw [indexedStepInverseAdaptive_eq_parts]
  simp only [indexedInverseStepSources, sequenceCircuit, adaptive_seq_assoc, adaptive_seq_done]

def indexedInverseStepProgram (n start : Nat) (r : IndexedStepRegisters) (T : Nat) : (count : Nat) × Straight n start (start+count) :=
  sequenceProgram n (indexedInverseStepSegments n r T) start
attribute [local irreducible] indexedInverseStepProgram
theorem indexedInverseStepProgram_run (n start : Nat) (r : IndexedStepRegisters) (T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (indexedInverseStepProgram n start r T) read history = (indexedStepInverseAdaptive r 256 T).run := by
  unfold indexedInverseStepProgram
  rw [← indexedInverseStepSources_eq r T]
  apply sequenceProgram_run
  unfold indexedInverseStepSegments indexedInverseStepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))))
  · intro cursor h
    exact literalProgram_run _ read h
  · intro cursor h
    exact phaseInverseProgram_run n cursor r.phaseUpdate r.shiftEpoch read h
  · intro cursor h
    exact literalProgram_run _ read h
  · intro cursor h
    exact coefficientInverseProgram_run n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .add true .work2 read h
  · intro cursor h
    exact literalProgram_run _ read h
  · intro cursor h
    exact coefficientInverseProgram_run n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .sub false .work2 read h
  · intro cursor h
    exact literalProgram_run _ read h
  · intro cursor h
    exact intervalInverseProgram_run n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .add false .work1 read h
  · intro cursor h
    exact literalProgram_run _ read h
  · intro cursor h
    exact intervalInverseProgram_run n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .sub true .work1 read h
  · intro cursor h
    exact literalProgram_run _ read h

theorem indexedInverseStepProgram_tCount (n start : Nat) (r : IndexedStepRegisters) (T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (indexedInverseStepProgram n start r T) read history = (indexedStepInverseAdaptive r 256 T).tCount := by
  unfold indexedInverseStepProgram
  rw [← indexedInverseStepSources_eq r T]
  apply sequenceProgram_tCount
  unfold indexedInverseStepSegments indexedInverseStepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))))
  · intro cursor h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]
  · intro cursor h
    exact phaseInverseProgram_tCount n cursor r.phaseUpdate r.shiftEpoch read h
  · intro cursor h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]
  · intro cursor h
    exact coefficientInverseProgram_tCount n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .add true .work2 read h
  · intro cursor h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]
  · intro cursor h
    exact coefficientInverseProgram_tCount n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .sub false .work2 read h
  · intro cursor h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]
  · intro cursor h
    exact intervalInverseProgram_tCount n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .add false .work1 read h
  · intro cursor h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]
  · intro cursor h
    exact intervalInverseProgram_tCount n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .sub true .work1 read h
  · intro cursor h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]

end ShorECDLP.Paper2607_13816.ChallengeMigration
