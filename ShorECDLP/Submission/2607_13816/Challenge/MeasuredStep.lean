import ShorECDLP.Submission.«2607_13816».Challenge.Endpoint
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredStep
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
attribute [local irreducible] remainderBlockProgram coefficientBlockProgram phaseProgram phaseInverseProgram
def measuredStepSources (r : IndexedStepRegisters) (width T : Nat) : List AdaptiveCircuit :=
  ([.unitary (blockAForward r) .done,
    blockBAdaptive r width (certifiedActiveWindows width T).remainder,
    .unitary (blockCForward r ++ blockDForward r (certifiedActiveWindows width T).quotientSwap) .done,
    blockEAdaptive r width (certifiedActiveWindows width T).coefficient,
    .unitary (blockFForward r) .done,
    phaseUpdateEpochAdaptive r.phaseUpdate r.shiftEpoch,
    measuredBlockHForward r width T] : List AdaptiveCircuit)
def measuredStepSegments (n : Nat) (r : IndexedStepRegisters) (width T : Nat) : List (FixedSegment n) :=
  ([(fun _ => ⟨0, literalProgram (blockAForward r)⟩),
    (fun cursor => remainderBlockProgram n cursor r width (certifiedActiveWindows width T).remainder),
    (fun _ => ⟨0, literalProgram (blockCForward r ++ blockDForward r (certifiedActiveWindows width T).quotientSwap)⟩),
    (fun cursor => coefficientBlockProgram n cursor r width (certifiedActiveWindows width T).coefficient),
    (fun _ => ⟨0, literalProgram (blockFForward r)⟩),
    (fun cursor => phaseProgram n cursor r.phaseUpdate r.shiftEpoch),
    (fun cursor => hProgram n cursor r width T)] : List (FixedSegment n))
theorem measuredStepSources_eq (r : IndexedStepRegisters) (width T : Nat) :
    sequenceCircuit (measuredStepSources r width T) = measuredIndexedStep r width T := by
  simp only [measuredStepSources, sequenceCircuit, measuredIndexedStep, measuredStepPrefix, adaptive_seq_assoc, adaptive_seq_done]
  rfl

def measuredStepProgram (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) : (count : Nat) × Straight n start (start+count) :=
  sequenceProgram n (measuredStepSegments n r width T) start
attribute [local irreducible] measuredStepProgram
theorem measuredStepProgram_run (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (measuredStepProgram n start r width T) read history = (measuredIndexedStep r width T).run := by
  unfold measuredStepProgram
  rw [← measuredStepSources_eq r width T]
  apply sequenceProgram_run
  unfold measuredStepSegments measuredStepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))
  · intro cursor h
    exact literalCompiled_run _ read h
  · intro cursor h
    exact remainderBlockProgram_run n cursor r width (certifiedActiveWindows width T).remainder read h
  · intro cursor h
    exact literalCompiled_run _ read h
  · intro cursor h
    exact coefficientBlockProgram_run n cursor r width (certifiedActiveWindows width T).coefficient read h
  · intro cursor h
    exact literalCompiled_run _ read h
  · intro cursor h
    exact phaseProgram_run n cursor r.phaseUpdate r.shiftEpoch read h
  · intro cursor h
    exact hProgram_run n cursor r width T read h

theorem measuredStepProgram_tCount (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (measuredStepProgram n start r width T) read history = (measuredIndexedStep r width T).tCount := by
  unfold measuredStepProgram
  rw [← measuredStepSources_eq r width T]
  apply sequenceProgram_tCount
  unfold measuredStepSegments measuredStepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))
  · intro cursor h
    exact literalCompiled_tCount _ read h
  · intro cursor h
    exact remainderBlockProgram_tCount n cursor r width (certifiedActiveWindows width T).remainder read h
  · intro cursor h
    exact literalCompiled_tCount _ read h
  · intro cursor h
    exact coefficientBlockProgram_tCount n cursor r width (certifiedActiveWindows width T).coefficient read h
  · intro cursor h
    exact literalCompiled_tCount _ read h
  · intro cursor h
    exact phaseProgram_tCount n cursor r.phaseUpdate r.shiftEpoch read h
  · intro cursor h
    exact hProgram_tCount n cursor r width T read h

def measuredInverseStepSources (r : IndexedStepRegisters) (T : Nat) : List AdaptiveCircuit :=
  ([measuredBlockHInverse r 256 T,
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
def measuredInverseStepSegments (n : Nat) (r : IndexedStepRegisters) (T : Nat) : List (FixedSegment n) :=
  ([(fun cursor => hInverseProgram n cursor r 256 T),
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
theorem measuredInverseStepSources_eq (r : IndexedStepRegisters) (T : Nat) :
    sequenceCircuit (measuredInverseStepSources r T) = measuredIndexedStepInverse r 256 T := by
  have h := indexedInverseStepSources_eq r T
  rw [indexedStepInverseAdaptive_factor] at h
  have ht : sequenceCircuit (indexedInverseStepSources r T).tail = indexedStepInverseTailAdaptive r 256 T := by
    change AdaptiveCircuit.unitary (blockHInverse r 256 T) (sequenceCircuit (indexedInverseStepSources r T).tail) =
      AdaptiveCircuit.unitary (blockHInverse r 256 T) (indexedStepInverseTailAdaptive r 256 T) at h
    injection h with ht
  change (measuredBlockHInverse r 256 T).seq (sequenceCircuit (indexedInverseStepSources r T).tail) = _
  rw [ht]
  rfl

def measuredInverseStepProgram (n start : Nat) (r : IndexedStepRegisters) (T : Nat) : (count : Nat) × Straight n start (start+count) :=
  sequenceProgram n (measuredInverseStepSegments n r T) start
attribute [local irreducible] measuredInverseStepProgram
theorem measuredInverseStepProgram_run (n start : Nat) (r : IndexedStepRegisters) (T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (measuredInverseStepProgram n start r T) read history = (measuredIndexedStepInverse r 256 T).run := by
  unfold measuredInverseStepProgram
  rw [← measuredInverseStepSources_eq r T]
  apply sequenceProgram_run
  unfold measuredInverseStepSegments measuredInverseStepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))))
  · intro cursor h
    exact hInverseProgram_run n cursor r 256 T read h
  · intro cursor h
    exact phaseInverseProgram_run n cursor r.phaseUpdate r.shiftEpoch read h
  · intro cursor h
    exact literalCompiled_run _ read h
  · intro cursor h
    exact coefficientInverseProgram_run n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .add true .work2 read h
  · intro cursor h
    exact literalCompiled_run _ read h
  · intro cursor h
    exact coefficientInverseProgram_run n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .sub false .work2 read h
  · intro cursor h
    exact literalCompiled_run _ read h
  · intro cursor h
    exact intervalInverseProgram_run n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .add false .work1 read h
  · intro cursor h
    exact literalCompiled_run _ read h
  · intro cursor h
    exact intervalInverseProgram_run n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .sub true .work1 read h
  · intro cursor h
    exact literalCompiled_run _ read h

theorem measuredInverseStepProgram_tCount (n start : Nat) (r : IndexedStepRegisters) (T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (measuredInverseStepProgram n start r T) read history = (measuredIndexedStepInverse r 256 T).tCount := by
  unfold measuredInverseStepProgram
  rw [← measuredInverseStepSources_eq r T]
  apply sequenceProgram_tCount
  unfold measuredInverseStepSegments measuredInverseStepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))))
  · intro cursor h
    exact hInverseProgram_tCount n cursor r 256 T read h
  · intro cursor h
    exact phaseInverseProgram_tCount n cursor r.phaseUpdate r.shiftEpoch read h
  · intro cursor h
    exact literalCompiled_tCount _ read h
  · intro cursor h
    exact coefficientInverseProgram_tCount n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .add true .work2 read h
  · intro cursor h
    exact literalCompiled_tCount _ read h
  · intro cursor h
    exact coefficientInverseProgram_tCount n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .sub false .work2 read h
  · intro cursor h
    exact literalCompiled_tCount _ read h
  · intro cursor h
    exact intervalInverseProgram_tCount n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .add false .work1 read h
  · intro cursor h
    exact literalCompiled_tCount _ read h
  · intro cursor h
    exact intervalInverseProgram_tCount n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .sub true .work1 read h
  · intro cursor h
    exact literalCompiled_tCount _ read h


end ShorECDLP.Paper2607_13816.ChallengeMigration
