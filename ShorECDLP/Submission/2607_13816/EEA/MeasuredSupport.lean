import ShorECDLP.Submission.«2607_13816».EEA.MeasuredBlockH
import ShorECDLP.Submission.«2607_13816».EEA.AdaptiveSupport
/-! All-branch physical support of the measured zero-map scans. -/
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Both erasure outcomes stay on the original three AND wires. -/
theorem measuredAndErase_wires_subset (a b t : Wire) :
    (measuredAndErase a b t).wires ⊆ [a,b,t] := by
  intro w hw
  simp [measuredAndErase,measureResetWithCorrection,measuredAndCorrection,
    controlledZ,AdaptiveCircuit.wires,circuitWires,gateWires] at hw ⊢
  aesop
/-- A measured cell uses only wires of the strict compute/erase reference. -/
theorem measuredZeroCell_wires_subset (base : Bool) (a b g d t : Wire) :
    (measuredZeroCell base a b g d t).wires ⊆
      circuitWires (measuredZeroPrefix base a b g d t ++ [.CCX a b t]) := by
  intro w hw
  cases base <;>
    simp_all [measuredZeroCell,measuredZeroPrefix,measuredAndErase,
      measureResetWithCorrection,measuredAndCorrection,controlledZ,
      AdaptiveCircuit.wires,circuitWires,gateWires] <;> aesop
/-- The adaptive upper forward leaf introduces no physical wire. -/
theorem measuredUpperForwardLeaf_wires_subset (k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label acc : Wire) :
    (measuredUpperForwardLeaf k K control temporary bitAt dirtyAt label acc).wires ⊆
      circuitWires (upperZeroForwardLeaf k K control temporary bitAt dirtyAt label acc) := by
  unfold measuredUpperForwardLeaf upperZeroForwardLeaf
  split
  · split
    · exact measuredZeroCell_wires_subset true _ _ _ _ _
    · exact measuredZeroCell_wires_subset false _ _ _ _ _
  · simp [AdaptiveCircuit.wires]
/-- The adaptive upper reverse leaf introduces no physical wire. -/
theorem measuredUpperReverseLeaf_wires_subset (k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label acc : Wire) :
    (measuredUpperReverseLeaf k K temporary bitAt dirtyAt label acc).wires ⊆
      circuitWires (upperZeroReverseLeaf k K temporary bitAt dirtyAt label acc) := by
  unfold measuredUpperReverseLeaf upperZeroReverseLeaf
  split
  · exact measuredZeroCell_wires_subset false _ _ _ _ _
  · simp [AdaptiveCircuit.wires]
/-- The adaptive lower forward leaf introduces no physical wire. -/
theorem measuredLowerForwardLeaf_wires_subset (k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label acc : Wire) :
    (measuredLowerForwardLeaf k K control temporary bitAt dirtyAt label acc).wires ⊆
      circuitWires (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt label acc) := by
  unfold measuredLowerForwardLeaf lowerZeroForwardLeaf
  split
  · split
    · exact measuredZeroCell_wires_subset true _ _ _ _ _
    · exact measuredZeroCell_wires_subset false _ _ _ _ _
  · simp [AdaptiveCircuit.wires]
/-- The adaptive lower reverse leaf introduces no physical wire. -/
theorem measuredLowerReverseLeaf_wires_subset (k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label acc : Wire) :
    (measuredLowerReverseLeaf k K temporary bitAt dirtyAt label acc).wires ⊆
      circuitWires (lowerZeroReverseLeaf k K temporary bitAt dirtyAt label acc) := by
  unfold measuredLowerReverseLeaf lowerZeroReverseLeaf
  split
  · exact measuredZeroCell_wires_subset false _ _ _ _ _
  · simp [AdaptiveCircuit.wires]
/-- A range pulse and payload retain the reference leaf support in either source order. -/
theorem measuredRangeLeaf_wires_subset (toggleAfter : Bool) (acc : Wire)
    (leaf : Nat → Wire → AdaptiveCircuit) (strict : Nat → Wire → Circuit)
    (h : ∀ l c, (leaf l c).wires ⊆ circuitWires (strict l c)) (label dynamic : Wire) :
    (measuredRangeLeaf toggleAfter acc leaf label dynamic).wires ⊆
      circuitWires (rangeScanLeafAction toggleAfter acc strict label dynamic) := by
  intro w hw
  have hs := h label acc
  simp only [List.subset_def,circuitWires,List.mem_flatMap] at hs
  cases toggleAfter <;>
    simp only [measuredRangeLeaf,rangeScanLeafAction,Bool.false_eq_true,if_false,if_true,
      modularWires_seq,AdaptiveCircuit.wires,circuitWires,List.flatMap_append,List.mem_append,
      List.not_mem_nil,or_false] at hw ⊢
  all_goals aesop
/-- Every decoder and payload branch stays within the literal strict scan support. -/
theorem measuredRangeScan_wires_subset (toggleAfter : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control acc : Wire) (path : List Wire)
    (leaf : Nat → Wire → AdaptiveCircuit) (strict : Nat → Wire → Circuit)
    (h : ∀ l c, (leaf l c).wires ⊆ circuitWires (strict l c)) :
    (measuredRangeScan toggleAfter order tree control acc path leaf).wires ⊆
      circuitWires (rangeScanUnitary toggleAfter order tree control acc path strict) := by
  have hs := unaryAdaptiveAction_wires_subset order
    (measuredRangeLeaf toggleAfter acc leaf) (rangeScanLeafAction toggleAfter acc strict)
    (measuredRangeLeaf_wires_subset toggleAfter acc leaf strict h) tree control path
  simp only [List.subset_def,circuitWires,List.mem_flatMap] at hs
  intro w hw
  cases toggleAfter <;>
    simp only [measuredRangeScan,rangeScanUnitary,Bool.false_eq_true,if_false,if_true,
      modularWires_seq,AdaptiveCircuit.wires,circuitWires,List.flatMap_append,List.mem_append,
      List.not_mem_nil,or_false] at hw ⊢
  all_goals aesop
/-- Both measured upper passes use only wires present in their strict source map. -/
theorem measuredUpperZeroMap_wires_subset (k K : Nat) (tree : UnaryActionTree)
    (control acc temporary : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) :
    (measuredUpperZeroMap k K tree control acc temporary path bitAt dirtyAt).wires ⊆
      circuitWires (upperZeroMapUnitary k K tree control acc temporary path bitAt dirtyAt) := by
  have hf := measuredRangeScan_wires_subset true .inc tree control acc path
    _ _ (measuredUpperForwardLeaf_wires_subset k K control temporary bitAt dirtyAt)
  have hr := measuredRangeScan_wires_subset false .dec tree control acc path
    _ _ (measuredUpperReverseLeaf_wires_subset k K temporary bitAt dirtyAt)
  simp only [List.subset_def,circuitWires,List.mem_flatMap] at hf hr
  intro w hw
  simp only [measuredUpperZeroMap,upperZeroMapUnitary,modularWires_seq,
    circuitWires,List.flatMap_append,List.mem_append] at hw ⊢
  aesop
/-- Both measured lower passes use only wires present in their strict source map. -/
theorem measuredLowerZeroMap_wires_subset (k K : Nat) (tree : UnaryActionTree)
    (control acc temporary : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) :
    (measuredLowerZeroMap k K tree control acc temporary path bitAt dirtyAt).wires ⊆
      circuitWires (lowerZeroMapUnitary k K tree control acc temporary path bitAt dirtyAt) := by
  have hf := measuredRangeScan_wires_subset true .dec tree control acc path
    _ _ (measuredLowerForwardLeaf_wires_subset k K control temporary bitAt dirtyAt)
  have hr := measuredRangeScan_wires_subset false .inc tree control acc path
    _ _ (measuredLowerReverseLeaf_wires_subset k K temporary bitAt dirtyAt)
  simp only [List.subset_def,circuitWires,List.mem_flatMap] at hf hr
  intro w hw
  simp only [measuredLowerZeroMap,lowerZeroMapUnitary,modularWires_seq,
    circuitWires,List.flatMap_append,List.mem_append] at hw ⊢
  aesop
/-- The measured writer stays on its strict source support, including borrowed data. -/
theorem measuredHighestPositionWrite_wires_subset (k K : Nat) (tree : UnaryActionTree)
    (control acc temporary : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (targets : List Wire) :
    (measuredHighestPositionWrite k K tree control acc temporary path bitAt dirtyAt targets).wires ⊆
      circuitWires (highestPositionXorWrite k K tree control acc temporary path bitAt dirtyAt targets) := by
  have hs := measuredUpperZeroMap_wires_subset k K tree control acc temporary path bitAt dirtyAt
  simp only [List.subset_def,circuitWires,List.mem_flatMap] at hs
  intro w hw
  simp only [measuredHighestPositionWrite,highestPositionXorWrite,modularWires_seq,AdaptiveCircuit.wires,
    circuitWires,List.flatMap_append,List.mem_append] at hw ⊢
  aesop
/-- The measured writer stays on its strict source support, including borrowed data. -/
theorem measuredRightLengthWrite_wires_subset (n k K : Nat) (tree : UnaryActionTree)
    (control acc temporary : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (targets : List Wire) :
    (measuredRightLengthWrite n k K tree control acc temporary path bitAt dirtyAt targets).wires ⊆
      circuitWires (rightLengthXorWrite n k K tree control acc temporary path bitAt dirtyAt targets) := by
  have hs := measuredLowerZeroMap_wires_subset k K tree control acc temporary path bitAt dirtyAt
  simp only [List.subset_def,circuitWires,List.mem_flatMap] at hs
  intro w hw
  simp only [measuredRightLengthWrite,rightLengthXorWrite,modularWires_seq,AdaptiveCircuit.wires,
    circuitWires,List.flatMap_append,List.mem_append] at hw ⊢
  aesop
/-- The complete measured length update uses no extra wire. -/
theorem measuredLenUpdateLtUnary_wires_subset (n k K : Nat) (tree : UnaryActionTree)
    (control acc temporary carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) :
    (measuredLenUpdateLtUnary n k K tree control acc temporary carry path work1At work2At lengthT lengthRP constants).wires ⊆
      circuitWires (lenUpdateLtUnary n k K tree control acc temporary carry path work1At work2At lengthT lengthRP constants) := by
  have h1 := measuredHighestPositionWrite_wires_subset k K tree control acc temporary path work1At work2At lengthT
  have h2 := measuredHighestPositionWrite_wires_subset k K tree control acc temporary path work2At work1At lengthT
  simp only [List.subset_def,circuitWires,List.mem_flatMap] at h1 h2
  intro w hw
  simp only [measuredLenUpdateLtUnary,lenUpdateLtUnary,modularWires_seq,AdaptiveCircuit.wires,
    circuitWires,List.flatMap_append,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
  aesop
/-- The complete measured length update uses no extra wire. -/
theorem measuredLenUpdateLrpUnary_wires_subset (n k K : Nat) (tree : UnaryActionTree)
    (control acc temporary carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) :
    (measuredLenUpdateLrpUnary n k K tree control acc temporary carry path work1At work2At lengthT lengthRP constants).wires ⊆
      circuitWires (lenUpdateLrpUnary n k K tree control acc temporary carry path work1At work2At lengthT lengthRP constants) := by
  have h1 := measuredRightLengthWrite_wires_subset n k K tree control acc temporary path work1At work2At lengthRP
  have h2 := measuredRightLengthWrite_wires_subset n k K tree control acc temporary path work2At work1At lengthRP
  simp only [List.subset_def,circuitWires,List.mem_flatMap] at h1 h2
  intro w hw
  simp only [measuredLenUpdateLrpUnary,lenUpdateLrpUnary,modularWires_seq,AdaptiveCircuit.wires,
    circuitWires,List.flatMap_append,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
  aesop
/-- The shared-bank measured upper update retains the strict support. -/
theorem measuredEndUpper_wires_subset (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) :
    (measuredEndUpper r n w).wires ⊆ circuitWires (strictEndUpper r n w) :=
  measuredLenUpdateLtUnary_wires_subset _ _ _ _ _ _ _ _ _ _ _ _ _ _
/-- The shared-bank measured lower update retains the strict support. -/
theorem measuredEndLower_wires_subset (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) :
    (measuredEndLower r n w).wires ⊆ circuitWires (strictEndLower r n w) :=
  measuredLenUpdateLrpUnary_wires_subset _ _ _ _ _ _ _ _ _ _ _ _ _ _
/-- The complete measured refresh stays within the original source allocation. -/
theorem measuredEndIteration_wires_subset (r : EndIterationRegisters) (n : Nat) (ws : EndIterationWindows) :
    (measuredEndIteration r n ws).wires ⊆ circuitWires (swapWorkAndLengthUnaryShared r n ws) := by
  have hu := measuredEndUpper_wires_subset r n ws
  have hl := measuredEndLower_wires_subset r n ws
  simp only [strictEndUpper,strictEndLower,List.subset_def,circuitWires,List.mem_flatMap] at hu hl
  intro w hw
  simp only [measuredEndIteration,swapWorkAndLengthUnaryShared,modularWires_seq,AdaptiveCircuit.wires,
    circuitWires,List.flatMap_append,List.mem_append] at hw ⊢
  aesop
/-- The complete measured refresh stays within the original source allocation. -/
theorem measuredEndIterationInverse_wires_subset (r : EndIterationRegisters) (n : Nat) (ws : EndIterationWindows) :
    (measuredEndIterationInverse r n ws).wires ⊆ circuitWires (swapWorkAndLengthUnarySharedInverse r n ws) := by
  have hu := measuredEndUpper_wires_subset r n ws
  have hl := measuredEndLower_wires_subset r n ws
  simp only [strictEndUpper,strictEndLower,List.subset_def,circuitWires,List.mem_flatMap] at hu hl
  intro w hw
  simp only [measuredEndIterationInverse,swapWorkAndLengthUnarySharedInverse,modularWires_seq,AdaptiveCircuit.wires,
    circuitWires,List.flatMap_append,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
  aesop
/-- The measured H block uses only wires of the original strict H block. -/
theorem measuredBlockHForward_wires_subset (r : IndexedStepRegisters) (n T : Nat) :
    (measuredBlockHForward r n T).wires ⊆ circuitWires (blockHForward r n T) := by
  have hs := measuredEndIteration_wires_subset (r.endIteration n T) n (endIterationWindowsAt n T)
  simp only [List.subset_def,circuitWires,List.mem_flatMap] at hs
  intro w hw
  by_cases ht : T%4=0
  · simp only [measuredBlockHForward,blockHForward,ht,if_true,blockHPrefix,blockHSuffix,
      modularWires_seq,AdaptiveCircuit.wires,circuitWires,List.flatMap_append,List.mem_append,
      List.not_mem_nil,or_false] at hw ⊢
    aesop
  · simp [measuredBlockHForward,ht,AdaptiveCircuit.wires] at hw
/-- The measured H block uses only wires of the original strict H block. -/
theorem measuredBlockHInverse_wires_subset (r : IndexedStepRegisters) (n T : Nat) :
    (measuredBlockHInverse r n T).wires ⊆ circuitWires (blockHInverse r n T) := by
  have hs := measuredEndIterationInverse_wires_subset (r.endIteration n T) n (endIterationWindowsAt n T)
  simp only [List.subset_def,circuitWires,List.mem_flatMap] at hs
  intro w hw
  by_cases ht : T%4=0
  · simp only [measuredBlockHInverse,blockHInverse,ht,if_true,blockHPrefix,blockHSuffix,
      modularWires_seq,AdaptiveCircuit.wires,circuitWires,List.flatMap_append,List.mem_append,
      List.not_mem_nil,or_false] at hw ⊢
    aesop
  · simp [measuredBlockHInverse,ht,AdaptiveCircuit.wires] at hw
end ShorECDLP.Paper2607_13816
