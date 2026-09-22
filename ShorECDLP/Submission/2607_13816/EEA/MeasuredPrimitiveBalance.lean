import ShorECDLP.Submission.«2607_13816».EEA.MeasuredSupport
import ShorECDLP.Submission.«2607_13816».EEA.DecoderPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.AdaptivePrimitiveCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Each removed Toffoli becomes one measurement, two H and one CNOT; X and phases agree. -/
def PrimitiveBalance (v w : PrimitiveResources) : Prop :=
  v.x=w.x ∧ v.h+2*w.measurements=w.h+2*v.measurements ∧
  v.cnot+w.measurements=w.cnot+v.measurements ∧
  v.toffoli+v.measurements=w.toffoli+w.measurements ∧ v.phase=w.phase
private def ur (c : Circuit) : PrimitiveResources := primitiveResources (.unitary c .done)
private theorem pr_unitary (c : Circuit) (a : AdaptiveCircuit) :
    primitiveResources (.unitary c a)=(ur c).add (primitiveResources a) := primitiveResources_seq (.unitary c .done) a
private theorem ur_append (c d : Circuit) : ur (c++d)=(ur c).add (ur d) := primitiveResources_unitary_append c d
private theorem balance_refl (v : PrimitiveResources) : PrimitiveBalance v v := by simp [PrimitiveBalance]
private theorem balance_add {a b c d : PrimitiveResources}
    (h : PrimitiveBalance a b) (j : PrimitiveBalance c d) : PrimitiveBalance (a.add c) (b.add d) := by
  simp only [PrimitiveBalance,PrimitiveResources.add] at *
  omega
private theorem compute_pr (a b c : Wire) : ur (computeZeroAnd a b c)=⟨2,0,0,1,0,0⟩ := rfl
private theorem cx_pr (a b : Wire) : ur [.CX a b]=⟨0,0,1,0,0,0⟩ := rfl
private theorem zero_cell_balance (base : Bool) (a b g d t : Wire) :
    PrimitiveBalance (primitiveResources (measuredZeroCell base a b g d t))
      (ur (measuredZeroPrefix base a b g d t ++ [.CCX a b t])) := by
  cases base <;> change PrimitiveBalance ⟨2,2,1,2,0,1⟩ ⟨2,0,0,3,0,0⟩ <;> simp [PrimitiveBalance]
private theorem unary_balance (order : UnaryOrder) (leaf : Nat → Wire → AdaptiveCircuit)
    (strict : Nat → Wire → Circuit) (h : ∀ l w, PrimitiveBalance (primitiveResources (leaf l w)) (ur (strict l w)))
    (tree : UnaryActionTree) (q : Wire) (path : List Wire) :
    PrimitiveBalance (primitiveResources (unaryAdaptiveAction order leaf tree q path))
      (ur (unaryActionUnitary order strict tree q path)) := by
  induction tree generalizing q path with
  | leaf l => exact h l q
  | node i z o iz io =>
    cases path with
    | nil => exact balance_refl _
    | cons w rest =>
      have hz := iz w rest
      have ho := io w rest
      cases order <;>
        simp only [unaryAdaptiveAction,unaryActionUnitary,pr_unitary,primitiveResources_seq,
          ur_append,compute_pr,cx_pr,eraseZeroAnd_primitive,PrimitiveBalance,PrimitiveResources.add] at * <;> omega

private def gr (g : Gate) := primitiveResources (.unitary [g] .done)
private theorem ur_cons (g : Gate) (c : Circuit) : ur (g::c)=(gr g).add (ur c) := ur_append [g] c
private theorem done_pr : primitiveResources .done=⟨0,0,0,0,0,0⟩ := rfl
private theorem ur_nil : ur []=⟨0,0,0,0,0,0⟩ := rfl
theorem measuredUpperForwardLeaf_balance (k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label acc : Wire) :
    PrimitiveBalance (primitiveResources (measuredUpperForwardLeaf k K control temporary bitAt dirtyAt label acc)) (ur (upperZeroForwardLeaf k K control temporary bitAt dirtyAt label acc)) := by
  unfold measuredUpperForwardLeaf upperZeroForwardLeaf
  split
  · split
    · exact zero_cell_balance true _ _ _ _ _
    · exact zero_cell_balance false _ _ _ _ _
  · exact balance_refl _
theorem measuredUpperReverseLeaf_balance (k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label acc : Wire) :
    PrimitiveBalance (primitiveResources (measuredUpperReverseLeaf k K temporary bitAt dirtyAt label acc)) (ur (upperZeroReverseLeaf k K temporary bitAt dirtyAt label acc)) := by
  unfold measuredUpperReverseLeaf upperZeroReverseLeaf
  split
  · exact zero_cell_balance false _ _ _ _ _
  · exact balance_refl _
theorem measuredLowerForwardLeaf_balance (k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label acc : Wire) :
    PrimitiveBalance (primitiveResources (measuredLowerForwardLeaf k K control temporary bitAt dirtyAt label acc)) (ur (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt label acc)) := by
  unfold measuredLowerForwardLeaf lowerZeroForwardLeaf
  split
  · split
    · exact zero_cell_balance true _ _ _ _ _
    · exact zero_cell_balance false _ _ _ _ _
  · exact balance_refl _
theorem measuredLowerReverseLeaf_balance (k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label acc : Wire) :
    PrimitiveBalance (primitiveResources (measuredLowerReverseLeaf k K temporary bitAt dirtyAt label acc)) (ur (lowerZeroReverseLeaf k K temporary bitAt dirtyAt label acc)) := by
  unfold measuredLowerReverseLeaf lowerZeroReverseLeaf
  split
  · exact zero_cell_balance false _ _ _ _ _
  · exact balance_refl _
theorem measuredRangeLeaf_balance (toggleAfter : Bool) (acc : Wire)
    (leaf : Nat → Wire → AdaptiveCircuit) (strict : Nat → Wire → Circuit)
    (h : ∀ l c, PrimitiveBalance (primitiveResources (leaf l c)) (ur (strict l c))) (label dynamic : Wire) :
    PrimitiveBalance (primitiveResources (measuredRangeLeaf toggleAfter acc leaf label dynamic)) (ur (rangeScanLeafAction toggleAfter acc strict label dynamic)) := by
  have hs := h label acc
  cases toggleAfter <;>
    simp only [measuredRangeLeaf,rangeScanLeafAction,Bool.false_eq_true,if_false,if_true,
      primitiveResources_seq,pr_unitary,ur_append,ur_nil,ur_cons,done_pr,PrimitiveBalance,PrimitiveResources.add] at * <;> omega
theorem measuredRangeScan_balance (toggleAfter : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control acc : Wire) (path : List Wire)
    (leaf : Nat → Wire → AdaptiveCircuit) (strict : Nat → Wire → Circuit)
    (h : ∀ l c, PrimitiveBalance (primitiveResources (leaf l c)) (ur (strict l c))) :
    PrimitiveBalance (primitiveResources (measuredRangeScan toggleAfter order tree control acc path leaf)) (ur (rangeScanUnitary toggleAfter order tree control acc path strict)) := by
  have hs := unary_balance order (measuredRangeLeaf toggleAfter acc leaf)
    (rangeScanLeafAction toggleAfter acc strict)
    (measuredRangeLeaf_balance toggleAfter acc leaf strict h) tree control path
  cases toggleAfter <;>
    simp only [measuredRangeScan,rangeScanUnitary,Bool.false_eq_true,if_false,if_true,
      primitiveResources_seq,pr_unitary,ur_append,ur_nil,ur_cons,done_pr,PrimitiveBalance,PrimitiveResources.add] at * <;> omega
theorem measuredUpperZeroMap_balance (k K : Nat) (tree : UnaryActionTree)
    (control acc temporary : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) :
    PrimitiveBalance (primitiveResources (measuredUpperZeroMap k K tree control acc temporary path bitAt dirtyAt)) (ur (upperZeroMapUnitary k K tree control acc temporary path bitAt dirtyAt)) := by
  have hf := measuredRangeScan_balance true .inc tree control acc path
    _ _ (measuredUpperForwardLeaf_balance k K control temporary bitAt dirtyAt)
  have hr := measuredRangeScan_balance false .dec tree control acc path
    _ _ (measuredUpperReverseLeaf_balance k K temporary bitAt dirtyAt)
  simp only [measuredUpperZeroMap,upperZeroMapUnitary,primitiveResources_seq,ur_append,PrimitiveBalance,PrimitiveResources.add] at *
  omega
theorem measuredLowerZeroMap_balance (k K : Nat) (tree : UnaryActionTree)
    (control acc temporary : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) :
    PrimitiveBalance (primitiveResources (measuredLowerZeroMap k K tree control acc temporary path bitAt dirtyAt)) (ur (lowerZeroMapUnitary k K tree control acc temporary path bitAt dirtyAt)) := by
  have hf := measuredRangeScan_balance true .dec tree control acc path
    _ _ (measuredLowerForwardLeaf_balance k K control temporary bitAt dirtyAt)
  have hr := measuredRangeScan_balance false .inc tree control acc path
    _ _ (measuredLowerReverseLeaf_balance k K temporary bitAt dirtyAt)
  simp only [measuredLowerZeroMap,lowerZeroMapUnitary,primitiveResources_seq,ur_append,PrimitiveBalance,PrimitiveResources.add] at *
  omega
theorem measuredHighestPositionWrite_balance (k K : Nat) (tree : UnaryActionTree)
    (control acc temporary : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (targets : List Wire) :
    PrimitiveBalance (primitiveResources (measuredHighestPositionWrite k K tree control acc temporary path bitAt dirtyAt targets)) (ur (highestPositionXorWrite k K tree control acc temporary path bitAt dirtyAt targets)) := by
  have hs := measuredUpperZeroMap_balance k K tree control acc temporary path bitAt dirtyAt
  simp only [measuredHighestPositionWrite,highestPositionXorWrite,primitiveResources_seq,pr_unitary,ur_append,PrimitiveBalance,PrimitiveResources.add] at *
  omega
theorem measuredRightLengthWrite_balance (n k K : Nat) (tree : UnaryActionTree)
    (control acc temporary : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (targets : List Wire) :
    PrimitiveBalance (primitiveResources (measuredRightLengthWrite n k K tree control acc temporary path bitAt dirtyAt targets)) (ur (rightLengthXorWrite n k K tree control acc temporary path bitAt dirtyAt targets)) := by
  have hs := measuredLowerZeroMap_balance k K tree control acc temporary path bitAt dirtyAt
  simp only [measuredRightLengthWrite,rightLengthXorWrite,primitiveResources_seq,pr_unitary,ur_append,PrimitiveBalance,PrimitiveResources.add] at *
  omega
theorem measuredLenUpdateLtUnary_balance (n k K : Nat) (tree : UnaryActionTree)
    (control acc temporary carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) :
    PrimitiveBalance (primitiveResources (measuredLenUpdateLtUnary n k K tree control acc temporary carry path work1At work2At lengthT lengthRP constants)) (ur (lenUpdateLtUnary n k K tree control acc temporary carry path work1At work2At lengthT lengthRP constants)) := by
  have h1 := measuredHighestPositionWrite_balance k K tree control acc temporary path work1At work2At lengthT
  have h2 := measuredHighestPositionWrite_balance k K tree control acc temporary path work2At work1At lengthT
  simp only [measuredLenUpdateLtUnary,lenUpdateLtUnary,primitiveResources_seq,pr_unitary,ur_append,done_pr,PrimitiveBalance,PrimitiveResources.add] at *
  omega
theorem measuredLenUpdateLrpUnary_balance (n k K : Nat) (tree : UnaryActionTree)
    (control acc temporary carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) :
    PrimitiveBalance (primitiveResources (measuredLenUpdateLrpUnary n k K tree control acc temporary carry path work1At work2At lengthT lengthRP constants)) (ur (lenUpdateLrpUnary n k K tree control acc temporary carry path work1At work2At lengthT lengthRP constants)) := by
  have h1 := measuredRightLengthWrite_balance n k K tree control acc temporary path work1At work2At lengthRP
  have h2 := measuredRightLengthWrite_balance n k K tree control acc temporary path work2At work1At lengthRP
  simp only [measuredLenUpdateLrpUnary,lenUpdateLrpUnary,primitiveResources_seq,pr_unitary,ur_append,done_pr,PrimitiveBalance,PrimitiveResources.add] at *
  omega
theorem measuredEndUpper_balance (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) :
    PrimitiveBalance (primitiveResources (measuredEndUpper r n w)) (ur (strictEndUpper r n w)) :=
  measuredLenUpdateLtUnary_balance _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem measuredEndLower_balance (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) :
    PrimitiveBalance (primitiveResources (measuredEndLower r n w)) (ur (strictEndLower r n w)) :=
  measuredLenUpdateLrpUnary_balance _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem measuredEndIteration_balance (r : EndIterationRegisters) (n : Nat) (ws : EndIterationWindows) :
    PrimitiveBalance (primitiveResources (measuredEndIteration r n ws)) (ur (swapWorkAndLengthUnaryShared r n ws)) := by
  have hu := measuredEndUpper_balance r n ws
  have hl := measuredEndLower_balance r n ws
  simp only [measuredEndIteration,swapWorkAndLengthUnaryShared,strictEndUpper,strictEndLower,primitiveResources_seq,pr_unitary,ur_append,PrimitiveBalance,PrimitiveResources.add] at *
  omega
theorem measuredEndIterationInverse_balance (r : EndIterationRegisters) (n : Nat) (ws : EndIterationWindows) :
    PrimitiveBalance (primitiveResources (measuredEndIterationInverse r n ws)) (ur (swapWorkAndLengthUnarySharedInverse r n ws)) := by
  have hu := measuredEndUpper_balance r n ws
  have hl := measuredEndLower_balance r n ws
  simp only [measuredEndIterationInverse,swapWorkAndLengthUnarySharedInverse,strictEndUpper,strictEndLower,primitiveResources_seq,pr_unitary,ur_append,done_pr,PrimitiveBalance,PrimitiveResources.add] at *
  omega
theorem measuredBlockHForward_balance (r : IndexedStepRegisters) (n T : Nat) :
    PrimitiveBalance (primitiveResources (measuredBlockHForward r n T)) (ur (blockHForward r n T)) := by
  have hs := measuredEndIteration_balance (r.endIteration n T) n (endIterationWindowsAt n T)
  by_cases ht : T%4=0
  · simp only [measuredBlockHForward,blockHForward,ht,if_true,blockHPrefix,blockHSuffix,
      primitiveResources_seq,pr_unitary,ur_append,ur_nil,ur_cons,done_pr,PrimitiveBalance,PrimitiveResources.add] at *
    omega
  · simp only [measuredBlockHForward,blockHForward,ht,if_false]
    exact balance_refl _
theorem measuredBlockHInverse_balance (r : IndexedStepRegisters) (n T : Nat) :
    PrimitiveBalance (primitiveResources (measuredBlockHInverse r n T)) (ur (blockHInverse r n T)) := by
  have hs := measuredEndIterationInverse_balance (r.endIteration n T) n (endIterationWindowsAt n T)
  by_cases ht : T%4=0
  · simp only [measuredBlockHInverse,blockHInverse,ht,if_true,blockHPrefix,blockHSuffix,
      primitiveResources_seq,pr_unitary,ur_append,ur_nil,ur_cons,done_pr,PrimitiveBalance,PrimitiveResources.add] at *
    omega
  · simp only [measuredBlockHInverse,blockHInverse,ht,if_false]
    exact balance_refl _
end ShorECDLP.Paper2607_13816
