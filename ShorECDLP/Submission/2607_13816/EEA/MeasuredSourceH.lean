import ShorECDLP.Submission.«2607_13816».EEA.SourceDecoders
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredPrimitiveCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
@[simp] private theorem erase_ite (p : Prop) [Decidable p] (a b : CorrectionProgram) :
    (if p then a else b).erase = if p then a.erase else b.erase := by split <;> rfl
private def ordinary (g : Circuit) (p : CorrectionProgram) : CorrectionProgram :=
  .unitary [.ordinary g] p
@[simp] private theorem ordinary_erase (g : Circuit) (p : CorrectionProgram) :
    (ordinary g p).erase = .unitary g p.erase := by
  simp [ordinary, CorrectionProgram.erase, correctionBlockErase, CorrectionFragment.erase]
private def Counted (p : CorrectionProgram) : Prop := p.events = p.erase.measurementCount
private theorem counted_done : Counted .done := rfl
private theorem counted_ordinary (g : Circuit) (p : CorrectionProgram) (h : Counted p) :
    Counted (ordinary g p) := by simpa [Counted, ordinary, CorrectionProgram.events,
      correctionBlockEvents, CorrectionFragment.events, AdaptiveCircuit.measurementCount] using h
private theorem counted_seq (a b : CorrectionProgram) (ha : Counted a) (hb : Counted b) :
    Counted (a.seq b) := by
  simp only [Counted, CorrectionProgram.events_seq, CorrectionProgram.erase_seq,
    modularMeasurements_seq] at *
  omega
private theorem counted_and (a b t : Wire) : Counted (measuredAndEraseSource a b t) := rfl
private theorem counted_zero (a b t : Wire) : Counted (eraseZeroAndSource a b t) := by
  unfold eraseZeroAndSource
  apply counted_seq
  · exact counted_ordinary _ _ (counted_and _ _ _)
  · exact counted_ordinary _ _ counted_done
private theorem counted_unary (order : UnaryOrder) (leaf : Nat → Wire → CorrectionProgram)
    (h : ∀ l w, Counted (leaf l w)) (tree : UnaryActionTree) (q : Wire) (path : List Wire) :
    Counted (unaryAdaptiveActionSource order leaf tree q path) := by
  induction tree generalizing q path with
  | leaf l => exact h l q
  | node index zero one ihz iho =>
    cases path with
    | nil => exact counted_done
    | cons w ws =>
      cases order <;> simp only [unaryAdaptiveActionSource]
      all_goals
        repeat' first
          | apply counted_seq
          | apply counted_ordinary
          | exact ihz _ _
          | exact iho _ _
          | exact counted_zero _ _ _
          | exact counted_and _ _ _
          | exact counted_done
private theorem counted_ite (p : Prop) [Decidable p] (a b : CorrectionProgram)
    (ha : Counted a) (hb : Counted b) : Counted (if p then a else b) := by
  split <;> assumption
def measuredZeroCellSource (base : Bool) (rangeControl bit guard target temporary : Wire) :
    CorrectionProgram :=
  ordinary (measuredZeroPrefix base rangeControl bit guard target temporary)
    (measuredAndEraseSource rangeControl bit temporary)
theorem measuredZeroCellSource_erase (base : Bool) (rangeControl bit guard target temporary : Wire) :
    (measuredZeroCellSource base rangeControl bit guard target temporary).erase = measuredZeroCell base rangeControl bit guard target temporary := by
  simp [measuredZeroCellSource, measuredZeroCell, ordinary_erase, measuredAndEraseSource_erase]
private theorem measuredZeroCellSource_counted (base : Bool) (rangeControl bit guard target temporary : Wire) :
    Counted (measuredZeroCellSource base rangeControl bit guard target temporary) := by
  unfold measuredZeroCellSource
  repeat' first
    | apply counted_ite
    | apply counted_seq
    | apply counted_ordinary
    | exact counted_done
    | exact counted_and _ _ _
attribute [local irreducible] measuredZeroCellSource
def measuredUpperForwardLeafSource (k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (rangeAccumulator : Wire) : CorrectionProgram :=
  if k ≤ label ∧ label ≤ K then
    if label = K then
      measuredZeroCellSource true rangeAccumulator (bitAt label) control (dirtyAt label) temporary
    else measuredZeroCellSource false rangeAccumulator (bitAt label) (dirtyAt (label + 1))
      (dirtyAt label) temporary
  else .done
theorem measuredUpperForwardLeafSource_erase (k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (rangeAccumulator : Wire) :
    (measuredUpperForwardLeafSource k K control temporary bitAt dirtyAt label rangeAccumulator).erase = measuredUpperForwardLeaf k K control temporary bitAt dirtyAt label rangeAccumulator := by
  simp [measuredUpperForwardLeafSource, measuredUpperForwardLeaf, CorrectionProgram.erase, measuredZeroCellSource_erase]
private theorem measuredUpperForwardLeafSource_counted (k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (rangeAccumulator : Wire) :
    Counted (measuredUpperForwardLeafSource k K control temporary bitAt dirtyAt label rangeAccumulator) := by
  unfold measuredUpperForwardLeafSource
  repeat' first
    | apply counted_ite
    | apply counted_seq
    | apply counted_ordinary
    | exact counted_done
    | exact counted_and _ _ _
    | intro l w
    | apply counted_unary
    | apply measuredZeroCellSource_counted
attribute [local irreducible] measuredUpperForwardLeafSource
def measuredUpperReverseLeafSource (k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (rangeAccumulator : Wire) : CorrectionProgram :=
  if k ≤ label ∧ label < K then
    measuredZeroCellSource false rangeAccumulator (bitAt label) (dirtyAt (label + 1))
      (dirtyAt label) temporary
  else .done
theorem measuredUpperReverseLeafSource_erase (k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (rangeAccumulator : Wire) :
    (measuredUpperReverseLeafSource k K temporary bitAt dirtyAt label rangeAccumulator).erase = measuredUpperReverseLeaf k K temporary bitAt dirtyAt label rangeAccumulator := by
  simp [measuredUpperReverseLeafSource, measuredUpperReverseLeaf, CorrectionProgram.erase, measuredZeroCellSource_erase]
private theorem measuredUpperReverseLeafSource_counted (k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (rangeAccumulator : Wire) :
    Counted (measuredUpperReverseLeafSource k K temporary bitAt dirtyAt label rangeAccumulator) := by
  unfold measuredUpperReverseLeafSource
  repeat' first
    | apply counted_ite
    | apply counted_seq
    | apply counted_ordinary
    | exact counted_done
    | exact counted_and _ _ _
    | intro l w
    | apply counted_unary
    | apply measuredZeroCellSource_counted
attribute [local irreducible] measuredUpperReverseLeafSource
def measuredLowerForwardLeafSource (k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (rangeAccumulator : Wire) : CorrectionProgram :=
  if k ≤ label ∧ label ≤ K then
    if label = k then
      measuredZeroCellSource true rangeAccumulator (bitAt label) control (dirtyAt label) temporary
    else measuredZeroCellSource false rangeAccumulator (bitAt label) (dirtyAt (label - 1))
      (dirtyAt label) temporary
  else .done
theorem measuredLowerForwardLeafSource_erase (k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (rangeAccumulator : Wire) :
    (measuredLowerForwardLeafSource k K control temporary bitAt dirtyAt label rangeAccumulator).erase = measuredLowerForwardLeaf k K control temporary bitAt dirtyAt label rangeAccumulator := by
  simp [measuredLowerForwardLeafSource, measuredLowerForwardLeaf, CorrectionProgram.erase, measuredZeroCellSource_erase]
private theorem measuredLowerForwardLeafSource_counted (k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (rangeAccumulator : Wire) :
    Counted (measuredLowerForwardLeafSource k K control temporary bitAt dirtyAt label rangeAccumulator) := by
  unfold measuredLowerForwardLeafSource
  repeat' first
    | apply counted_ite
    | apply counted_seq
    | apply counted_ordinary
    | exact counted_done
    | exact counted_and _ _ _
    | intro l w
    | apply counted_unary
    | apply measuredZeroCellSource_counted
attribute [local irreducible] measuredLowerForwardLeafSource
def measuredLowerReverseLeafSource (k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (rangeAccumulator : Wire) : CorrectionProgram :=
  if k < label ∧ label ≤ K then
    measuredZeroCellSource false rangeAccumulator (bitAt label) (dirtyAt (label - 1))
      (dirtyAt label) temporary
  else .done
theorem measuredLowerReverseLeafSource_erase (k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (rangeAccumulator : Wire) :
    (measuredLowerReverseLeafSource k K temporary bitAt dirtyAt label rangeAccumulator).erase = measuredLowerReverseLeaf k K temporary bitAt dirtyAt label rangeAccumulator := by
  simp [measuredLowerReverseLeafSource, measuredLowerReverseLeaf, CorrectionProgram.erase, measuredZeroCellSource_erase]
private theorem measuredLowerReverseLeafSource_counted (k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (rangeAccumulator : Wire) :
    Counted (measuredLowerReverseLeafSource k K temporary bitAt dirtyAt label rangeAccumulator) := by
  unfold measuredLowerReverseLeafSource
  repeat' first
    | apply counted_ite
    | apply counted_seq
    | apply counted_ordinary
    | exact counted_done
    | exact counted_and _ _ _
    | intro l w
    | apply counted_unary
    | apply measuredZeroCellSource_counted
attribute [local irreducible] measuredLowerReverseLeafSource
def measuredRangeLeafSource (toggleAfter : Bool) (rangeAccumulator : Wire)
    (leaf : Nat → Wire → CorrectionProgram) (label : Nat) (dynamic : Wire) : CorrectionProgram :=
  if toggleAfter then
    (leaf label rangeAccumulator).seq (ordinary [.CX dynamic rangeAccumulator] .done)
  else ordinary [.CX dynamic rangeAccumulator] (leaf label rangeAccumulator)
theorem measuredRangeLeafSource_erase (toggleAfter : Bool) (rangeAccumulator : Wire)
    (leaf : Nat → Wire → CorrectionProgram) (label : Nat) (dynamic : Wire) :
    (measuredRangeLeafSource toggleAfter rangeAccumulator leaf label dynamic).erase = measuredRangeLeaf toggleAfter rangeAccumulator (fun l w => (leaf l w).erase) label dynamic := by
  simp [measuredRangeLeafSource, measuredRangeLeaf, ordinary_erase, CorrectionProgram.erase_seq, CorrectionProgram.erase]
private theorem measuredRangeLeafSource_counted (toggleAfter : Bool) (rangeAccumulator : Wire)
    (leaf : Nat → Wire → CorrectionProgram) (label : Nat) (dynamic : Wire) (h : ∀ l w, Counted (leaf l w)) :
    Counted (measuredRangeLeafSource toggleAfter rangeAccumulator leaf label dynamic) := by
  unfold measuredRangeLeafSource
  repeat' first
    | apply counted_ite
    | apply counted_seq
    | apply counted_ordinary
    | exact counted_done
    | exact counted_and _ _ _
    | intro l w
    | apply counted_unary
    | assumption
    | intro l w
    | exact h _ _
attribute [local irreducible] measuredRangeLeafSource
def measuredRangeScanSource (toggleAfter : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control rangeAccumulator : Wire) (path : List Wire)
    (leaf : Nat → Wire → CorrectionProgram) : CorrectionProgram :=
  if toggleAfter then
    ordinary [.CX control rangeAccumulator]
      (unaryAdaptiveActionSource order (measuredRangeLeafSource true rangeAccumulator leaf) tree control path)
  else
    (unaryAdaptiveActionSource order (measuredRangeLeafSource false rangeAccumulator leaf) tree control path).seq
      (ordinary [.CX control rangeAccumulator] .done)
theorem measuredRangeScanSource_erase (toggleAfter : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control rangeAccumulator : Wire) (path : List Wire)
    (leaf : Nat → Wire → CorrectionProgram) :
    (measuredRangeScanSource toggleAfter order tree control rangeAccumulator path leaf).erase = measuredRangeScan toggleAfter order tree control rangeAccumulator path (fun l w => (leaf l w).erase) := by
  simp [measuredRangeScanSource, measuredRangeScan, ordinary_erase, CorrectionProgram.erase_seq, CorrectionProgram.erase, unaryAdaptiveActionSource_erase, measuredRangeLeafSource_erase]
private theorem measuredRangeScanSource_counted (toggleAfter : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control rangeAccumulator : Wire) (path : List Wire)
    (leaf : Nat → Wire → CorrectionProgram) (h : ∀ l w, Counted (leaf l w)) :
    Counted (measuredRangeScanSource toggleAfter order tree control rangeAccumulator path leaf) := by
  unfold measuredRangeScanSource
  repeat' first
    | apply counted_ite
    | apply counted_seq
    | apply counted_ordinary
    | exact counted_done
    | exact counted_and _ _ _
    | intro l w
    | apply counted_unary
    | apply measuredRangeLeafSource_counted
    | assumption
    | intro l w
    | exact h _ _
attribute [local irreducible] measuredRangeScanSource
def measuredUpperZeroMapSource (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) : CorrectionProgram :=
  (measuredRangeScanSource true .inc tree control rangeAccumulator path
    (measuredUpperForwardLeafSource k K control temporary bitAt dirtyAt)).seq
  (measuredRangeScanSource false .dec tree control rangeAccumulator path
    (measuredUpperReverseLeafSource k K temporary bitAt dirtyAt))
theorem measuredUpperZeroMapSource_erase (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) :
    (measuredUpperZeroMapSource k K tree control rangeAccumulator temporary path bitAt dirtyAt).erase = measuredUpperZeroMap k K tree control rangeAccumulator temporary path bitAt dirtyAt := by
  simp [measuredUpperZeroMapSource, measuredUpperZeroMap, CorrectionProgram.erase_seq, measuredUpperForwardLeafSource_erase, measuredUpperReverseLeafSource_erase, measuredRangeScanSource_erase]
private theorem measuredUpperZeroMapSource_counted (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) :
    Counted (measuredUpperZeroMapSource k K tree control rangeAccumulator temporary path bitAt dirtyAt) := by
  unfold measuredUpperZeroMapSource
  repeat' first
    | apply counted_ite
    | apply counted_seq
    | apply counted_ordinary
    | exact counted_done
    | exact counted_and _ _ _
    | intro l w
    | apply counted_unary
    | apply measuredUpperForwardLeafSource_counted
    | apply measuredUpperReverseLeafSource_counted
    | apply measuredRangeScanSource_counted
attribute [local irreducible] measuredUpperZeroMapSource
def measuredLowerZeroMapSource (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) : CorrectionProgram :=
  (measuredRangeScanSource true .dec tree control rangeAccumulator path
    (measuredLowerForwardLeafSource k K control temporary bitAt dirtyAt)).seq
  (measuredRangeScanSource false .inc tree control rangeAccumulator path
    (measuredLowerReverseLeafSource k K temporary bitAt dirtyAt))
theorem measuredLowerZeroMapSource_erase (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) :
    (measuredLowerZeroMapSource k K tree control rangeAccumulator temporary path bitAt dirtyAt).erase = measuredLowerZeroMap k K tree control rangeAccumulator temporary path bitAt dirtyAt := by
  simp [measuredLowerZeroMapSource, measuredLowerZeroMap, CorrectionProgram.erase_seq, measuredLowerForwardLeafSource_erase, measuredLowerReverseLeafSource_erase, measuredRangeScanSource_erase]
private theorem measuredLowerZeroMapSource_counted (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) :
    Counted (measuredLowerZeroMapSource k K tree control rangeAccumulator temporary path bitAt dirtyAt) := by
  unfold measuredLowerZeroMapSource
  repeat' first
    | apply counted_ite
    | apply counted_seq
    | apply counted_ordinary
    | exact counted_done
    | exact counted_and _ _ _
    | intro l w
    | apply counted_unary
    | apply measuredLowerForwardLeafSource_counted
    | apply measuredLowerReverseLeafSource_counted
    | apply measuredRangeScanSource_counted
attribute [local irreducible] measuredLowerZeroMapSource
def measuredHighestPositionWriteSource (k K : Nat) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) :
    CorrectionProgram :=
  ordinary (controlledXorConstant control targets (truthMinusOneValue targets.length K) ++ highestPositionDirtyWrites k K targets dirtyAt)
    ((measuredUpperZeroMapSource k K tree control r t path bitAt dirtyAt).seq
      (ordinary (highestPositionDirtyWrites k K targets dirtyAt)
        (measuredUpperZeroMapSource k K tree control r t path bitAt dirtyAt)))
theorem measuredHighestPositionWriteSource_erase (k K : Nat) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) :
    (measuredHighestPositionWriteSource k K tree control r t path bitAt dirtyAt targets).erase = measuredHighestPositionWrite k K tree control r t path bitAt dirtyAt targets := by
  simp [measuredHighestPositionWriteSource, measuredHighestPositionWrite, ordinary_erase, CorrectionProgram.erase_seq, measuredUpperZeroMapSource_erase]
private theorem measuredHighestPositionWriteSource_counted (k K : Nat) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) :
    Counted (measuredHighestPositionWriteSource k K tree control r t path bitAt dirtyAt targets) := by
  unfold measuredHighestPositionWriteSource
  repeat' first
    | apply counted_ite
    | apply counted_seq
    | apply counted_ordinary
    | exact counted_done
    | exact counted_and _ _ _
    | intro l w
    | apply counted_unary
    | apply measuredUpperZeroMapSource_counted
attribute [local irreducible] measuredHighestPositionWriteSource
def measuredRightLengthWriteSource (n k K : Nat) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) :
    CorrectionProgram :=
  ordinary (controlledXorConstant control targets (rightLengthValue n targets.length k) ++ rightLengthDirtyWrites n k K targets dirtyAt)
    ((measuredLowerZeroMapSource k K tree control r t path bitAt dirtyAt).seq
      (ordinary (rightLengthDirtyWrites n k K targets dirtyAt)
        (measuredLowerZeroMapSource k K tree control r t path bitAt dirtyAt)))
theorem measuredRightLengthWriteSource_erase (n k K : Nat) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) :
    (measuredRightLengthWriteSource n k K tree control r t path bitAt dirtyAt targets).erase = measuredRightLengthWrite n k K tree control r t path bitAt dirtyAt targets := by
  simp [measuredRightLengthWriteSource, measuredRightLengthWrite, ordinary_erase, CorrectionProgram.erase_seq, measuredLowerZeroMapSource_erase]
private theorem measuredRightLengthWriteSource_counted (n k K : Nat) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) :
    Counted (measuredRightLengthWriteSource n k K tree control r t path bitAt dirtyAt targets) := by
  unfold measuredRightLengthWriteSource
  repeat' first
    | apply counted_ite
    | apply counted_seq
    | apply counted_ordinary
    | exact counted_done
    | exact counted_and _ _ _
    | intro l w
    | apply counted_unary
    | apply measuredLowerZeroMapSource_counted
attribute [local irreducible] measuredRightLengthWriteSource
def measuredLenUpdateLtUnarySource
    (n k K : Nat) (tree : UnaryActionTree)
    (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) : CorrectionProgram :=
  ordinary (constMinus lengthRP constants carry (n+2))
    ((measuredHighestPositionWriteSource k K tree control r t path work2At work1At lengthT).seq
      ((measuredHighestPositionWriteSource k K tree control r t path work1At work2At lengthT).seq
        (ordinary (constMinus lengthRP constants carry (n+2)) .done)))
theorem measuredLenUpdateLtUnarySource_erase (n k K : Nat) (tree : UnaryActionTree)
    (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) :
    (measuredLenUpdateLtUnarySource n k K tree control r t carry path work1At work2At lengthT lengthRP constants).erase = measuredLenUpdateLtUnary n k K tree control r t carry path work1At work2At lengthT lengthRP constants := by
  simp [measuredLenUpdateLtUnarySource, measuredLenUpdateLtUnary, ordinary_erase, CorrectionProgram.erase_seq, CorrectionProgram.erase, measuredHighestPositionWriteSource_erase]
private theorem measuredLenUpdateLtUnarySource_counted (n k K : Nat) (tree : UnaryActionTree)
    (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) :
    Counted (measuredLenUpdateLtUnarySource n k K tree control r t carry path work1At work2At lengthT lengthRP constants) := by
  unfold measuredLenUpdateLtUnarySource
  repeat' first
    | apply counted_ite
    | apply counted_seq
    | apply counted_ordinary
    | exact counted_done
    | exact counted_and _ _ _
    | intro l w
    | apply counted_unary
    | apply measuredHighestPositionWriteSource_counted
attribute [local irreducible] measuredLenUpdateLtUnarySource
def measuredLenUpdateLrpUnarySource
    (n k K : Nat) (tree : UnaryActionTree)
    (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) : CorrectionProgram :=
  ordinary (addConstant lengthT constants carry 3)
    ((measuredRightLengthWriteSource n k K tree control r t path work1At work2At lengthRP).seq
      ((measuredRightLengthWriteSource n k K tree control r t path work2At work1At lengthRP).seq
        (ordinary (subConstant lengthT constants carry 3) .done)))
theorem measuredLenUpdateLrpUnarySource_erase (n k K : Nat) (tree : UnaryActionTree)
    (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) :
    (measuredLenUpdateLrpUnarySource n k K tree control r t carry path work1At work2At lengthT lengthRP constants).erase = measuredLenUpdateLrpUnary n k K tree control r t carry path work1At work2At lengthT lengthRP constants := by
  simp [measuredLenUpdateLrpUnarySource, measuredLenUpdateLrpUnary, ordinary_erase, CorrectionProgram.erase_seq, CorrectionProgram.erase, measuredRightLengthWriteSource_erase]
private theorem measuredLenUpdateLrpUnarySource_counted (n k K : Nat) (tree : UnaryActionTree)
    (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) :
    Counted (measuredLenUpdateLrpUnarySource n k K tree control r t carry path work1At work2At lengthT lengthRP constants) := by
  unfold measuredLenUpdateLrpUnarySource
  repeat' first
    | apply counted_ite
    | apply counted_seq
    | apply counted_ordinary
    | exact counted_done
    | exact counted_and _ _ _
    | intro l w
    | apply counted_unary
    | apply measuredRightLengthWriteSource_counted
attribute [local irreducible] measuredLenUpdateLrpUnarySource
def measuredEndUpperSource (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) : CorrectionProgram :=
  measuredLenUpdateLtUnarySource n w.k4 w.K4 (r.upperTree w) r.control
    (r.rangeAccumulator w.k4 w.K4) (r.temporary w.k4 w.K4) r.carry
    (r.path w.k4 w.K4) r.work1At r.work2At r.lengthT r.lengthRP r.constants
theorem measuredEndUpperSource_erase (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) :
    (measuredEndUpperSource r n w).erase = measuredEndUpper r n w := by
  simp [measuredEndUpperSource, measuredEndUpper, measuredLenUpdateLtUnarySource_erase]
private theorem measuredEndUpperSource_counted (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) :
    Counted (measuredEndUpperSource r n w) := by
  unfold measuredEndUpperSource
  repeat' first
    | apply counted_ite
    | apply counted_seq
    | apply counted_ordinary
    | exact counted_done
    | exact counted_and _ _ _
    | intro l w
    | apply counted_unary
    | apply measuredLenUpdateLtUnarySource_counted
attribute [local irreducible] measuredEndUpperSource
def measuredEndLowerSource (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) : CorrectionProgram :=
  measuredLenUpdateLrpUnarySource n w.k5 (w.K5Decode n) (r.lowerTree n w) r.control
    (r.rangeAccumulator w.k5 (w.K5Decode n)) (r.temporary w.k5 (w.K5Decode n)) r.carry
    (r.path w.k5 (w.K5Decode n)) r.work1At r.work2At r.lengthT r.lengthRP r.constants
theorem measuredEndLowerSource_erase (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) :
    (measuredEndLowerSource r n w).erase = measuredEndLower r n w := by
  simp [measuredEndLowerSource, measuredEndLower, measuredLenUpdateLrpUnarySource_erase]
private theorem measuredEndLowerSource_counted (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) :
    Counted (measuredEndLowerSource r n w) := by
  unfold measuredEndLowerSource
  repeat' first
    | apply counted_ite
    | apply counted_seq
    | apply counted_ordinary
    | exact counted_done
    | exact counted_and _ _ _
    | intro l w
    | apply counted_unary
    | apply measuredLenUpdateLrpUnarySource_counted
attribute [local irreducible] measuredEndLowerSource
def measuredEndIterationSource (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) : CorrectionProgram :=
  ordinary (controlledWorkSwap r.control r.work1 r.work2)
    ((measuredEndUpperSource r n w).seq (measuredEndLowerSource r n w))
theorem measuredEndIterationSource_erase (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) :
    (measuredEndIterationSource r n w).erase = measuredEndIteration r n w := by
  simp [measuredEndIterationSource, measuredEndIteration, ordinary_erase, CorrectionProgram.erase_seq, measuredEndUpperSource_erase, measuredEndLowerSource_erase]
private theorem measuredEndIterationSource_counted (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) :
    Counted (measuredEndIterationSource r n w) := by
  unfold measuredEndIterationSource
  repeat' first
    | apply counted_ite
    | apply counted_seq
    | apply counted_ordinary
    | exact counted_done
    | exact counted_and _ _ _
    | intro l w
    | apply counted_unary
    | apply measuredEndUpperSource_counted
    | apply measuredEndLowerSource_counted
attribute [local irreducible] measuredEndIterationSource
def measuredEndIterationInverseSource (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) : CorrectionProgram :=
  (measuredEndLowerSource r n w).seq ((measuredEndUpperSource r n w).seq
    (ordinary (controlledWorkSwapInverse r.control r.work1 r.work2) .done))
theorem measuredEndIterationInverseSource_erase (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) :
    (measuredEndIterationInverseSource r n w).erase = measuredEndIterationInverse r n w := by
  simp [measuredEndIterationInverseSource, measuredEndIterationInverse, ordinary_erase, CorrectionProgram.erase_seq, CorrectionProgram.erase, measuredEndUpperSource_erase, measuredEndLowerSource_erase]
private theorem measuredEndIterationInverseSource_counted (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) :
    Counted (measuredEndIterationInverseSource r n w) := by
  unfold measuredEndIterationInverseSource
  repeat' first
    | apply counted_ite
    | apply counted_seq
    | apply counted_ordinary
    | exact counted_done
    | exact counted_and _ _ _
    | intro l w
    | apply counted_unary
    | apply measuredEndUpperSource_counted
    | apply measuredEndLowerSource_counted
attribute [local irreducible] measuredEndIterationInverseSource
def measuredBlockHForwardSource (r : IndexedStepRegisters) (n T : Nat) : CorrectionProgram :=
  if T%4=0 then
    ordinary (blockHPrefix r)
      ((measuredEndIterationSource (r.endIteration n T) n (endIterationWindowsAt n T)).seq
        (ordinary ([.CX r.control r.iter] ++ blockHSuffix r) .done))
  else .done
theorem measuredBlockHForwardSource_erase (r : IndexedStepRegisters) (n T : Nat) :
    (measuredBlockHForwardSource r n T).erase = measuredBlockHForward r n T := by
  simp [measuredBlockHForwardSource, measuredBlockHForward, ordinary_erase, CorrectionProgram.erase_seq, CorrectionProgram.erase, measuredEndIterationSource_erase]
private theorem measuredBlockHForwardSource_counted (r : IndexedStepRegisters) (n T : Nat) :
    Counted (measuredBlockHForwardSource r n T) := by
  unfold measuredBlockHForwardSource
  repeat' first
    | apply counted_ite
    | apply counted_seq
    | apply counted_ordinary
    | exact counted_done
    | exact counted_and _ _ _
    | intro l w
    | apply counted_unary
    | apply measuredEndIterationSource_counted
attribute [local irreducible] measuredBlockHForwardSource
def measuredBlockHInverseSource (r : IndexedStepRegisters) (n T : Nat) : CorrectionProgram :=
  if T%4=0 then
    ordinary (blockHPrefix r ++ [.CX r.control r.iter])
      ((measuredEndIterationInverseSource (r.endIteration n T) n (endIterationWindowsAt n T)).seq
        (ordinary (blockHSuffix r) .done))
  else .done
theorem measuredBlockHInverseSource_erase (r : IndexedStepRegisters) (n T : Nat) :
    (measuredBlockHInverseSource r n T).erase = measuredBlockHInverse r n T := by
  simp [measuredBlockHInverseSource, measuredBlockHInverse, ordinary_erase, CorrectionProgram.erase_seq, CorrectionProgram.erase, measuredEndIterationInverseSource_erase]
private theorem measuredBlockHInverseSource_counted (r : IndexedStepRegisters) (n T : Nat) :
    Counted (measuredBlockHInverseSource r n T) := by
  unfold measuredBlockHInverseSource
  repeat' first
    | apply counted_ite
    | apply counted_seq
    | apply counted_ordinary
    | exact counted_done
    | exact counted_and _ _ _
    | intro l w
    | apply counted_unary
    | apply measuredEndIterationInverseSource_counted
theorem measuredBlockHForwardSource_events (r : IndexedStepRegisters) (n T : Nat) :
    (measuredBlockHForwardSource r n T).events = (measuredBlockHForward r n T).measurementCount := by
  have h := measuredBlockHForwardSource_counted r n T
  simpa only [Counted, measuredBlockHForwardSource_erase] using h
theorem measuredBlockHInverseSource_events (r : IndexedStepRegisters) (n T : Nat) :
    (measuredBlockHInverseSource r n T).events = (measuredBlockHInverse r n T).measurementCount := by
  have h := measuredBlockHInverseSource_counted r n T
  simpa only [Counted, measuredBlockHInverseSource_erase] using h
end ShorECDLP.Paper2607_13816
