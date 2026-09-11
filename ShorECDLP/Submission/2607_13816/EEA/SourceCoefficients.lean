import ShorECDLP.Submission.«2607_13816».EEA.SourceDecoders
import ShorECDLP.Submission.«2607_13816».EEA.CoefficientPrefixInverse

namespace ShorECDLP.Paper2607_13816
open Quantum
def coefficientPrefixFirstLeafSource
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) : CorrectionProgram :=
  (rippleFirstCellSource mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K)).seq
    (.unitary [.ordinary [.CX equalityControl (registers.accumulator k K)]] .done)
theorem coefficientPrefixFirstLeafSource_erase (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) :
    (coefficientPrefixFirstLeafSource registers k K mode target label equalityControl).erase=coefficientPrefixFirstLeafAdaptive registers k K mode target label equalityControl := by
  simp [coefficientPrefixFirstLeafSource,coefficientPrefixFirstLeafAdaptive,rippleFirstCellSource_erase,CorrectionProgram.erase,
    correctionBlockErase,CorrectionFragment.erase,CorrectionProgram.erase_seq]
theorem coefficientPrefixFirstLeafSource_events (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) :
    (coefficientPrefixFirstLeafSource registers k K mode target label equalityControl).events=1 := by
  simp [coefficientPrefixFirstLeafSource,rippleFirstCellSource_events,CorrectionProgram.events,
    correctionBlockEvents,CorrectionFragment.events,CorrectionProgram.events_seq]
def coefficientPrefixSecondLeafSource
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) : CorrectionProgram :=
  .unitary [.ordinary [.CX equalityControl (registers.accumulator k K)]]
    (rippleSecondCellSource mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K))
theorem coefficientPrefixSecondLeafSource_erase (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) :
    (coefficientPrefixSecondLeafSource registers k K mode target label equalityControl).erase=coefficientPrefixSecondLeafAdaptive registers k K mode target label equalityControl := by
  simp [coefficientPrefixSecondLeafSource,coefficientPrefixSecondLeafAdaptive,rippleSecondCellSource_erase,CorrectionProgram.erase,
    correctionBlockErase,CorrectionFragment.erase]
theorem coefficientPrefixSecondLeafSource_events (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) :
    (coefficientPrefixSecondLeafSource registers k K mode target label equalityControl).events=1 := by
  simp [coefficientPrefixSecondLeafSource,rippleSecondCellSource_events,CorrectionProgram.events,
    correctionBlockEvents,CorrectionFragment.events]
def coefficientPrefixSource
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) :
    CorrectionProgram :=
  .unitary [.ordinary [.CX registers.control (registers.accumulator k K)]]
    ((unaryAdaptiveActionSource .inc
      (coefficientPrefixFirstLeafSource registers k K mode target)
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K)).seq
      (.unitary [.ordinary (coefficientPrefixSignCircuit registers k K signUpdate)]
        ((unaryAdaptiveActionSource .dec
          (coefficientPrefixSecondLeafSource registers k K mode target)
          (coefficientPrefixTree registers k K) registers.control
          (registers.path k K)).seq
          (.unitary [.ordinary [.CX registers.control (registers.accumulator k K)]] .done))))
theorem coefficientPrefixSource_erase (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) :
    (coefficientPrefixSource registers k K mode signUpdate target).erase=coefficientPrefixAdaptive registers k K mode signUpdate target := by
  simp [coefficientPrefixSource,coefficientPrefixAdaptive,unaryAdaptiveActionSource_erase,coefficientPrefixFirstLeafSource_erase,coefficientPrefixSecondLeafSource_erase,CorrectionProgram.erase,
    correctionBlockErase,CorrectionFragment.erase,CorrectionProgram.erase_seq]
theorem coefficientPrefixSource_events (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hl : (coefficientPrefixTree registers k K).Layout registers.control (registers.path k K)) :
    (coefficientPrefixSource registers k K mode signUpdate target).events=
      2*((coefficientPrefixTree registers k K).leaves+(coefficientPrefixTree registers k K).internalNodes) := by
  simp only [coefficientPrefixSource,CorrectionProgram.events_seq,CorrectionProgram.events,
    correctionBlockEvents,CorrectionFragment.events,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Nat.zero_add,Nat.add_zero,unaryAdaptiveActionSource_events _ _ _ _ _ hl,
    coefficientPrefixFirstLeafSource_events,coefficientPrefixSecondLeafSource_events]
  have leafsum (tree : UnaryActionTree) (q : Wire) (path : List Wire) (h : tree.Layout q path) :
      tree.leafCostSum (fun _ _ => 1) q path=tree.leaves := by
    induction h with
    | leaf => rfl
    | node i q p zero one rest hlocal hzero hone ihZero ihOne =>
      simp [UnaryActionTree.leafCostSum,UnaryActionTree.leaves,ihZero,ihOne]
  have h := leafsum _ _ _ hl
  rw [h]
  omega
def coefficientPrefixInverseSource (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) : CorrectionProgram :=
  coefficientPrefixSource registers k K mode.inverse signUpdate target
theorem coefficientPrefixInverseSource_erase (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) :
    (coefficientPrefixInverseSource registers k K mode signUpdate target).erase=coefficientPrefixInverseAdaptive registers k K mode signUpdate target := by
  exact coefficientPrefixSource_erase registers k K mode.inverse signUpdate target
theorem coefficientPrefixInverseSource_events (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hl : (coefficientPrefixTree registers k K).Layout registers.control (registers.path k K)) :
    (coefficientPrefixInverseSource registers k K mode signUpdate target).events=
      2*((coefficientPrefixTree registers k K).leaves+(coefficientPrefixTree registers k K).internalNodes) := by
  exact coefficientPrefixSource_events registers k K mode.inverse signUpdate target hl
end ShorECDLP.Paper2607_13816
