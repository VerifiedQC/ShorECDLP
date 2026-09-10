import ShorECDLP.Submission.«2607_13816».EEA.AdaptiveSupport
import ShorECDLP.Submission.«2607_13816».EEA.CoefficientPrefixInverse
namespace ShorECDLP.Paper2607_13816
open Quantum
theorem coefficientPrefixFirstLeafAdaptive_wires_subset
    (r : CoefficientPrefixRegisters) (k K : Nat) (mode : RippleMode)
    (target : CoefficientTarget) (label : Nat) (control : Wire) :
    (coefficientPrefixFirstLeafAdaptive r k K mode target label control).wires ⊆
      circuitWires (coefficientPrefixFirstLeaf r k K mode target label control) := by
  have h := rippleFirstCellAdaptive_wires_subset mode (r.accumulator k K)
    (r.targetAt target k label) (r.addendAt target k label) (r.carry k K) (r.cellScratch k K)
  simp only [List.subset_def, circuitWires, List.mem_flatMap] at h
  intro w hw
  simp only [coefficientPrefixFirstLeafAdaptive, coefficientPrefixFirstLeaf,
    modularWires_seq, AdaptiveCircuit.wires, circuitWires, List.flatMap_append,
    List.mem_append, List.not_mem_nil, or_false] at hw ⊢
  aesop
theorem coefficientPrefixSecondLeafAdaptive_wires_subset
    (r : CoefficientPrefixRegisters) (k K : Nat) (mode : RippleMode)
    (target : CoefficientTarget) (label : Nat) (control : Wire) :
    (coefficientPrefixSecondLeafAdaptive r k K mode target label control).wires ⊆
      circuitWires (coefficientPrefixSecondLeaf r k K mode target label control) := by
  have h := rippleSecondCellAdaptive_wires_subset mode (r.accumulator k K)
    (r.targetAt target k label) (r.addendAt target k label) (r.carry k K) (r.cellScratch k K)
  simp only [List.subset_def, circuitWires, List.mem_flatMap] at h
  intro w hw
  simp only [coefficientPrefixSecondLeafAdaptive, coefficientPrefixSecondLeaf,
    AdaptiveCircuit.wires, circuitWires, List.flatMap_append, List.mem_append] at hw ⊢
  aesop
theorem coefficientPrefixAdaptive_wires_subset
    (r : CoefficientPrefixRegisters) (k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : CoefficientTarget) :
    (coefficientPrefixAdaptive r k K mode signUpdate target).wires ⊆
      circuitWires (coefficientPrefixUnitary r k K mode signUpdate target) := by
  have hfirst := unaryAdaptiveAction_wires_subset .inc
    (coefficientPrefixFirstLeafAdaptive r k K mode target)
    (coefficientPrefixFirstLeaf r k K mode target)
    (coefficientPrefixFirstLeafAdaptive_wires_subset r k K mode target)
    (coefficientPrefixTree r k K) r.control (r.path k K)
  have hsecond := unaryAdaptiveAction_wires_subset .dec
    (coefficientPrefixSecondLeafAdaptive r k K mode target)
    (coefficientPrefixSecondLeaf r k K mode target)
    (coefficientPrefixSecondLeafAdaptive_wires_subset r k K mode target)
    (coefficientPrefixTree r k K) r.control (r.path k K)
  simp only [List.subset_def,circuitWires,List.mem_flatMap] at hfirst hsecond
  intro w hw
  simp only [coefficientPrefixAdaptive,coefficientPrefixUnitary,modularWires_seq,
    AdaptiveCircuit.wires,circuitWires,List.flatMap_append,List.mem_append,
    List.not_mem_nil,or_false] at hw ⊢
  aesop
theorem coefficientPrefixInverseAdaptive_wires_subset
    (r : CoefficientPrefixRegisters) (k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : CoefficientTarget) :
    (coefficientPrefixInverseAdaptive r k K mode signUpdate target).wires ⊆
      circuitWires (coefficientPrefixInverseUnitary r k K mode signUpdate target) :=
  coefficientPrefixAdaptive_wires_subset r k K mode.inverse signUpdate target
end ShorECDLP.Paper2607_13816
