import ShorECDLP.Submission.«2607_13816».EEA.RipplePrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.CoefficientPrefixInverse
namespace ShorECDLP.Paper2607_13816
open Quantum
private theorem prefix_nil_primitive (next : AdaptiveCircuit) :
    primitiveResources (.unitary [] next)=primitiveResources next := by
  simp [primitiveResources,gidneyGateCount,gidneyCnotCount,gidneyToffoliCount,
    AdaptiveCircuit.measurementCount]
private theorem prefix_cx_primitive (a b : Wire) (next : AdaptiveCircuit) :
    primitiveResources (.unitary [.CX a b] next)=
      (⟨0,0,1,0,0,0⟩ : PrimitiveResources).add (primitiveResources next) := by
  simp [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
    gidneyToffoliCount,primitiveXCost,primitiveHCost,primitivePhaseCost,AdaptiveCircuit.measurementCount]
theorem coefficientPrefixFirstLeafAdaptive_primitive (r : CoefficientPrefixRegisters)
    (k K : Nat) (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (q : Wire) :
    primitiveResources (coefficientPrefixFirstLeafAdaptive r k K mode target label q)=
      (⟨0,2,4,rippleFirstCellToffoliCost mode-1,0,1⟩ : PrimitiveResources) := by
  rw [coefficientPrefixFirstLeafAdaptive,primitiveResources_seq,rippleFirstCellAdaptive_primitive]
  cases mode <;> rfl
theorem coefficientPrefixSecondLeafAdaptive_primitive (r : CoefficientPrefixRegisters)
    (k K : Nat) (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (q : Wire) :
    primitiveResources (coefficientPrefixSecondLeafAdaptive r k K mode target label q)=
      (⟨0,2,4,rippleSecondCellToffoliCost mode-1,0,1⟩ : PrimitiveResources) := by
  rw [coefficientPrefixSecondLeafAdaptive,prefix_cx_primitive,rippleSecondCellAdaptive_primitive]
  cases mode <;> rfl

/-- Exact primitive count for the actual prepared-boundary coefficient prefix. -/
theorem coefficientPrefixAdaptive_primitive (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hl : CoefficientPrefixLayout r k K) :
    primitiveResources (coefficientPrefixAdaptive r k K mode signUpdate target)=
      (⟨8*(coefficientPrefixTree r k K).internalNodes,
        4*(coefficientPrefixTree r k K).leaves+4*(coefficientPrefixTree r k K).internalNodes,
        2+8*(coefficientPrefixTree r k K).leaves+6*(coefficientPrefixTree r k K).internalNodes+
          (if signUpdate then 1 else 0),
        5*(coefficientPrefixTree r k K).leaves+2*(coefficientPrefixTree r k K).internalNodes,
        0,2*(coefficientPrefixTree r k K).leaves+2*(coefficientPrefixTree r k K).internalNodes⟩ : PrimitiveResources) := by
  rw [coefficientPrefixAdaptive,prefix_cx_primitive,primitiveResources_seq,
    unaryAdaptiveAction_primitive _ _ _ _ _ hl.tree]
  cases signUpdate <;>
    simp only [coefficientPrefixSignCircuit,Bool.false_eq_true,if_false,if_true,
      prefix_nil_primitive,prefix_cx_primitive,primitiveResources_seq,
      unaryAdaptiveAction_primitive _ _ _ _ _ hl.tree,
      coefficientPrefixFirstLeafAdaptive_primitive,coefficientPrefixSecondLeafAdaptive_primitive,
      coefficientPrefix_leafCostSum_const _ _ _ _ hl.tree]
  all_goals
    generalize (coefficientPrefixTree r k K).leaves = leaves
    generalize (coefficientPrefixTree r k K).internalNodes = nodes
    cases mode <;>
      simp [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
        gidneyToffoliCount,AdaptiveCircuit.measurementCount,rippleFirstCellToffoliCost,rippleSecondCellToffoliCost]
    all_goals omega

theorem coefficientPrefixInverseAdaptive_primitive (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hl : CoefficientPrefixLayout r k K) :
    primitiveResources (coefficientPrefixInverseAdaptive r k K mode signUpdate target)=
      primitiveResources (coefficientPrefixAdaptive r k K mode signUpdate target) := by
  rw [coefficientPrefixInverseAdaptive,coefficientPrefixAdaptive_primitive _ _ _ _ _ _ hl,
    coefficientPrefixAdaptive_primitive _ _ _ _ _ _ hl]
end ShorECDLP.Paper2607_13816
