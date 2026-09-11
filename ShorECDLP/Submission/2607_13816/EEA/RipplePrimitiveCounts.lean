import ShorECDLP.Submission.«2607_13816».EEA.SelectorPrimitiveCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Exact primitive vector of the adaptive first ripple cell. -/
theorem rippleFirstCellAdaptive_primitive (mode : RippleMode) (q a b c d : Wire) :
    primitiveResources (rippleFirstCellAdaptive mode q a b c d)=
      (⟨0,2,3,rippleFirstCellToffoliCost mode-1,0,1⟩ : PrimitiveResources) := by
  cases mode <;> rfl
/-- Exact primitive vector of the adaptive second ripple cell. -/
theorem rippleSecondCellAdaptive_primitive (mode : RippleMode) (q a b c d : Wire) :
    primitiveResources (rippleSecondCellAdaptive mode q a b c d)=
      (⟨0,2,3,rippleSecondCellToffoliCost mode-1,0,1⟩ : PrimitiveResources) := by
  cases mode <;> rfl
private theorem endpoint_primitive (special : Bool) (label : Nat) (top q acc : Wire)
    (next : AdaptiveCircuit) :
    primitiveResources (.unitary (endpointLeafToggle special label top q acc) next)=
      (⟨if maskedZeroLeaf special label then 2 else 0,0,
        if maskedZeroLeaf special label then 0 else 1,
        if maskedZeroLeaf special label then 1 else 0,0,0⟩ : PrimitiveResources).add
        (primitiveResources next) := by
  unfold endpointLeafToggle
  split <;> simp_all [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
    gidneyToffoliCount,primitiveXCost,primitiveHCost,primitivePhaseCost,AdaptiveCircuit.measurementCount]
/-- Main-tree leaf counts include both endpoint toggles, including the masked zero label. -/
theorem intervalFirstLeafAdaptive_primitive (mode : RippleMode) (special : Bool)
    (rt lt acc target addend carry scratch : Wire) (label : Nat) (rq lq : Wire) :
    primitiveResources (intervalFirstLeafAdaptive mode special rt lt acc target addend carry scratch label rq lq)=
      (⟨if maskedZeroLeaf special label then 4 else 0,2,
        if maskedZeroLeaf special label then 3 else 5,
        rippleFirstCellToffoliCost mode-1+(if maskedZeroLeaf special label then 2 else 0),0,1⟩ : PrimitiveResources) := by
  have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
  rw [intervalFirstLeafAdaptive,endpoint_primitive,primitiveResources_seq,
    rippleFirstCellAdaptive_primitive,endpoint_primitive,hdone]
  cases maskedZeroLeaf special label <;> simp [PrimitiveResources.add]
  omega
/-- Main-tree leaf counts include both endpoint toggles, including the masked zero label. -/
theorem intervalSecondLeafAdaptive_primitive (mode : RippleMode) (special : Bool)
    (rt lt acc target addend carry scratch : Wire) (label : Nat) (rq lq : Wire) :
    primitiveResources (intervalSecondLeafAdaptive mode special rt lt acc target addend carry scratch label rq lq)=
      (⟨if maskedZeroLeaf special label then 4 else 0,2,
        if maskedZeroLeaf special label then 3 else 5,
        rippleSecondCellToffoliCost mode-1+(if maskedZeroLeaf special label then 2 else 0),0,1⟩ : PrimitiveResources) := by
  have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
  rw [intervalSecondLeafAdaptive,endpoint_primitive,primitiveResources_seq,
    rippleSecondCellAdaptive_primitive,endpoint_primitive,hdone]
  cases maskedZeroLeaf special label <;> simp [PrimitiveResources.add]
  omega
/-- The separately emitted top leaf includes both 9-bit equality selectors. -/
theorem topSpecialFirstLeafAdaptive9_primitive (mode : RippleMode) (value : Nat)
    (right left : List Wire) (acc target addend carry scratch flag : Wire)
    (eqScratch : List Wire) (rq lq : Wire) (hr : right.length=9) (hl : left.length=9)
    (hs : 7≤eqScratch.length) :
    primitiveResources (topSpecialFirstLeafAdaptive mode value right left acc target addend carry scratch flag eqScratch rq lq)=
      (⟨8*zeroBitCount value 0 9,58,31,34+(rippleFirstCellToffoliCost mode-1),0,29⟩ : PrimitiveResources) := by
  rw [topSpecialFirstLeafAdaptive,primitiveResources_seq,primitiveResources_seq,
    rippleFirstCellAdaptive_primitive]
  simp only [toggleEqConstUnderControlAdaptive_primitive _ right _ _ _ _ (by simpa only [hr] using hs),
    toggleEqConstUnderControlAdaptive_primitive _ left _ _ _ _ (by simpa only [hl] using hs),
    hr,hl]
  norm_num [PrimitiveResources.add]
  omega
/-- The separately emitted top leaf includes both 9-bit equality selectors. -/
theorem topSpecialSecondLeafAdaptive9_primitive (mode : RippleMode) (value : Nat)
    (right left : List Wire) (acc target addend carry scratch flag : Wire)
    (eqScratch : List Wire) (rq lq : Wire) (hr : right.length=9) (hl : left.length=9)
    (hs : 7≤eqScratch.length) :
    primitiveResources (topSpecialSecondLeafAdaptive mode value right left acc target addend carry scratch flag eqScratch rq lq)=
      (⟨8*zeroBitCount value 0 9,58,31,34+(rippleSecondCellToffoliCost mode-1),0,29⟩ : PrimitiveResources) := by
  rw [topSpecialSecondLeafAdaptive,primitiveResources_seq,primitiveResources_seq,
    rippleSecondCellAdaptive_primitive]
  simp only [toggleEqConstUnderControlAdaptive_primitive _ right _ _ _ _ (by simpa only [hr] using hs),
    toggleEqConstUnderControlAdaptive_primitive _ left _ _ _ _ (by simpa only [hl] using hs),
    hr,hl]
  norm_num [PrimitiveResources.add]
  omega
end ShorECDLP.Paper2607_13816
