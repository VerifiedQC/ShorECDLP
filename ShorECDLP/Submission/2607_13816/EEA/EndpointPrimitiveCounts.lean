import ShorECDLP.Submission.«2607_13816».Arithmetic.UnitaryPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.EndIteration
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Actual 9-bit endpoint preparation, with X masks counted from constants. -/
theorem prepareIntervalEndpoints9_primitive (t q s scratch : List Wire) (carry : Wire)
    (n k : Nat) (ht : t.length=9) (hq : q.length=9) (hs : s.length=9)
    (hw : 9≤scratch.length) :
    primitiveResources (.unitary (prepareIntervalEndpoints t q s scratch carry n k) .done)=
      (⟨10+2*(constantBits 9 4).count true+2*(constantBits 9 (n+2)).count true+
        4*(constantBits 9 k).count true,0,190,104,0,0⟩ : PrimitiveResources) := by
  have hqsc : (endpointScratch q scratch).length=q.length := by simp [endpointScratch,List.length_take,hq,Nat.min_eq_left hw]
  have hssc : (endpointScratch s scratch).length=s.length := by simp [endpointScratch,List.length_take,hs,Nat.min_eq_left hw]
  have hx : eeaXCount (prepareIntervalEndpoints t q s scratch carry n k)=
      10+2*(constantBits 9 4).count true+2*(constantBits 9 (n+2)).count true+
        4*(constantBits 9 k).count true := by
    simp only [prepareIntervalEndpoints,eeaXCount_append,endIteration_cuccaroAdd_xCount,
      endIteration_addConstant_xCount,endIteration_subConstant_xCount,
      endIteration_constMinus_xCount s _ carry (n+2) (by omega) hssc,hqsc,hssc,hq,hs]
    omega
  rw [primitiveResources_unitary_HPFree _ _ (prepareIntervalEndpoints_HPFree t q s scratch carry n k),hx,
    prepareIntervalEndpoints_toffoliCount t q s scratch carry n k (ht.trans hq.symm)
      (hq ▸ hw) (hs ▸ hw) (by omega)]
  have hc : eeaCnotCount (prepareIntervalEndpoints t q s scratch carry n k)=190 := by
    cases s with
    | nil => simp at hs
    | cons a rest =>
      cases rest with
      | nil => simp at hs
      | cons b rest =>
        rw [prepareIntervalEndpoints_cnotCount t q scratch rest a b carry n k
          (ht.trans hq.symm) (hq ▸ hw) (hs ▸ hw)]
        simp [intervalEndpointCnotFormula,ht,hq,hs]
  rw [hc]
  norm_num [intervalEndpointToffoliFormula,ht,hq,hs,PrimitiveResources.add,primitiveResources,
    gidneyGateCount,gidneyCnotCount,gidneyToffoliCount,AdaptiveCircuit.measurementCount]
/-- Actual 9-bit endpoint restoration, with X masks counted from constants. -/
theorem restoreIntervalEndpoints9_primitive (t q s scratch : List Wire) (carry : Wire)
    (n k : Nat) (ht : t.length=9) (hq : q.length=9) (hs : s.length=9)
    (hw : 9≤scratch.length) :
    primitiveResources (.unitary (restoreIntervalEndpoints t q s scratch carry n k) .done)=
      (⟨10+2*(constantBits 9 4).count true+2*(constantBits 9 (n+2)).count true+
        4*(constantBits 9 k).count true,0,190,104,0,0⟩ : PrimitiveResources) := by
  have hqsc : (endpointScratch q scratch).length=q.length := by simp [endpointScratch,List.length_take,hq,Nat.min_eq_left hw]
  have hssc : (endpointScratch s scratch).length=s.length := by simp [endpointScratch,List.length_take,hs,Nat.min_eq_left hw]
  have hx : eeaXCount (restoreIntervalEndpoints t q s scratch carry n k)=
      10+2*(constantBits 9 4).count true+2*(constantBits 9 (n+2)).count true+
        4*(constantBits 9 k).count true := by
    simp only [restoreIntervalEndpoints,eeaXCount_append,endIteration_cuccaroSub_xCount,
      endIteration_addConstant_xCount,endIteration_subConstant_xCount,
      endIteration_constMinus_xCount s _ carry (n+2) (by omega) hssc,hqsc,hssc,hq,hs]
    omega
  rw [primitiveResources_unitary_HPFree _ _ (restoreIntervalEndpoints_HPFree t q s scratch carry n k),hx,
    restoreIntervalEndpoints_toffoliCount t q s scratch carry n k (ht.trans hq.symm)
      (hq ▸ hw) (hs ▸ hw) (by omega)]
  have hc : eeaCnotCount (restoreIntervalEndpoints t q s scratch carry n k)=190 := by
    cases s with
    | nil => simp at hs
    | cons a rest =>
      cases rest with
      | nil => simp at hs
      | cons b rest =>
        rw [restoreIntervalEndpoints_cnotCount t q scratch rest a b carry n k
          (ht.trans hq.symm) (hq ▸ hw) (hs ▸ hw)]
        simp [intervalEndpointCnotFormula,ht,hq,hs]
  rw [hc]
  norm_num [intervalEndpointToffoliFormula,ht,hq,hs,PrimitiveResources.add,primitiveResources,
    gidneyGateCount,gidneyCnotCount,gidneyToffoliCount,AdaptiveCircuit.measurementCount]
end ShorECDLP.Paper2607_13816
