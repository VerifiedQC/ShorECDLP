import ShorECDLP.Submission.«2607_13816».EEA.ControlPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.QuotientPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.IndexedStep
namespace ShorECDLP.Paper2607_13816
open Quantum

private theorem increment9_primitive (q : Wire) (r c : List Wire)
    (hr : r.length=9) (hc : c.length=8) :
    primitiveResources (.unitary (controlledIncrement q r c) .done)=
      (⟨0,0,11,16,0,0⟩ : PrimitiveResources) := by
  have he : r.length=c.length+1 := by omega
  have hcx : eeaCnotCount (controlledIncrement q r c)=11 := by
    cases r with
    | nil => simp at hr
    | cons a rs =>
      cases rs with
      | nil => simp at hr
      | cons b rs => simpa only [hr] using controlledIncrement_cnotCount q a b rs c he
  rw [primitiveResources_unitary_HPFree _ _ (controlledIncrement_HPFree _ _ _),
    controlledIncrement_xCount,hcx,controlledIncrement_toffoliCount _ _ _ he,hr]
  rfl
private theorem decrement9_primitive (q : Wire) (r c : List Wire)
    (hr : r.length=9) (hc : c.length=8) :
    primitiveResources (.unitary (controlledDecrement q r c) .done)=
      (⟨32,0,11,16,0,0⟩ : PrimitiveResources) := by
  have he : r.length=c.length+1 := by omega
  have hcx : eeaCnotCount (controlledDecrement q r c)=11 := by
    cases r with
    | nil => simp at hr
    | cons a rs =>
      cases rs with
      | nil => simp at hr
      | cons a rs => simpa only [hr] using controlledDecrement_cnotCount q _ _ rs c he
  rw [primitiveResources_unitary_HPFree _ _ (controlledDecrement_HPFree _ _ _),
    controlledDecrement_xCount _ _ _ he,hcx,controlledDecrement_toffoliCount _ _ _ he,hr]
  rfl

/-- Exact production quotient-length and sign-selection block, including explicit decrement masks. -/
theorem blockDForward9_primitive (r : IndexedStepRegisters) (w : ActiveWindow)
    (hl : QuotientSwapLayout (r.quotient w) w.start w.stop)
    (ht : r.lengthT.length=9) (hq : r.lengthQ.length=9) (hs : 8≤r.sourceScratch.length) :
    primitiveResources (.unitary (blockDForward r w) .done)=
      (⟨48+4*(quotientSwapTree (r.quotient w) w.start w.stop).internalNodes,0,
        170+2*(quotientSwapTree (r.quotient w) w.start w.stop).leaves+
          2*(quotientSwapTree (r.quotient w) w.start w.stop).internalNodes,
        108+(quotientSwapTree (r.quotient w) w.start w.stop).leaves+
          2*(quotientSwapTree (r.quotient w) w.start w.stop).internalNodes,0,0⟩ : PrimitiveResources) := by
  have hc : (r.sourceScratch.take (r.lengthQ.length-1)).length=8 := by
    simp only [List.length_take,hq]; omega
  change primitiveResources (.unitary ((((computeControl [r.phase1,r.phase2] 2 r.control r.sourceScratch ++
    controlledIncrement r.control r.lengthQ (r.sourceScratch.take (r.lengthQ.length-1))) ++
    computeControl [r.phase1,r.phase2] 2 r.control r.sourceScratch) ++
    (([.CX r.phase1 r.control,.CX r.phase2 r.control] ++ quotientSwapUnitary (r.quotient w) w.start w.stop) ++
      [.CX r.phase2 r.control,.CX r.phase1 r.control])) ++
    ((computeControl [r.phase1,r.phase2] 1 r.control r.sourceScratch ++
      controlledDecrement r.control r.lengthQ (r.sourceScratch.take (r.lengthQ.length-1))) ++
      computeControl [r.phase1,r.phase2] 1 r.control r.sourceScratch)) .done)=_
  simp only [primitiveResources_unitary_append]
  rw [computeControl_primitive _ _ _ _ (by simp),computeControl_primitive _ _ _ _ (by simp),
    increment9_primitive _ _ _ hq hc,decrement9_primitive _ _ _ hq hc,
    quotientSwapUnitary9_primitive _ hl ht]
  norm_num [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
    gidneyToffoliCount,AdaptiveCircuit.measurementCount,primitiveXCost,primitiveHCost,primitivePhaseCost,
    zeroBitCount,Nat.testBit,Nat.shiftRight_eq_div_pow,mcxVChainCnotCost,mcxVChainToffoliCost]
  omega
end ShorECDLP.Paper2607_13816
