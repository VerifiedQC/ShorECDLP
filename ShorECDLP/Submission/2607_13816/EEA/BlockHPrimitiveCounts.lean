import ShorECDLP.Submission.«2607_13816».EEA.ControlPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.EndIteration
import ShorECDLP.Submission.«2607_13816».EEA.IndexedStep
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Exact primitive vector of the literal end-of-iteration aggregate. -/
theorem swapWorkAndLengthUnaryShared_primitive (r : EndIterationRegisters) (n : Nat)
    (w : EndIterationWindows) (hw : 2≤r.width) (hl : EndIterationLayout r n w) :
    primitiveResources (.unitary (swapWorkAndLengthUnaryShared r n w) .done)=
      (⟨endIterationXFormula r.width n w,0,endIterationCnotFormula r.work1.length r.width n w,
        endIterationToffoliFormula r.work1.length r.width n w,0,0⟩ : PrimitiveResources) := by
  have h := swapWorkAndLengthUnaryShared_resourceCounts r n w hw hl
  rw [primitiveResources_unitary_HPFree _ _ (swapWorkAndLengthUnaryShared_HPFree _ _ _),h.1,h.2.1,h.2.2.1]
  rfl
private theorem h_mcx_primitive (r : List Wire) (q : Wire) (s : List Wire)
    (hs : r.length-2≤s.length) :
    primitiveResources (.unitary (mcxVChain r q s) .done)=
      (⟨if r.length=0 then 1 else 0,0,mcxVChainCnotCost r.length,
        mcxVChainToffoliCost r.length,0,0⟩ : PrimitiveResources) := by
  rw [primitiveResources_unitary_HPFree _ _ (mcxVChain_HPFree _ _ _),
    mcxVChain_control_xCount,mcxVChain_cnotCount,mcxVChain_toffoliCount _ _ _ hs]
  rfl
/-- Every fourth production step includes the full boundary refresh and its two zero tests. -/
theorem blockHForward256_primitive (r : IndexedStepRegisters) (T : Nat)
    (hw : r.work1.length=259) (ht : r.lengthT.length=9) (hq : r.lengthQ.length=9)
    (hs : r.lengthS.length=9) (hsc : 10≤r.sourceScratch.length)
    (hl : T%4=0 → EndIterationLayout (r.endIteration 256 T) 256 (endIterationWindowsAt 256 T)) :
    primitiveResources (.unitary (blockHForward r 256 T) .done)=
      if T%4=0 then
        (⟨4+endIterationXFormula 9 256 (endIterationWindowsAt 256 T),0,
          1+endIterationCnotFormula 259 9 256 (endIterationWindowsAt 256 T),
          66+endIterationToffoliFormula 259 9 256 (endIterationWindowsAt 256 T),0,0⟩ : PrimitiveResources)
      else ⟨0,0,0,0,0,0⟩ := by
  by_cases hT : T%4=0
  · simp only [blockHForward,if_pos hT,primitiveResources_unitary_append]
    rw [h_mcx_primitive _ _ _ (by simp only [List.length_drop,hq]; omega),
      h_mcx_primitive _ _ _ (by simp only [List.length_append,List.length_singleton,List.length_drop,hs]; omega),
      swapWorkAndLengthUnaryShared_primitive _ _ _ (by change 2≤r.lengthT.length; omega) (hl hT)]
    simp only [IndexedStepRegisters.endIteration,EndIterationRegisters.width,hw,ht,hq,hs,
      List.length_append,List.length_singleton]
    norm_num [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
      gidneyToffoliCount,AdaptiveCircuit.measurementCount,primitiveXCost,primitiveHCost,primitivePhaseCost,
      mcxVChainCnotCost,mcxVChainToffoliCost]
    omega
  · simp only [blockHForward,if_neg hT]
    rfl
/-- Explicit inverse endpoint refresh preserves the forward vector; this is proved from
its emitted gates rather than inferred from semantic cancellation. -/
theorem swapWorkAndLengthUnarySharedInverse_primitive (r : EndIterationRegisters) (n : Nat)
    (w : EndIterationWindows) (hl : EndIterationLayout r n w) :
    primitiveResources (.unitary (swapWorkAndLengthUnarySharedInverse r n w) .done)=
      primitiveResources (.unitary (swapWorkAndLengthUnaryShared r n w) .done) := by
  rw [primitiveResources_unitary_HPFree _ _ (swapWorkAndLengthUnarySharedInverse_HPFree _ _ _),
    primitiveResources_unitary_HPFree _ _ (swapWorkAndLengthUnaryShared_HPFree _ _ _),
    swapWorkAndLengthUnarySharedInverse_xCount,
    swapWorkAndLengthUnarySharedInverse_cnotCount _ _ _ (hl.work1_length.trans hl.work2_length.symm),
    swapWorkAndLengthUnarySharedInverse_toffoliCount _ _ _ (hl.work1_length.trans hl.work2_length.symm)]

private theorem inverse_unitary_cons (g h : Gate) (gs : Circuit) :
    primitiveResources (.unitary (g::h::gs) .done)=
      (primitiveResources (.unitary [g] .done)).add (primitiveResources (.unitary (h::gs) .done)) := by
  simp [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
    gidneyToffoliCount,AdaptiveCircuit.measurementCount]

/-- The explicit inverse H refresh has the same vector as its forward block. -/
theorem blockHInverse_primitive (r : IndexedStepRegisters) (n T : Nat)
    (hl : T%4=0 → EndIterationLayout (r.endIteration n T) n (endIterationWindowsAt n T)) :
    primitiveResources (.unitary (blockHInverse r n T) .done)=
      primitiveResources (.unitary (blockHForward r n T) .done) := by
  by_cases hT : T%4=0
  · simp only [blockHInverse,blockHForward,if_pos hT,primitiveResources_unitary_append]
    rw [swapWorkAndLengthUnarySharedInverse_primitive _ _ _ (hl hT)]
    simp only [inverse_unitary_cons,PrimitiveResources.add]
    congr 1; omega
  · simp only [blockHInverse,blockHForward,if_neg hT]


end ShorECDLP.Paper2607_13816
