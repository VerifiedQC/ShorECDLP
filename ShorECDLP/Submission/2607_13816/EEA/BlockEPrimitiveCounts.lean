import ShorECDLP.Submission.«2607_13816».EEA.ControlPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.CoefficientPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.IndexedStep
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Actual production coefficient-boundary preparation at n=256 and width=9. -/
theorem prepareLatestPaperTBoundary256_primitive (r : TBoundaryRegisters)
    (hl : TBoundaryLayout r) (hw : r.width=9) :
    primitiveResources (.unitary (prepareLatestPaperTBoundary r 256) .done)=
      (⟨16,0,136,77,0,0⟩ : PrimitiveResources) := by
  rw [primitiveResources_unitary_HPFree _ _ (prepareLatestPaperTBoundary_HPFree _ _),
    prepareLatestPaperTBoundary_xCount _ _ hl,prepareLatestPaperTBoundary_cnotCount _ _ hl (by omega),
    prepareLatestPaperTBoundary_toffoliCount _ _ hl (by omega),hw]
  rfl
/-- Actual restoration has its own emitted stream but the same primitive vector. -/
theorem restoreLatestPaperTBoundary256_primitive (r : TBoundaryRegisters)
    (hl : TBoundaryLayout r) (hw : r.width=9) :
    primitiveResources (.unitary (restoreLatestPaperTBoundary r 256) .done)=
      (⟨16,0,136,77,0,0⟩ : PrimitiveResources) := by
  rw [primitiveResources_unitary_HPFree _ _ (restoreLatestPaperTBoundary_HPFree _ _),
    restoreLatestPaperTBoundary_xCount _ _ hl,restoreLatestPaperTBoundary_cnotCount _ _ hl (by omega),
    restoreLatestPaperTBoundary_toffoliCount _ _ hl (by omega),hw]
  rfl
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum

/-- Complete production coefficient block, including its controls and both boundary transforms. -/
theorem blockEAdaptive256_primitive (r : IndexedStepRegisters) (w : ActiveWindow)
    (hb : TBoundaryLayout r.tBoundary) (ht : r.lengthT.length=9)
    (hc : CoefficientPrefixLayout (r.coefficient w) w.start w.stop) :
    primitiveResources (blockEAdaptive r 256 w)=
      (⟨44+16*(coefficientPrefixTree (r.coefficient w) w.start w.stop).internalNodes,
        8*((coefficientPrefixTree (r.coefficient w) w.start w.stop).leaves+
          (coefficientPrefixTree (r.coefficient w) w.start w.stop).internalNodes),
        280+16*(coefficientPrefixTree (r.coefficient w) w.start w.stop).leaves+
          12*(coefficientPrefixTree (r.coefficient w) w.start w.stop).internalNodes,
        160+10*(coefficientPrefixTree (r.coefficient w) w.start w.stop).leaves+
          4*(coefficientPrefixTree (r.coefficient w) w.start w.stop).internalNodes,
        0,4*((coefficientPrefixTree (r.coefficient w) w.start w.stop).leaves+
          (coefficientPrefixTree (r.coefficient w) w.start w.stop).internalNodes)⟩ : PrimitiveResources) := by
  let temp := computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch
  let sub := computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch
  let add := computeControl [r.phase1] 1 r.control r.blockScratch
  have htemp : primitiveResources (.unitary temp .done)=(⟨2,0,0,1,0,0⟩ : PrimitiveResources) := by
    dsimp only [temp]
    rw [computeControl_primitive _ _ _ _ (by simp)]
    rfl
  have hsub : primitiveResources (.unitary sub .done)=(⟨2,0,0,1,0,0⟩ : PrimitiveResources) := by
    dsimp only [sub]
    rw [computeControl_primitive _ _ _ _ (by simp)]
    rfl
  have hadd : primitiveResources (.unitary add .done)=(⟨0,0,1,0,0,0⟩ : PrimitiveResources) := by
    dsimp only [add]
    rw [computeControl_primitive _ _ _ _ (by simp)]
    rfl
  simp only [blockEAdaptive_eq_parts,primitiveResources_seq]
  dsimp only [temp,sub,add] at htemp hsub hadd
  simp only [primitiveResources_unitary_append,htemp,hsub,hadd]
  rw [prepareLatestPaperTBoundary256_primitive _ hb ht,restoreLatestPaperTBoundary256_primitive _ hb ht,
    coefficientPrefixAdaptive_primitive _ _ _ _ _ _ hc,
    coefficientPrefixAdaptive_primitive _ _ _ _ _ _ hc]
  simp only [PrimitiveResources.add,primitiveResources,gidneyGateCount,gidneyCnotCount,
    gidneyToffoliCount,AdaptiveCircuit.measurementCount,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,primitiveXCost,primitiveHCost,primitivePhaseCost,Bool.false_eq_true,if_false,if_true]
  congr 1 <;> omega
end ShorECDLP.Paper2607_13816
