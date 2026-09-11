import ShorECDLP.Submission.«2607_13816».EEA.ControlPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.IntervalPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.IndexedStep
namespace ShorECDLP.Paper2607_13816
open Quantum

/-- Complete measured remainder block, with every surrounding coherent control counted. -/
theorem blockBAdaptive9_primitive (r : IndexedStepRegisters) (n : Nat) (w : ActiveWindow)
    (hl : IntervalLayout (r.remainder w) w.start w.stop .work1)
    (ht : r.lengthT.length=9) (hq : r.lengthQ.length=9) (hs : r.lengthS.length=9)
    (hr : r.lengthRPrime.length=9) (hsc : 8≤r.blockScratch.length)
    (he : 9≤(r.remainder w).endpointScratch.length)
    (heq : 7≤((r.remainder w).equalityScratch w.start w.stop).length) :
    primitiveResources (blockBAdaptive r n w)=
      (⟨28,0,1,198,0,0⟩ : PrimitiveResources).add
        ((intervalPrimitiveFormula9 (r.remainder w) n w.start w.stop .sub true).add
          (intervalPrimitiveFormula9 (r.remainder w) n w.start w.stop .add false)) := by
  let subControl := rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch
  let phaseControl := rControlNonterminal [r.phase1,r.phase2] 2 r.control r.lengthRPrime r.terminal r.blockScratch
  let restoreControl := ([.CCX r.phase2 r.sign r.terminal] ++
    rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime
      (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal]
  have hsub : primitiveResources (AdaptiveCircuit.unitary subControl .done)=(⟨4,0,0,31,0,0⟩ : PrimitiveResources) := by
    dsimp only [subControl]
    rw [rControlNonterminal_primitive _ _ _ _ _ _ (by omega) (by simp)]
    rw [hr]
    norm_num [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
      gidneyToffoliCount,AdaptiveCircuit.measurementCount,primitiveXCost,primitiveHCost,primitivePhaseCost,
      zeroBitCount,Nat.testBit,Nat.shiftRight_eq_div_pow,mcxVChainCnotCost,mcxVChainToffoliCost]
  have hphase : primitiveResources (AdaptiveCircuit.unitary phaseControl .done)=(⟨4,0,0,33,0,0⟩ : PrimitiveResources) := by
    dsimp only [phaseControl]
    rw [rControlNonterminal_primitive _ _ _ _ _ _ (by omega) (by simp; omega)]
    rw [hr]
    norm_num [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
      gidneyToffoliCount,AdaptiveCircuit.measurementCount,primitiveXCost,primitiveHCost,primitivePhaseCost,
      zeroBitCount,Nat.testBit,Nat.shiftRight_eq_div_pow,mcxVChainCnotCost,mcxVChainToffoliCost]
  have hrestore : primitiveResources (AdaptiveCircuit.unitary restoreControl .done)=(⟨6,0,0,35,0,0⟩ : PrimitiveResources) := by
    simp only [restoreControl,primitiveResources_unitary_append]
    rw [rControlNonterminal_primitive _ _ _ _ _ _ (by simp only [List.length_drop]; omega)
      (by simp only [List.length_cons,List.length_nil,List.length_drop]; omega),hr]
    norm_num [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
      gidneyToffoliCount,AdaptiveCircuit.measurementCount,primitiveXCost,primitiveHCost,primitivePhaseCost,
      zeroBitCount,Nat.testBit,Nat.shiftRight_eq_div_pow,mcxVChainCnotCost,mcxVChainToffoliCost]
  change primitiveResources (((AdaptiveCircuit.unitary subControl .done).seq
    ((intervalAddSub (r.remainder w) n w.start w.stop .sub true .work1).seq (AdaptiveCircuit.unitary subControl .done))).seq
    ((AdaptiveCircuit.unitary ((phaseControl ++ [.CX r.control r.sign]) ++ phaseControl) .done).seq
      ((AdaptiveCircuit.unitary restoreControl .done).seq
        ((intervalAddSub (r.remainder w) n w.start w.stop .add false .work1).seq
          (AdaptiveCircuit.unitary restoreControl .done)))))=_
  simp only [primitiveResources_seq,primitiveResources_unitary_append,hsub,hphase,hrestore]
  rw [intervalAddSub9_primitive _ _ _ _ _ _ _ hl ht hq hs he heq,
    intervalAddSub9_primitive _ _ _ _ _ _ _ hl ht hq hs he heq]
  simp only [PrimitiveResources.add,primitiveResources,gidneyGateCount,gidneyCnotCount,
    gidneyToffoliCount,AdaptiveCircuit.measurementCount,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,primitiveXCost,primitiveHCost,primitivePhaseCost]
  congr 1 <;> omega
end ShorECDLP.Paper2607_13816
