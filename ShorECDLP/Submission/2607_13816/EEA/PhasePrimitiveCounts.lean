import ShorECDLP.Submission.«2607_13816».EEA.SelectorPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.PhaseUpdate
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Exact production-width phase/sign update, including all three tests and epoch conjugations. -/
theorem phaseUpdateEpochAdaptive9_primitive (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (hq : registers.lengthQ.length=9) (hr : registers.lengthRPrime.length=9)
    (hs : registers.lengthS.length=9) (hw : 8≤registers.equalityScratch.length) :
    primitiveResources (phaseUpdateEpochAdaptive registers shiftEpoch) =
      (⟨8,88,50,54,0,44⟩ : PrimitiveResources) := by
  change primitiveResources ((((((((mcxVChainAdaptive (registers.withShiftEpoch shiftEpoch).lengthQ (registers.withShiftEpoch shiftEpoch).zeroQ (registers.withShiftEpoch shiftEpoch).equalityScratch).seq
    (mcxVChainAdaptive (registers.withShiftEpoch shiftEpoch).lengthRPrime (registers.withShiftEpoch shiftEpoch).zeroRPrime
      (registers.withShiftEpoch shiftEpoch).equalityScratch)).seq
    (.unitary [.X shiftEpoch] .done)).seq
    (mcxVChainAdaptive (registers.withShiftEpoch shiftEpoch).lengthS (registers.withShiftEpoch shiftEpoch).zeroS (registers.withShiftEpoch shiftEpoch).equalityScratch)).seq
    (.unitary [.X shiftEpoch] .done))).seq (.unitary ([.X (registers.withShiftEpoch shiftEpoch).zeroRPrime,
    .CCX (registers.withShiftEpoch shiftEpoch).zeroQ (registers.withShiftEpoch shiftEpoch).zeroRPrime (registers.withShiftEpoch shiftEpoch).condition,
    .X (registers.withShiftEpoch shiftEpoch).zeroRPrime,
    .CX (registers.withShiftEpoch shiftEpoch).sign (registers.withShiftEpoch shiftEpoch).temporary,
    .CX (registers.withShiftEpoch shiftEpoch).phase1 (registers.withShiftEpoch shiftEpoch).temporary,
    .CCX (registers.withShiftEpoch shiftEpoch).condition (registers.withShiftEpoch shiftEpoch).temporary (registers.withShiftEpoch shiftEpoch).phase2,
    .CX (registers.withShiftEpoch shiftEpoch).phase1 (registers.withShiftEpoch shiftEpoch).temporary,
    .CX (registers.withShiftEpoch shiftEpoch).sign (registers.withShiftEpoch shiftEpoch).temporary,
    .CCX (registers.withShiftEpoch shiftEpoch).condition (registers.withShiftEpoch shiftEpoch).phase2 (registers.withShiftEpoch shiftEpoch).sign,
    .X (registers.withShiftEpoch shiftEpoch).zeroRPrime,
    .CCX (registers.withShiftEpoch shiftEpoch).zeroQ (registers.withShiftEpoch shiftEpoch).zeroRPrime (registers.withShiftEpoch shiftEpoch).condition,
    .X (registers.withShiftEpoch shiftEpoch).zeroRPrime,
    .CX (registers.withShiftEpoch shiftEpoch).zeroS (registers.withShiftEpoch shiftEpoch).phase1,
    .CX (registers.withShiftEpoch shiftEpoch).zeroS (registers.withShiftEpoch shiftEpoch).phase2]) .done)).seq ((((((Quantum.AdaptiveCircuit.unitary [.X shiftEpoch] .done).seq
    (mcxVChainAdaptive (registers.withShiftEpoch shiftEpoch).lengthS (registers.withShiftEpoch shiftEpoch).zeroS (registers.withShiftEpoch shiftEpoch).equalityScratch)).seq
    (.unitary [.X shiftEpoch] .done)).seq
    (mcxVChainAdaptive (registers.withShiftEpoch shiftEpoch).lengthRPrime (registers.withShiftEpoch shiftEpoch).zeroRPrime
      (registers.withShiftEpoch shiftEpoch).equalityScratch)).seq
    (mcxVChainAdaptive (registers.withShiftEpoch shiftEpoch).lengthQ (registers.withShiftEpoch shiftEpoch).zeroQ (registers.withShiftEpoch shiftEpoch).equalityScratch)))) = _
  simp only [primitiveResources_seq,PhaseUpdateRegisters.withShiftEpoch]
  simp only [mcxVChainAdaptive_primitive registers.lengthQ registers.zeroQ registers.equalityScratch (by omega),
    mcxVChainAdaptive_primitive registers.lengthRPrime registers.zeroRPrime registers.equalityScratch (by omega),
    mcxVChainAdaptive_primitive (registers.lengthS ++ [shiftEpoch]) registers.zeroS registers.equalityScratch (by simp only [List.length_append,List.length_singleton,hs]; omega),
    hq,hr,hs,List.length_append,List.length_singleton]
  norm_num [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
    gidneyToffoliCount,primitiveXCost,primitiveHCost,primitivePhaseCost,AdaptiveCircuit.measurementCount]
/-- Exact production-width phase/sign update, including all three tests and epoch conjugations. -/
theorem phaseUpdateEpochInverseAdaptive9_primitive (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (hq : registers.lengthQ.length=9) (hr : registers.lengthRPrime.length=9)
    (hs : registers.lengthS.length=9) (hw : 8≤registers.equalityScratch.length) :
    primitiveResources (phaseUpdateEpochInverseAdaptive registers shiftEpoch) =
      (⟨8,88,50,54,0,44⟩ : PrimitiveResources) := by
  change primitiveResources ((((((((mcxVChainAdaptive (registers.withShiftEpoch shiftEpoch).lengthQ (registers.withShiftEpoch shiftEpoch).zeroQ (registers.withShiftEpoch shiftEpoch).equalityScratch).seq
    (mcxVChainAdaptive (registers.withShiftEpoch shiftEpoch).lengthRPrime (registers.withShiftEpoch shiftEpoch).zeroRPrime
      (registers.withShiftEpoch shiftEpoch).equalityScratch)).seq
    (.unitary [.X shiftEpoch] .done)).seq
    (mcxVChainAdaptive (registers.withShiftEpoch shiftEpoch).lengthS (registers.withShiftEpoch shiftEpoch).zeroS (registers.withShiftEpoch shiftEpoch).equalityScratch)).seq
    (.unitary [.X shiftEpoch] .done))).seq (.unitary ([.CX (registers.withShiftEpoch shiftEpoch).zeroS (registers.withShiftEpoch shiftEpoch).phase2,
    .CX (registers.withShiftEpoch shiftEpoch).zeroS (registers.withShiftEpoch shiftEpoch).phase1,
    .X (registers.withShiftEpoch shiftEpoch).zeroRPrime,
    .CCX (registers.withShiftEpoch shiftEpoch).zeroQ (registers.withShiftEpoch shiftEpoch).zeroRPrime (registers.withShiftEpoch shiftEpoch).condition,
    .X (registers.withShiftEpoch shiftEpoch).zeroRPrime,
    .CCX (registers.withShiftEpoch shiftEpoch).condition (registers.withShiftEpoch shiftEpoch).phase2 (registers.withShiftEpoch shiftEpoch).sign,
    .CX (registers.withShiftEpoch shiftEpoch).sign (registers.withShiftEpoch shiftEpoch).temporary,
    .CX (registers.withShiftEpoch shiftEpoch).phase1 (registers.withShiftEpoch shiftEpoch).temporary,
    .CCX (registers.withShiftEpoch shiftEpoch).condition (registers.withShiftEpoch shiftEpoch).temporary (registers.withShiftEpoch shiftEpoch).phase2,
    .CX (registers.withShiftEpoch shiftEpoch).phase1 (registers.withShiftEpoch shiftEpoch).temporary,
    .CX (registers.withShiftEpoch shiftEpoch).sign (registers.withShiftEpoch shiftEpoch).temporary,
    .X (registers.withShiftEpoch shiftEpoch).zeroRPrime,
    .CCX (registers.withShiftEpoch shiftEpoch).zeroQ (registers.withShiftEpoch shiftEpoch).zeroRPrime (registers.withShiftEpoch shiftEpoch).condition,
    .X (registers.withShiftEpoch shiftEpoch).zeroRPrime]) .done)).seq ((((((Quantum.AdaptiveCircuit.unitary [.X shiftEpoch] .done).seq
    (mcxVChainAdaptive (registers.withShiftEpoch shiftEpoch).lengthS (registers.withShiftEpoch shiftEpoch).zeroS (registers.withShiftEpoch shiftEpoch).equalityScratch)).seq
    (.unitary [.X shiftEpoch] .done)).seq
    (mcxVChainAdaptive (registers.withShiftEpoch shiftEpoch).lengthRPrime (registers.withShiftEpoch shiftEpoch).zeroRPrime
      (registers.withShiftEpoch shiftEpoch).equalityScratch)).seq
    (mcxVChainAdaptive (registers.withShiftEpoch shiftEpoch).lengthQ (registers.withShiftEpoch shiftEpoch).zeroQ (registers.withShiftEpoch shiftEpoch).equalityScratch)))) = _
  simp only [primitiveResources_seq,PhaseUpdateRegisters.withShiftEpoch]
  simp only [mcxVChainAdaptive_primitive registers.lengthQ registers.zeroQ registers.equalityScratch (by omega),
    mcxVChainAdaptive_primitive registers.lengthRPrime registers.zeroRPrime registers.equalityScratch (by omega),
    mcxVChainAdaptive_primitive (registers.lengthS ++ [shiftEpoch]) registers.zeroS registers.equalityScratch (by simp only [List.length_append,List.length_singleton,hs]; omega),
    hq,hr,hs,List.length_append,List.length_singleton]
  norm_num [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
    gidneyToffoliCount,primitiveXCost,primitiveHCost,primitivePhaseCost,AdaptiveCircuit.measurementCount]
end ShorECDLP.Paper2607_13816
