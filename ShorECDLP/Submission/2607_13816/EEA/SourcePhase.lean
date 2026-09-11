import ShorECDLP.Submission.«2607_13816».EEA.SourcePrimitives
import ShorECDLP.Submission.«2607_13816».EEA.PhaseUpdate
namespace ShorECDLP.Paper2607_13816
open Quantum
private def phaseUpdateEpochForwardTestsSource
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) :
    CorrectionProgram :=
  let inner := registers.withShiftEpoch shiftEpoch
  (((((mcxVChainSource inner.lengthQ inner.zeroQ inner.equalityScratch).seq
    (mcxVChainSource inner.lengthRPrime inner.zeroRPrime
      inner.equalityScratch)).seq
    (.unitary [.ordinary [.X shiftEpoch]] .done)).seq
    (mcxVChainSource inner.lengthS inner.zeroS inner.equalityScratch)).seq
    (.unitary [.ordinary [.X shiftEpoch]] .done))
private def phaseUpdateEpochCleanupTestsSource
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) :
    CorrectionProgram :=
  let inner := registers.withShiftEpoch shiftEpoch
  (((((CorrectionProgram.unitary [.ordinary [.X shiftEpoch]] .done).seq
    (mcxVChainSource inner.lengthS inner.zeroS inner.equalityScratch)).seq
    (.unitary [.ordinary [.X shiftEpoch]] .done)).seq
    (mcxVChainSource inner.lengthRPrime inner.zeroRPrime
      inner.equalityScratch)).seq
    (mcxVChainSource inner.lengthQ inner.zeroQ inner.equalityScratch))
def phaseUpdateEpochSource (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) : CorrectionProgram :=
  ((phaseUpdateEpochForwardTestsSource registers shiftEpoch).seq
    (.unitary [.ordinary ([.X (registers.withShiftEpoch shiftEpoch).zeroRPrime,
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
    .CX (registers.withShiftEpoch shiftEpoch).zeroS (registers.withShiftEpoch shiftEpoch).phase2])] .done)).seq
    (phaseUpdateEpochCleanupTestsSource registers shiftEpoch)
theorem phaseUpdateEpochSource_erase (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) :
    (phaseUpdateEpochSource registers shiftEpoch).erase=phaseUpdateEpochAdaptive registers shiftEpoch := by
  simp only [phaseUpdateEpochSource,phaseUpdateEpochForwardTestsSource,phaseUpdateEpochCleanupTestsSource,
    CorrectionProgram.erase_seq,mcxVChainSource_erase,CorrectionProgram.erase,
    correctionBlockErase,CorrectionFragment.erase,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rfl
theorem phaseUpdateEpochSource_events (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (hq : registers.lengthQ.length-2≤registers.equalityScratch.length)
    (hr : registers.lengthRPrime.length-2≤registers.equalityScratch.length)
    (hs : registers.lengthS.length+1-2≤registers.equalityScratch.length) :
    (phaseUpdateEpochSource registers shiftEpoch).events=
      2*((registers.lengthQ.length-2)+(registers.lengthRPrime.length-2)+(registers.lengthS.length+1-2)) := by
  have hs' : (registers.lengthS++[shiftEpoch]).length-2≤registers.equalityScratch.length := by simpa using hs
  simp only [phaseUpdateEpochSource,phaseUpdateEpochForwardTestsSource,phaseUpdateEpochCleanupTestsSource,
    PhaseUpdateRegisters.withShiftEpoch,CorrectionProgram.events_seq,CorrectionProgram.events,
    correctionBlockEvents,CorrectionFragment.events,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Nat.zero_add,Nat.add_zero,
    mcxVChainSource_events registers.lengthQ registers.zeroQ registers.equalityScratch hq,
    mcxVChainSource_events registers.lengthRPrime registers.zeroRPrime registers.equalityScratch hr,
    mcxVChainSource_events (registers.lengthS++[shiftEpoch]) registers.zeroS registers.equalityScratch hs',
    List.length_append,List.length_singleton]
  omega
def phaseUpdateEpochInverseSource (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) : CorrectionProgram :=
  ((phaseUpdateEpochForwardTestsSource registers shiftEpoch).seq
    (.unitary [.ordinary ([.CX (registers.withShiftEpoch shiftEpoch).zeroS (registers.withShiftEpoch shiftEpoch).phase2,
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
    .X (registers.withShiftEpoch shiftEpoch).zeroRPrime])] .done)).seq
    (phaseUpdateEpochCleanupTestsSource registers shiftEpoch)
theorem phaseUpdateEpochInverseSource_erase (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) :
    (phaseUpdateEpochInverseSource registers shiftEpoch).erase=phaseUpdateEpochInverseAdaptive registers shiftEpoch := by
  simp only [phaseUpdateEpochInverseSource,phaseUpdateEpochForwardTestsSource,phaseUpdateEpochCleanupTestsSource,
    CorrectionProgram.erase_seq,mcxVChainSource_erase,CorrectionProgram.erase,
    correctionBlockErase,CorrectionFragment.erase,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rfl
theorem phaseUpdateEpochInverseSource_events (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (hq : registers.lengthQ.length-2≤registers.equalityScratch.length)
    (hr : registers.lengthRPrime.length-2≤registers.equalityScratch.length)
    (hs : registers.lengthS.length+1-2≤registers.equalityScratch.length) :
    (phaseUpdateEpochInverseSource registers shiftEpoch).events=
      2*((registers.lengthQ.length-2)+(registers.lengthRPrime.length-2)+(registers.lengthS.length+1-2)) := by
  have hs' : (registers.lengthS++[shiftEpoch]).length-2≤registers.equalityScratch.length := by simpa using hs
  simp only [phaseUpdateEpochInverseSource,phaseUpdateEpochForwardTestsSource,phaseUpdateEpochCleanupTestsSource,
    PhaseUpdateRegisters.withShiftEpoch,CorrectionProgram.events_seq,CorrectionProgram.events,
    correctionBlockEvents,CorrectionFragment.events,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Nat.zero_add,Nat.add_zero,
    mcxVChainSource_events registers.lengthQ registers.zeroQ registers.equalityScratch hq,
    mcxVChainSource_events registers.lengthRPrime registers.zeroRPrime registers.equalityScratch hr,
    mcxVChainSource_events (registers.lengthS++[shiftEpoch]) registers.zeroS registers.equalityScratch hs',
    List.length_append,List.length_singleton]
  omega
end ShorECDLP.Paper2607_13816
