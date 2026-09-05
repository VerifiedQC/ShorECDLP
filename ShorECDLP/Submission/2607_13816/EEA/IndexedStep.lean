import ShorECDLP.Submission.«2607_13816».EEA.CoefficientPrefixInverse
import ShorECDLP.Submission.«2607_13816».EEA.EndIteration
import ShorECDLP.Submission.«2607_13816».EEA.PhaseUpdate
import ShorECDLP.Submission.«2607_13816».EEA.StepControl
import ShorECDLP.Submission.«2607_13816».EEA.TBoundary

/-!
# One indexed Algorithm-3 microstep

This module composes the source-exact Phase-5 building blocks into the literal forward and
explicit reverse bodies of `append_one_step_T` from the pinned arXiv:2607.13816v2 supplement.
The scheduler uses `certifiedActiveWindows`: in particular the remainder block keeps the proved
one-lane conservative repair, while the other four windows agree with Appendix A.2.

The twenty-wire source auxiliary pool is shared serially.  `Aux[0]` is the temporary control,
`Aux[1]` is the borrowed shift epoch, and `Aux[2:]` supplies the block-local scratch views below.
-/

namespace ShorECDLP.Paper2607_13816

open Classical Quantum

noncomputable section

/-! ## Global source register map -/

/-- Physical registers of one fixed-index Algorithm-3 step. -/
structure IndexedStepRegisters where
  phase1 : Wire
  phase2 : Wire
  iter : Wire
  sign : Wire
  work1 : List Wire
  work2 : List Wire
  lengthT : List Wire
  lengthQ : List Wire
  lengthS : List Wire
  lengthRPrime : List Wire
  aux : List Wire
deriving Repr

namespace IndexedStepRegisters

/-- `Aux[0]`, the source's step-local temporary control. -/
def control (registers : IndexedStepRegisters) : Wire :=
  registers.aux.getD 0 0

/-- `Aux[1]`, the borrowed high bit of the terminal shift counter. -/
def shiftEpoch (registers : IndexedStepRegisters) : Wire :=
  registers.aux.getD 1 0

/-- `Aux[2:]`, called `scratch` by the pinned source. -/
def sourceScratch (registers : IndexedStepRegisters) : List Wire :=
  registers.aux.drop 2

/-- `scratch[0]`, the terminal flag and the later temporary condition bit. -/
def terminal (registers : IndexedStepRegisters) : Wire :=
  registers.sourceScratch.getD 0 0

/-- `scratch[1:]`, the pool available while `terminal` is live. -/
def blockScratch (registers : IndexedStepRegisters) : List Wire :=
  registers.sourceScratch.drop 1

/-- The low quotient-length bit used to spill the borrowed terminal epoch. -/
def quotientLow (registers : IndexedStepRegisters) : Wire :=
  registers.lengthQ.getD 0 0

/-- Every role declared by the source-level register map. -/
def allWires (registers : IndexedStepRegisters) : List Wire :=
  [registers.phase1, registers.phase2, registers.iter, registers.sign] ++
    registers.work1 ++ registers.work2 ++ registers.lengthT ++
      registers.lengthQ ++ registers.lengthS ++ registers.lengthRPrime ++
        registers.aux

/-- Inclusive, one-based source window projected to its physical Work slice. -/
def windowSlice (work : List Wire) (window : ActiveWindow) : List Wire :=
  (work.drop (window.start - 1)).take (window.stop - window.start + 1)

/-- Exact terminal-padding view of `block_scratch`. -/
def terminalPadding (registers : IndexedStepRegisters) : TerminalPaddingRegisters where
  terminal := registers.terminal
  shiftEpoch := registers.shiftEpoch
  work2 := registers.work2
  lengthS := registers.lengthS
  wrapped := registers.blockScratch.getD 0 0
  carryTail := (registers.blockScratch.drop 1).take (registers.lengthS.length - 2)
  equalityExtra := registers.blockScratch.getD (registers.lengthS.length - 1) 0

/-- Exact `pre_shift_gate` view, whose scratch begins after the terminal flag. -/
def preShift (registers : IndexedStepRegisters) : ShiftRegisters where
  phase1 := registers.phase1
  phase2 := registers.phase2
  work := registers.work2
  lengthS := registers.lengthS
  phase1IsZero := registers.blockScratch.getD 0 0
  both := registers.blockScratch.getD 1 0
  carries := (registers.blockScratch.drop 2).take (registers.lengthS.length - 1)
  reserved := (registers.blockScratch.drop (registers.lengthS.length + 1)).take 3

/-- Exact `post_shift_gate` view, whose scratch begins at `scratch[0]`. -/
def postShift (registers : IndexedStepRegisters) : ShiftRegisters where
  phase1 := registers.phase1
  phase2 := registers.phase2
  work := registers.work2
  lengthS := registers.lengthS
  phase1IsZero := registers.sourceScratch.getD 0 0
  both := registers.sourceScratch.getD 1 0
  carries := (registers.sourceScratch.drop 2).take (registers.lengthS.length - 1)
  reserved := (registers.sourceScratch.drop (registers.lengthS.length + 1)).take 3

/-- Scratch-free skeleton used only to compute the exact interval scratch arity. -/
private def remainderBase
    (registers : IndexedStepRegisters) (window : ActiveWindow) : IntervalRegisters where
  control := registers.control
  sign := registers.sign
  work1 := windowSlice registers.work1 window
  work2 := windowSlice registers.work2 window
  lengthT := registers.lengthT
  lengthQ := registers.lengthQ
  lengthS := registers.lengthS
  scratch := []

/-- Number of source scratch roles consumed by the remainder interval at this index. -/
def remainderScratchSize
    (registers : IndexedStepRegisters) (window : ActiveWindow) : Nat :=
  intervalScratchBase (registers.remainderBase window) window.start window.stop + 3

/-- Exact `lc_interval_addsub_unary_gate` view.  Its scratch starts at `Aux[1]`, after the
borrowed epoch has been spilled and cleared. -/
def remainder
    (registers : IndexedStepRegisters) (window : ActiveWindow) : IntervalRegisters :=
  { registers.remainderBase window with
    scratch := (registers.aux.drop 1).take (registers.remainderScratchSize window) }

/-- Exact Figure-9 quotient-selector view. -/
def quotient
    (registers : IndexedStepRegisters) (window : ActiveWindow) : QuotientSwapRegisters where
  control := registers.control
  sign := registers.sign
  work1 := windowSlice registers.work1 window
  lengthT := registers.lengthT
  lengthQ := registers.lengthQ
  scratch := registers.sourceScratch.take
    (max registers.lengthQ.length
      (quotientSwapUnaryDepth window.start window.stop) + 1)

/-- Exact phase-dependent coefficient-boundary view. -/
def tBoundary (registers : IndexedStepRegisters) : TBoundaryRegisters where
  phase2 := registers.phase2
  lengthT := registers.lengthT
  lengthRP := registers.lengthRPrime
  lengthS := registers.lengthS
  scratch := registers.blockScratch

/-- Exact prepared-boundary coefficient-prefix view. -/
def coefficient
    (registers : IndexedStepRegisters) (window : ActiveWindow) :
    CoefficientPrefixRegisters where
  control := registers.control
  sign := registers.sign
  work1 := windowSlice registers.work1 window
  work2 := windowSlice registers.work2 window
  boundary := registers.lengthT
  scratch := registers.blockScratch.take
    (max (quotientSwapUnaryDepth window.start window.stop)
      registers.lengthT.length + 3)

/-- Equality-v-chain capacity used by the three epoch-aware phase tests. -/
def phaseEqualityScratchSize (registers : IndexedStepRegisters) : Nat :=
  max (registers.lengthQ.length - 2)
    (max (registers.lengthRPrime.length - 2) (registers.lengthS.length - 1))

/-- Exact phase-update view before the borrowed epoch is appended to `lengthS`. -/
def phaseUpdate (registers : IndexedStepRegisters) : PhaseUpdateRegisters where
  phase1 := registers.phase1
  phase2 := registers.phase2
  sign := registers.sign
  lengthQ := registers.lengthQ
  lengthRPrime := registers.lengthRPrime
  lengthS := registers.lengthS
  zeroQ := registers.sourceScratch.getD 0 0
  zeroRPrime := registers.sourceScratch.getD 1 0
  zeroS := registers.sourceScratch.getD 2 0
  condition := registers.sourceScratch.getD 3 0
  temporary := registers.sourceScratch.getD 4 0
  equalityScratch := (registers.sourceScratch.drop 5).take
    registers.phaseEqualityScratchSize

/-- Exact end-of-iteration aggregate view.  The first two source-scratch wires hold the two
zero flags, so the shared writer scratch begins at `scratch[2:]`. -/
def endIteration
    (registers : IndexedStepRegisters) (n T : Nat) : EndIterationRegisters :=
  let windows := endIterationWindowsAt n T
  let base : EndIterationRegisters := {
    control := registers.control
    work1 := registers.work1
    work2 := registers.work2
    lengthT := registers.lengthT
    lengthRP := registers.lengthRPrime
    scratch := [] }
  let scratch := (registers.sourceScratch.drop 2).take
    (endIterationScratchSize base n windows)
  { base with scratch := scratch }

end IndexedStepRegisters

/-! ## Literal source blocks -/

private def terminalConditionWires (registers : IndexedStepRegisters) : List Wire :=
  registers.phase1 :: registers.lengthRPrime

private def terminalConditionValue (registers : IndexedStepRegisters) : Nat :=
  2 ^ (registers.lengthRPrime.length + 1) - 2

private def toggleTerminal (registers : IndexedStepRegisters) : Circuit :=
  computeControl (terminalConditionWires registers) (terminalConditionValue registers)
    registers.terminal registers.blockScratch

private def toggleRControl
    (registers : IndexedStepRegisters) (conditions : List Wire) (value : Nat)
    (zeroRPrime : Wire) (scratch : List Wire) : Circuit :=
  rControlNonterminal conditions value registers.control registers.lengthRPrime
    zeroRPrime scratch

private def blockAForward
    (registers : IndexedStepRegisters) : Circuit :=
  circuit! {
    toggleTerminal registers;
    terminalPaddingForward registers.terminalPadding;
    gate! Gate.CX registers.terminal registers.phase1;
    preShiftUnitary registers.preShift;
    gate! Gate.CX registers.terminal registers.phase1;
    terminalEpochSpill registers.terminal registers.shiftEpoch registers.quotientLow;
    toggleTerminal registers
  }

private def blockAInverse
    (registers : IndexedStepRegisters) : Circuit :=
  circuit! {
    toggleTerminal registers;
    terminalEpochRestore registers.terminal registers.shiftEpoch registers.quotientLow;
    gate! Gate.CX registers.terminal registers.phase1;
    (preShiftUnitary registers.preShift).adjoint;
    gate! Gate.CX registers.terminal registers.phase1;
    terminalPaddingInverse registers.terminalPadding;
    toggleTerminal registers
  }

private def remainderSubControl (registers : IndexedStepRegisters) : Circuit :=
  toggleRControl registers ([registers.phase1]) 0 registers.terminal registers.blockScratch

private def remainderPhase2Control (registers : IndexedStepRegisters) : Circuit :=
  toggleRControl registers ([registers.phase1, registers.phase2]) 2
    registers.terminal registers.blockScratch

private def remainderRestoreControl (registers : IndexedStepRegisters) : Circuit :=
  circuit! {
    gate! Gate.CCX registers.phase2 registers.sign registers.terminal;
    toggleRControl registers ([registers.phase1, registers.terminal]) 0
      (registers.blockScratch.getD 0 0) (registers.blockScratch.drop 1);
    gate! Gate.CCX registers.phase2 registers.sign registers.terminal
  }

private def blockB1Forward
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) : Circuit :=
  circuit! {
    remainderSubControl registers;
    intervalAddSubUnitary (registers.remainder window) n window.start window.stop
      .sub true .work1;
    remainderSubControl registers
  }

private def blockB1Inverse
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) : Circuit :=
  circuit! {
    remainderSubControl registers;
    intervalAddSubInverseUnitary (registers.remainder window) n window.start window.stop
      .sub true .work1;
    remainderSubControl registers
  }

private def blockB2 (registers : IndexedStepRegisters) : Circuit :=
  circuit! {
    remainderPhase2Control registers;
    gate! Gate.CX registers.control registers.sign;
    remainderPhase2Control registers
  }

private def blockB3Forward
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) : Circuit :=
  circuit! {
    remainderRestoreControl registers;
    intervalAddSubUnitary (registers.remainder window) n window.start window.stop
      .add false .work1;
    remainderRestoreControl registers
  }

private def blockB3Inverse
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) : Circuit :=
  circuit! {
    remainderRestoreControl registers;
    intervalAddSubInverseUnitary (registers.remainder window) n window.start window.stop
      .add false .work1;
    remainderRestoreControl registers
  }

private def blockBForward
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) : Circuit :=
  circuit! {
    blockB1Forward registers n window;
    blockB2 registers;
    blockB3Forward registers n window
  }

private def blockBInverse
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) : Circuit :=
  circuit! {
    blockB3Inverse registers n window;
    blockB2 registers;
    blockB1Inverse registers n window
  }

private def blockCForward (registers : IndexedStepRegisters) : Circuit :=
  circuit! {
    toggleTerminal registers;
    terminalEpochRestore registers.terminal registers.shiftEpoch registers.quotientLow;
    toggleTerminal registers
  }

private def blockCInverse (registers : IndexedStepRegisters) : Circuit :=
  circuit! {
    toggleTerminal registers;
    terminalEpochSpill registers.terminal registers.shiftEpoch registers.quotientLow;
    toggleTerminal registers
  }

private def phase2LengthControl (registers : IndexedStepRegisters) : Circuit :=
  computeControl ([registers.phase1, registers.phase2]) 2 registers.control
    registers.sourceScratch

private def phase3LengthControl (registers : IndexedStepRegisters) : Circuit :=
  computeControl ([registers.phase1, registers.phase2]) 1 registers.control
    registers.sourceScratch

private def quotientXorControl (registers : IndexedStepRegisters) : Circuit :=
  [.CX registers.phase1 registers.control, .CX registers.phase2 registers.control]

private def quotientXorControlInverse (registers : IndexedStepRegisters) : Circuit :=
  [.CX registers.phase2 registers.control, .CX registers.phase1 registers.control]

private def lengthCarries (registers : IndexedStepRegisters) : List Wire :=
  registers.sourceScratch.take (registers.lengthQ.length - 1)

private def blockDForward
    (registers : IndexedStepRegisters) (window : ActiveWindow) : Circuit :=
  circuit! {
    phase2LengthControl registers;
    controlledIncrement registers.control registers.lengthQ (lengthCarries registers);
    phase2LengthControl registers;
    quotientXorControl registers;
    quotientSwapUnitary (registers.quotient window) window.start window.stop;
    quotientXorControlInverse registers;
    phase3LengthControl registers;
    controlledDecrement registers.control registers.lengthQ (lengthCarries registers);
    phase3LengthControl registers
  }

private def blockDInverse
    (registers : IndexedStepRegisters) (window : ActiveWindow) : Circuit :=
  circuit! {
    phase3LengthControl registers;
    controlledIncrement registers.control registers.lengthQ (lengthCarries registers);
    phase3LengthControl registers;
    quotientXorControl registers;
    quotientSwapUnitary (registers.quotient window) window.start window.stop;
    quotientXorControlInverse registers;
    phase2LengthControl registers;
    controlledDecrement registers.control registers.lengthQ (lengthCarries registers);
    phase2LengthControl registers
  }

private def coefficientTemporaryControl (registers : IndexedStepRegisters) : Circuit :=
  computeControl ([registers.phase2, registers.sign]) 2 registers.terminal
    registers.blockScratch

private def coefficientSubControl (registers : IndexedStepRegisters) : Circuit :=
  computeControl ([registers.phase1, registers.terminal]) 1 registers.control
    registers.blockScratch

private def coefficientAddControl (registers : IndexedStepRegisters) : Circuit :=
  computeControl ([registers.phase1]) 1 registers.control registers.blockScratch

private def blockEForward
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) : Circuit :=
  circuit! {
    coefficientTemporaryControl registers;
    coefficientSubControl registers;
    coefficientTemporaryControl registers;
    prepareLatestPaperTBoundary registers.tBoundary n;
    coefficientPrefixUnitary (registers.coefficient window) window.start window.stop
      .sub false .work2;
    coefficientTemporaryControl registers;
    coefficientSubControl registers;
    coefficientTemporaryControl registers;
    gate! Gate.CX registers.phase1 registers.sign;
    coefficientAddControl registers;
    coefficientPrefixUnitary (registers.coefficient window) window.start window.stop
      .add true .work2;
    coefficientAddControl registers;
    restoreLatestPaperTBoundary registers.tBoundary n
  }

private def blockEInverse
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) : Circuit :=
  circuit! {
    prepareLatestPaperTBoundary registers.tBoundary n;
    coefficientAddControl registers;
    coefficientPrefixInverseUnitary (registers.coefficient window) window.start window.stop
      .add true .work2;
    coefficientAddControl registers;
    gate! Gate.CX registers.phase1 registers.sign;
    coefficientTemporaryControl registers;
    coefficientSubControl registers;
    coefficientTemporaryControl registers;
    coefficientPrefixInverseUnitary (registers.coefficient window) window.start window.stop
      .sub false .work2;
    coefficientTemporaryControl registers;
    coefficientSubControl registers;
    coefficientTemporaryControl registers;
    restoreLatestPaperTBoundary registers.tBoundary n
  }

private def blockFForward (registers : IndexedStepRegisters) : Circuit :=
  postShiftUnitary registers.postShift

private def blockFInverse (registers : IndexedStepRegisters) : Circuit :=
  (postShiftUnitary registers.postShift).adjoint

private def blockGForward (registers : IndexedStepRegisters) : Circuit :=
  phaseUpdateEpochUnitary registers.phaseUpdate registers.shiftEpoch

private def blockGInverse (registers : IndexedStepRegisters) : Circuit :=
  phaseUpdateEpochInverseUnitary registers.phaseUpdate registers.shiftEpoch

private def blockHForward
    (registers : IndexedStepRegisters) (n T : Nat) : Circuit :=
  if T % 4 = 0 then
    circuit! {
      mcxVChain registers.lengthQ (registers.sourceScratch.getD 0 0)
        (registers.sourceScratch.drop 2);
      gate! Gate.X registers.shiftEpoch;
      mcxVChain (registers.lengthS ++ [registers.shiftEpoch])
        (registers.sourceScratch.getD 1 0) (registers.sourceScratch.drop 2);
      gate! Gate.X registers.shiftEpoch;
      gate! Gate.CCX (registers.sourceScratch.getD 0 0)
        (registers.sourceScratch.getD 1 0) registers.control;
      swapWorkAndLengthUnaryShared (registers.endIteration n T) n
        (endIterationWindowsAt n T);
      gate! Gate.CX registers.control registers.iter;
      gate! Gate.CCX (registers.sourceScratch.getD 0 0)
        (registers.sourceScratch.getD 1 0) registers.control;
      gate! Gate.X registers.shiftEpoch;
      mcxVChain (registers.lengthS ++ [registers.shiftEpoch])
        (registers.sourceScratch.getD 1 0) (registers.sourceScratch.drop 2);
      gate! Gate.X registers.shiftEpoch;
      mcxVChain registers.lengthQ (registers.sourceScratch.getD 0 0)
        (registers.sourceScratch.drop 2)
    }
  else []

private def blockHInverse
    (registers : IndexedStepRegisters) (n T : Nat) : Circuit :=
  if T % 4 = 0 then
    circuit! {
      mcxVChain registers.lengthQ (registers.sourceScratch.getD 0 0)
        (registers.sourceScratch.drop 2);
      gate! Gate.X registers.shiftEpoch;
      mcxVChain (registers.lengthS ++ [registers.shiftEpoch])
        (registers.sourceScratch.getD 1 0) (registers.sourceScratch.drop 2);
      gate! Gate.X registers.shiftEpoch;
      gate! Gate.CCX (registers.sourceScratch.getD 0 0)
        (registers.sourceScratch.getD 1 0) registers.control;
      gate! Gate.CX registers.control registers.iter;
      swapWorkAndLengthUnarySharedInverse (registers.endIteration n T) n
        (endIterationWindowsAt n T);
      gate! Gate.CCX (registers.sourceScratch.getD 0 0)
        (registers.sourceScratch.getD 1 0) registers.control;
      gate! Gate.X registers.shiftEpoch;
      mcxVChain (registers.lengthS ++ [registers.shiftEpoch])
        (registers.sourceScratch.getD 1 0) (registers.sourceScratch.drop 2);
      gate! Gate.X registers.shiftEpoch;
      mcxVChain registers.lengthQ (registers.sourceScratch.getD 0 0)
        (registers.sourceScratch.drop 2)
    }
  else []

/-! ## Measurement-uncomputed source blocks -/

private def adaptiveUnitary (circuit : Circuit) : Quantum.AdaptiveCircuit :=
  .unitary circuit .done

private def blockB1Adaptive
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) :
    Quantum.AdaptiveCircuit :=
  (adaptiveUnitary (remainderSubControl registers)).seq
    ((intervalAddSub (registers.remainder window) n window.start window.stop
      .sub true .work1).seq
      (adaptiveUnitary (remainderSubControl registers)))

private def blockB3Adaptive
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) :
    Quantum.AdaptiveCircuit :=
  (adaptiveUnitary (remainderRestoreControl registers)).seq
    ((intervalAddSub (registers.remainder window) n window.start window.stop
      .add false .work1).seq
      (adaptiveUnitary (remainderRestoreControl registers)))

private def blockBAdaptive
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) :
    Quantum.AdaptiveCircuit :=
  (blockB1Adaptive registers n window).seq
    ((adaptiveUnitary (blockB2 registers)).seq
      (blockB3Adaptive registers n window))

private def blockEPrefix
    (registers : IndexedStepRegisters) (n : Nat) : Circuit :=
  circuit! {
    coefficientTemporaryControl registers;
    coefficientSubControl registers;
    coefficientTemporaryControl registers;
    prepareLatestPaperTBoundary registers.tBoundary n
  }

private def blockEMiddle (registers : IndexedStepRegisters) : Circuit :=
  circuit! {
    coefficientTemporaryControl registers;
    coefficientSubControl registers;
    coefficientTemporaryControl registers;
    gate! Gate.CX registers.phase1 registers.sign;
    coefficientAddControl registers
  }

private def blockESuffix
    (registers : IndexedStepRegisters) (n : Nat) : Circuit :=
  circuit! {
    coefficientAddControl registers;
    restoreLatestPaperTBoundary registers.tBoundary n
  }

private def blockEFirstAdaptive
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) :
    Quantum.AdaptiveCircuit :=
  (adaptiveUnitary (blockEPrefix registers n)).seq
    (coefficientPrefixAdaptive (registers.coefficient window)
      window.start window.stop .sub false .work2)

private def blockETailAdaptive
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) :
    Quantum.AdaptiveCircuit :=
  (adaptiveUnitary (blockEMiddle registers)).seq
    ((coefficientPrefixAdaptive (registers.coefficient window)
      window.start window.stop .add true .work2).seq
      (adaptiveUnitary (blockESuffix registers n)))

private def blockEAdaptive
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) :
    Quantum.AdaptiveCircuit :=
  (blockEFirstAdaptive registers n window).seq
    (blockETailAdaptive registers n window)

/-! ## Physical composition contract -/

/-- Physical and component-level conditions for one source-indexed step.  Every field is attached
to a literal source block above; the contract adds no semantic oracle for the composed circuit. -/
structure IndexedStepLayout
    (registers : IndexedStepRegisters) (n T : Nat) : Prop where
  aux_length : registers.aux.length = 20
  work1_length : registers.work1.length = n + 3
  work2_length : registers.work2.length = n + 3
  physical : registers.allWires.Nodup
  terminalControl : ComputeControlLayout
    (terminalConditionWires registers) registers.terminal registers.blockScratch
  terminalPaddingCapacity : registers.lengthS.length < registers.blockScratch.length
  terminalPadding : TerminalPaddingLayout registers.terminalPadding
  terminalPhase : [registers.terminal, registers.phase1].Nodup
  terminalEpoch :
    [registers.terminal, registers.shiftEpoch, registers.quotientLow].Nodup
  preShift : ShiftLayout registers.preShift
  remainderSub : RControlNonterminalLayout [registers.phase1] registers.control
    registers.lengthRPrime registers.terminal registers.blockScratch
  remainderPhase2 : RControlNonterminalLayout [registers.phase1, registers.phase2]
    registers.control registers.lengthRPrime registers.terminal registers.blockScratch
  remainderRestoreCCX :
    [registers.phase2, registers.sign, registers.terminal].Nodup
  controlSign : [registers.control, registers.sign].Nodup
  remainderRestore : RControlNonterminalLayout [registers.phase1, registers.terminal]
    registers.control registers.lengthRPrime (registers.blockScratch.getD 0 0)
      (registers.blockScratch.drop 1)
  remainder : IntervalLayout
    (registers.remainder (certifiedActiveWindows n T).remainder)
    (certifiedActiveWindows n T).remainder.start
    (certifiedActiveWindows n T).remainder.stop .work1
  lengthQ_positive : 0 < registers.lengthQ.length
  phase2Length : ComputeControlLayout [registers.phase1, registers.phase2]
    registers.control registers.sourceScratch
  phase3Length : ComputeControlLayout [registers.phase1, registers.phase2]
    registers.control registers.sourceScratch
  lengthCarryCapacity :
    registers.lengthQ.length = (lengthCarries registers).length + 1
  lengthCarryPhysical :
    (registers.control :: registers.lengthQ ++ lengthCarries registers).Nodup
  quotientControls : [registers.phase1, registers.phase2, registers.control].Nodup
  quotient : QuotientSwapLayout
    (registers.quotient (certifiedActiveWindows n T).quotientSwap)
    (certifiedActiveWindows n T).quotientSwap.start
    (certifiedActiveWindows n T).quotientSwap.stop
  coefficientTemporary : ComputeControlLayout [registers.phase2, registers.sign]
    registers.terminal registers.blockScratch
  coefficientSub : ComputeControlLayout [registers.phase1, registers.terminal]
    registers.control registers.blockScratch
  coefficientAdd : ComputeControlLayout [registers.phase1]
    registers.control registers.blockScratch
  coefficientSign : [registers.phase1, registers.sign].Nodup
  tBoundary : TBoundaryLayout registers.tBoundary
  coefficient : CoefficientPrefixLayout
    (registers.coefficient (certifiedActiveWindows n T).coefficient)
    (certifiedActiveWindows n T).coefficient.start
    (certifiedActiveWindows n T).coefficient.stop
  postShift : ShiftLayout registers.postShift
  phaseUpdate : PhaseUpdateEpochLayout registers.phaseUpdate registers.shiftEpoch
  endQ : registers.lengthQ.length - 2 ≤ (registers.sourceScratch.drop 2).length ∧
    McxVChainLayout registers.lengthQ (registers.sourceScratch.getD 0 0)
      (registers.sourceScratch.drop 2)
  endS : (registers.lengthS ++ [registers.shiftEpoch]).length - 2 ≤
      (registers.sourceScratch.drop 2).length ∧
    McxVChainLayout (registers.lengthS ++ [registers.shiftEpoch])
      (registers.sourceScratch.getD 1 0) (registers.sourceScratch.drop 2)
  endControls :
    [registers.sourceScratch.getD 0 0, registers.sourceScratch.getD 1 0,
      registers.control, registers.iter].Nodup
  endIteration : T % 4 = 0 → EndIterationLayout (registers.endIteration n T) n
    (endIterationWindowsAt n T)

/-! ## Closed nonterminal layout witness -/

/-- A compact, source-shaped allocation for the first nonterminal step at `n = T = 1`.
The optional end-of-iteration block is absent at this index; its production layout is certified
separately by `endIterationProduction_layout`. -/
private def indexedStepSmallRegisters : IndexedStepRegisters where
  phase1 := 0
  phase2 := 1
  iter := 2
  sign := 3
  work1 := List.range' 4 4
  work2 := List.range' 8 4
  lengthT := List.range' 12 3
  lengthQ := List.range' 15 3
  lengthS := List.range' 18 3
  lengthRPrime := List.range' 21 3
  aux := List.range' 24 20

private theorem indexedStepSmall_remainder_tree :
    intervalTree
        (indexedStepSmallRegisters.remainder
          (certifiedActiveWindows 1 1).remainder) 2 4 =
      .node 18 15 (.leaf 0) (.leaf 1) := by
  rfl

private theorem indexedStepSmall_remainder_layout :
    IntervalLayout
      (indexedStepSmallRegisters.remainder
        (certifiedActiveWindows 1 1).remainder) 2 4 .work1 := by
  let registers := indexedStepSmallRegisters.remainder
    (certifiedActiveWindows 1 1).remainder
  refine {
    k_le_K := by decide
    work1_length := by decide
    work2_length := by decide
    lengthT_eq_lengthQ := by decide
    lengthT_two_le := by decide
    lengthS_two_le := by decide
    right_index_capacity := by decide
    left_index_capacity := by decide
    right_top_capacity := by decide
    left_top_capacity := by decide
    scratch_length := by decide
    physical := by decide
    endpoints := by
      change IntervalEndpointLayout ([12, 13, 14] : List Wire)
        ([15, 16, 17] : List Wire) ([18, 19, 20] : List Wire)
        ([25, 26, 27] : List Wire) 28
      norm_num [IntervalEndpointLayout]
    traversal := ?_
    topSpecial := ?_
  }
  · rw [IntervalTraversalLayout]
    constructor
    · change DualUnaryActionTree.Layout
        (.node 18 15 (.leaf 0) (.leaf 1)) 24 24
          ([25] : List Wire) ([26] : List Wire)
      apply DualUnaryActionTree.Layout.node
      · decide
      · apply DualUnaryActionTree.Layout.leaf
        decide
      · apply DualUnaryActionTree.Layout.leaf
        decide
    · intro label hlabel
      rw [show intervalTree registers 2 4 =
          .node 18 15 (.leaf 0) (.leaf 1) by
        exact indexedStepSmall_remainder_tree] at hlabel
      simp [DualUnaryActionTree.labels] at hlabel
      rcases hlabel with rfl | rfl
      · change ([19, 16, 29, 5, 9, 28, 30] : List Wire).Nodup ∧
          DecoderOutsideIntervalRoles ([24, 18, 15, 25, 26] : List Wire)
            19 16 29 5 9 28 30
        norm_num [DecoderOutsideIntervalRoles]
      · change ([19, 16, 29, 6, 10, 28, 30] : List Wire).Nodup ∧
          DecoderOutsideIntervalRoles ([24, 18, 15, 25, 26] : List Wire)
            19 16 29 6 10 28 30
        norm_num [DecoderOutsideIntervalRoles]
  · intro _
    change TopSpecialLeafLayout 24 24 ([18, 19, 20] : List Wire)
      ([15, 16, 17] : List Wire) 29 7 11 28 30 30
      ([25, 26, 27] : List Wire)
    norm_num [TopSpecialLeafLayout, EqControlLayout]

private theorem indexedStepSmall_quotient_layout :
    QuotientSwapLayout
      (indexedStepSmallRegisters.quotient
        (certifiedActiveWindows 1 1).quotientSwap) 2 2 := by
  refine {
    k_le_K := by decide
    work1_length := by decide
    lengthT_eq_lengthQ := by decide
    index_width := by decide
    scratch_length := by decide
    physical := by decide
    tree := ?_
  }
  change UnaryActionTree.Layout (.leaf 2) 24 ([] : List Wire)
  exact UnaryActionTree.Layout.leaf 2 24 ([] : List Wire) (by decide)

private theorem indexedStepSmall_coefficient_layout :
    CoefficientPrefixLayout
      (indexedStepSmallRegisters.coefficient
        (certifiedActiveWindows 1 1).coefficient) 1 2 := by
  refine {
    k_le_K := by decide
    work1_length := by decide
    work2_length := by decide
    index_width := by decide
    scratch_length := by decide
    physical := by decide
    tree := ?_
  }
  change UnaryActionTree.Layout
    (.node 13 (.leaf 1) (.leaf 2)) 24 ([27] : List Wire)
  exact UnaryActionTree.Layout.node 13 24 27 (.leaf 1) (.leaf 2)
    ([] : List Wire) (by decide)
    (UnaryActionTree.Layout.leaf 1 27 ([] : List Wire) (by decide))
    (UnaryActionTree.Layout.leaf 2 27 ([] : List Wire) (by decide))

private theorem indexedStepSmall_layout :
    IndexedStepLayout indexedStepSmallRegisters 1 1 := by
  refine {
    aux_length := by decide
    work1_length := by decide
    work2_length := by decide
    physical := by decide
    terminalControl := by
      change 2 ≤ 17 ∧
        (([0, 21, 22, 23] : List Wire) ++
          26 :: List.range' 27 17).Nodup
      decide
    terminalPaddingCapacity := by decide
    terminalPadding := ⟨by decide, by decide⟩
    terminalPhase := by decide
    terminalEpoch := by decide
    preShift := ⟨by decide, by decide, by decide⟩
    remainderSub := by
      refine ⟨?_, ?_, by decide⟩
      · change 1 ≤ 17 ∧
          (([21, 22, 23] : List Wire) ++ 26 :: List.range' 27 17).Nodup
        decide
      · change 0 ≤ 17 ∧
          (([0, 26] : List Wire) ++ 24 :: List.range' 27 17).Nodup
        decide
    remainderPhase2 := by
      refine ⟨?_, ?_, by decide⟩
      · change 1 ≤ 17 ∧
          (([21, 22, 23] : List Wire) ++ 26 :: List.range' 27 17).Nodup
        decide
      · change 1 ≤ 17 ∧
          (([0, 1, 26] : List Wire) ++ 24 :: List.range' 27 17).Nodup
        decide
    remainderRestoreCCX := by decide
    controlSign := by decide
    remainderRestore := by
      refine ⟨?_, ?_, by decide⟩
      · change 1 ≤ 16 ∧
          (([21, 22, 23] : List Wire) ++ 27 :: List.range' 28 16).Nodup
        decide
      · change 1 ≤ 16 ∧
          (([0, 26, 27] : List Wire) ++ 24 :: List.range' 28 16).Nodup
        decide
    remainder := indexedStepSmall_remainder_layout
    lengthQ_positive := by decide
    phase2Length := by
      change 0 ≤ 18 ∧
        (([0, 1] : List Wire) ++ 24 :: List.range' 26 18).Nodup
      decide
    phase3Length := by
      change 0 ≤ 18 ∧
        (([0, 1] : List Wire) ++ 24 :: List.range' 26 18).Nodup
      decide
    lengthCarryCapacity := by decide
    lengthCarryPhysical := by decide
    quotientControls := by decide
    quotient := indexedStepSmall_quotient_layout
    coefficientTemporary := by
      change 0 ≤ 17 ∧
        (([1, 3] : List Wire) ++ 26 :: List.range' 27 17).Nodup
      decide
    coefficientSub := by
      change 0 ≤ 17 ∧
        (([0, 26] : List Wire) ++ 24 :: List.range' 27 17).Nodup
      decide
    coefficientAdd := by
      change 0 ≤ 17 ∧
        (([0] : List Wire) ++ 24 :: List.range' 27 17).Nodup
      decide
    coefficientSign := by decide
    tBoundary := ⟨by decide, by decide, by decide, by decide, by decide⟩
    coefficient := indexedStepSmall_coefficient_layout
    postShift := ⟨by decide, by decide, by decide⟩
    phaseUpdate := ⟨by decide, by decide, by decide, by decide, by decide⟩
    endQ := by
      change 1 ≤ 16 ∧
        (([15, 16, 17] : List Wire) ++ 26 :: List.range' 28 16).Nodup
      decide
    endS := by
      change 2 ≤ 16 ∧
        (([18, 19, 20, 25] : List Wire) ++ 27 :: List.range' 28 16).Nodup
      decide
    endControls := by decide
    endIteration := by norm_num
  }

/-- The full indexed-step physical contract is inhabited by a 44-role nonterminal source
allocation.  The theorem keeps the concrete fixture private while making non-vacuity explicit. -/
theorem indexedStepLayout_inhabited :
    ∃ registers : IndexedStepRegisters,
      registers.allWires.length = 44 ∧ IndexedStepLayout registers 1 1 := by
  exact ⟨indexedStepSmallRegisters, by decide, indexedStepSmall_layout⟩

/-- Scratch that is genuinely temporary at an indexed step boundary.  The borrowed epoch is
deliberately excluded: it is persistent padding state, not a clean ancilla. -/
def IndexedStepRegisters.sharedScratch
    (registers : IndexedStepRegisters) : List Wire :=
  registers.control :: registers.sourceScratch

/-- Every temporary source role is clean at a step boundary. -/
def IndexedStepReady
    (registers : IndexedStepRegisters) (state : BasisState) : Prop :=
  Clean registers.sharedScratch state

/-- During remainder arithmetic the borrowed epoch has been spilled, so the entire source Aux
bank—including `Aux[1]`—is a clean serial workspace. -/
def IndexedStepBorrowedReady
    (registers : IndexedStepRegisters) (state : BasisState) : Prop :=
  Clean registers.aux state

/-- Reachable terminal branches store logical `ell_q = 0` in truth-minus-one form, so its low bit
is one and can receive the borrowed epoch. -/
def IndexedStepTerminalEncoded
    (registers : IndexedStepRegisters) (state : BasisState) : Prop :=
  registerMatches (terminalConditionWires registers)
      (terminalConditionValue registers) state = true →
    state registers.quotientLow = true

/-- The borrowed high shift bit is live only on padding frames.  On an active frame it is zero;
on a terminal frame the truth-minus-one quotient word provides the clean spill destination. -/
def IndexedStepEpochEncoded
    (registers : IndexedStepRegisters) (state : BasisState) : Prop :=
  if registerMatches (terminalConditionWires registers)
      (terminalConditionValue registers) state then
    state registers.quotientLow = true
  else
    state registers.shiftEpoch = false

/-! ## Gate-independent state combinators -/

private def xorWireState
    (control target : Wire) (state : BasisState) : BasisState :=
  state[target ↦ Bool.xor (state target) (state control)]

private def andXorWireState
    (first second target : Wire) (state : BasisState) : BasisState :=
  state[target ↦ Bool.xor (state target) (state first && state second)]

private def matchXorState
    (controls : List Wire) (value : Nat) (target : Wire)
    (state : BasisState) : BasisState :=
  state[target ↦ Bool.xor (state target)
    (registerMatches controls value state)]

private theorem matchXorState_preserves
    (controls : List Wire) (value : Nat) (target : Wire)
    (state : BasisState) {wire : Wire} (hwire : wire ≠ target) :
    matchXorState controls value target state wire = state wire := by
  simp [matchXorState, upd, hwire]

private def rControlState
    (conditions : List Wire) (value : Nat) (control : Wire)
    (lengthRPrime : List Wire) (zeroRPrime : Wire)
    (state : BasisState) : BasisState :=
  state[control ↦ Bool.xor (state control)
    (rControlNonterminalPredicate conditions value
      lengthRPrime zeroRPrime state)]

private def swapWireState
    (left right : Wire) (state : BasisState) : BasisState :=
  state[left ↦ state right][right ↦ state left]

private def controlledSwapState
    (control left right : Wire) (state : BasisState) : BasisState :=
  if state control then swapWireState left right state else state

private def terminalEpochSpillState
    (terminal shiftEpoch quotientLow : Wire) (state : BasisState) : BasisState :=
  controlledSwapState terminal shiftEpoch quotientLow
    (xorWireState terminal quotientLow state)

private def terminalEpochRestoreState
    (terminal shiftEpoch quotientLow : Wire) (state : BasisState) : BasisState :=
  xorWireState terminal quotientLow
    (controlledSwapState terminal shiftEpoch quotientLow state)

private theorem terminalEpochSpillState_preserves
    (terminal shiftEpoch quotientLow : Wire) (state : BasisState)
    {wire : Wire} (hshift : wire ≠ shiftEpoch)
    (hquotient : wire ≠ quotientLow)
    (hterminalQuotient : terminal ≠ quotientLow) :
    terminalEpochSpillState terminal shiftEpoch quotientLow state wire =
      state wire := by
  cases hterminal : state terminal <;>
    simp [terminalEpochSpillState, controlledSwapState, xorWireState,
      swapWireState, upd, hterminal, hshift, hquotient,
      hterminalQuotient]

private theorem terminalEpochRestoreState_preserves
    (terminal shiftEpoch quotientLow : Wire) (state : BasisState)
    {wire : Wire} (hshift : wire ≠ shiftEpoch)
    (hquotient : wire ≠ quotientLow) :
    terminalEpochRestoreState terminal shiftEpoch quotientLow state wire =
      state wire := by
  cases hterminal : state terminal <;>
    simp [terminalEpochRestoreState, controlledSwapState, xorWireState,
      swapWireState, upd, hterminal, hshift, hquotient]

private theorem run_xorWireState
    (control target : Wire) (state : BasisState) :
    run ([.CX control target] : Circuit) state =
      xorWireState control target state := by
  rfl

private theorem run_andXorWireState
    (first second target : Wire) (state : BasisState) :
    run ([.CCX first second target] : Circuit) state =
      andXorWireState first second target state := by
  rfl

private theorem run_terminalEpochSpillState
    (terminal shiftEpoch quotientLow : Wire) (state : BasisState)
    (hlayout : TerminalEpochLayout terminal shiftEpoch quotientLow) :
    run (terminalEpochSpill terminal shiftEpoch quotientLow) state =
      terminalEpochSpillState terminal shiftEpoch quotientLow state := by
  simp only [TerminalEpochLayout, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hlayout
  rw [terminalEpochSpill, Classical.run_append,
    run_controlledSwap terminal shiftEpoch quotientLow]
  · rfl
  · exact hlayout.1.1
  · exact hlayout.1.2
  · exact hlayout.2.1

private theorem run_terminalEpochRestoreState
    (terminal shiftEpoch quotientLow : Wire) (state : BasisState)
    (hlayout : TerminalEpochLayout terminal shiftEpoch quotientLow) :
    run (terminalEpochRestore terminal shiftEpoch quotientLow) state =
      terminalEpochRestoreState terminal shiftEpoch quotientLow state := by
  simp only [TerminalEpochLayout, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hlayout
  rw [terminalEpochRestore, Classical.run_append,
    run_controlledSwap terminal shiftEpoch quotientLow]
  · rfl
  · exact hlayout.1.1
  · exact hlayout.1.2
  · exact hlayout.2.1

private theorem clean_mono
    {large small : List Wire} {state : BasisState}
    (hclean : Clean large state)
    (hsub : ∀ wire ∈ small, wire ∈ large) : Clean small state := by
  intro wire hwire
  exact hclean wire (hsub wire hwire)

private theorem clean_upd_not_mem
    {wires : List Wire} {state : BasisState} {target : Wire} {value : Bool}
    (hclean : Clean wires state) (houtside : target ∉ wires) :
    Clean wires state[target ↦ value] := by
  intro wire hwire
  rw [upd_other]
  · exact hclean wire hwire
  · intro equality
    subst wire
    exact houtside hwire

private theorem writeReg_apply_outside
    (register : List Wire) (value : Nat) (state : BasisState)
    {wire : Wire} (hwire : wire ∉ register) :
    writeReg register value state wire = state wire := by
  induction register generalizing value state with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.mem_cons, not_or] at hwire
      rw [writeReg, ih (state := state[head ↦ value.testBit 0])
        (value := value / 2) hwire.2, upd_other]
      exact hwire.1

private def indexedWriteWireValues : List Wire → List Bool → BasisState → BasisState
  | wire :: wires, bit :: bits, state =>
      (indexedWriteWireValues wires bits state)[wire ↦ bit]
  | _, _, state => state

private theorem indexedWriteWireValues_preservesOutside
    (wires : List Wire) (bits : List Bool) (state : BasisState)
    {wire : Wire} (hwire : wire ∉ wires) :
    indexedWriteWireValues wires bits state wire = state wire := by
  induction wires generalizing bits state with
  | nil => simp [indexedWriteWireValues]
  | cons head tail ih =>
      cases bits with
      | nil => simp [indexedWriteWireValues]
      | cons bit bits =>
          simp only [List.mem_cons, not_or] at hwire
          simp [indexedWriteWireValues, upd, hwire.1, ih bits state hwire.2]

private theorem indexedWireValues_writeWireValues
    (wires : List Wire) (bits : List Bool) (state : BasisState)
    (hnd : wires.Nodup) (hlength : bits.length = wires.length) :
    wireValues wires (indexedWriteWireValues wires bits state) = bits := by
  induction wires generalizing bits state with
  | nil =>
      have : bits = [] := List.length_eq_zero_iff.mp (by simpa using hlength)
      subst bits
      rfl
  | cons head tail ih =>
      cases bits with
      | nil => simp at hlength
      | cons bit bits =>
          have hhead : head ∉ tail := (List.nodup_cons.mp hnd).1
          have htail : tail.Nodup := (List.nodup_cons.mp hnd).2
          have htailLength : bits.length = tail.length := by simpa using hlength
          have htailUpdated :
              wireValues tail
                  ((indexedWriteWireValues tail bits state)[head ↦ bit]) =
                wireValues tail (indexedWriteWireValues tail bits state) := by
            unfold wireValues
            apply List.map_congr_left
            intro wire hwire
            have hne : wire ≠ head := by
              intro equality
              subst wire
              exact hhead hwire
            simp [upd, hne]
          simp only [indexedWriteWireValues, wireValues, List.map_cons]
          change
            (indexedWriteWireValues tail bits state)[head ↦ bit] head ::
                wireValues tail
                  ((indexedWriteWireValues tail bits state)[head ↦ bit]) =
              bit :: bits
          rw [htailUpdated, ih bits state htail htailLength]
          simp [upd]

private theorem indexedWireValues_eq_at
    (wires : List Wire) (left right : BasisState)
    (hvalues : wireValues wires left = wireValues wires right)
    {wire : Wire} (hwire : wire ∈ wires) :
    left wire = right wire := by
  induction wires with
  | nil => simp at hwire
  | cons head tail ih =>
      simp only [wireValues, List.map_cons, List.cons.injEq] at hvalues
      rcases List.mem_cons.mp hwire with rfl | hwire
      · exact hvalues.1
      · exact ih hvalues.2 hwire

private theorem indexedState_eq_writeWireValues
    (wires : List Wire) (bits : List Bool)
    (before after : BasisState)
    (hnd : wires.Nodup) (hlength : bits.length = wires.length)
    (hvalues : wireValues wires after = bits)
    (houtside : ∀ wire, wire ∉ wires → after wire = before wire) :
    after = indexedWriteWireValues wires bits before := by
  funext wire
  by_cases hwire : wire ∈ wires
  · apply indexedWireValues_eq_at wires
    calc
      wireValues wires after = bits := hvalues
      _ = wireValues wires (indexedWriteWireValues wires bits before) :=
        (indexedWireValues_writeWireValues wires bits before hnd hlength).symm
    exact hwire
  · rw [houtside wire hwire,
      indexedWriteWireValues_preservesOutside wires bits before hwire]

private theorem indexedIncrementBits_length (carry : Bool) (bits : List Bool) :
    (incrementBits carry bits).length = bits.length := by
  induction bits generalizing carry with
  | nil => rfl
  | cons bit bits ih => simp [incrementBits, ih]

private theorem indexedDecrementBits_length (borrow : Bool) (bits : List Bool) :
    (decrementBits borrow bits).length = bits.length := by
  induction bits generalizing borrow with
  | nil => rfl
  | cons bit bits ih => simp [decrementBits, ih]

private def indexedIncrementWordState
    (enabled : Bool) (register : List Wire) (state : BasisState) : BasisState :=
  indexedWriteWireValues register
    (incrementBits enabled (wireValues register state)) state

private def indexedDecrementWordState
    (enabled : Bool) (register : List Wire) (state : BasisState) : BasisState :=
  indexedWriteWireValues register
    (decrementBits enabled (wireValues register state)) state

private theorem run_controlledIncrement_indexedState
    (control : Wire) (register carries : List Wire) (state : BasisState)
    (hlength : register.length = carries.length + 1)
    (hnd : (control :: register ++ carries).Nodup)
    (hclean : Clean carries state) :
    run (controlledIncrement control register carries) state =
      indexedIncrementWordState (state control) register state := by
  have hcorrect := controlledIncrement_correct control register carries state
    hlength hnd hclean
  apply indexedState_eq_writeWireValues register _ state _
  · exact (List.nodup_append.mp (List.nodup_cons.mp hnd).2).1
  · rw [indexedIncrementBits_length]
    simp [wireValues]
  · exact hcorrect.1
  · exact hcorrect.2

private theorem run_controlledDecrement_indexedState
    (control : Wire) (register carries : List Wire) (state : BasisState)
    (hlength : register.length = carries.length + 1)
    (hnd : (control :: register ++ carries).Nodup)
    (hclean : Clean carries state) :
    run (controlledDecrement control register carries) state =
      indexedDecrementWordState (state control) register state := by
  have hcorrect := controlledDecrement_correct control register carries state
    hlength hnd hclean
  apply indexedState_eq_writeWireValues register _ state _
  · exact (List.nodup_append.mp (List.nodup_cons.mp hnd).2).1
  · rw [indexedDecrementBits_length]
    simp [wireValues]
  · exact hcorrect.1
  · exact hcorrect.2

private theorem indexedIncrementWordState_preservesOutside
    (enabled : Bool) (register : List Wire) (state : BasisState)
    {wire : Wire} (hwire : wire ∉ register) :
    indexedIncrementWordState enabled register state wire = state wire :=
  indexedWriteWireValues_preservesOutside register _ state hwire

private theorem indexedDecrementWordState_preservesOutside
    (enabled : Bool) (register : List Wire) (state : BasisState)
    {wire : Wire} (hwire : wire ∉ register) :
    indexedDecrementWordState enabled register state wire = state wire :=
  indexedWriteWireValues_preservesOutside register _ state hwire

private theorem indexedRouteLabel_congr
    (tree : UnaryActionTree) (left right : BasisState)
    (hagrees : ∀ wire ∈ tree.indexWires, left wire = right wire) :
    tree.routeLabel left = tree.routeLabel right := by
  induction tree with
  | leaf => rfl
  | node indexBit zero one ihZero ihOne =>
      simp only [UnaryActionTree.routeLabel]
      rw [hagrees indexBit (by simp [UnaryActionTree.indexWires])]
      split
      · apply ihOne
        intro wire hwire
        exact hagrees wire (by simp [UnaryActionTree.indexWires, hwire])
      · apply ihZero
        intro wire hwire
        exact hagrees wire (by simp [UnaryActionTree.indexWires, hwire])

private theorem run_computeControl_state
    (controls : List Wire) (value : Nat) (target : Wire)
    (scratch : List Wire) (state : BasisState)
    (hlayout : ComputeControlLayout controls target scratch)
    (hclean : Clean scratch state) :
    run (computeControl controls value target scratch) state =
        matchXorState controls value target state ∧
      Clean scratch (matchXorState controls value target state) := by
  have hrun := run_computeControl controls value target scratch state hlayout hclean
  have htarget : target ∉ scratch := by
    obtain ⟨_, htail, _⟩ := List.nodup_append.mp hlayout.2
    exact (List.nodup_cons.mp htail).1
  constructor
  · simpa [matchXorState] using hrun
  · intro wire hwire
    simp [matchXorState, upd,
      show wire ≠ target by intro equality; subst wire; exact htarget hwire,
      hclean wire hwire]

private theorem clean_after_local_circuit
    {large localScratch support : List Wire} {circuit : Circuit}
    {state : BasisState}
    (hlarge : Clean large state)
    (hlocal : Clean localScratch (run circuit state))
    (huses : PaperCircuitUsesOnly support circuit)
    (hintersection : ∀ wire ∈ large, wire ∈ support → wire ∈ localScratch) :
    Clean large (run circuit state) := by
  intro wire hwire
  by_cases hsupport : wire ∈ support
  · exact hlocal wire (hintersection wire hwire hsupport)
  · rw [huses.preservesOutside state hsupport]
    exact hlarge wire hwire

private theorem nodup_middle_ne
    {before middle after : List α} {middleWire outsideWire : α}
    (hnodup : (before ++ (middle ++ after)).Nodup)
    (hmiddle : middleWire ∈ middle)
    (houtside : outsideWire ∈ before ∨ outsideWire ∈ after) :
    middleWire ≠ outsideWire := by
  obtain ⟨_, htail, hcrossBefore⟩ := List.nodup_append.mp hnodup
  obtain ⟨_, _, hsuffix⟩ := List.nodup_append.mp htail
  rcases houtside with hbefore | hafter
  · intro equality
    exact hcrossBefore outsideWire hbefore middleWire
      (List.mem_append_left after hmiddle) equality.symm
  · intro equality
    exact hsuffix middleWire hmiddle outsideWire hafter equality

private theorem registerMatchesFrom_congr
    (register : List Wire) (value bit : Nat) (left right : BasisState)
    (hagrees : ∀ wire ∈ register, left wire = right wire) :
    registerMatchesFrom register value bit left =
      registerMatchesFrom register value bit right := by
  induction register generalizing bit with
  | nil => rfl
  | cons wire wires ih =>
      simp only [registerMatchesFrom]
      rw [hagrees wire (by simp), ih (bit := bit + 1)]
      intro next hnext
      exact hagrees next (by simp [hnext])

private theorem registerMatches_congr
    (register : List Wire) (value : Nat) (left right : BasisState)
    (hagrees : ∀ wire ∈ register, left wire = right wire) :
    registerMatches register value left = registerMatches register value right := by
  exact registerMatchesFrom_congr register value 0 left right hagrees

private theorem matchXorState_clears
    (controls : List Wire) (value : Nat) (target : Wire)
    (initial middle : BasisState)
    (htarget : middle target = registerMatches controls value initial)
    (hcontrols : ∀ wire ∈ controls, middle wire = initial wire) :
    matchXorState controls value target middle target = false := by
  have hpredicate := registerMatches_congr controls value middle initial hcontrols
  simp [matchXorState, htarget, hpredicate]

private theorem wireAnd_congr
    (register : List Wire) (left right : BasisState)
    (hagrees : ∀ wire ∈ register, left wire = right wire) :
    wireAnd register left = wireAnd register right := by
  induction register with
  | nil => rfl
  | cons wire rest ih =>
      simp only [wireAnd]
      rw [hagrees wire (by simp), ih]
      intro next hnext
      exact hagrees next (by simp [hnext])

private theorem rControlNonterminalPredicate_congr
    (conditions : List Wire) (value : Nat) (lengthRPrime : List Wire)
    (zeroRPrime : Wire) (left right : BasisState)
    (hzeroNotConditions : zeroRPrime ∉ conditions)
    (hconditions : ∀ wire ∈ conditions, left wire = right wire)
    (hlength : ∀ wire ∈ lengthRPrime, left wire = right wire) :
    rControlNonterminalPredicate conditions value lengthRPrime zeroRPrime left =
      rControlNonterminalPredicate conditions value lengthRPrime zeroRPrime right := by
  rw [rControlNonterminalPredicate_eq conditions value lengthRPrime zeroRPrime left
      hzeroNotConditions,
    rControlNonterminalPredicate_eq conditions value lengthRPrime zeroRPrime right
      hzeroNotConditions,
    registerMatches_congr conditions (value % 2 ^ conditions.length) left right hconditions,
    wireAnd_congr lengthRPrime left right hlength]

private theorem rControlState_preserves
    (conditions : List Wire) (value : Nat) (control : Wire)
    (lengthRPrime : List Wire) (zeroRPrime : Wire) (state : BasisState)
    {wire : Wire} (hwire : wire ≠ control) :
    rControlState conditions value control lengthRPrime zeroRPrime state wire =
      state wire := by
  simp [rControlState, upd, hwire]

private theorem windowSlice_mem
    (work : List Wire) (window : ActiveWindow) {wire : Wire}
    (hwire : wire ∈ IndexedStepRegisters.windowSlice work window) :
    wire ∈ work :=
  List.mem_of_mem_drop (List.mem_of_mem_take hwire)

private def indexedStepPayload
    (registers : IndexedStepRegisters) : List Wire :=
  [registers.phase1, registers.phase2, registers.iter, registers.sign] ++
    registers.work1 ++ registers.work2 ++ registers.lengthT ++
      registers.lengthQ ++ registers.lengthS ++ registers.lengthRPrime

private def indexedStepAfterPhase1
    (registers : IndexedStepRegisters) : List Wire :=
  [registers.phase2, registers.iter, registers.sign] ++
    registers.work1 ++ registers.work2 ++ registers.lengthT ++
      registers.lengthQ ++ registers.lengthS ++ registers.lengthRPrime ++
        registers.aux

private def indexedStepAfterPhase2
    (registers : IndexedStepRegisters) : List Wire :=
  [registers.iter, registers.sign] ++ registers.work1 ++ registers.work2 ++
    registers.lengthT ++ registers.lengthQ ++ registers.lengthS ++
      registers.lengthRPrime ++ registers.aux

private def indexedStepAfterSign
    (registers : IndexedStepRegisters) : List Wire :=
  registers.work1 ++ registers.work2 ++ registers.lengthT ++
    registers.lengthQ ++ registers.lengthS ++ registers.lengthRPrime ++
      registers.aux

private def indexedStepBeforeLengthQ
    (registers : IndexedStepRegisters) : List Wire :=
  [registers.phase1, registers.phase2, registers.iter, registers.sign] ++
    registers.work1 ++ registers.work2 ++ registers.lengthT

private def indexedStepAfterLengthQ
    (registers : IndexedStepRegisters) : List Wire :=
  registers.lengthS ++ registers.lengthRPrime ++ registers.aux

private def indexedStepBeforeLengthRPrime
    (registers : IndexedStepRegisters) : List Wire :=
  [registers.phase1, registers.phase2, registers.iter, registers.sign] ++
    registers.work1 ++ registers.work2 ++ registers.lengthT ++
      registers.lengthQ ++ registers.lengthS

private theorem IndexedStepLayout.phase1_ne_after
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ indexedStepAfterPhase1 registers) :
    registers.phase1 ≠ wire := by
  have hphysical :
      (registers.phase1 :: indexedStepAfterPhase1 registers).Nodup := by
    simpa [indexedStepAfterPhase1, IndexedStepRegisters.allWires,
      List.append_assoc] using hlayout.physical
  intro equality
  subst wire
  exact (List.nodup_cons.mp hphysical).1 hwire

private theorem IndexedStepLayout.phase2_ne_after
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ indexedStepAfterPhase2 registers) :
    registers.phase2 ≠ wire := by
  have hphysical :
      (registers.phase1 :: registers.phase2 ::
        indexedStepAfterPhase2 registers).Nodup := by
    simpa [indexedStepAfterPhase2, IndexedStepRegisters.allWires,
      List.append_assoc] using hlayout.physical
  intro equality
  subst wire
  exact (List.nodup_cons.mp (List.nodup_cons.mp hphysical).2).1 hwire

private theorem IndexedStepLayout.sign_ne_after
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ indexedStepAfterSign registers) :
    registers.sign ≠ wire := by
  have hphysical :
      (registers.phase1 :: registers.phase2 :: registers.iter ::
        registers.sign :: indexedStepAfterSign registers).Nodup := by
    simpa [indexedStepAfterSign, IndexedStepRegisters.allWires,
      List.append_assoc] using hlayout.physical
  intro equality
  subst wire
  exact (List.nodup_cons.mp
    (List.nodup_cons.mp
      (List.nodup_cons.mp
        (List.nodup_cons.mp hphysical).2).2).2).1 hwire

private theorem IndexedStepLayout.lengthQ_ne_outside
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {lengthWire outsideWire : Wire}
    (hlength : lengthWire ∈ registers.lengthQ)
    (houtside : outsideWire ∈ indexedStepBeforeLengthQ registers ∨
      outsideWire ∈ indexedStepAfterLengthQ registers) :
    lengthWire ≠ outsideWire := by
  apply nodup_middle_ne
    (before := indexedStepBeforeLengthQ registers)
    (middle := registers.lengthQ)
    (after := indexedStepAfterLengthQ registers) ?_ hlength houtside
  simpa [indexedStepBeforeLengthQ, indexedStepAfterLengthQ,
    IndexedStepRegisters.allWires, List.append_assoc] using hlayout.physical

private theorem IndexedStepLayout.lengthRPrime_ne_outside
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {lengthWire outsideWire : Wire}
    (hlength : lengthWire ∈ registers.lengthRPrime)
    (houtside : outsideWire ∈ indexedStepBeforeLengthRPrime registers ∨
      outsideWire ∈ registers.aux) :
    lengthWire ≠ outsideWire := by
  apply nodup_middle_ne
    (before := indexedStepBeforeLengthRPrime registers)
    (middle := registers.lengthRPrime)
    (after := registers.aux) ?_ hlength houtside
  simpa [indexedStepBeforeLengthRPrime, IndexedStepRegisters.allWires,
    List.append_assoc] using hlayout.physical

private theorem IndexedStepLayout.aux_not_payload
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {auxWire payloadWire : Wire}
    (haux : auxWire ∈ registers.aux)
    (hpayload : payloadWire ∈ indexedStepPayload registers) :
    auxWire ≠ payloadWire := by
  have hphysical :
      (indexedStepPayload registers ++ registers.aux).Nodup := by
    simpa [indexedStepPayload, IndexedStepRegisters.allWires,
      List.append_assoc] using hlayout.physical
  have hcross := (List.nodup_append.mp hphysical).2.2
  intro equality
  exact hcross payloadWire hpayload auxWire haux equality.symm

private theorem IndexedStepLayout.aux_nodup
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) : registers.aux.Nodup := by
  have hphysical :
      (indexedStepPayload registers ++ registers.aux).Nodup := by
    simpa [indexedStepPayload, IndexedStepRegisters.allWires,
      List.append_assoc] using hlayout.physical
  exact (List.nodup_append.mp hphysical).2.1

private theorem indexedStep_getD_mem
    (list : List α) (index : Nat) (fallback : α)
    (hindex : index < list.length) :
    list.getD index fallback ∈ list := by
  rw [List.getD_eq_getElem list fallback hindex]
  exact List.getElem_mem hindex

private theorem IndexedStepLayout.control_mem_aux
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.control ∈ registers.aux := by
  exact indexedStep_getD_mem registers.aux 0 0 (by
    rw [hlayout.aux_length]
    omega)

private theorem IndexedStepLayout.shiftEpoch_mem_aux
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.shiftEpoch ∈ registers.aux := by
  exact indexedStep_getD_mem registers.aux 1 0 (by
    rw [hlayout.aux_length]
    omega)

private theorem IndexedStepLayout.sourceScratch_mem_aux
    {registers : IndexedStepRegisters} {n T : Nat}
    (_hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ registers.sourceScratch) :
    wire ∈ registers.aux := by
  exact List.mem_of_mem_drop hwire

private theorem IndexedStepLayout.sharedScratch_mem_aux
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ registers.sharedScratch) :
    wire ∈ registers.aux := by
  simp only [IndexedStepRegisters.sharedScratch, List.mem_cons] at hwire
  rcases hwire with rfl | hsource
  · exact hlayout.control_mem_aux
  · exact hlayout.sourceScratch_mem_aux hsource

private theorem IndexedStepLayout.blockScratch_mem_aux
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ registers.blockScratch) :
    wire ∈ registers.aux := by
  exact hlayout.sourceScratch_mem_aux (List.mem_of_mem_drop hwire)

private theorem IndexedStepLayout.aux_view
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    [registers.control, registers.shiftEpoch] ++ registers.sourceScratch =
      registers.aux := by
  cases haux : registers.aux with
  | nil =>
      have hlength := hlayout.aux_length
      simp [haux] at hlength
  | cons first tail =>
      cases htail : tail with
      | nil =>
          have hlength := hlayout.aux_length
          simp [haux, htail] at hlength
      | cons second rest =>
          simp [IndexedStepRegisters.control, IndexedStepRegisters.shiftEpoch,
            IndexedStepRegisters.sourceScratch, haux, htail]

private theorem IndexedStepLayout.scratch_view
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.terminal :: registers.blockScratch =
      registers.sourceScratch := by
  cases hscratch : registers.sourceScratch with
  | nil =>
      have hview := congrArg List.length hlayout.aux_view
      simp [hscratch, hlayout.aux_length] at hview
  | cons terminal rest =>
      simp [IndexedStepRegisters.terminal, IndexedStepRegisters.blockScratch,
        hscratch]

private theorem IndexedStepLayout.sourceScratch_length
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.sourceScratch.length = 18 := by
  have hview := congrArg List.length hlayout.aux_view
  simp [hlayout.aux_length] at hview
  omega

private theorem IndexedStepLayout.aux_view_nodup
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ([registers.control, registers.shiftEpoch] ++
      registers.sourceScratch).Nodup := by
  rw [hlayout.aux_view]
  exact hlayout.aux_nodup

private theorem IndexedStepLayout.control_not_sourceScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.control ∉ registers.sourceScratch := by
  have hcross := (List.nodup_append.mp hlayout.aux_view_nodup).2.2
  intro hmem
  exact hcross registers.control (by simp) registers.control hmem rfl

private theorem IndexedStepLayout.shiftEpoch_not_sourceScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.shiftEpoch ∉ registers.sourceScratch := by
  have hcross := (List.nodup_append.mp hlayout.aux_view_nodup).2.2
  intro hmem
  exact hcross registers.shiftEpoch (by simp) registers.shiftEpoch hmem rfl

private theorem IndexedStepLayout.sourceScratch_nodup
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.sourceScratch.Nodup :=
  (List.nodup_append.mp hlayout.aux_view_nodup).2.1

private theorem IndexedStepLayout.sourceScratch_view2
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.sourceScratch.getD 0 0 ::
      registers.sourceScratch.getD 1 0 :: registers.sourceScratch.drop 2 =
        registers.sourceScratch := by
  cases hsource : registers.sourceScratch with
  | nil =>
      have hlength := hlayout.sourceScratch_length
      simp [hsource] at hlength
  | cons first tail =>
      cases htail : tail with
      | nil =>
          have hlength := hlayout.sourceScratch_length
          simp [hsource, htail] at hlength
      | cons second rest =>
          rfl

private theorem IndexedStepLayout.terminal_not_blockScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.terminal ∉ registers.blockScratch := by
  have hnodup : (registers.terminal :: registers.blockScratch).Nodup := by
    rw [hlayout.scratch_view]
    exact hlayout.sourceScratch_nodup
  exact (List.nodup_cons.mp hnodup).1

private theorem IndexedStepLayout.remainder_scratch_sub_aux
    {registers : IndexedStepRegisters} {n T : Nat}
    (_hlayout : IndexedStepLayout registers n T) (window : ActiveWindow) :
    ∀ wire ∈ (registers.remainder window).scratch, wire ∈ registers.aux := by
  intro wire hwire
  exact List.mem_of_mem_drop (List.mem_of_mem_take hwire)

private theorem IndexedStepLayout.control_not_remainder_scratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow)
    (hwindow : window = (certifiedActiveWindows n T).remainder) :
    registers.control ∉ (registers.remainder window).scratch := by
  subst window
  change (registers.remainder (certifiedActiveWindows n T).remainder).control ∉
    (registers.remainder (certifiedActiveWindows n T).remainder).scratch
  have hphysical := hlayout.remainder.physical
  rw [IntervalRegisters.allWires] at hphysical
  have hcross := (List.nodup_append.mp hphysical).2.2
  intro hscratch
  exact hcross
    (registers.remainder (certifiedActiveWindows n T).remainder).control (by simp)
    (registers.remainder (certifiedActiveWindows n T).remainder).control (by
      simp only [List.mem_append]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hscratch))))) rfl

private theorem IndexedStepLayout.aux_outside_remainder
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow)
    {wire : Wire} (haux : wire ∈ registers.aux)
    (hcontrol : wire ≠ registers.control)
    (hscratch : wire ∉ (registers.remainder window).scratch) :
    wire ∉ (registers.remainder window).allWires := by
  intro hused
  simp only [IntervalRegisters.allWires, IndexedStepRegisters.remainder,
    IndexedStepRegisters.remainderBase, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hused
  rcases hused with hcontrols | hwork1 | hwork2 | hlengthT |
      hlengthQ | hlengthS | hscratchUsed
  · rcases hcontrols with hcontrolUsed | hsign
    · exact hcontrol hcontrolUsed
    · exact (hlayout.aux_not_payload haux (by
        simp [indexedStepPayload, hsign])) rfl
  · exact (hlayout.aux_not_payload haux (by
      simp [indexedStepPayload, windowSlice_mem registers.work1 window hwork1])) rfl
  · exact (hlayout.aux_not_payload haux (by
      simp [indexedStepPayload, windowSlice_mem registers.work2 window hwork2])) rfl
  · exact (hlayout.aux_not_payload haux (by
      simp [indexedStepPayload, hlengthT])) rfl
  · exact (hlayout.aux_not_payload haux (by
      simp [indexedStepPayload, hlengthQ])) rfl
  · exact (hlayout.aux_not_payload haux (by
      simp [indexedStepPayload, hlengthS])) rfl
  · exact hscratch hscratchUsed

private theorem IndexedStepLayout.remainder_mem_after_phase1
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow)
    {wire : Wire} (hwire : wire ∈ (registers.remainder window).allWires) :
    wire ∈ indexedStepAfterPhase1 registers := by
  simp only [IntervalRegisters.allWires, IndexedStepRegisters.remainder,
    IndexedStepRegisters.remainderBase, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hwire
  rcases hwire with hcontrols | hwork1 | hwork2 | hlengthT |
      hlengthQ | hlengthS | hscratch
  · rcases hcontrols with rfl | rfl
    · simp [indexedStepAfterPhase1, hlayout.control_mem_aux]
    · simp [indexedStepAfterPhase1]
  · simp [indexedStepAfterPhase1, windowSlice_mem registers.work1 window hwork1]
  · simp [indexedStepAfterPhase1, windowSlice_mem registers.work2 window hwork2]
  · simp [indexedStepAfterPhase1, hlengthT]
  · simp [indexedStepAfterPhase1, hlengthQ]
  · simp [indexedStepAfterPhase1, hlengthS]
  · simp [indexedStepAfterPhase1,
      hlayout.remainder_scratch_sub_aux window wire hscratch]

private theorem IndexedStepLayout.remainder_mem_after_phase2
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow)
    {wire : Wire} (hwire : wire ∈ (registers.remainder window).allWires) :
    wire ∈ indexedStepAfterPhase2 registers := by
  simp only [IntervalRegisters.allWires, IndexedStepRegisters.remainder,
    IndexedStepRegisters.remainderBase, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hwire
  rcases hwire with hcontrols | hwork1 | hwork2 | hlengthT |
      hlengthQ | hlengthS | hscratch
  · rcases hcontrols with rfl | rfl
    · simp [indexedStepAfterPhase2, hlayout.control_mem_aux]
    · simp [indexedStepAfterPhase2]
  · simp [indexedStepAfterPhase2, windowSlice_mem registers.work1 window hwork1]
  · simp [indexedStepAfterPhase2, windowSlice_mem registers.work2 window hwork2]
  · simp [indexedStepAfterPhase2, hlengthT]
  · simp [indexedStepAfterPhase2, hlengthQ]
  · simp [indexedStepAfterPhase2, hlengthS]
  · simp [indexedStepAfterPhase2,
      hlayout.remainder_scratch_sub_aux window wire hscratch]

private theorem IndexedStepLayout.phase1_not_remainder
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow) :
    registers.phase1 ∉ (registers.remainder window).allWires := by
  intro hused
  exact (hlayout.phase1_ne_after
    (hlayout.remainder_mem_after_phase1 window hused)) rfl

private theorem IndexedStepLayout.phase2_not_remainder
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow) :
    registers.phase2 ∉ (registers.remainder window).allWires := by
  intro hused
  exact (hlayout.phase2_ne_after
    (hlayout.remainder_mem_after_phase2 window hused)) rfl

private theorem IndexedStepLayout.lengthRPrime_not_remainder
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow)
    {wire : Wire} (hwire : wire ∈ registers.lengthRPrime) :
    wire ∉ (registers.remainder window).allWires := by
  intro hused
  simp only [IntervalRegisters.allWires, IndexedStepRegisters.remainder,
    IndexedStepRegisters.remainderBase, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hused
  rcases hused with hcontrols | hwork1 | hwork2 | hlengthT |
      hlengthQ | hlengthS | hscratch
  · rcases hcontrols with hcontrol | hsign
    · exact (hlayout.lengthRPrime_ne_outside hwire (Or.inr
        (hcontrol ▸ hlayout.control_mem_aux))) rfl
    · exact (hlayout.lengthRPrime_ne_outside hwire (Or.inl (by
        simp [indexedStepBeforeLengthRPrime, hsign]))) rfl
  · exact (hlayout.lengthRPrime_ne_outside hwire (Or.inl (by
      simp [indexedStepBeforeLengthRPrime,
        windowSlice_mem registers.work1 window hwork1]))) rfl
  · exact (hlayout.lengthRPrime_ne_outside hwire (Or.inl (by
      simp [indexedStepBeforeLengthRPrime,
        windowSlice_mem registers.work2 window hwork2]))) rfl
  · exact (hlayout.lengthRPrime_ne_outside hwire (Or.inl (by
      simp [indexedStepBeforeLengthRPrime, hlengthT]))) rfl
  · exact (hlayout.lengthRPrime_ne_outside hwire (Or.inl (by
      simp [indexedStepBeforeLengthRPrime, hlengthQ]))) rfl
  · exact (hlayout.lengthRPrime_ne_outside hwire (Or.inl (by
      simp [indexedStepBeforeLengthRPrime, hlengthS]))) rfl
  · exact (hlayout.lengthRPrime_ne_outside hwire (Or.inr
      (hlayout.remainder_scratch_sub_aux window wire hscratch))) rfl

private theorem remainderInterval_clean_auxAwayControl
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (mode : RippleMode) (signUpdate : Bool) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder)
    (hclean : ∀ wire ∈ registers.aux, wire ≠ registers.control →
      state wire = false) :
    ∀ wire ∈ registers.aux, wire ≠ registers.control →
      run (intervalAddSubUnitary (registers.remainder window) n
        window.start window.stop mode signUpdate .work1) state wire = false := by
  subst window
  let window := (certifiedActiveWindows n T).remainder
  have hready : IntervalReady (registers.remainder window) state := by
    intro wire hwire
    apply hclean wire (hlayout.remainder_scratch_sub_aux window wire hwire)
    intro equality
    subst wire
    exact hlayout.control_not_remainder_scratch window rfl hwire
  have houtputReady := intervalAddSubUnitary_ready (registers.remainder window) n
    window.start window.stop mode signUpdate .work1 state hlayout.remainder hready
  intro wire haux hcontrol
  by_cases hscratch : wire ∈ (registers.remainder window).scratch
  · exact houtputReady wire hscratch
  · rw [intervalAddSubUnitary_preservesOutside (registers.remainder window) n
      window.start window.stop mode signUpdate .work1 state hlayout.remainder
      (hlayout.aux_outside_remainder window haux hcontrol hscratch)]
    exact hclean wire haux hcontrol

private theorem IndexedStepLayout.terminalPadding_scratch_sub_block
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ∀ wire ∈ registers.terminalPadding.scratch,
      wire ∈ registers.blockScratch := by
  intro wire hwire
  change wire ∈
    registers.blockScratch.getD 0 0 ::
      ((registers.blockScratch.drop 1).take
          (registers.lengthS.length - 2) ++
        [registers.blockScratch.getD (registers.lengthS.length - 1) 0]) at hwire
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hwire
  rcases hwire with hwrapped | htail | hextra
  · rw [hwrapped]
    exact indexedStep_getD_mem registers.blockScratch 0 0 (by
      have := hlayout.terminalPaddingCapacity
      omega)
  · exact List.mem_of_mem_drop (List.mem_of_mem_take htail)
  · rw [hextra]
    exact indexedStep_getD_mem registers.blockScratch
      (registers.lengthS.length - 1) 0 (by
        have := hlayout.terminalPaddingCapacity
        omega)

private theorem IndexedStepLayout.terminalPadding_support_intersection
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ∀ wire ∈ registers.blockScratch,
      wire ∈ registers.terminalPadding.usedWires →
        wire ∈ registers.terminalPadding.scratch := by
  intro wire hblock hsupport
  rw [TerminalPaddingRegisters.usedWires] at hsupport
  rcases List.mem_append.mp hsupport with hprefix | hscratch
  · rcases List.mem_append.mp hprefix with hhead | hlength
    · rcases List.mem_cons.mp hhead with hterminal | hhead
      · subst wire
        exact (hlayout.terminal_not_blockScratch hblock).elim
      · rcases List.mem_cons.mp hhead with hepoch | hwork
        · subst wire
          exact (hlayout.shiftEpoch_not_sourceScratch
            (List.mem_of_mem_drop hblock)).elim
        · change wire ∈ registers.work2 at hwork
          exact (hlayout.aux_not_payload (auxWire := wire) (payloadWire := wire)
            (hlayout.blockScratch_mem_aux hblock)
            (by simp [indexedStepPayload, hwork]) rfl).elim
    · change wire ∈ registers.lengthS at hlength
      exact (hlayout.aux_not_payload (auxWire := wire) (payloadWire := wire)
        (hlayout.blockScratch_mem_aux hblock)
        (by simp [indexedStepPayload, hlength]) rfl).elim
  · exact hscratch

private theorem IndexedStepLayout.preShift_scratch_sub_block
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ∀ wire ∈ registers.preShift.scratch,
      wire ∈ registers.blockScratch := by
  have hreserved :
      ((registers.blockScratch.drop (registers.lengthS.length + 1)).take 3).length = 3 := by
    simpa [IndexedStepRegisters.preShift] using hlayout.preShift.reserved_size
  have hblockLength : registers.lengthS.length + 4 ≤ registers.blockScratch.length := by
    simp only [List.length_take, List.length_drop] at hreserved
    omega
  intro wire hwire
  change wire ∈
    [registers.blockScratch.getD 0 0, registers.blockScratch.getD 1 0] ++
      (registers.blockScratch.drop 2).take (registers.lengthS.length - 1) ++
        (registers.blockScratch.drop (registers.lengthS.length + 1)).take 3 at hwire
  rcases List.mem_append.mp hwire with hprefix | hreservedWire
  · rcases List.mem_append.mp hprefix with hflag | hcarry
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hflag
      rcases hflag with hzero | hboth
      · rw [hzero]
        exact indexedStep_getD_mem registers.blockScratch 0 0 (by omega)
      · rw [hboth]
        exact indexedStep_getD_mem registers.blockScratch 1 0 (by omega)
    · exact List.mem_of_mem_drop (List.mem_of_mem_take hcarry)
  · exact List.mem_of_mem_drop (List.mem_of_mem_take hreservedWire)

private theorem IndexedStepLayout.preShift_support_intersection
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ∀ wire ∈ registers.blockScratch,
      wire ∈ registers.preShift.preUsedWires →
        wire ∈ registers.preShift.scratch := by
  intro wire hblock hsupport
  by_cases hscratch : wire ∈ registers.preShift.scratch
  · exact hscratch
  · have hpayload : wire ∈ indexedStepPayload registers := by
      change wire ∈
        [registers.phase1, registers.blockScratch.getD 0 0,
          registers.phase2, registers.blockScratch.getD 1 0] ++
          registers.work2 ++ registers.lengthS ++
            (registers.blockScratch.drop 2).take
              (registers.lengthS.length - 1) at hsupport
      change wire ∉
        [registers.blockScratch.getD 0 0, registers.blockScratch.getD 1 0] ++
          (registers.blockScratch.drop 2).take (registers.lengthS.length - 1) ++
            (registers.blockScratch.drop (registers.lengthS.length + 1)).take 3
          at hscratch
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hsupport hscratch
      simp only [indexedStepPayload, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false]
      aesop
    exact (hlayout.aux_not_payload (auxWire := wire) (payloadWire := wire)
      (hlayout.blockScratch_mem_aux hblock) hpayload rfl).elim

private theorem IndexedStepLayout.postShift_scratch_sub_source
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ∀ wire ∈ registers.postShift.scratch,
      wire ∈ registers.sourceScratch := by
  have hreserved :
      ((registers.sourceScratch.drop (registers.lengthS.length + 1)).take 3).length =
        3 := by
    simpa [IndexedStepRegisters.postShift] using hlayout.postShift.reserved_size
  have hsourceLength :
      registers.lengthS.length + 4 ≤ registers.sourceScratch.length := by
    simp only [List.length_take, List.length_drop] at hreserved
    omega
  intro wire hwire
  change wire ∈
    [registers.sourceScratch.getD 0 0, registers.sourceScratch.getD 1 0] ++
      (registers.sourceScratch.drop 2).take (registers.lengthS.length - 1) ++
        (registers.sourceScratch.drop (registers.lengthS.length + 1)).take 3 at hwire
  rcases List.mem_append.mp hwire with hprefix | hreservedWire
  · rcases List.mem_append.mp hprefix with hflag | hcarry
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hflag
      rcases hflag with hzero | hboth
      · rw [hzero]
        exact indexedStep_getD_mem registers.sourceScratch 0 0 (by omega)
      · rw [hboth]
        exact indexedStep_getD_mem registers.sourceScratch 1 0 (by omega)
    · exact List.mem_of_mem_drop (List.mem_of_mem_take hcarry)
  · exact List.mem_of_mem_drop (List.mem_of_mem_take hreservedWire)

private theorem IndexedStepLayout.postShift_support_intersection
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ∀ wire ∈ registers.sharedScratch,
      wire ∈ registers.postShift.postUsedWires →
        wire ∈ registers.postShift.scratch := by
  intro wire hshared hsupport
  by_cases hscratch : wire ∈ registers.postShift.scratch
  · exact hscratch
  · have haux : wire ∈ registers.aux := by
      simp only [IndexedStepRegisters.sharedScratch, List.mem_cons] at hshared
      rcases hshared with rfl | hsource
      · exact hlayout.control_mem_aux
      · exact hlayout.sourceScratch_mem_aux hsource
    have hpayload : wire ∈ indexedStepPayload registers := by
      change wire ∈
        [registers.phase1, registers.phase2,
          registers.sourceScratch.getD 1 0] ++
          registers.work2 ++ registers.lengthS ++
            (registers.sourceScratch.drop 2).take
              (registers.lengthS.length - 1) at hsupport
      change wire ∉
        [registers.sourceScratch.getD 0 0,
          registers.sourceScratch.getD 1 0] ++
          (registers.sourceScratch.drop 2).take
              (registers.lengthS.length - 1) ++
            (registers.sourceScratch.drop
              (registers.lengthS.length + 1)).take 3 at hscratch
      simp only [indexedStepPayload, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, not_or] at hsupport hscratch ⊢
      aesop
    exact (hlayout.aux_not_payload (auxWire := wire) (payloadWire := wire)
      haux hpayload rfl).elim

private theorem IndexedStepLayout.phaseUpdate_scratch_sub_source
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ∀ wire ∈ registers.phaseUpdate.scratch,
      wire ∈ registers.sourceScratch := by
  intro wire hwire
  change wire ∈
    [registers.sourceScratch.getD 0 0, registers.sourceScratch.getD 1 0,
      registers.sourceScratch.getD 2 0, registers.sourceScratch.getD 3 0,
      registers.sourceScratch.getD 4 0] ++
        (registers.sourceScratch.drop 5).take
          registers.phaseEqualityScratchSize at hwire
  rcases List.mem_append.mp hwire with hhead | htail
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hhead
    rcases hhead with hzeroQ | hzeroRPrime | hzeroS | hcondition | htemporary
    · rw [hzeroQ]
      exact indexedStep_getD_mem registers.sourceScratch 0 0 (by
        rw [hlayout.sourceScratch_length]
        omega)
    · rw [hzeroRPrime]
      exact indexedStep_getD_mem registers.sourceScratch 1 0 (by
        rw [hlayout.sourceScratch_length]
        omega)
    · rw [hzeroS]
      exact indexedStep_getD_mem registers.sourceScratch 2 0 (by
        rw [hlayout.sourceScratch_length]
        omega)
    · rw [hcondition]
      exact indexedStep_getD_mem registers.sourceScratch 3 0 (by
        rw [hlayout.sourceScratch_length]
        omega)
    · rw [htemporary]
      exact indexedStep_getD_mem registers.sourceScratch 4 0 (by
        rw [hlayout.sourceScratch_length]
        omega)
  · exact List.mem_of_mem_drop (List.mem_of_mem_take htail)

private theorem IndexedStepLayout.phaseUpdate_support_intersection
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ∀ wire ∈ registers.sharedScratch,
      wire ∈ registers.phaseUpdate.epochWires registers.shiftEpoch →
        wire ∈ registers.phaseUpdate.scratch := by
  intro wire hshared hsupport
  by_cases hscratch : wire ∈ registers.phaseUpdate.scratch
  · exact hscratch
  · have haux : wire ∈ registers.aux := by
      simp only [IndexedStepRegisters.sharedScratch, List.mem_cons] at hshared
      rcases hshared with rfl | hsource
      · exact hlayout.control_mem_aux
      · exact hlayout.sourceScratch_mem_aux hsource
    have hpayloadOrEpoch :
        wire ∈ indexedStepPayload registers ∨ wire = registers.shiftEpoch := by
      change wire ∈
        [registers.phase1, registers.phase2, registers.sign] ++
          registers.lengthQ ++ registers.lengthRPrime ++
            (registers.lengthS ++ [registers.shiftEpoch]) ++
              registers.phaseUpdate.scratch at hsupport
      simp only [indexedStepPayload, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hsupport hscratch ⊢
      aesop
    rcases hpayloadOrEpoch with hpayload | hepoch
    · exact (hlayout.aux_not_payload (auxWire := wire) (payloadWire := wire)
        haux hpayload rfl).elim
    · subst wire
      simp only [IndexedStepRegisters.sharedScratch, List.mem_cons] at hshared
      rcases hshared with hcontrol | hsource
      · have hnodup :
            (registers.control :: registers.shiftEpoch ::
              registers.sourceScratch).Nodup := by
            simpa only [List.cons_append, List.nil_append] using
              hlayout.aux_view_nodup
        have hne : registers.control ≠ registers.shiftEpoch := by
          intro equality
          exact (List.nodup_cons.mp hnodup).1 (by simp [equality])
        exact (hne hcontrol.symm).elim
      · exact (hlayout.shiftEpoch_not_sourceScratch hsource).elim

private theorem IndexedStepLayout.tBoundary_usedScratch_sub_block
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ∀ wire ∈ registers.tBoundary.usedScratch,
      wire ∈ registers.blockScratch := by
  intro wire hwire
  change wire ∈
    registers.blockScratch.take registers.lengthT.length ++
      [registers.blockScratch.getD registers.lengthT.length 0] at hwire
  rcases List.mem_append.mp hwire with hconstants | hcarry
  · exact List.mem_of_mem_take hconstants
  · simp only [List.mem_singleton] at hcarry
    rw [hcarry]
    exact indexedStep_getD_mem registers.blockScratch registers.lengthT.length 0
      (by simpa [IndexedStepRegisters.tBoundary, TBoundaryRegisters.width] using
        hlayout.tBoundary.scratch_capacity)

private theorem IndexedStepLayout.tBoundary_words_nodup
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    (registers.lengthT ++ registers.lengthRPrime).Nodup := by
  have hswap :
      (registers.phase2 :: registers.lengthT ++ registers.lengthRPrime).Nodup := by
    apply List.Nodup.sublist ?_ hlayout.tBoundary.physical
    unfold TBoundaryRegisters.allWires
    simpa only [IndexedStepRegisters.tBoundary, List.nil_append,
      List.cons_append, List.append_assoc] using
      List.Sublist.cons₂ registers.phase2
        (List.Sublist.cons registers.tBoundary.carry
          (List.sublist_append_right
            (registers.tBoundary.constants ++ registers.tBoundary.lengthSLow)
            (registers.lengthT ++ registers.lengthRPrime)))
  exact (List.nodup_cons.mp hswap).2

private theorem IndexedStepLayout.coefficient_scratch_sub_block
    {registers : IndexedStepRegisters} {n T : Nat}
    (_hlayout : IndexedStepLayout registers n T) (window : ActiveWindow) :
    ∀ wire ∈ (registers.coefficient window).scratch,
      wire ∈ registers.blockScratch := by
  intro wire hwire
  exact List.mem_of_mem_take hwire

private theorem IndexedStepLayout.blockScratch_outside_coefficient
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow)
    {wire : Wire} (hblock : wire ∈ registers.blockScratch)
    (hscratch : wire ∉ (registers.coefficient window).scratch) :
    wire ∉ (registers.coefficient window).allWires := by
  intro hused
  change wire ∈
    [registers.control, registers.sign] ++
      (IndexedStepRegisters.windowSlice registers.work1 window ++
        (IndexedStepRegisters.windowSlice registers.work2 window ++
          (registers.lengthT ++ (registers.coefficient window).scratch))) at hused
  rcases List.mem_append.mp hused with hfixed | hrest
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfixed
    rcases hfixed with hcontrol | hsign
    · subst wire
      exact hlayout.control_not_sourceScratch (List.mem_of_mem_drop hblock)
    · exact (hlayout.aux_not_payload
        (hlayout.blockScratch_mem_aux hblock)
        (by simp [indexedStepPayload, hsign])) rfl
  · rcases List.mem_append.mp hrest with hwork1 | hrest
    · exact (hlayout.aux_not_payload
        (hlayout.blockScratch_mem_aux hblock)
        (by simp [indexedStepPayload,
          windowSlice_mem registers.work1 window hwork1])) rfl
    · rcases List.mem_append.mp hrest with hwork2 | hrest
      · exact (hlayout.aux_not_payload
          (hlayout.blockScratch_mem_aux hblock)
          (by simp [indexedStepPayload,
            windowSlice_mem registers.work2 window hwork2])) rfl
      · rcases List.mem_append.mp hrest with hlengthT | hscratchUsed
        · exact (hlayout.aux_not_payload
            (hlayout.blockScratch_mem_aux hblock)
            (by simp [indexedStepPayload, hlengthT])) rfl
        · exact hscratch hscratchUsed

private theorem IndexedStepLayout.phase1_not_coefficient
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow) :
    registers.phase1 ∉ (registers.coefficient window).allWires := by
  intro hused
  have hafter : registers.phase1 ∈ indexedStepAfterPhase1 registers := by
    change registers.phase1 ∈
      [registers.control, registers.sign] ++
        (IndexedStepRegisters.windowSlice registers.work1 window ++
          (IndexedStepRegisters.windowSlice registers.work2 window ++
            (registers.lengthT ++ (registers.coefficient window).scratch))) at hused
    rcases List.mem_append.mp hused with hfixed | hrest
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfixed
      rcases hfixed with hcontrol | hsign
      · rw [hcontrol]
        simp [indexedStepAfterPhase1, hlayout.control_mem_aux]
      · simp [indexedStepAfterPhase1, hsign]
    · rcases List.mem_append.mp hrest with hwork1 | hrest
      · simp [indexedStepAfterPhase1,
          windowSlice_mem registers.work1 window hwork1]
      · rcases List.mem_append.mp hrest with hwork2 | hrest
        · simp [indexedStepAfterPhase1,
            windowSlice_mem registers.work2 window hwork2]
        · rcases List.mem_append.mp hrest with hlengthT | hscratch
          · simp [indexedStepAfterPhase1, hlengthT]
          · simp [indexedStepAfterPhase1,
              hlayout.blockScratch_mem_aux
                (hlayout.coefficient_scratch_sub_block window _ hscratch)]
  exact (hlayout.phase1_ne_after hafter) rfl

private theorem IndexedStepLayout.phase2_not_coefficient
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow) :
    registers.phase2 ∉ (registers.coefficient window).allWires := by
  intro hused
  have hafter : registers.phase2 ∈ indexedStepAfterPhase2 registers := by
    change registers.phase2 ∈
      [registers.control, registers.sign] ++
        (IndexedStepRegisters.windowSlice registers.work1 window ++
          (IndexedStepRegisters.windowSlice registers.work2 window ++
            (registers.lengthT ++ (registers.coefficient window).scratch))) at hused
    rcases List.mem_append.mp hused with hfixed | hrest
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfixed
      rcases hfixed with hcontrol | hsign
      · rw [hcontrol]
        simp [indexedStepAfterPhase2, hlayout.control_mem_aux]
      · simp [indexedStepAfterPhase2, hsign]
    · rcases List.mem_append.mp hrest with hwork1 | hrest
      · simp [indexedStepAfterPhase2,
          windowSlice_mem registers.work1 window hwork1]
      · rcases List.mem_append.mp hrest with hwork2 | hrest
        · simp [indexedStepAfterPhase2,
            windowSlice_mem registers.work2 window hwork2]
        · rcases List.mem_append.mp hrest with hlengthT | hscratch
          · simp [indexedStepAfterPhase2, hlengthT]
          · simp [indexedStepAfterPhase2,
              hlayout.blockScratch_mem_aux
                (hlayout.coefficient_scratch_sub_block window _ hscratch)]
  exact (hlayout.phase2_ne_after hafter) rfl

private theorem IndexedStepLayout.terminal_not_coefficient
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow) :
    registers.terminal ∉ (registers.coefficient window).allWires := by
  intro hused
  have hterminalSource : registers.terminal ∈ registers.sourceScratch := by
    rw [← hlayout.scratch_view]
    simp
  have hterminalAux := hlayout.sourceScratch_mem_aux hterminalSource
  change registers.terminal ∈
    [registers.control, registers.sign] ++
      (IndexedStepRegisters.windowSlice registers.work1 window ++
        (IndexedStepRegisters.windowSlice registers.work2 window ++
          (registers.lengthT ++ (registers.coefficient window).scratch))) at hused
  rcases List.mem_append.mp hused with hfixed | hrest
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfixed
    rcases hfixed with hcontrol | hsign
    · exact hlayout.control_not_sourceScratch
        (hcontrol ▸ hterminalSource)
    · exact (hlayout.aux_not_payload hterminalAux
        (by simp [indexedStepPayload, hsign])) rfl
  · rcases List.mem_append.mp hrest with hwork1 | hrest
    · exact (hlayout.aux_not_payload hterminalAux
        (by simp [indexedStepPayload,
          windowSlice_mem registers.work1 window hwork1])) rfl
    · rcases List.mem_append.mp hrest with hwork2 | hrest
      · exact (hlayout.aux_not_payload hterminalAux
          (by simp [indexedStepPayload,
            windowSlice_mem registers.work2 window hwork2])) rfl
      · rcases List.mem_append.mp hrest with hlengthT | hscratch
        · exact (hlayout.aux_not_payload hterminalAux
            (by simp [indexedStepPayload, hlengthT])) rfl
        · exact hlayout.terminal_not_blockScratch
            (hlayout.coefficient_scratch_sub_block window _ hscratch)

private def indexedStepShiftPayload
    (registers : IndexedStepRegisters) : List Wire :=
  [registers.phase1, registers.phase2] ++ registers.work2 ++ registers.lengthS

private theorem IndexedStepLayout.preShift_used_payload_or_scratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (_hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hwire : wire ∈ registers.preShift.preUsedWires) :
    wire ∈ indexedStepShiftPayload registers ∨
      wire ∈ registers.preShift.scratch := by
  simp only [ShiftRegisters.preUsedWires, ShiftRegisters.scratch,
    IndexedStepRegisters.preShift, indexedStepShiftPayload,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hwire ⊢
  aesop

private theorem IndexedStepLayout.lengthRPrime_not_preShift
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ registers.lengthRPrime) :
    wire ∉ registers.preShift.preUsedWires := by
  intro hused
  rcases hlayout.preShift_used_payload_or_scratch hused with hpayload | hscratch
  · exact (hlayout.lengthRPrime_ne_outside hwire (Or.inl (by
      simp only [indexedStepShiftPayload, indexedStepBeforeLengthRPrime,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hpayload ⊢
      aesop))) rfl
  · exact (hlayout.lengthRPrime_ne_outside hwire (Or.inr
      (hlayout.blockScratch_mem_aux
        (hlayout.preShift_scratch_sub_block wire hscratch)))) rfl

private theorem IndexedStepLayout.quotientLow_mem_lengthQ
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.quotientLow ∈ registers.lengthQ :=
  indexedStep_getD_mem registers.lengthQ 0 0 hlayout.lengthQ_positive

private theorem IndexedStepLayout.quotientLow_not_preShift
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.quotientLow ∉ registers.preShift.preUsedWires := by
  intro hused
  rcases hlayout.preShift_used_payload_or_scratch hused with hpayload | hscratch
  · exact (hlayout.lengthQ_ne_outside hlayout.quotientLow_mem_lengthQ (by
      simp only [indexedStepShiftPayload, indexedStepBeforeLengthQ,
        indexedStepAfterLengthQ, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hpayload ⊢
      aesop)) rfl
  · exact (hlayout.lengthQ_ne_outside hlayout.quotientLow_mem_lengthQ
      (Or.inr (by
        have haux := hlayout.blockScratch_mem_aux
          (hlayout.preShift_scratch_sub_block registers.quotientLow hscratch)
        simp [indexedStepAfterLengthQ, haux]))) rfl

private theorem IndexedStepLayout.terminal_not_preShift
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.terminal ∉ registers.preShift.preUsedWires := by
  intro hused
  rcases hlayout.preShift_used_payload_or_scratch hused with hpayload | hscratch
  · exact (hlayout.aux_not_payload
      (auxWire := registers.terminal) (payloadWire := registers.terminal)
      (hlayout.sourceScratch_mem_aux (by rw [← hlayout.scratch_view]; simp))
      (by
        simp only [indexedStepPayload,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        simp only [indexedStepShiftPayload, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hpayload
        aesop)) rfl
  · exact hlayout.terminal_not_blockScratch
      (hlayout.preShift_scratch_sub_block registers.terminal hscratch)

private theorem IndexedStepLayout.shiftEpoch_not_preShift
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.shiftEpoch ∉ registers.preShift.preUsedWires := by
  intro hused
  rcases hlayout.preShift_used_payload_or_scratch hused with hpayload | hscratch
  · exact (hlayout.aux_not_payload
      (auxWire := registers.shiftEpoch) (payloadWire := registers.shiftEpoch)
      hlayout.shiftEpoch_mem_aux (by
      simp only [indexedStepShiftPayload, indexedStepPayload,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hpayload ⊢
      aesop)) rfl
  · exact hlayout.shiftEpoch_not_sourceScratch
      (List.mem_of_mem_drop
        (hlayout.preShift_scratch_sub_block registers.shiftEpoch hscratch))

private theorem IndexedStepLayout.phase1_not_blockScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.phase1 ∉ registers.blockScratch := by
  intro hmem
  exact (hlayout.aux_not_payload
    (auxWire := registers.phase1) (payloadWire := registers.phase1)
    (hlayout.blockScratch_mem_aux hmem)
    (by simp [indexedStepPayload]) rfl).elim

private theorem IndexedStepLayout.quotientLow_not_blockScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.quotientLow ∉ registers.blockScratch := by
  intro hmem
  have hlow : registers.quotientLow ∈ registers.lengthQ := by
    exact indexedStep_getD_mem registers.lengthQ 0 0 hlayout.lengthQ_positive
  exact (hlayout.aux_not_payload
    (auxWire := registers.quotientLow) (payloadWire := registers.quotientLow)
    (hlayout.blockScratch_mem_aux hmem)
    (by simp [indexedStepPayload, hlow]) rfl).elim

private theorem IndexedStepLayout.blockScratch_outside_terminalEpoch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ∀ wire ∈ registers.blockScratch,
      wire ∉ [registers.terminal, registers.shiftEpoch,
        registers.quotientLow] := by
  intro wire hwire
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  constructor
  · intro equality
    subst wire
    exact hlayout.terminal_not_blockScratch hwire
  constructor
  · intro equality
    subst wire
    exact hlayout.shiftEpoch_not_sourceScratch (List.mem_of_mem_drop hwire)
  · intro equality
    subst wire
    exact hlayout.quotientLow_not_blockScratch hwire

private theorem terminalPaddingForwardState_preserves
    (registers : TerminalPaddingRegisters) (state : BasisState)
    {wire : Wire} (hwork : wire ∉ registers.work2)
    (hlength : wire ∉ registers.lengthS)
    (hepoch : wire ≠ registers.shiftEpoch) :
    terminalPaddingForwardState registers state wire = state wire := by
  unfold terminalPaddingForwardState
  rw [upd_other _ _ _ hepoch,
    writeReg_apply_outside _ _ _ hlength,
    writeReg_apply_outside _ _ _ hwork]

private theorem terminalPaddingForwardState_shiftEpoch_of_terminal_false
    (registers : TerminalPaddingRegisters) (state : BasisState)
    (hterminal : state registers.terminal = false)
    (hepochWork : registers.shiftEpoch ∉ registers.work2)
    (hepochLength : registers.shiftEpoch ∉ registers.lengthS)
    (hterminalWork : registers.terminal ∉ registers.work2)
    (hterminalLength : registers.terminal ∉ registers.lengthS) :
    terminalPaddingForwardState registers state registers.shiftEpoch =
      state registers.shiftEpoch := by
  unfold terminalPaddingForwardState
  simp only [upd_same]
  rw [writeReg_apply_outside _ _ _ hepochLength,
    writeReg_apply_outside _ _ _ hepochWork,
    writeReg_apply_outside _ _ _ hterminalLength,
    writeReg_apply_outside _ _ _ hterminalWork, hterminal]
  simp

private theorem IndexedStepLayout.phase1_not_work2
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.phase1 ∉ registers.work2 := by
  intro hmem
  exact (hlayout.phase1_ne_after (by
    simp [indexedStepAfterPhase1, hmem])) rfl

private theorem IndexedStepLayout.phase1_not_lengthS
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.phase1 ∉ registers.lengthS := by
  intro hmem
  exact (hlayout.phase1_ne_after (by
    simp [indexedStepAfterPhase1, hmem])) rfl

private theorem IndexedStepLayout.phase1_ne_shiftEpoch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.phase1 ≠ registers.shiftEpoch := by
  exact hlayout.phase1_ne_after (by
    simp [indexedStepAfterPhase1, hlayout.shiftEpoch_mem_aux])

private theorem IndexedStepLayout.lengthRPrime_not_work2
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hwire : wire ∈ registers.lengthRPrime) : wire ∉ registers.work2 := by
  intro hmem
  exact (hlayout.lengthRPrime_ne_outside hwire (Or.inl (by
    simp [indexedStepBeforeLengthRPrime, hmem]))) rfl

private theorem IndexedStepLayout.lengthRPrime_not_lengthS
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hwire : wire ∈ registers.lengthRPrime) : wire ∉ registers.lengthS := by
  intro hmem
  exact (hlayout.lengthRPrime_ne_outside hwire (Or.inl (by
    simp [indexedStepBeforeLengthRPrime, hmem]))) rfl

private theorem IndexedStepLayout.lengthRPrime_ne_shiftEpoch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hwire : wire ∈ registers.lengthRPrime) : wire ≠ registers.shiftEpoch := by
  exact hlayout.lengthRPrime_ne_outside hwire (Or.inr hlayout.shiftEpoch_mem_aux)

private theorem IndexedStepLayout.quotientLow_not_work2
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.quotientLow ∉ registers.work2 := by
  intro hmem
  exact (hlayout.lengthQ_ne_outside hlayout.quotientLow_mem_lengthQ
    (Or.inl (by simp [indexedStepBeforeLengthQ, hmem]))) rfl

private theorem IndexedStepLayout.quotientLow_not_lengthS
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.quotientLow ∉ registers.lengthS := by
  intro hmem
  exact (hlayout.lengthQ_ne_outside hlayout.quotientLow_mem_lengthQ
    (Or.inr (by simp [indexedStepAfterLengthQ, hmem]))) rfl

private theorem IndexedStepLayout.quotientLow_ne_shiftEpoch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.quotientLow ≠ registers.shiftEpoch := by
  exact hlayout.lengthQ_ne_outside hlayout.quotientLow_mem_lengthQ
    (Or.inr (by simp [indexedStepAfterLengthQ, hlayout.shiftEpoch_mem_aux]))

private theorem IndexedStepLayout.terminalCondition_payload
    {registers : IndexedStepRegisters} {n T : Nat}
    (_hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hwire : wire ∈ terminalConditionWires registers) :
    wire ∈ indexedStepPayload registers := by
  simp only [terminalConditionWires, indexedStepPayload,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hwire ⊢
  aesop

private theorem IndexedStepLayout.control_ne_shiftEpoch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.control ≠ registers.shiftEpoch := by
  have hnodup :
      (registers.control :: registers.shiftEpoch ::
        registers.sourceScratch).Nodup := by
    simpa only [List.cons_append, List.nil_append] using hlayout.aux_view_nodup
  intro equality
  exact (List.nodup_cons.mp hnodup).1 (by simp [equality])

private theorem IndexedStepLayout.control_ne_phase1
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.control ≠ registers.phase1 := by
  exact hlayout.aux_not_payload
    (auxWire := registers.control) (payloadWire := registers.phase1)
    hlayout.control_mem_aux (by simp [indexedStepPayload])

private theorem IndexedStepLayout.control_ne_quotientLow
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.control ≠ registers.quotientLow := by
  exact hlayout.aux_not_payload
    (auxWire := registers.control) (payloadWire := registers.quotientLow)
    hlayout.control_mem_aux (by
      simp [indexedStepPayload, hlayout.quotientLow_mem_lengthQ])

private theorem IndexedStepLayout.control_ne_terminal
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.control ≠ registers.terminal := by
  intro equality
  apply hlayout.control_not_sourceScratch
  rw [equality, ← hlayout.scratch_view]
  simp

private theorem IndexedStepLayout.control_not_work2
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.control ∉ registers.work2 := by
  intro hmem
  exact (hlayout.aux_not_payload
    (auxWire := registers.control) (payloadWire := registers.control)
    hlayout.control_mem_aux (by simp [indexedStepPayload, hmem])) rfl

private theorem IndexedStepLayout.control_not_lengthS
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.control ∉ registers.lengthS := by
  intro hmem
  exact (hlayout.aux_not_payload
    (auxWire := registers.control) (payloadWire := registers.control)
    hlayout.control_mem_aux (by simp [indexedStepPayload, hmem])) rfl

private theorem IndexedStepLayout.control_not_preShift
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.control ∉ registers.preShift.preUsedWires := by
  intro hused
  rcases hlayout.preShift_used_payload_or_scratch hused with hpayload | hscratch
  · exact (hlayout.aux_not_payload
      (auxWire := registers.control) (payloadWire := registers.control)
      hlayout.control_mem_aux (by
        simp only [indexedStepShiftPayload, indexedStepPayload,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hpayload ⊢
        aesop)) rfl
  · exact hlayout.control_not_sourceScratch
      (List.mem_of_mem_drop
        (hlayout.preShift_scratch_sub_block registers.control hscratch))

private theorem IndexedStepLayout.shiftEpoch_not_work2
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.shiftEpoch ∉ registers.work2 := by
  intro hmem
  exact (hlayout.aux_not_payload
    (auxWire := registers.shiftEpoch) (payloadWire := registers.shiftEpoch)
    hlayout.shiftEpoch_mem_aux (by simp [indexedStepPayload, hmem])) rfl

private theorem IndexedStepLayout.shiftEpoch_not_lengthS
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.shiftEpoch ∉ registers.lengthS := by
  intro hmem
  exact (hlayout.aux_not_payload
    (auxWire := registers.shiftEpoch) (payloadWire := registers.shiftEpoch)
    hlayout.shiftEpoch_mem_aux (by simp [indexedStepPayload, hmem])) rfl

private theorem IndexedStepLayout.terminal_not_work2
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.terminal ∉ registers.work2 := by
  intro hmem
  exact (hlayout.aux_not_payload
    (auxWire := registers.terminal) (payloadWire := registers.terminal)
    (hlayout.sourceScratch_mem_aux (by rw [← hlayout.scratch_view]; simp))
    (by simp [indexedStepPayload, hmem])) rfl

private theorem IndexedStepLayout.terminal_not_lengthS
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.terminal ∉ registers.lengthS := by
  intro hmem
  exact (hlayout.aux_not_payload
    (auxWire := registers.terminal) (payloadWire := registers.terminal)
    (hlayout.sourceScratch_mem_aux (by rw [← hlayout.scratch_view]; simp))
    (by simp [indexedStepPayload, hmem])) rfl

private theorem IndexedStepLayout.terminal_not_condition
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.terminal ∉ terminalConditionWires registers := by
  intro hmem
  exact (hlayout.aux_not_payload
    (auxWire := registers.terminal) (payloadWire := registers.terminal)
    (hlayout.sourceScratch_mem_aux (by rw [← hlayout.scratch_view]; simp))
    (hlayout.terminalCondition_payload hmem)) rfl

private theorem IndexedStepLayout.shiftEpoch_not_condition
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.shiftEpoch ∉ terminalConditionWires registers := by
  intro hmem
  exact (hlayout.aux_not_payload
    (auxWire := registers.shiftEpoch) (payloadWire := registers.shiftEpoch)
    hlayout.shiftEpoch_mem_aux (hlayout.terminalCondition_payload hmem)) rfl

private theorem IndexedStepLayout.quotientLow_not_condition
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.quotientLow ∉ terminalConditionWires registers := by
  simp only [terminalConditionWires, List.mem_cons, not_or]
  constructor
  · exact fun equality ↦ (hlayout.phase1_ne_after (by
      simp [indexedStepAfterPhase1, hlayout.quotientLow_mem_lengthQ])) equality.symm
  · intro hmem
    exact (hlayout.lengthRPrime_ne_outside hmem (Or.inl (by
      simp [indexedStepBeforeLengthRPrime, hlayout.quotientLow_mem_lengthQ]))) rfl

private def blockAForwardState
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  let marked := matchXorState (terminalConditionWires registers)
    (terminalConditionValue registers) registers.terminal state
  let padded := terminalPaddingForwardState registers.terminalPadding marked
  let disabled := xorWireState registers.terminal registers.phase1 padded
  let shifted := preShiftState registers.preShift disabled
  let restoredPhase := xorWireState registers.terminal registers.phase1 shifted
  let spilled := terminalEpochSpillState registers.terminal registers.shiftEpoch
    registers.quotientLow restoredPhase
  matchXorState (terminalConditionWires registers)
    (terminalConditionValue registers) registers.terminal spilled

private def remainderRestoreControlState
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  let marked := andXorWireState registers.phase2 registers.sign registers.terminal state
  let enabled := rControlState [registers.phase1, registers.terminal] 0
    registers.control registers.lengthRPrime (registers.blockScratch.getD 0 0) marked
  andXorWireState registers.phase2 registers.sign registers.terminal enabled

private theorem remainderRestoreControlState_preserves
    (registers : IndexedStepRegisters) (state : BasisState) {wire : Wire}
    (hterminal : wire ≠ registers.terminal)
    (hcontrol : wire ≠ registers.control) :
    remainderRestoreControlState registers state wire = state wire := by
  simp [remainderRestoreControlState, andXorWireState, rControlState, upd,
    hterminal, hcontrol]

private def blockB1ForwardState
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow)
    (state : BasisState) : BasisState :=
  let enabled := rControlState [registers.phase1] 0 registers.control
    registers.lengthRPrime registers.terminal state
  let changed := intervalAddSubState (registers.remainder window) n
    window.start window.stop .sub true .work1 enabled
  rControlState [registers.phase1] 0 registers.control registers.lengthRPrime
    registers.terminal changed

private def blockB2State
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  let enabled := rControlState [registers.phase1, registers.phase2] 2
    registers.control registers.lengthRPrime registers.terminal state
  let changed := xorWireState registers.control registers.sign enabled
  rControlState [registers.phase1, registers.phase2] 2 registers.control
    registers.lengthRPrime registers.terminal changed

private def blockB3ForwardState
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow)
    (state : BasisState) : BasisState :=
  let enabled := remainderRestoreControlState registers state
  let changed := intervalAddSubState (registers.remainder window) n
    window.start window.stop .add false .work1 enabled
  remainderRestoreControlState registers changed

private def blockBForwardState
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow)
    (state : BasisState) : BasisState :=
  blockB3ForwardState registers n window
    (blockB2State registers (blockB1ForwardState registers n window state))

private def blockCForwardState
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  let marked := matchXorState (terminalConditionWires registers)
    (terminalConditionValue registers) registers.terminal state
  let restored := terminalEpochRestoreState registers.terminal registers.shiftEpoch
    registers.quotientLow marked
  matchXorState (terminalConditionWires registers)
    (terminalConditionValue registers) registers.terminal restored

private def quotientPreparedBits
    (registers : QuotientSwapRegisters) (state : BasisState) : List Bool :=
  cuccaroAddBits false
    (constantBits registers.constantScratch.length 3)
    (cuccaroAddBits false (wireValues registers.lengthT state)
      (wireValues registers.lengthQ state))

private def quotientPreparedState
    (registers : QuotientSwapRegisters) (state : BasisState) : BasisState :=
  indexedWriteWireValues registers.lengthQ
    (quotientPreparedBits registers state) state

private def indexedQuotientSwapState
    (registers : QuotientSwapRegisters) (k K : Nat)
    (state : BasisState) : BasisState :=
  quotientSwapState registers k
    ((quotientSwapTree registers k K).routeLabel
      (quotientPreparedState registers state))
    (state registers.control) state

private def blockD1ForwardState
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  let enabled := matchXorState [registers.phase1, registers.phase2] 2
    registers.control state
  let changed := indexedIncrementWordState (enabled registers.control)
    registers.lengthQ enabled
  matchXorState [registers.phase1, registers.phase2] 2 registers.control changed

private def blockD2ForwardState
    (registers : IndexedStepRegisters) (window : ActiveWindow)
    (state : BasisState) : BasisState :=
  let enabled1 := xorWireState registers.phase1 registers.control state
  let enabled2 := xorWireState registers.phase2 registers.control enabled1
  let changed := indexedQuotientSwapState (registers.quotient window)
    window.start window.stop enabled2
  let disabled2 := xorWireState registers.phase2 registers.control changed
  xorWireState registers.phase1 registers.control disabled2

private def blockD3ForwardState
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  let enabled := matchXorState [registers.phase1, registers.phase2] 1
    registers.control state
  let changed := indexedDecrementWordState (enabled registers.control)
    registers.lengthQ enabled
  matchXorState [registers.phase1, registers.phase2] 1 registers.control changed

private def blockDForwardState
    (registers : IndexedStepRegisters) (window : ActiveWindow)
    (state : BasisState) : BasisState :=
  blockD3ForwardState registers
    (blockD2ForwardState registers window (blockD1ForwardState registers state))

private def tBoundaryPrepareState
    (registers : IndexedStepRegisters) (n : Nat)
    (state : BasisState) : BasisState :=
  let words := prepareLatestPaperTBoundaryWords (state registers.phase2)
    (wireValues registers.lengthT state)
    (wireValues registers.lengthRPrime state)
    (wireValues registers.tBoundary.lengthSLow state) n
  indexedWriteWireValues (registers.lengthT ++ registers.lengthRPrime)
    (words.1 ++ words.2) state

private def tBoundaryRestoreState
    (registers : IndexedStepRegisters) (n : Nat)
    (state : BasisState) : BasisState :=
  let words := restoreLatestPaperTBoundaryWords (state registers.phase2)
    (wireValues registers.lengthT state)
    (wireValues registers.lengthRPrime state)
    (wireValues registers.tBoundary.lengthSLow state) n
  indexedWriteWireValues (registers.lengthT ++ registers.lengthRPrime)
    (words.1 ++ words.2) state

private def blockEForwardState
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow)
    (state : BasisState) : BasisState :=
  let temporary1 := matchXorState [registers.phase2, registers.sign] 2
    registers.terminal state
  let subEnabled := matchXorState [registers.phase1, registers.terminal] 1
    registers.control temporary1
  let temporaryCleared1 := matchXorState [registers.phase2, registers.sign] 2
    registers.terminal subEnabled
  let prepared := tBoundaryPrepareState registers n temporaryCleared1
  let subtracted := coefficientPrefixState (registers.coefficient window)
    window.start window.stop .sub false .work2 prepared
  let temporary2 := matchXorState [registers.phase2, registers.sign] 2
    registers.terminal subtracted
  let subCleared := matchXorState [registers.phase1, registers.terminal] 1
    registers.control temporary2
  let temporaryCleared2 := matchXorState [registers.phase2, registers.sign] 2
    registers.terminal subCleared
  let signChanged := xorWireState registers.phase1 registers.sign temporaryCleared2
  let addEnabled := matchXorState [registers.phase1] 1 registers.control signChanged
  let added := coefficientPrefixState (registers.coefficient window)
    window.start window.stop .add true .work2 addEnabled
  let addCleared := matchXorState [registers.phase1] 1 registers.control added
  tBoundaryRestoreState registers n addCleared

private theorem tBoundaryPrepareState_preservesOutside
    (registers : IndexedStepRegisters) (n : Nat) (state : BasisState)
    {wire : Wire} (ht : wire ∉ registers.lengthT)
    (hrp : wire ∉ registers.lengthRPrime) :
    tBoundaryPrepareState registers n state wire = state wire := by
  unfold tBoundaryPrepareState
  exact indexedWriteWireValues_preservesOutside _ _ _ (by
    simp [ht, hrp])

private theorem tBoundaryRestoreState_preservesOutside
    (registers : IndexedStepRegisters) (n : Nat) (state : BasisState)
    {wire : Wire} (ht : wire ∉ registers.lengthT)
    (hrp : wire ∉ registers.lengthRPrime) :
    tBoundaryRestoreState registers n state wire = state wire := by
  unfold tBoundaryRestoreState
  exact indexedWriteWireValues_preservesOutside _ _ _ (by
    simp [ht, hrp])

private def blockFForwardState
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  postShiftState registers.postShift state

private def blockGForwardState
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  phaseUpdateEpochState registers.phaseUpdate registers.shiftEpoch state

private def andListXorState
    (controls : List Wire) (target : Wire) (state : BasisState) : BasisState :=
  state[target ↦ Bool.xor (state target) (wireAnd controls state)]

private def endIterationMutableWires
    (registers : IndexedStepRegisters) : List Wire :=
  registers.work1 ++ registers.work2 ++ registers.lengthT ++
    registers.lengthRPrime

private def endIterationForwardBits
    (registers : IndexedStepRegisters) (n T boundary4 boundary5 : Nat)
    (state : BasisState) : List Bool :=
  let inner := registers.endIteration n T
  let windows := endIterationWindowsAt n T
  let work := endIterationSwappedWorkWords inner state
  let lengths := endIterationLengthWords inner n windows boundary4 boundary5 state
  work.1 ++ work.2 ++ lengths.1 ++ lengths.2

private def endIterationForwardState
    (registers : IndexedStepRegisters) (n T boundary4 boundary5 : Nat)
    (state : BasisState) : BasisState :=
  indexedWriteWireValues (endIterationMutableWires registers)
    (endIterationForwardBits registers n T boundary4 boundary5 state) state

private def blockHZeroQState
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  andListXorState registers.lengthQ (registers.sourceScratch.getD 0 0) state

private def blockHBeforeSState
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  (blockHZeroQState registers state)
    [registers.shiftEpoch ↦ !(blockHZeroQState registers state) registers.shiftEpoch]

private def blockHZeroSState
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  andListXorState (registers.lengthS ++ [registers.shiftEpoch])
    (registers.sourceScratch.getD 1 0) (blockHBeforeSState registers state)

private def blockHEndInputState
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  let zeroS := blockHZeroSState registers state
  let restoredEpoch := zeroS[registers.shiftEpoch ↦ !zeroS registers.shiftEpoch]
  andXorWireState (registers.sourceScratch.getD 0 0)
    (registers.sourceScratch.getD 1 0) registers.control restoredEpoch

private def blockHForwardState
    (registers : IndexedStepRegisters) (n T boundary4 boundary5 : Nat)
    (state : BasisState) : BasisState :=
  if T % 4 = 0 then
    let enabled := blockHEndInputState registers state
    let changed := endIterationForwardState registers n T boundary4 boundary5 enabled
    let iterated := xorWireState registers.control registers.iter changed
    let disabled := andXorWireState (registers.sourceScratch.getD 0 0)
      (registers.sourceScratch.getD 1 0) registers.control iterated
    let epochBeforeClear := disabled[registers.shiftEpoch ↦ !disabled registers.shiftEpoch]
    let clearedS := andListXorState (registers.lengthS ++ [registers.shiftEpoch])
      (registers.sourceScratch.getD 1 0) epochBeforeClear
    let restoredEpochAgain :=
      clearedS[registers.shiftEpoch ↦ !clearedS registers.shiftEpoch]
    andListXorState registers.lengthQ (registers.sourceScratch.getD 0 0)
      restoredEpochAgain
  else state

private theorem run_mcxVChain_andListXorState
    (controls : List Wire) (target : Wire) (scratches : List Wire)
    (state : BasisState)
    (henough : controls.length - 2 ≤ scratches.length)
    (hlayout : McxVChainLayout controls target scratches)
    (hclean : Clean scratches state) :
    run (mcxVChain controls target scratches) state =
        andListXorState controls target state ∧
      Clean scratches (andListXorState controls target state) := by
  have hrun := run_mcxVChain controls target scratches state henough hlayout hclean
  have htarget : target ∉ scratches := by
    obtain ⟨_, htail, _⟩ := List.nodup_append.mp hlayout
    exact (List.nodup_cons.mp htail).1
  constructor
  · simpa only [andListXorState] using hrun
  · intro wire hwire
    simp [andListXorState, upd,
      show wire ≠ target by intro equality; subst wire; exact htarget hwire,
      hclean wire hwire]

private theorem andListXorState_preserves
    (controls : List Wire) (target : Wire) (state : BasisState)
    {wire : Wire} (hwire : wire ≠ target) :
    andListXorState controls target state wire = state wire := by
  simp [andListXorState, upd, hwire]

private theorem xorWireState_preserves
    (control target : Wire) (state : BasisState)
    {wire : Wire} (hwire : wire ≠ target) :
    xorWireState control target state wire = state wire := by
  simp [xorWireState, upd, hwire]

private theorem andXorWireState_preserves
    (first second target : Wire) (state : BasisState)
    {wire : Wire} (hwire : wire ≠ target) :
    andXorWireState first second target state wire = state wire := by
  simp [andXorWireState, upd, hwire]

private theorem endIterationForwardState_preservesOutside
    (registers : IndexedStepRegisters) (n T boundary4 boundary5 : Nat)
    (state : BasisState) {wire : Wire}
    (hwire : wire ∉ endIterationMutableWires registers) :
    endIterationForwardState registers n T boundary4 boundary5 state wire =
      state wire := by
  exact indexedWriteWireValues_preservesOutside _ _ _ hwire

private theorem IndexedStepLayout.aux_not_endIterationMutable
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (haux : wire ∈ registers.aux) :
    wire ∉ endIterationMutableWires registers := by
  intro hmutable
  apply (hlayout.aux_not_payload haux ?_) rfl
  simp only [endIterationMutableWires, indexedStepPayload,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmutable ⊢
  aesop

private theorem IndexedStepLayout.lengthQ_not_endIterationMutable
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hlength : wire ∈ registers.lengthQ) :
    wire ∉ endIterationMutableWires registers := by
  intro hmutable
  apply (hlayout.lengthQ_ne_outside hlength ?_) rfl
  simp only [endIterationMutableWires, indexedStepBeforeLengthQ,
    indexedStepAfterLengthQ, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hmutable ⊢
  aesop

private theorem IndexedStepLayout.lengthS_not_endIterationMutable
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hlength : wire ∈ registers.lengthS) :
    wire ∉ endIterationMutableWires registers := by
  intro hmutable
  let before := [registers.phase1, registers.phase2, registers.iter,
      registers.sign] ++ registers.work1 ++ registers.work2 ++
        registers.lengthT ++ registers.lengthQ
  let after := registers.lengthRPrime ++ registers.aux
  have hphysical :
      (before ++ (registers.lengthS ++ after)).Nodup := by
    simpa [before, after, IndexedStepRegisters.allWires,
      List.append_assoc] using hlayout.physical
  apply (nodup_middle_ne hphysical hlength ?_) rfl
  simp only [endIterationMutableWires, before, after, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hmutable ⊢
  aesop

private theorem IndexedStepLayout.lengthS_ne_iter
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hlength : wire ∈ registers.lengthS) :
    wire ≠ registers.iter := by
  let before := [registers.phase1, registers.phase2, registers.iter,
      registers.sign] ++ registers.work1 ++ registers.work2 ++
        registers.lengthT ++ registers.lengthQ
  let after := registers.lengthRPrime ++ registers.aux
  have hphysical :
      (before ++ (registers.lengthS ++ after)).Nodup := by
    simpa [before, after, IndexedStepRegisters.allWires,
      List.append_assoc] using hlayout.physical
  exact nodup_middle_ne hphysical hlength (Or.inl (by
    simp [before]))

private theorem endIterationMutableWires_nodup
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T)
    (hstep : T % 4 = 0) :
    (endIterationMutableWires registers).Nodup := by
  have hphysical := (hlayout.endIteration hstep).physical
  change (registers.control :: endIterationMutableWires registers ++
    (registers.endIteration n T).scratch).Nodup at hphysical
  exact (List.nodup_append.mp (List.nodup_cons.mp hphysical).2).1

private theorem endIterationForwardBits_length
    (registers : IndexedStepRegisters) (n T boundary4 boundary5 : Nat)
    (state : BasisState)
    (hwork : registers.work1.length = registers.work2.length) :
    (endIterationForwardBits registers n T boundary4 boundary5 state).length =
      (endIterationMutableWires registers).length := by
  have hxor (bits : List Bool) (value : Nat) :
      (xorConstantBits bits value).length = bits.length := by
    induction bits generalizing value with
    | nil => rfl
    | cons bit bits ih => simp [xorConstantBits, ih]
  have hgated (enabled : Bool) (bits : List Bool) (value : Nat) :
      (gatedXorConstantBits enabled bits value).length = bits.length := by
    cases enabled <;> simp [gatedXorConstantBits, hxor]
  have hwrite (valueAt : Nat → Nat) (labels : List Nat)
      (selectors : List Bool) (bits : List Bool) :
      (constantWriteWord valueAt labels selectors bits).length = bits.length := by
    induction labels generalizing selectors bits with
    | nil => rfl
    | cons label labels ih =>
        cases selectors with
        | nil => rfl
        | cons selector selectors =>
            rw [constantWriteWord, ih, hgated]
  have hhighest (width k K : Nat) (enabled : Bool)
      (rangeBits targetBits : List Bool) :
      (highestPositionWordAction width k K enabled rangeBits targetBits).length =
        targetBits.length := by
    simp [highestPositionWordAction, hwrite, hgated]
  have hright (width k K : Nat) (enabled : Bool)
      (rangeBits targetBits : List Bool) :
      (rightLengthWordAction n width k K enabled rangeBits targetBits).length =
        targetBits.length := by
    simp [rightLengthWordAction, hwrite, hgated]
  simp only [endIterationForwardBits, endIterationMutableWires,
    List.length_append]
  unfold endIterationLengthWords
  dsimp only
  rw [hhighest, hhighest, hright, hright]
  cases hcontrol : state registers.control <;>
    simp [endIterationSwappedWorkWords, wireValues,
      IndexedStepRegisters.endIteration, hwork, hcontrol]

private theorem run_endIterationForwardState
    (registers : IndexedStepRegisters) (n T boundary4 boundary5 : Nat)
    (hboundary4 : (endIterationWindowsAt n T).k4 ≤ boundary4 ∧
      boundary4 ≤ (endIterationWindowsAt n T).K4)
    (hboundary5 : (endIterationWindowsAt n T).k5 ≤ boundary5 ∧
      boundary5 ≤ (endIterationWindowsAt n T).K5Decode n)
    (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hstep : T % 4 = 0)
    (hroute4 : ((registers.endIteration n T).upperTree
        (endIterationWindowsAt n T)).routeLabel
      (run (constMinus (registers.endIteration n T).lengthRP
          (registers.endIteration n T).constants
          (registers.endIteration n T).carry (n + 2))
        (run (controlledWorkSwap (registers.endIteration n T).control
          (registers.endIteration n T).work1
          (registers.endIteration n T).work2) state)) = boundary4)
    (hroute5 : ((registers.endIteration n T).lowerTree n
        (endIterationWindowsAt n T)).routeLabel
      (run (addConstant (registers.endIteration n T).lengthT
          (registers.endIteration n T).constants
          (registers.endIteration n T).carry 3)
        (run (lenUpdateLtUnary n (endIterationWindowsAt n T).k4
          (endIterationWindowsAt n T).K4
          ((registers.endIteration n T).upperTree (endIterationWindowsAt n T))
          (registers.endIteration n T).control
          ((registers.endIteration n T).rangeAccumulator
            (endIterationWindowsAt n T).k4 (endIterationWindowsAt n T).K4)
          ((registers.endIteration n T).temporary
            (endIterationWindowsAt n T).k4 (endIterationWindowsAt n T).K4)
          (registers.endIteration n T).carry
          ((registers.endIteration n T).path
            (endIterationWindowsAt n T).k4 (endIterationWindowsAt n T).K4)
          (registers.endIteration n T).work1At
          (registers.endIteration n T).work2At
          (registers.endIteration n T).lengthT
          (registers.endIteration n T).lengthRP
          (registers.endIteration n T).constants)
        (run (controlledWorkSwap (registers.endIteration n T).control
          (registers.endIteration n T).work1
          (registers.endIteration n T).work2) state))) = boundary5)
    (hready : EndIterationReady (registers.endIteration n T) state) :
    run (swapWorkAndLengthUnaryShared (registers.endIteration n T) n
        (endIterationWindowsAt n T)) state =
        endIterationForwardState registers n T boundary4 boundary5 state ∧
      EndIterationReady (registers.endIteration n T)
        (endIterationForwardState registers n T boundary4 boundary5 state) := by
  have hcorrect := swapWorkAndLengthUnaryShared_correct
    (registers.endIteration n T) n (endIterationWindowsAt n T)
    boundary4 boundary5 hboundary4 hboundary5 state
    (hlayout.endIteration hstep) hroute4 hroute5 hready
  rcases hcorrect with ⟨hwork1, hwork2, hlengths, hafterReady, houtside⟩
  have hwork1' :
      wireValues registers.work1
          (run (swapWorkAndLengthUnaryShared (registers.endIteration n T) n
            (endIterationWindowsAt n T)) state) =
        (endIterationSwappedWorkWords (registers.endIteration n T) state).1 := by
    simpa [IndexedStepRegisters.endIteration] using hwork1
  have hwork2' :
      wireValues registers.work2
          (run (swapWorkAndLengthUnaryShared (registers.endIteration n T) n
            (endIterationWindowsAt n T)) state) =
        (endIterationSwappedWorkWords (registers.endIteration n T) state).2 := by
    simpa [IndexedStepRegisters.endIteration] using hwork2
  have hlengthT :
      wireValues registers.lengthT
          (run (swapWorkAndLengthUnaryShared (registers.endIteration n T) n
            (endIterationWindowsAt n T)) state) =
        (endIterationLengthWords (registers.endIteration n T) n
          (endIterationWindowsAt n T) boundary4 boundary5 state).1 := by
    simpa [IndexedStepRegisters.endIteration] using congrArg Prod.fst hlengths
  have hlengthRP :
      wireValues registers.lengthRPrime
          (run (swapWorkAndLengthUnaryShared (registers.endIteration n T) n
            (endIterationWindowsAt n T)) state) =
        (endIterationLengthWords (registers.endIteration n T) n
          (endIterationWindowsAt n T) boundary4 boundary5 state).2 := by
    simpa [IndexedStepRegisters.endIteration] using congrArg Prod.snd hlengths
  have hstate :
      run (swapWorkAndLengthUnaryShared (registers.endIteration n T) n
          (endIterationWindowsAt n T)) state =
        endIterationForwardState registers n T boundary4 boundary5 state := by
    apply indexedState_eq_writeWireValues
    · exact endIterationMutableWires_nodup registers n T hlayout hstep
    · exact endIterationForwardBits_length registers n T boundary4 boundary5 state
        (hlayout.work1_length.trans hlayout.work2_length.symm)
    · simp only [endIterationMutableWires, endIterationForwardBits,
        wireValues, List.map_append]
      simp only [wireValues] at hwork1' hwork2' hlengthT hlengthRP
      rw [hwork1', hwork2', hlengthT, hlengthRP]
    · intro wire hwire
      simp only [endIterationMutableWires, List.mem_append, not_or] at hwire
      rcases hwire with ⟨⟨⟨hwork1, hwork2⟩, hlengthT⟩, hlengthRP⟩
      exact houtside wire hwork1 hwork2 hlengthT hlengthRP
  constructor
  · exact hstate
  · rw [← hstate]
    exact hafterReady

private theorem terminalPaddingForwardState_terminal
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T) :
    terminalPaddingForwardState registers.terminalPadding state
        registers.terminal =
      state registers.terminal := by
  have hterminalWork : registers.terminal ∉ registers.work2 := by
    intro hmem
    exact (hlayout.aux_not_payload
      (auxWire := registers.terminal) (payloadWire := registers.terminal)
      (hlayout.sourceScratch_mem_aux (by
        rw [← hlayout.scratch_view]
        simp))
      (by simp [indexedStepPayload, hmem]) rfl).elim
  have hterminalLength : registers.terminal ∉ registers.lengthS := by
    intro hmem
    exact (hlayout.aux_not_payload
      (auxWire := registers.terminal) (payloadWire := registers.terminal)
      (hlayout.sourceScratch_mem_aux (by
        rw [← hlayout.scratch_view]
        simp))
      (by simp [indexedStepPayload, hmem]) rfl).elim
  have hterminalEpoch : registers.terminal ≠ registers.shiftEpoch := by
    have hphysical := hlayout.terminalEpoch
    simp only [List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at hphysical
    exact hphysical.1.1
  change terminalPaddingForwardState registers.terminalPadding state
      registers.terminalPadding.terminal =
    state registers.terminalPadding.terminal
  change registers.terminalPadding.terminal ∉
    registers.terminalPadding.work2 at hterminalWork
  change registers.terminalPadding.terminal ∉
    registers.terminalPadding.lengthS at hterminalLength
  change registers.terminalPadding.terminal ≠
    registers.terminalPadding.shiftEpoch at hterminalEpoch
  simp only [terminalPaddingForwardState]
  rw [upd_other _ _ _ hterminalEpoch,
    writeReg_apply_outside _ _ _ hterminalLength,
    writeReg_apply_outside _ _ _ hterminalWork]

private theorem blockAForward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state) :
    run (blockAForward registers) state = blockAForwardState registers state ∧
      Clean registers.blockScratch (run (blockAForward registers) state) := by
  let marked := matchXorState (terminalConditionWires registers)
    (terminalConditionValue registers) registers.terminal state
  have hblock : Clean registers.blockScratch state := by
    apply clean_mono hready
    intro wire hwire
    exact List.mem_cons_of_mem registers.control (List.mem_of_mem_drop hwire)
  have hmarkedRun : run (toggleTerminal registers) state = marked := by
    simpa [toggleTerminal, marked, matchXorState] using
      run_computeControl (terminalConditionWires registers)
        (terminalConditionValue registers) registers.terminal
        registers.blockScratch state hlayout.terminalControl hblock
  have hterminalNotBlock : registers.terminal ∉ registers.blockScratch :=
    hlayout.terminal_not_blockScratch
  have hmarkedBlock : Clean registers.blockScratch marked := by
    simpa [marked, matchXorState] using
      clean_upd_not_mem hblock hterminalNotBlock
  let padded := terminalPaddingForwardState registers.terminalPadding marked
  have hterminalPaddingReady :
      Clean registers.terminalPadding.scratch marked :=
    clean_mono hmarkedBlock hlayout.terminalPadding_scratch_sub_block
  have hpaddedRun :
      run (terminalPaddingForward registers.terminalPadding) marked = padded := by
    simpa only [padded] using run_terminalPaddingForward registers.terminalPadding
      marked hlayout.terminalPadding hterminalPaddingReady
  have hpaddedLocal : Clean registers.terminalPadding.scratch padded := by
    rw [← hpaddedRun]
    exact terminalPaddingForward_clean registers.terminalPadding marked
      hlayout.terminalPadding hterminalPaddingReady
  have hpaddedBlock : Clean registers.blockScratch padded := by
    rw [← hpaddedRun]
    exact clean_after_local_circuit hmarkedBlock
      (by simpa only [hpaddedRun] using hpaddedLocal)
      (terminalPaddingForward_usesOnly registers.terminalPadding)
      hlayout.terminalPadding_support_intersection
  let disabled := xorWireState registers.terminal registers.phase1 padded
  have hdisabledBlock : Clean registers.blockScratch disabled := by
    simpa [disabled, xorWireState] using
      clean_upd_not_mem hpaddedBlock hlayout.phase1_not_blockScratch
  have hpreReady : ShiftReady registers.preShift disabled :=
    clean_mono hdisabledBlock hlayout.preShift_scratch_sub_block
  let shifted := preShiftState registers.preShift disabled
  have hshiftedRun : run (preShiftUnitary registers.preShift) disabled = shifted := by
    simpa only [shifted] using
      run_preShiftUnitary registers.preShift disabled hlayout.preShift hpreReady
  have hshiftedLocal : ShiftReady registers.preShift shifted := by
    rw [← hshiftedRun]
    exact preShiftUnitary_ready registers.preShift disabled hlayout.preShift hpreReady
  have hshiftedBlock : Clean registers.blockScratch shifted := by
    rw [← hshiftedRun]
    exact clean_after_local_circuit hdisabledBlock
      (by simpa only [hshiftedRun] using hshiftedLocal)
      (preShiftUnitary_usesOnly registers.preShift)
      hlayout.preShift_support_intersection
  let restoredPhase := xorWireState registers.terminal registers.phase1 shifted
  have hrestoredBlock : Clean registers.blockScratch restoredPhase := by
    simpa [restoredPhase, xorWireState] using
      clean_upd_not_mem hshiftedBlock hlayout.phase1_not_blockScratch
  let spilled := terminalEpochSpillState registers.terminal registers.shiftEpoch
    registers.quotientLow restoredPhase
  have hspilledRun : run
      (terminalEpochSpill registers.terminal registers.shiftEpoch registers.quotientLow)
      restoredPhase = spilled := by
    simpa only [spilled] using run_terminalEpochSpillState registers.terminal
      registers.shiftEpoch registers.quotientLow restoredPhase hlayout.terminalEpoch
  have hspilledBlock : Clean registers.blockScratch spilled := by
    rw [← hspilledRun]
    intro wire hwire
    rw [(terminalEpochSpill_usesOnly registers.terminal registers.shiftEpoch
      registers.quotientLow).preservesOutside restoredPhase
        (hlayout.blockScratch_outside_terminalEpoch wire hwire)]
    exact hrestoredBlock wire hwire
  have hunmarkedRun : run (toggleTerminal registers) spilled =
      matchXorState (terminalConditionWires registers)
        (terminalConditionValue registers) registers.terminal spilled := by
    simpa [toggleTerminal, matchXorState] using
      run_computeControl (terminalConditionWires registers)
        (terminalConditionValue registers) registers.terminal
        registers.blockScratch spilled hlayout.terminalControl hspilledBlock
  have hunmarkedBlock : Clean registers.blockScratch
      (matchXorState (terminalConditionWires registers)
        (terminalConditionValue registers) registers.terminal spilled) := by
    simpa [matchXorState] using
      clean_upd_not_mem hspilledBlock hlayout.terminal_not_blockScratch
  have hrun :
      run (blockAForward registers) state = blockAForwardState registers state := by
    simp only [blockAForward, Classical.run_append]
    rw [hmarkedRun, hpaddedRun,
      run_xorWireState registers.terminal registers.phase1 padded,
      hshiftedRun,
      run_xorWireState registers.terminal registers.phase1 shifted,
      hspilledRun, hunmarkedRun]
    rfl
  exact ⟨hrun, by rw [hrun]; exact hunmarkedBlock⟩

private theorem blockAForward_borrowedReady
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state)
    (hencoded : IndexedStepEpochEncoded registers state) :
    IndexedStepBorrowedReady registers
      (run (blockAForward registers) state) := by
  let terminalMatch := registerMatches (terminalConditionWires registers)
    (terminalConditionValue registers) state
  let marked := matchXorState (terminalConditionWires registers)
    (terminalConditionValue registers) registers.terminal state
  let padded := terminalPaddingForwardState registers.terminalPadding marked
  let disabled := xorWireState registers.terminal registers.phase1 padded
  let shifted := preShiftState registers.preShift disabled
  let restoredPhase := xorWireState registers.terminal registers.phase1 shifted
  let spilled := terminalEpochSpillState registers.terminal registers.shiftEpoch
    registers.quotientLow restoredPhase
  have hcorrect := blockAForward_correct registers n T state hlayout hready
  have hcontrolFalse : state registers.control = false := by
    exact hready registers.control (by
      simp [IndexedStepRegisters.sharedScratch])
  have hterminalFalse : state registers.terminal = false := by
    exact hready registers.terminal (by
      simp only [IndexedStepRegisters.sharedScratch, List.mem_cons]
      right
      rw [← hlayout.scratch_view]
      simp)
  have hblock : Clean registers.blockScratch state := by
    apply clean_mono hready
    intro wire hwire
    exact List.mem_cons_of_mem registers.control (List.mem_of_mem_drop hwire)
  have hterminalEpoch := hlayout.terminalEpoch
  simp only [List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hterminalEpoch
  have hterminalShift : registers.terminal ≠ registers.shiftEpoch :=
    hterminalEpoch.1.1
  have hterminalQuotient : registers.terminal ≠ registers.quotientLow :=
    hterminalEpoch.1.2
  have hshiftQuotient : registers.shiftEpoch ≠ registers.quotientLow :=
    hterminalEpoch.2.1
  have hterminalPhase := hlayout.terminalPhase
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false] at hterminalPhase
  have hphaseTerminal : registers.phase1 ≠ registers.terminal :=
    Ne.symm hterminalPhase.1
  have hmarkedTerminal : marked registers.terminal = terminalMatch := by
    simp [marked, terminalMatch, matchXorState, hterminalFalse]
  have hmarkedControl : marked registers.control = state registers.control := by
    simp [marked, matchXorState, upd, hlayout.control_ne_terminal]
  have hmarkedQuotient : marked registers.quotientLow =
      state registers.quotientLow := by
    simp [marked, matchXorState, upd, Ne.symm hterminalQuotient]
  have hmarkedEpoch : marked registers.shiftEpoch = state registers.shiftEpoch := by
    simp [marked, matchXorState, upd, Ne.symm hterminalShift]
  have hmarkedCondition :
      registerMatches (terminalConditionWires registers)
          (terminalConditionValue registers) marked = terminalMatch := by
    change registerMatches (terminalConditionWires registers)
        (terminalConditionValue registers) marked =
      registerMatches (terminalConditionWires registers)
        (terminalConditionValue registers) state
    apply registerMatches_congr
    intro wire hwire
    have hne : wire ≠ registers.terminal := by
      intro equality
      apply hlayout.terminal_not_condition
      simpa [equality] using hwire
    simp [marked, matchXorState, upd, hne]
  have hmarkedBlock : Clean registers.blockScratch marked := by
    simpa [marked, matchXorState] using
      clean_upd_not_mem hblock hlayout.terminal_not_blockScratch
  have hpaddingReady : Clean registers.terminalPadding.scratch marked :=
    clean_mono hmarkedBlock hlayout.terminalPadding_scratch_sub_block
  have hpaddedRun :
      run (terminalPaddingForward registers.terminalPadding) marked = padded := by
    simpa only [padded] using run_terminalPaddingForward registers.terminalPadding
      marked hlayout.terminalPadding hpaddingReady
  have hpaddedLocal : Clean registers.terminalPadding.scratch padded := by
    rw [← hpaddedRun]
    exact terminalPaddingForward_clean registers.terminalPadding marked
      hlayout.terminalPadding hpaddingReady
  have hpaddedBlock : Clean registers.blockScratch padded := by
    rw [← hpaddedRun]
    exact clean_after_local_circuit hmarkedBlock
      (by simpa only [hpaddedRun] using hpaddedLocal)
      (terminalPaddingForward_usesOnly registers.terminalPadding)
      hlayout.terminalPadding_support_intersection
  have hpaddedTerminal : padded registers.terminal = terminalMatch := by
    calc
      padded registers.terminal = marked registers.terminal :=
        terminalPaddingForwardState_terminal registers n T marked hlayout
      _ = terminalMatch := hmarkedTerminal
  have hpaddedControl : padded registers.control = state registers.control := by
    calc
      padded registers.control = marked registers.control :=
        terminalPaddingForwardState_preserves registers.terminalPadding marked
          hlayout.control_not_work2 hlayout.control_not_lengthS
          hlayout.control_ne_shiftEpoch
      _ = state registers.control := hmarkedControl
  have hpaddedQuotient : padded registers.quotientLow =
      state registers.quotientLow := by
    calc
      padded registers.quotientLow = marked registers.quotientLow :=
        terminalPaddingForwardState_preserves registers.terminalPadding marked
          hlayout.quotientLow_not_work2 hlayout.quotientLow_not_lengthS
          hlayout.quotientLow_ne_shiftEpoch
      _ = state registers.quotientLow := hmarkedQuotient
  have hpaddedPhase : padded registers.phase1 = state registers.phase1 := by
    calc
      padded registers.phase1 = marked registers.phase1 :=
        terminalPaddingForwardState_preserves registers.terminalPadding marked
          hlayout.phase1_not_work2 hlayout.phase1_not_lengthS
          hlayout.phase1_ne_shiftEpoch
      _ = state registers.phase1 := by
        simp [marked, matchXorState, upd, hphaseTerminal]
  have hpaddedCondition :
      registerMatches (terminalConditionWires registers)
          (terminalConditionValue registers) padded = terminalMatch := by
    calc
      registerMatches (terminalConditionWires registers)
          (terminalConditionValue registers) padded =
          registerMatches (terminalConditionWires registers)
            (terminalConditionValue registers) marked := by
        apply registerMatches_congr
        intro wire hwire
        simp only [terminalConditionWires, List.mem_cons] at hwire
        rcases hwire with rfl | hlength
        · exact terminalPaddingForwardState_preserves registers.terminalPadding marked
            hlayout.phase1_not_work2 hlayout.phase1_not_lengthS
            hlayout.phase1_ne_shiftEpoch
        · exact terminalPaddingForwardState_preserves registers.terminalPadding marked
            (hlayout.lengthRPrime_not_work2 hlength)
            (hlayout.lengthRPrime_not_lengthS hlength)
            (hlayout.lengthRPrime_ne_shiftEpoch hlength)
      _ = terminalMatch := hmarkedCondition
  have hdisabledBlock : Clean registers.blockScratch disabled := by
    simpa [disabled, xorWireState] using
      clean_upd_not_mem hpaddedBlock hlayout.phase1_not_blockScratch
  have hpreReady : ShiftReady registers.preShift disabled :=
    clean_mono hdisabledBlock hlayout.preShift_scratch_sub_block
  have hpreRun : run (preShiftUnitary registers.preShift) disabled = shifted := by
    simpa only [shifted] using
      run_preShiftUnitary registers.preShift disabled hlayout.preShift hpreReady
  have hdisabledTerminal : disabled registers.terminal = terminalMatch := by
    simp [disabled, xorWireState, upd, Ne.symm hphaseTerminal, hpaddedTerminal]
  have hdisabledControl : disabled registers.control = state registers.control := by
    simp [disabled, xorWireState, upd, hlayout.control_ne_phase1,
      hpaddedControl]
  have hdisabledQuotient : disabled registers.quotientLow =
      state registers.quotientLow := by
    have hne : registers.quotientLow ≠ registers.phase1 := by
      exact fun equality ↦ (hlayout.phase1_ne_after (by
        simp [indexedStepAfterPhase1, hlayout.quotientLow_mem_lengthQ])) equality.symm
    simp [disabled, xorWireState, upd, hne, hpaddedQuotient]
  have hshiftedTerminal : shifted registers.terminal = terminalMatch := by
    rw [← hpreRun,
      preShiftUnitary_preservesOutside registers.preShift disabled
        hlayout.terminal_not_preShift]
    exact hdisabledTerminal
  have hshiftedControl : shifted registers.control = state registers.control := by
    rw [← hpreRun,
      preShiftUnitary_preservesOutside registers.preShift disabled
        hlayout.control_not_preShift]
    exact hdisabledControl
  have hshiftedQuotient : shifted registers.quotientLow =
      state registers.quotientLow := by
    rw [← hpreRun,
      preShiftUnitary_preservesOutside registers.preShift disabled
        hlayout.quotientLow_not_preShift]
    exact hdisabledQuotient
  have hshiftedPhase : shifted registers.phase1 = disabled registers.phase1 := by
    rw [← hpreRun]
    exact preShiftUnitary_preserves_phase1 registers.preShift disabled
      hlayout.preShift hpreReady
  have hrestoredTerminal : restoredPhase registers.terminal = terminalMatch := by
    simp [restoredPhase, xorWireState, upd, Ne.symm hphaseTerminal,
      hshiftedTerminal]
  have hrestoredControl : restoredPhase registers.control = state registers.control := by
    simp [restoredPhase, xorWireState, upd, hlayout.control_ne_phase1,
      hshiftedControl]
  have hrestoredQuotient : restoredPhase registers.quotientLow =
      state registers.quotientLow := by
    have hne : registers.quotientLow ≠ registers.phase1 := by
      exact fun equality ↦ (hlayout.phase1_ne_after (by
        simp [indexedStepAfterPhase1, hlayout.quotientLow_mem_lengthQ])) equality.symm
    simp [restoredPhase, xorWireState, upd, hne, hshiftedQuotient]
  have hrestoredControls : ∀ wire ∈ terminalConditionWires registers,
      restoredPhase wire = state wire := by
    intro wire hwire
    simp only [terminalConditionWires, List.mem_cons] at hwire
    rcases hwire with rfl | hlength
    · simp [restoredPhase, xorWireState, disabled, hshiftedPhase,
        hshiftedTerminal, hpaddedTerminal, hpaddedPhase]
    · have houtside := preShiftUnitary_preservesOutside registers.preShift disabled
        (hlayout.lengthRPrime_not_preShift hlength)
      rw [hpreRun] at houtside
      have hphaseNe : wire ≠ registers.phase1 := by
        exact fun equality ↦
          (hlayout.lengthRPrime_ne_outside hlength (Or.inl (by
            simp [indexedStepBeforeLengthRPrime]))) equality
      have hterminalNe : wire ≠ registers.terminal := by
        exact hlayout.lengthRPrime_ne_outside hlength (Or.inr
          (hlayout.sourceScratch_mem_aux (by rw [← hlayout.scratch_view]; simp)))
      calc
        restoredPhase wire = shifted wire := by
          simp [restoredPhase, xorWireState, upd, hphaseNe]
        _ = disabled wire := houtside
        _ = padded wire := by simp [disabled, xorWireState, upd, hphaseNe]
        _ = marked wire := terminalPaddingForwardState_preserves
          registers.terminalPadding marked
          (hlayout.lengthRPrime_not_work2 hlength)
          (hlayout.lengthRPrime_not_lengthS hlength)
          (hlayout.lengthRPrime_ne_shiftEpoch hlength)
        _ = state wire := by simp [marked, matchXorState, upd, hterminalNe]
  have hrestoredCondition :
      registerMatches (terminalConditionWires registers)
          (terminalConditionValue registers) restoredPhase = terminalMatch := by
    change registerMatches (terminalConditionWires registers)
        (terminalConditionValue registers) restoredPhase =
      registerMatches (terminalConditionWires registers)
        (terminalConditionValue registers) state
    exact registerMatches_congr _ _ _ _ hrestoredControls
  have hspilledTerminal : spilled registers.terminal = terminalMatch := by
    calc
      spilled registers.terminal = restoredPhase registers.terminal :=
        terminalEpochSpillState_preserves _ _ _ _ hterminalShift
          hterminalQuotient hterminalQuotient
      _ = terminalMatch := hrestoredTerminal
  have hspilledControl : spilled registers.control = state registers.control := by
    calc
      spilled registers.control = restoredPhase registers.control :=
        terminalEpochSpillState_preserves _ _ _ _
          hlayout.control_ne_shiftEpoch hlayout.control_ne_quotientLow
          hterminalQuotient
      _ = state registers.control := hrestoredControl
  have hspilledControls : ∀ wire ∈ terminalConditionWires registers,
      spilled wire = state wire := by
    intro wire hwire
    have hterminalNe : wire ≠ registers.terminal := by
      intro equality
      exact hlayout.terminal_not_condition (by simpa [equality] using hwire)
    have hepochNe : wire ≠ registers.shiftEpoch := by
      intro equality
      exact hlayout.shiftEpoch_not_condition (by simpa [equality] using hwire)
    have hquotientNe : wire ≠ registers.quotientLow := by
      intro equality
      exact hlayout.quotientLow_not_condition (by simpa [equality] using hwire)
    calc
      spilled wire = restoredPhase wire :=
        terminalEpochSpillState_preserves _ _ _ _ hepochNe hquotientNe
          hterminalQuotient
      _ = state wire := hrestoredControls wire hwire
  have hspilledCondition :
      registerMatches (terminalConditionWires registers)
          (terminalConditionValue registers) spilled = terminalMatch := by
    change registerMatches (terminalConditionWires registers)
        (terminalConditionValue registers) spilled =
      registerMatches (terminalConditionWires registers)
        (terminalConditionValue registers) state
    exact registerMatches_congr _ _ _ _ hspilledControls
  have hspilledEpoch : spilled registers.shiftEpoch = false := by
    by_cases hmatch : terminalMatch = true
    · have hquotient : state registers.quotientLow = true := by
        simpa [IndexedStepEpochEncoded, terminalMatch, hmatch] using hencoded
      simp [spilled, terminalEpochSpillState, controlledSwapState, xorWireState,
        swapWireState, upd, hterminalQuotient,
        hshiftQuotient, hrestoredTerminal, hrestoredQuotient,
        hmatch, hquotient]
    · have hmatchFalse : terminalMatch = false := by
        cases hvalue : terminalMatch <;> simp_all
      have hepoch : state registers.shiftEpoch = false := by
        simpa [IndexedStepEpochEncoded, terminalMatch, hmatchFalse] using hencoded
      have hpaddedEpoch : padded registers.shiftEpoch = state registers.shiftEpoch := by
        calc
          padded registers.shiftEpoch = marked registers.shiftEpoch :=
            terminalPaddingForwardState_shiftEpoch_of_terminal_false
              registers.terminalPadding marked (by
                simpa [hmatchFalse] using hmarkedTerminal)
              hlayout.shiftEpoch_not_work2 hlayout.shiftEpoch_not_lengthS
              hlayout.terminal_not_work2 hlayout.terminal_not_lengthS
          _ = state registers.shiftEpoch := hmarkedEpoch
      have hdisabledEpoch : disabled registers.shiftEpoch = state registers.shiftEpoch := by
        simp [disabled, xorWireState, upd, hlayout.phase1_ne_shiftEpoch.symm,
          hpaddedEpoch]
      have hshiftedEpoch : shifted registers.shiftEpoch = state registers.shiftEpoch := by
        rw [← hpreRun,
          preShiftUnitary_preservesOutside registers.preShift disabled
            hlayout.shiftEpoch_not_preShift]
        exact hdisabledEpoch
      have hrestoredEpoch : restoredPhase registers.shiftEpoch =
          state registers.shiftEpoch := by
        simp [restoredPhase, xorWireState, upd,
          hlayout.phase1_ne_shiftEpoch.symm, hshiftedEpoch]
      simp [spilled, terminalEpochSpillState, controlledSwapState, xorWireState,
        upd, hterminalQuotient,
        hshiftQuotient, hrestoredTerminal, hrestoredEpoch, hmatchFalse, hepoch]
  have hfinalTerminal : blockAForwardState registers state registers.terminal = false := by
    change matchXorState (terminalConditionWires registers)
      (terminalConditionValue registers) registers.terminal spilled
        registers.terminal = false
    simp [matchXorState, hspilledTerminal, hspilledCondition]
  have hfinalEpoch : blockAForwardState registers state registers.shiftEpoch = false := by
    change matchXorState (terminalConditionWires registers)
      (terminalConditionValue registers) registers.terminal spilled
        registers.shiftEpoch = false
    simp [matchXorState, upd, Ne.symm hterminalShift, hspilledEpoch]
  have hfinalControl : blockAForwardState registers state registers.control = false := by
    change matchXorState (terminalConditionWires registers)
      (terminalConditionValue registers) registers.terminal spilled
        registers.control = false
    simp [matchXorState, upd, hlayout.control_ne_terminal,
      hspilledControl, hcontrolFalse]
  intro wire hwire
  rw [← hlayout.aux_view] at hwire
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hwire
  by_cases hcontrol : wire = registers.control
  · rw [hcontrol, hcorrect.1]
    exact hfinalControl
  by_cases hepoch : wire = registers.shiftEpoch
  · rw [hepoch, hcorrect.1]
    exact hfinalEpoch
  have hsource : wire ∈ registers.sourceScratch := by
    simpa [hcontrol, hepoch] using hwire
  rw [← hlayout.scratch_view] at hsource
  simp only [List.mem_cons] at hsource
  by_cases hterminal : wire = registers.terminal
  · rw [hterminal, hcorrect.1]
    exact hfinalTerminal
  have hblockWire : wire ∈ registers.blockScratch := by
    simpa [hterminal] using hsource
  exact hcorrect.2 wire hblockWire

private theorem blockB1Forward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder)
    (hready : IndexedStepBorrowedReady registers state) :
    run (blockB1Forward registers n window) state =
        blockB1ForwardState registers n window state ∧
      IndexedStepBorrowedReady registers
        (run (blockB1Forward registers n window) state) := by
  have hcontrolFalse : state registers.control = false :=
    hready registers.control hlayout.control_mem_aux
  have hsourceClean : Clean (registers.terminal :: registers.blockScratch) state := by
    intro wire hwire
    apply hready wire
    apply hlayout.sourceScratch_mem_aux
    rw [← hlayout.scratch_view]
    exact hwire
  let predicate := rControlNonterminalPredicate [registers.phase1] 0
    registers.lengthRPrime registers.terminal state
  let enabled := rControlState [registers.phase1] 0 registers.control
    registers.lengthRPrime registers.terminal state
  have henabledRun : run (remainderSubControl registers) state = enabled := by
    simpa [remainderSubControl, toggleRControl, enabled, rControlState] using
      (run_rControlNonterminal [registers.phase1] 0 registers.control
        registers.lengthRPrime registers.terminal registers.blockScratch state
        hlayout.remainderSub hsourceClean)
  have hcontrolNePhase1 : registers.control ≠ registers.phase1 :=
    hlayout.aux_not_payload hlayout.control_mem_aux (by
      simp [indexedStepPayload])
  have henabledAway : ∀ wire ∈ registers.aux, wire ≠ registers.control →
      enabled wire = false := by
    intro wire haux hcontrol
    change rControlState [registers.phase1] 0 registers.control
      registers.lengthRPrime registers.terminal state wire = false
    rw [rControlState_preserves _ _ _ _ _ _ hcontrol]
    exact hready wire haux
  have henabledReady : IntervalReady (registers.remainder window) enabled := by
    intro wire hwire
    exact henabledAway wire (hlayout.remainder_scratch_sub_aux window wire hwire) (by
      intro equality
      subst wire
      exact hlayout.control_not_remainder_scratch window hwindow hwire)
  let changed := intervalAddSubState (registers.remainder window) n
    window.start window.stop .sub true .work1 enabled
  have hchangedRun : run
      (intervalAddSubUnitary (registers.remainder window) n window.start window.stop
        .sub true .work1) enabled = changed := by
    subst window
    simpa only [changed] using
      run_intervalAddSubUnitary_state
        (registers.remainder (certifiedActiveWindows n T).remainder) n
        (certifiedActiveWindows n T).remainder.start
        (certifiedActiveWindows n T).remainder.stop .sub true .work1 enabled
        hlayout.remainder (by simpa using henabledReady)
  have hchangedAway : ∀ wire ∈ registers.aux, wire ≠ registers.control →
      changed wire = false := by
    intro wire haux hcontrol
    rw [← hchangedRun]
    exact remainderInterval_clean_auxAwayControl registers n T window .sub true enabled
      hlayout hwindow henabledAway wire haux hcontrol
  have hchangedSourceClean : Clean
      (registers.terminal :: registers.blockScratch) changed := by
    intro wire hwire
    have hsource : wire ∈ registers.sourceScratch := by
      rw [← hlayout.scratch_view]
      exact hwire
    exact hchangedAway wire (hlayout.sourceScratch_mem_aux hsource)
      (by intro equality; subst wire; exact hlayout.control_not_sourceScratch hsource)
  have hchangedControl : changed registers.control = enabled registers.control := by
    rw [← hchangedRun]
    subst window
    exact intervalAddSubUnitary_preserves_control
      (registers.remainder (certifiedActiveWindows n T).remainder) n
      (certifiedActiveWindows n T).remainder.start
      (certifiedActiveWindows n T).remainder.stop .sub true .work1 enabled
      hlayout.remainder (by simpa using henabledReady)
  have hphase1 : changed registers.phase1 = state registers.phase1 := by
    rw [← hchangedRun,
      intervalAddSubUnitary_preservesOutside (registers.remainder window) n
        window.start window.stop .sub true .work1 enabled (by
          subst window
          exact hlayout.remainder) (hlayout.phase1_not_remainder window)]
    exact rControlState_preserves _ _ _ _ _ _ hcontrolNePhase1.symm
  have hlength : ∀ wire ∈ registers.lengthRPrime,
      changed wire = state wire := by
    intro wire hwire
    rw [← hchangedRun,
      intervalAddSubUnitary_preservesOutside (registers.remainder window) n
        window.start window.stop .sub true .work1 enabled (by
          subst window
          exact hlayout.remainder) (hlayout.lengthRPrime_not_remainder window hwire)]
    have hcontrolNotR : registers.control ∉ registers.lengthRPrime :=
      hlayout.remainderSub.control_not_r
    exact rControlState_preserves _ _ _ _ _ _
      (by intro equality; subst wire; exact hcontrolNotR hwire)
  have hterminalNePhase1 : registers.terminal ≠ registers.phase1 := by
    have hphysical := hlayout.terminalPhase
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false] at hphysical
    exact hphysical.1
  have hpredicate : rControlNonterminalPredicate [registers.phase1] 0
      registers.lengthRPrime registers.terminal changed = predicate := by
    change rControlNonterminalPredicate [registers.phase1] 0
        registers.lengthRPrime registers.terminal changed =
      rControlNonterminalPredicate [registers.phase1] 0
        registers.lengthRPrime registers.terminal state
    exact rControlNonterminalPredicate_congr [registers.phase1] 0
      registers.lengthRPrime registers.terminal changed state
      (by simpa only [List.mem_singleton] using hterminalNePhase1)
      (by
        intro wire hwire
        simp only [List.mem_singleton] at hwire
        subst wire
        exact hphase1)
      hlength
  have henabledControl : enabled registers.control = predicate := by
    simp [enabled, rControlState, predicate, hcontrolFalse]
  have hfinalRun : run (remainderSubControl registers) changed =
      rControlState [registers.phase1] 0 registers.control
        registers.lengthRPrime registers.terminal changed := by
    simpa [remainderSubControl, toggleRControl, rControlState] using
      (run_rControlNonterminal [registers.phase1] 0 registers.control
        registers.lengthRPrime registers.terminal registers.blockScratch changed
        hlayout.remainderSub hchangedSourceClean)
  have hfinalControl :
      rControlState [registers.phase1] 0 registers.control
          registers.lengthRPrime registers.terminal changed registers.control = false := by
    simp [rControlState, hchangedControl, henabledControl, hpredicate]
  have hrun : run (blockB1Forward registers n window) state =
      blockB1ForwardState registers n window state := by
    simp only [blockB1Forward, Classical.run_append]
    rw [henabledRun, hchangedRun, hfinalRun]
    rfl
  constructor
  · exact hrun
  · rw [hrun]
    intro wire haux
    by_cases hcontrol : wire = registers.control
    · subst wire
      exact hfinalControl
    · change rControlState [registers.phase1] 0 registers.control
        registers.lengthRPrime registers.terminal changed wire = false
      rw [rControlState_preserves _ _ _ _ _ _ hcontrol]
      exact hchangedAway wire haux hcontrol

private theorem blockB2_correct
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepBorrowedReady registers state) :
    run (blockB2 registers) state = blockB2State registers state ∧
      IndexedStepBorrowedReady registers (run (blockB2 registers) state) := by
  have hcontrolFalse : state registers.control = false :=
    hready registers.control hlayout.control_mem_aux
  have hsourceClean : Clean (registers.terminal :: registers.blockScratch) state := by
    intro wire hwire
    apply hready wire
    apply hlayout.sourceScratch_mem_aux
    rw [← hlayout.scratch_view]
    exact hwire
  let predicate := rControlNonterminalPredicate
    [registers.phase1, registers.phase2] 2 registers.lengthRPrime registers.terminal state
  let enabled := rControlState [registers.phase1, registers.phase2] 2
    registers.control registers.lengthRPrime registers.terminal state
  have henabledRun : run (remainderPhase2Control registers) state = enabled := by
    simpa [remainderPhase2Control, toggleRControl, enabled, rControlState] using
      (run_rControlNonterminal [registers.phase1, registers.phase2] 2 registers.control
        registers.lengthRPrime registers.terminal registers.blockScratch state
        hlayout.remainderPhase2 hsourceClean)
  have hcontrolNePhase1 : registers.control ≠ registers.phase1 :=
    hlayout.aux_not_payload hlayout.control_mem_aux (by simp [indexedStepPayload])
  have hcontrolNePhase2 : registers.control ≠ registers.phase2 :=
    hlayout.aux_not_payload hlayout.control_mem_aux (by simp [indexedStepPayload])
  have hcontrolNeSign : registers.control ≠ registers.sign := by
    have hphysical := hlayout.controlSign
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hphysical
    exact hphysical.1
  have henabledAway : ∀ wire ∈ registers.aux, wire ≠ registers.control →
      enabled wire = false := by
    intro wire haux hcontrol
    change rControlState [registers.phase1, registers.phase2] 2 registers.control
      registers.lengthRPrime registers.terminal state wire = false
    rw [rControlState_preserves _ _ _ _ _ _ hcontrol]
    exact hready wire haux
  let changed := xorWireState registers.control registers.sign enabled
  have hchangedRun : run ([.CX registers.control registers.sign] : Circuit) enabled =
      changed := by
    exact run_xorWireState registers.control registers.sign enabled
  have hchangedAway : ∀ wire ∈ registers.aux, wire ≠ registers.control →
      changed wire = false := by
    intro wire haux hcontrol
    have hsign : wire ≠ registers.sign :=
      hlayout.aux_not_payload (auxWire := wire) (payloadWire := registers.sign)
        haux (by simp [indexedStepPayload])
    change xorWireState registers.control registers.sign enabled wire = false
    simp [xorWireState, upd, hsign, henabledAway wire haux hcontrol]
  have hchangedSourceClean : Clean
      (registers.terminal :: registers.blockScratch) changed := by
    intro wire hwire
    have hsource : wire ∈ registers.sourceScratch := by
      rw [← hlayout.scratch_view]
      exact hwire
    exact hchangedAway wire (hlayout.sourceScratch_mem_aux hsource)
      (by intro equality; subst wire; exact hlayout.control_not_sourceScratch hsource)
  have hphase1NeSign : registers.phase1 ≠ registers.sign :=
    hlayout.phase1_ne_after (by simp [indexedStepAfterPhase1])
  have hphase2NeSign : registers.phase2 ≠ registers.sign :=
    hlayout.phase2_ne_after (by simp [indexedStepAfterPhase2])
  have hphase1 : changed registers.phase1 = state registers.phase1 := by
    change xorWireState registers.control registers.sign enabled registers.phase1 =
      state registers.phase1
    rw [show xorWireState registers.control registers.sign enabled registers.phase1 =
      enabled registers.phase1 by simp [xorWireState, upd, hphase1NeSign]]
    exact rControlState_preserves _ _ _ _ _ _ hcontrolNePhase1.symm
  have hphase2 : changed registers.phase2 = state registers.phase2 := by
    change xorWireState registers.control registers.sign enabled registers.phase2 =
      state registers.phase2
    rw [show xorWireState registers.control registers.sign enabled registers.phase2 =
      enabled registers.phase2 by simp [xorWireState, upd, hphase2NeSign]]
    exact rControlState_preserves _ _ _ _ _ _ hcontrolNePhase2.symm
  have hlength : ∀ wire ∈ registers.lengthRPrime,
      changed wire = state wire := by
    intro wire hwire
    have hwireNeControl : wire ≠ registers.control := by
      intro equality
      subst wire
      exact hlayout.remainderPhase2.control_not_r hwire
    have hwireNeSign : wire ≠ registers.sign := by
      exact hlayout.lengthRPrime_ne_outside hwire (Or.inl (by
        simp [indexedStepBeforeLengthRPrime]))
    change xorWireState registers.control registers.sign enabled wire = state wire
    rw [show xorWireState registers.control registers.sign enabled wire = enabled wire by
      simp [xorWireState, upd, hwireNeSign]]
    exact rControlState_preserves _ _ _ _ _ _ hwireNeControl
  have hterminalNotConditions : registers.terminal ∉
      [registers.phase1, registers.phase2] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    constructor
    · exact hlayout.aux_not_payload
        (hlayout.sourceScratch_mem_aux (by rw [← hlayout.scratch_view]; simp))
        (by simp [indexedStepPayload])
    · exact hlayout.aux_not_payload
        (hlayout.sourceScratch_mem_aux (by rw [← hlayout.scratch_view]; simp))
        (by simp [indexedStepPayload])
  have hpredicate : rControlNonterminalPredicate
      [registers.phase1, registers.phase2] 2 registers.lengthRPrime
        registers.terminal changed = predicate := by
    change rControlNonterminalPredicate [registers.phase1, registers.phase2] 2
        registers.lengthRPrime registers.terminal changed =
      rControlNonterminalPredicate [registers.phase1, registers.phase2] 2
        registers.lengthRPrime registers.terminal state
    exact rControlNonterminalPredicate_congr _ _ _ _ _ _ hterminalNotConditions
      (by
        intro wire hwire
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
        rcases hwire with rfl | rfl
        · exact hphase1
        · exact hphase2)
      hlength
  have henabledControl : enabled registers.control = predicate := by
    simp [enabled, rControlState, predicate, hcontrolFalse]
  have hchangedControl : changed registers.control = enabled registers.control := by
    simp [changed, xorWireState, upd, hcontrolNeSign]
  have hfinalRun : run (remainderPhase2Control registers) changed =
      rControlState [registers.phase1, registers.phase2] 2 registers.control
        registers.lengthRPrime registers.terminal changed := by
    simpa [remainderPhase2Control, toggleRControl, rControlState] using
      (run_rControlNonterminal [registers.phase1, registers.phase2] 2 registers.control
        registers.lengthRPrime registers.terminal registers.blockScratch changed
        hlayout.remainderPhase2 hchangedSourceClean)
  have hfinalControl :
      rControlState [registers.phase1, registers.phase2] 2 registers.control
          registers.lengthRPrime registers.terminal changed registers.control = false := by
    simp [rControlState, hchangedControl, henabledControl, hpredicate]
  have hrun : run (blockB2 registers) state = blockB2State registers state := by
    simp only [blockB2, Classical.run_append]
    rw [henabledRun, hchangedRun, hfinalRun]
    rfl
  constructor
  · exact hrun
  · rw [hrun]
    intro wire haux
    by_cases hcontrol : wire = registers.control
    · subst wire
      exact hfinalControl
    · change rControlState [registers.phase1, registers.phase2] 2 registers.control
        registers.lengthRPrime registers.terminal changed wire = false
      rw [rControlState_preserves _ _ _ _ _ _ hcontrol]
      exact hchangedAway wire haux hcontrol

private theorem remainderRestoreControl_correct
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hclean : ∀ wire ∈ registers.aux, wire ≠ registers.control →
      state wire = false) :
    run (remainderRestoreControl registers) state =
        remainderRestoreControlState registers state ∧
      ∀ wire ∈ registers.aux, wire ≠ registers.control →
        remainderRestoreControlState registers state wire = false := by
  let marked := andXorWireState registers.phase2 registers.sign registers.terminal state
  let enabled := rControlState [registers.phase1, registers.terminal] 0
    registers.control registers.lengthRPrime (registers.blockScratch.getD 0 0) marked
  let middle := toggleRControl registers ([registers.phase1, registers.terminal]) 0
    (registers.blockScratch.getD 0 0) (registers.blockScratch.drop 1)
  have hterminalSource : registers.terminal ∈ registers.sourceScratch := by
    rw [← hlayout.scratch_view]
    simp
  have hterminalAux : registers.terminal ∈ registers.aux :=
    hlayout.sourceScratch_mem_aux hterminalSource
  have hterminalNeControl : registers.terminal ≠ registers.control := by
    intro equality
    exact hlayout.control_not_sourceScratch (equality ▸ hterminalSource)
  have hphase2NeTerminal : registers.phase2 ≠ registers.terminal := by
    have hphysical := hlayout.remainderRestoreCCX
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at hphysical
    exact hphysical.1.2
  have hsignNeTerminal : registers.sign ≠ registers.terminal := by
    have hphysical := hlayout.remainderRestoreCCX
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at hphysical
    exact hphysical.2.1
  have hcontrolNePhase2 : registers.control ≠ registers.phase2 :=
    hlayout.aux_not_payload hlayout.control_mem_aux (by simp [indexedStepPayload])
  have hcontrolNeSign : registers.control ≠ registers.sign :=
    hlayout.aux_not_payload hlayout.control_mem_aux (by simp [indexedStepPayload])
  have hmarkedRun : run ([.CCX registers.phase2 registers.sign registers.terminal] :
      Circuit) state = marked := by
    exact run_andXorWireState registers.phase2 registers.sign registers.terminal state
  have hblockPositive : 0 < registers.blockScratch.length := by
    have := hlayout.terminalPaddingCapacity
    omega
  have hmarkedClean : Clean
      (registers.blockScratch.getD 0 0 :: registers.blockScratch.drop 1) marked := by
    intro wire hwire
    have hblock : wire ∈ registers.blockScratch := by
      rcases List.mem_cons.mp hwire with hzero | htail
      · rw [hzero]
        exact indexedStep_getD_mem registers.blockScratch 0 0 hblockPositive
      · exact List.mem_of_mem_drop htail
    have haux := hlayout.blockScratch_mem_aux hblock
    have hcontrol : wire ≠ registers.control := by
      intro equality
      subst wire
      exact hlayout.control_not_sourceScratch
        (List.mem_of_mem_drop hblock)
    have hterminal : wire ≠ registers.terminal := by
      intro equality
      subst wire
      exact hlayout.terminal_not_blockScratch hblock
    change andXorWireState registers.phase2 registers.sign registers.terminal state wire =
      false
    simp [andXorWireState, upd, hterminal, hclean wire haux hcontrol]
  have henabledRun : run middle marked = enabled := by
    simpa [middle, toggleRControl, enabled, rControlState] using
      (run_rControlNonterminal [registers.phase1, registers.terminal] 0
        registers.control registers.lengthRPrime (registers.blockScratch.getD 0 0)
        (registers.blockScratch.drop 1) marked hlayout.remainderRestore hmarkedClean)
  have hfinalRun : run ([.CCX registers.phase2 registers.sign registers.terminal] :
      Circuit) enabled =
      andXorWireState registers.phase2 registers.sign registers.terminal enabled := by
    exact run_andXorWireState registers.phase2 registers.sign registers.terminal enabled
  have hinnerRun : run
      (.CCX registers.phase2 registers.sign registers.terminal :: middle) state =
      enabled := by
    rw [Classical.run_cons]
    rw [show Classical.applyGate
        (.CCX registers.phase2 registers.sign registers.terminal) state = marked by
      simpa [Classical.run] using hmarkedRun]
    exact henabledRun
  have hrun : run (remainderRestoreControl registers) state =
      remainderRestoreControlState registers state := by
    simp only [remainderRestoreControl, Classical.run_append]
    rw [hinnerRun, hfinalRun]
    rfl
  constructor
  · exact hrun
  · intro wire haux hcontrol
    by_cases hterminal : wire = registers.terminal
    · subst wire
      have hterminalFalse : state registers.terminal = false :=
        hclean registers.terminal hterminalAux hterminalNeControl
      simp [remainderRestoreControlState, andXorWireState,
        rControlState, upd, hterminalFalse, hterminalNeControl,
        hphase2NeTerminal, hsignNeTerminal,
        Ne.symm hcontrolNePhase2, Ne.symm hcontrolNeSign]
    · have hwireFalse := hclean wire haux hcontrol
      simp [remainderRestoreControlState, andXorWireState,
        rControlState, upd, hterminal, hcontrol, hwireFalse]

private theorem blockB3Forward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder)
    (hready : IndexedStepBorrowedReady registers state) :
    run (blockB3Forward registers n window) state =
        blockB3ForwardState registers n window state ∧
      IndexedStepBorrowedReady registers
        (run (blockB3Forward registers n window) state) := by
  have hinitialAway : ∀ wire ∈ registers.aux, wire ≠ registers.control →
      state wire = false := by
    intro wire hwire _
    exact hready wire hwire
  let enabled := remainderRestoreControlState registers state
  have hfirst := remainderRestoreControl_correct registers n T state hlayout hinitialAway
  have hfirstRun : run (remainderRestoreControl registers) state = enabled := by
    simpa only [enabled] using hfirst.1
  have henabledAway : ∀ wire ∈ registers.aux, wire ≠ registers.control →
      enabled wire = false := by
    simpa only [enabled] using hfirst.2
  have henabledReady : IntervalReady (registers.remainder window) enabled := by
    intro wire hwire
    exact henabledAway wire (hlayout.remainder_scratch_sub_aux window wire hwire) (by
      intro equality
      subst wire
      exact hlayout.control_not_remainder_scratch window hwindow hwire)
  let changed := intervalAddSubState (registers.remainder window) n
    window.start window.stop .add false .work1 enabled
  have hchangedRun : run
      (intervalAddSubUnitary (registers.remainder window) n window.start window.stop
        .add false .work1) enabled = changed := by
    subst window
    simpa only [changed] using
      run_intervalAddSubUnitary_state
        (registers.remainder (certifiedActiveWindows n T).remainder) n
        (certifiedActiveWindows n T).remainder.start
        (certifiedActiveWindows n T).remainder.stop .add false .work1 enabled
        hlayout.remainder (by simpa using henabledReady)
  have hchangedAway : ∀ wire ∈ registers.aux, wire ≠ registers.control →
      changed wire = false := by
    intro wire haux hcontrol
    rw [← hchangedRun]
    exact remainderInterval_clean_auxAwayControl registers n T window .add false enabled
      hlayout hwindow henabledAway wire haux hcontrol
  have hsecond := remainderRestoreControl_correct registers n T changed hlayout hchangedAway
  have hterminalSource : registers.terminal ∈ registers.sourceScratch := by
    rw [← hlayout.scratch_view]
    simp
  have hterminalAux : registers.terminal ∈ registers.aux :=
    hlayout.sourceScratch_mem_aux hterminalSource
  have hterminalNeControl : registers.terminal ≠ registers.control := by
    intro equality
    exact hlayout.control_not_sourceScratch (equality ▸ hterminalSource)
  have hcontrolNePhase1 : registers.control ≠ registers.phase1 :=
    hlayout.aux_not_payload hlayout.control_mem_aux (by simp [indexedStepPayload])
  have hcontrolNePhase2 : registers.control ≠ registers.phase2 :=
    hlayout.aux_not_payload hlayout.control_mem_aux (by simp [indexedStepPayload])
  have hcontrolNeSign : registers.control ≠ registers.sign :=
    hlayout.aux_not_payload hlayout.control_mem_aux (by simp [indexedStepPayload])
  have hterminalNePhase1 : registers.terminal ≠ registers.phase1 :=
    hlayout.aux_not_payload hterminalAux (by simp [indexedStepPayload])
  have hterminalNePhase2 : registers.terminal ≠ registers.phase2 :=
    hlayout.aux_not_payload hterminalAux (by simp [indexedStepPayload])
  have hterminalNeSign : registers.terminal ≠ registers.sign :=
    hlayout.aux_not_payload hterminalAux (by simp [indexedStepPayload])
  have hphase1 : changed registers.phase1 = state registers.phase1 := by
    rw [← hchangedRun,
      intervalAddSubUnitary_preservesOutside (registers.remainder window) n
        window.start window.stop .add false .work1 enabled (by
          subst window
          exact hlayout.remainder) (hlayout.phase1_not_remainder window)]
    exact remainderRestoreControlState_preserves registers state
      hterminalNePhase1.symm hcontrolNePhase1.symm
  have hphase2 : changed registers.phase2 = state registers.phase2 := by
    rw [← hchangedRun,
      intervalAddSubUnitary_preservesOutside (registers.remainder window) n
        window.start window.stop .add false .work1 enabled (by
          subst window
          exact hlayout.remainder) (hlayout.phase2_not_remainder window)]
    exact remainderRestoreControlState_preserves registers state
      hterminalNePhase2.symm hcontrolNePhase2.symm
  have hsign : changed registers.sign = state registers.sign := by
    rw [← hchangedRun]
    have hpreserves : run
        (intervalAddSubUnitary (registers.remainder window) n window.start window.stop
          .add false .work1) enabled registers.sign = enabled registers.sign := by
      subst window
      simpa [IndexedStepRegisters.remainder, IndexedStepRegisters.remainderBase] using
        intervalAddSubUnitary_preserves_sign_of_false
          (registers.remainder (certifiedActiveWindows n T).remainder) n
          (certifiedActiveWindows n T).remainder.start
          (certifiedActiveWindows n T).remainder.stop .add .work1 enabled
          hlayout.remainder (by simpa using henabledReady)
    rw [hpreserves]
    exact remainderRestoreControlState_preserves registers state
      hterminalNeSign.symm hcontrolNeSign.symm
  have hlength : ∀ wire ∈ registers.lengthRPrime,
      changed wire = state wire := by
    intro wire hwire
    rw [← hchangedRun,
      intervalAddSubUnitary_preservesOutside (registers.remainder window) n
        window.start window.stop .add false .work1 enabled (by
          subst window
          exact hlayout.remainder) (hlayout.lengthRPrime_not_remainder window hwire)]
    have hwireNeTerminal : wire ≠ registers.terminal := by
      exact (hlayout.aux_not_payload hterminalAux (by
        simp [indexedStepPayload, hwire])).symm
    have hwireNeControl : wire ≠ registers.control := by
      intro equality
      subst wire
      exact hlayout.remainderRestore.control_not_r hwire
    exact remainderRestoreControlState_preserves registers state
      hwireNeTerminal hwireNeControl
  have hinitialTerminal : state registers.terminal = false :=
    hready registers.terminal hterminalAux
  have hchangedTerminal : changed registers.terminal = false :=
    hchangedAway registers.terminal hterminalAux hterminalNeControl
  let markedInitial := andXorWireState registers.phase2 registers.sign
    registers.terminal state
  let markedChanged := andXorWireState registers.phase2 registers.sign
    registers.terminal changed
  let predicateInitial := rControlNonterminalPredicate
    [registers.phase1, registers.terminal] 0 registers.lengthRPrime
      (registers.blockScratch.getD 0 0) markedInitial
  let predicateChanged := rControlNonterminalPredicate
    [registers.phase1, registers.terminal] 0 registers.lengthRPrime
      (registers.blockScratch.getD 0 0) markedChanged
  have hmarkedPhase1 : markedChanged registers.phase1 =
      markedInitial registers.phase1 := by
    simp [markedChanged, markedInitial, andXorWireState, upd,
      hterminalNePhase1.symm, hphase1]
  have hmarkedTerminal : markedChanged registers.terminal =
      markedInitial registers.terminal := by
    simp [markedChanged, markedInitial, andXorWireState,
      hinitialTerminal, hchangedTerminal, hphase2, hsign]
  have hmarkedLength : ∀ wire ∈ registers.lengthRPrime,
      markedChanged wire = markedInitial wire := by
    intro wire hwire
    have hwireNeTerminal : wire ≠ registers.terminal :=
      (hlayout.aux_not_payload hterminalAux (by
        simp [indexedStepPayload, hwire])).symm
    simp [markedChanged, markedInitial, andXorWireState, upd,
      hwireNeTerminal, hlength wire hwire]
  have hblockPositive : 0 < registers.blockScratch.length := by
    have := hlayout.terminalPaddingCapacity
    omega
  have hzeroBlock : registers.blockScratch.getD 0 0 ∈ registers.blockScratch :=
    indexedStep_getD_mem registers.blockScratch 0 0 hblockPositive
  have hzeroNotConditions : registers.blockScratch.getD 0 0 ∉
      [registers.phase1, registers.terminal] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    constructor
    · exact hlayout.aux_not_payload (hlayout.blockScratch_mem_aux hzeroBlock)
        (by simp [indexedStepPayload])
    · exact fun equality ↦ hlayout.terminal_not_blockScratch
        (equality ▸ hzeroBlock)
  have hpredicate : predicateChanged = predicateInitial := by
    exact rControlNonterminalPredicate_congr _ _ _ _ _ _ hzeroNotConditions
      (by
        intro wire hwire
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
        rcases hwire with rfl | rfl
        · exact hmarkedPhase1
        · exact hmarkedTerminal)
      hmarkedLength
  have hinitialControl : state registers.control = false :=
    hready registers.control hlayout.control_mem_aux
  have henabledControl : enabled registers.control = predicateInitial := by
    simp [enabled, remainderRestoreControlState, markedInitial, predicateInitial,
      andXorWireState, rControlState, upd, hterminalNeControl,
      hterminalNeControl.symm, hcontrolNePhase2.symm,
      hcontrolNeSign.symm, hterminalNePhase2.symm,
      hterminalNeSign.symm, hinitialControl]
  have hchangedControl : changed registers.control = enabled registers.control := by
    rw [← hchangedRun]
    subst window
    exact intervalAddSubUnitary_preserves_control
      (registers.remainder (certifiedActiveWindows n T).remainder) n
      (certifiedActiveWindows n T).remainder.start
      (certifiedActiveWindows n T).remainder.stop .add false .work1 enabled
      hlayout.remainder (by simpa using henabledReady)
  have hfinalControl : remainderRestoreControlState registers changed
      registers.control = false := by
    have hshape : remainderRestoreControlState registers changed registers.control =
        Bool.xor (changed registers.control) predicateChanged := by
      simp [remainderRestoreControlState, markedChanged, predicateChanged,
        andXorWireState, rControlState, upd, hterminalNeControl,
        hterminalNeControl.symm, hcontrolNePhase2.symm,
        hcontrolNeSign.symm, hterminalNePhase2.symm,
        hterminalNeSign.symm]
    rw [hshape, hchangedControl, henabledControl, hpredicate]
    simp
  have hrun : run (blockB3Forward registers n window) state =
      blockB3ForwardState registers n window state := by
    simp only [blockB3Forward, Classical.run_append]
    rw [hfirstRun, hchangedRun, hsecond.1]
    rfl
  constructor
  · exact hrun
  · rw [hrun]
    intro wire haux
    by_cases hcontrol : wire = registers.control
    · subst wire
      exact hfinalControl
    · exact hsecond.2 wire haux hcontrol

private theorem blockBForward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder)
    (hready : IndexedStepBorrowedReady registers state) :
    run (blockBForward registers n window) state =
        blockBForwardState registers n window state ∧
      IndexedStepBorrowedReady registers
        (run (blockBForward registers n window) state) := by
  have hfirst := blockB1Forward_correct registers n T window state hlayout hwindow hready
  have hfirstReady : IndexedStepBorrowedReady registers
      (blockB1ForwardState registers n window state) := by
    rw [← hfirst.1]
    exact hfirst.2
  have hsecond := blockB2_correct registers n T
    (blockB1ForwardState registers n window state) hlayout hfirstReady
  have hsecondReady : IndexedStepBorrowedReady registers
      (blockB2State registers (blockB1ForwardState registers n window state)) := by
    rw [← hsecond.1]
    exact hsecond.2
  have hthird := blockB3Forward_correct registers n T window
    (blockB2State registers (blockB1ForwardState registers n window state))
      hlayout hwindow hsecondReady
  have hrun : run (blockBForward registers n window) state =
      blockBForwardState registers n window state := by
    simp only [blockBForward, Classical.run_append]
    rw [hfirst.1, hsecond.1, hthird.1]
    rfl
  constructor
  · exact hrun
  · rw [hrun]
    change IndexedStepBorrowedReady registers
      (blockB3ForwardState registers n window
        (blockB2State registers (blockB1ForwardState registers n window state)))
    rw [← hthird.1]
    exact hthird.2

private theorem blockCForward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepBorrowedReady registers state) :
    run (blockCForward registers) state = blockCForwardState registers state ∧
      IndexedStepReady registers (run (blockCForward registers) state) := by
  let terminalMatch := registerMatches (terminalConditionWires registers)
    (terminalConditionValue registers) state
  let marked := matchXorState (terminalConditionWires registers)
    (terminalConditionValue registers) registers.terminal state
  have hblock : Clean registers.blockScratch state := by
    intro wire hwire
    exact hready wire (hlayout.blockScratch_mem_aux hwire)
  have hmarkedRun : run (toggleTerminal registers) state = marked := by
    simpa [toggleTerminal, marked, matchXorState] using
      run_computeControl (terminalConditionWires registers)
        (terminalConditionValue registers) registers.terminal
        registers.blockScratch state hlayout.terminalControl hblock
  have hmarkedBlock : Clean registers.blockScratch marked := by
    simpa [marked, matchXorState] using
      clean_upd_not_mem hblock hlayout.terminal_not_blockScratch
  let restored := terminalEpochRestoreState registers.terminal registers.shiftEpoch
    registers.quotientLow marked
  have hrestoredRun : run
      (terminalEpochRestore registers.terminal registers.shiftEpoch registers.quotientLow)
      marked = restored := by
    simpa only [restored] using run_terminalEpochRestoreState registers.terminal
      registers.shiftEpoch registers.quotientLow marked hlayout.terminalEpoch
  have hrestoredBlock : Clean registers.blockScratch restored := by
    intro wire hwire
    have houtside := hlayout.blockScratch_outside_terminalEpoch wire hwire
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at houtside
    change restored wire = false
    rw [show restored wire = marked wire by
      exact terminalEpochRestoreState_preserves _ _ _ _ houtside.2.1 houtside.2.2]
    exact hmarkedBlock wire hwire
  have hrestoredCondition : registerMatches (terminalConditionWires registers)
      (terminalConditionValue registers) restored = terminalMatch := by
    change registerMatches (terminalConditionWires registers)
        (terminalConditionValue registers) restored =
      registerMatches (terminalConditionWires registers)
        (terminalConditionValue registers) state
    apply registerMatches_congr
    intro wire hwire
    have hterminal : wire ≠ registers.terminal := by
      intro equality
      subst wire
      exact hlayout.terminal_not_condition hwire
    have hshift : wire ≠ registers.shiftEpoch := by
      intro equality
      subst wire
      exact hlayout.shiftEpoch_not_condition hwire
    have hquotient : wire ≠ registers.quotientLow := by
      intro equality
      subst wire
      exact hlayout.quotientLow_not_condition hwire
    rw [show restored wire = marked wire by
      exact terminalEpochRestoreState_preserves _ _ _ _ hshift hquotient]
    simp [marked, matchXorState, upd, hterminal]
  have hunmarkedRun : run (toggleTerminal registers) restored =
      matchXorState (terminalConditionWires registers)
        (terminalConditionValue registers) registers.terminal restored := by
    simpa [toggleTerminal, matchXorState] using
      run_computeControl (terminalConditionWires registers)
        (terminalConditionValue registers) registers.terminal
        registers.blockScratch restored hlayout.terminalControl hrestoredBlock
  have hterminalAux : registers.terminal ∈ registers.aux :=
    hlayout.sourceScratch_mem_aux (by rw [← hlayout.scratch_view]; simp)
  have hterminalFalse : state registers.terminal = false :=
    hready registers.terminal hterminalAux
  have hmarkedTerminal : marked registers.terminal = terminalMatch := by
    simp [marked, matchXorState, terminalMatch, hterminalFalse]
  have hterminalEpoch := hlayout.terminalEpoch
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hterminalEpoch
  have hrestoredTerminal : restored registers.terminal = terminalMatch := by
    rw [show restored registers.terminal = marked registers.terminal by
      exact terminalEpochRestoreState_preserves _ _ _ _
        hterminalEpoch.1.1 hterminalEpoch.1.2]
    exact hmarkedTerminal
  have hfinalTerminal : blockCForwardState registers state registers.terminal = false := by
    change matchXorState (terminalConditionWires registers)
      (terminalConditionValue registers) registers.terminal restored
        registers.terminal = false
    simp [matchXorState, hrestoredTerminal, hrestoredCondition]
  have hcontrolFalse : state registers.control = false :=
    hready registers.control hlayout.control_mem_aux
  have hmarkedControl : marked registers.control = false := by
    simp [marked, matchXorState, upd, hlayout.control_ne_terminal, hcontrolFalse]
  have hrestoredControl : restored registers.control = false := by
    rw [show restored registers.control = marked registers.control by
      exact terminalEpochRestoreState_preserves _ _ _ _
        hlayout.control_ne_shiftEpoch hlayout.control_ne_quotientLow]
    exact hmarkedControl
  have hfinalControl : blockCForwardState registers state registers.control = false := by
    change matchXorState (terminalConditionWires registers)
      (terminalConditionValue registers) registers.terminal restored
        registers.control = false
    simp [matchXorState, upd, hlayout.control_ne_terminal, hrestoredControl]
  have hfinalBlock : Clean registers.blockScratch (blockCForwardState registers state) := by
    intro wire hwire
    have hterminal : wire ≠ registers.terminal := by
      intro equality
      subst wire
      exact hlayout.terminal_not_blockScratch hwire
    change matchXorState (terminalConditionWires registers)
      (terminalConditionValue registers) registers.terminal restored wire = false
    simp [matchXorState, upd, hterminal, hrestoredBlock wire hwire]
  have hrun : run (blockCForward registers) state =
      blockCForwardState registers state := by
    simp only [blockCForward, Classical.run_append]
    rw [hmarkedRun, hrestoredRun, hunmarkedRun]
    rfl
  constructor
  · exact hrun
  · rw [hrun]
    intro wire hwire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons] at hwire
    rcases hwire with rfl | hsource
    · exact hfinalControl
    · rw [← hlayout.scratch_view] at hsource
      simp only [List.mem_cons] at hsource
      rcases hsource with rfl | hblockWire
      · exact hfinalTerminal
      · exact hfinalBlock wire hblockWire

private theorem run_quotientSwapUnitary_indexedState
    (registers : QuotientSwapRegisters) {k K : Nat} (state : BasisState)
    (hlayout : QuotientSwapLayout registers k K)
    (hready : QuotientSwapReady registers state) :
    run (quotientSwapUnitary registers k K) state =
      indexedQuotientSwapState registers k K state := by
  let afterAdd := run
    (cuccaroAdd registers.lengthT registers.lengthQ
      (registers.carry k K)) state
  let prepared := run
    (addConstant registers.lengthQ registers.constantScratch
      (registers.carry k K) 3) afterAdd
  let purePrepared := quotientPreparedState registers state
  have hcorrect := quotientSwapUnitary_correct registers state hlayout hready
  have hbits : wireValues registers.lengthQ prepared =
      quotientPreparedBits registers state := by
    simpa [afterAdd, prepared, quotientPreparedBits] using hcorrect.2.2.1
  have hlength : (quotientPreparedBits registers state).length =
      registers.lengthQ.length := by
    have := congrArg List.length hbits
    simpa [wireValues] using this.symm
  have hlengthQNodup : registers.lengthQ.Nodup := by
    have hphysical := hlayout.physical
    rw [QuotientSwapRegisters.allWires] at hphysical
    have hrest := (List.nodup_append.mp hphysical).2.1
    have harithmetic := (List.nodup_append.mp hrest).2.1
    have hqScratch := (List.nodup_append.mp harithmetic).2.1
    exact (List.nodup_append.mp hqScratch).1
  have hpureBits : wireValues registers.lengthQ purePrepared =
      quotientPreparedBits registers state := by
    exact indexedWireValues_writeWireValues registers.lengthQ
      (quotientPreparedBits registers state) state hlengthQNodup hlength
  have hroute : (quotientSwapTree registers k K).routeLabel prepared =
      (quotientSwapTree registers k K).routeLabel purePrepared := by
    apply indexedRouteLabel_congr
    intro wire hwire
    have hlengthWire := quotientSwapTree_indexWires_mem_lengthQ registers
      hlayout.k_le_K hlayout.index_width wire hwire
    exact indexedWireValues_eq_at registers.lengthQ prepared purePrepared
      (hbits.trans hpureBits.symm) hlengthWire
  rw [hcorrect.1, hroute]
  rfl

private theorem indexedQuotientWorkAt_mem_any
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) (label : Nat) :
    registers.workAt k label ∈ registers.work1 := by
  have hpositive : 0 < registers.work1.length := by
    rw [hlayout.work1_length]
    omega
  by_cases hindex : label - k < registers.work1.length
  · exact indexedStep_getD_mem registers.work1 (label - k)
      (registers.work1.getD 0 0) hindex
  · rw [QuotientSwapRegisters.workAt,
      List.getD_eq_default registers.work1 (registers.work1.getD 0 0)
        (Nat.le_of_not_gt hindex)]
    exact indexedStep_getD_mem registers.work1 0 0 hpositive

private theorem indexedQuotientSwapState_preserves
    (registers : QuotientSwapRegisters) {k K : Nat}
    (state : BasisState) (hlayout : QuotientSwapLayout registers k K)
    {wire : Wire} (hsign : wire ≠ registers.sign)
    (hwork : wire ∉ registers.work1) :
    indexedQuotientSwapState registers k K state wire = state wire := by
  have hworkAt : wire ≠ registers.workAt k
      ((quotientSwapTree registers k K).routeLabel
        (quotientPreparedState registers state)) := by
    intro equality
    subst wire
    exact hwork (indexedQuotientWorkAt_mem_any registers hlayout _)
  unfold indexedQuotientSwapState quotientSwapState
  split <;> simp [upd, hsign, hworkAt]

private theorem blockD1Forward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state) :
    run (circuit! {
      phase2LengthControl registers;
      controlledIncrement registers.control registers.lengthQ (lengthCarries registers);
      phase2LengthControl registers
    }) state = blockD1ForwardState registers state ∧
      IndexedStepReady registers
        (run (circuit! {
          phase2LengthControl registers;
          controlledIncrement registers.control registers.lengthQ
            (lengthCarries registers);
          phase2LengthControl registers
        }) state) := by
  have hsource : Clean registers.sourceScratch state := by
    intro wire hwire
    exact hready wire (by
      simp [IndexedStepRegisters.sharedScratch, hwire])
  let enabled := matchXorState [registers.phase1, registers.phase2] 2
    registers.control state
  have henabled := run_computeControl_state [registers.phase1, registers.phase2] 2
    registers.control registers.sourceScratch state hlayout.phase2Length hsource
  have henabledRun : run (phase2LengthControl registers) state = enabled := by
    simpa [phase2LengthControl, enabled] using henabled.1
  have henabledSource : Clean registers.sourceScratch enabled := by
    simpa only [enabled] using henabled.2
  have hcarries : Clean (lengthCarries registers) enabled := by
    intro wire hwire
    exact henabledSource wire (List.mem_of_mem_take hwire)
  let changed := indexedIncrementWordState (enabled registers.control)
    registers.lengthQ enabled
  have hchangedRun : run
      (controlledIncrement registers.control registers.lengthQ
        (lengthCarries registers)) enabled = changed := by
    simpa only [changed] using run_controlledIncrement_indexedState
      registers.control registers.lengthQ (lengthCarries registers) enabled
      hlayout.lengthCarryCapacity hlayout.lengthCarryPhysical hcarries
  have hchangedSource : Clean registers.sourceScratch changed := by
    intro wire hwire
    have hnotLengthQ : wire ∉ registers.lengthQ := by
      intro hlength
      exact (hlayout.aux_not_payload
        (auxWire := wire) (payloadWire := wire)
        (hlayout.sourceScratch_mem_aux hwire)
        (by simp [indexedStepPayload, hlength])) rfl
    change changed wire = false
    rw [show changed wire = enabled wire by
      exact indexedIncrementWordState_preservesOutside _ _ _ hnotLengthQ]
    exact henabledSource wire hwire
  have hcleared := run_computeControl_state [registers.phase1, registers.phase2] 2
    registers.control registers.sourceScratch changed hlayout.phase2Length hchangedSource
  have hclearedRun : run (phase2LengthControl registers) changed =
      matchXorState [registers.phase1, registers.phase2] 2
        registers.control changed := by
    simpa [phase2LengthControl] using hcleared.1
  have hcontrolFalse : state registers.control = false :=
    hready registers.control (by simp [IndexedStepRegisters.sharedScratch])
  have hcontrolNePhase2 : registers.control ≠ registers.phase2 :=
    hlayout.aux_not_payload hlayout.control_mem_aux (by simp [indexedStepPayload])
  have hphase1NotQ : registers.phase1 ∉ registers.lengthQ := by
    intro hmem
    exact (hlayout.phase1_ne_after (by
      simp [indexedStepAfterPhase1, hmem])) rfl
  have hphase2NotQ : registers.phase2 ∉ registers.lengthQ := by
    intro hmem
    exact (hlayout.phase2_ne_after (by
      simp [indexedStepAfterPhase2, hmem])) rfl
  have hcontrolNotQ : registers.control ∉ registers.lengthQ := by
    intro hmem
    exact (hlayout.aux_not_payload
      (auxWire := registers.control) (payloadWire := registers.control)
      hlayout.control_mem_aux (by simp [indexedStepPayload, hmem])) rfl
  have henabledControl : enabled registers.control =
      registerMatches [registers.phase1, registers.phase2] 2 state := by
    simp [enabled, matchXorState, hcontrolFalse]
  have hchangedControl : changed registers.control = enabled registers.control := by
    exact indexedIncrementWordState_preservesOutside _ _ _ hcontrolNotQ
  have hpredicate : registerMatches [registers.phase1, registers.phase2] 2 changed =
      registerMatches [registers.phase1, registers.phase2] 2 state := by
    apply registerMatches_congr
    intro wire hwire
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
    rcases hwire with rfl | rfl
    · change indexedIncrementWordState (enabled registers.control)
        registers.lengthQ enabled registers.phase1 = state registers.phase1
      rw [indexedIncrementWordState_preservesOutside _ _ _ hphase1NotQ]
      simp [enabled, matchXorState, upd, hlayout.control_ne_phase1.symm]
    · change indexedIncrementWordState (enabled registers.control)
        registers.lengthQ enabled registers.phase2 = state registers.phase2
      rw [indexedIncrementWordState_preservesOutside _ _ _ hphase2NotQ]
      simp [enabled, matchXorState, upd, hcontrolNePhase2.symm]
  have hfinalControl : matchXorState [registers.phase1, registers.phase2] 2
      registers.control changed registers.control = false := by
    simp [matchXorState, hchangedControl, henabledControl, hpredicate]
  have hrun : run (circuit! {
      phase2LengthControl registers;
      controlledIncrement registers.control registers.lengthQ (lengthCarries registers);
      phase2LengthControl registers
    }) state = blockD1ForwardState registers state := by
    simp only [Classical.run_append]
    rw [henabledRun, hchangedRun, hclearedRun]
    rfl
  constructor
  · exact hrun
  · rw [hrun]
    intro wire hwire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons] at hwire
    rcases hwire with rfl | hsourceWire
    · exact hfinalControl
    · exact hcleared.2 wire hsourceWire

private theorem blockD2Forward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).quotientSwap)
    (hready : IndexedStepReady registers state) :
    run (circuit! {
      quotientXorControl registers;
      quotientSwapUnitary (registers.quotient window) window.start window.stop;
      quotientXorControlInverse registers
    }) state = blockD2ForwardState registers window state ∧
      IndexedStepReady registers
        (run (circuit! {
          quotientXorControl registers;
          quotientSwapUnitary (registers.quotient window) window.start window.stop;
          quotientXorControlInverse registers
        }) state) := by
  have hqLayout : QuotientSwapLayout (registers.quotient window)
      window.start window.stop := by
    subst window
    exact hlayout.quotient
  have hcontrolFalse : state registers.control = false :=
    hready registers.control (by simp [IndexedStepRegisters.sharedScratch])
  have hsource : Clean registers.sourceScratch state := by
    intro wire hwire
    exact hready wire (by simp [IndexedStepRegisters.sharedScratch, hwire])
  let enabled1 := xorWireState registers.phase1 registers.control state
  let enabled2 := xorWireState registers.phase2 registers.control enabled1
  have henabledRun : run (quotientXorControl registers) state = enabled2 := by
    rfl
  have henabledSource : Clean registers.sourceScratch enabled2 := by
    intro wire hwire
    have hcontrol : wire ≠ registers.control := by
      intro equality
      subst wire
      exact hlayout.control_not_sourceScratch hwire
    simp [enabled2, enabled1, xorWireState, upd, hcontrol,
      hsource wire hwire]
  have hqReady : QuotientSwapReady (registers.quotient window) enabled2 := by
    intro wire hwire
    exact henabledSource wire (List.mem_of_mem_take hwire)
  let changed := indexedQuotientSwapState (registers.quotient window)
    window.start window.stop enabled2
  have hchangedRun : run
      (quotientSwapUnitary (registers.quotient window) window.start window.stop)
      enabled2 = changed := by
    simpa only [changed] using run_quotientSwapUnitary_indexedState
      (registers.quotient window) enabled2 hqLayout hqReady
  have hchangedSource : Clean registers.sourceScratch changed := by
    intro wire hwire
    have hsign : wire ≠ registers.sign :=
      hlayout.aux_not_payload
        (auxWire := wire) (payloadWire := registers.sign)
        (hlayout.sourceScratch_mem_aux hwire) (by simp [indexedStepPayload])
    have hwork : wire ∉ (registers.quotient window).work1 := by
      intro hwindowWire
      change wire ∈ IndexedStepRegisters.windowSlice registers.work1 window at hwindowWire
      have hglobal := windowSlice_mem registers.work1 window hwindowWire
      exact (hlayout.aux_not_payload
        (auxWire := wire) (payloadWire := wire)
        (hlayout.sourceScratch_mem_aux hwire)
        (by simp [indexedStepPayload, hglobal])) rfl
    change changed wire = false
    rw [show changed wire = enabled2 wire by
      exact indexedQuotientSwapState_preserves
        (registers.quotient window) enabled2 hqLayout hsign hwork]
    exact henabledSource wire hwire
  let disabled2 := xorWireState registers.phase2 registers.control changed
  let disabled1 := xorWireState registers.phase1 registers.control disabled2
  have hdisabledRun : run (quotientXorControlInverse registers) changed = disabled1 := by
    rfl
  have hcontrolNeSign : registers.control ≠ registers.sign :=
    hlayout.aux_not_payload hlayout.control_mem_aux (by simp [indexedStepPayload])
  have hcontrolNotWork : registers.control ∉
      (registers.quotient window).work1 := by
    intro hwindowWire
    change registers.control ∈
      IndexedStepRegisters.windowSlice registers.work1 window at hwindowWire
    have hglobal := windowSlice_mem registers.work1 window hwindowWire
    exact (hlayout.aux_not_payload
      (auxWire := registers.control) (payloadWire := registers.control)
      hlayout.control_mem_aux (by simp [indexedStepPayload, hglobal])) rfl
  have hphase1NeSign : registers.phase1 ≠ registers.sign :=
    hlayout.phase1_ne_after (by simp [indexedStepAfterPhase1])
  have hphase1NotWork : registers.phase1 ∉
      (registers.quotient window).work1 := by
    intro hwindowWire
    change registers.phase1 ∈
      IndexedStepRegisters.windowSlice registers.work1 window at hwindowWire
    exact (hlayout.phase1_ne_after (by
      simp [indexedStepAfterPhase1,
        windowSlice_mem registers.work1 window hwindowWire])) rfl
  have hphase2NeSign : registers.phase2 ≠ registers.sign :=
    hlayout.phase2_ne_after (by simp [indexedStepAfterPhase2])
  have hphase2NotWork : registers.phase2 ∉
      (registers.quotient window).work1 := by
    intro hwindowWire
    change registers.phase2 ∈
      IndexedStepRegisters.windowSlice registers.work1 window at hwindowWire
    exact (hlayout.phase2_ne_after (by
      simp [indexedStepAfterPhase2,
        windowSlice_mem registers.work1 window hwindowWire])) rfl
  have hchangedControl : changed registers.control = enabled2 registers.control := by
    change indexedQuotientSwapState (registers.quotient window)
      window.start window.stop enabled2 registers.control = enabled2 registers.control
    exact indexedQuotientSwapState_preserves
      (registers.quotient window) enabled2 hqLayout hcontrolNeSign hcontrolNotWork
  have hchangedPhase1 : changed registers.phase1 = state registers.phase1 := by
    change indexedQuotientSwapState (registers.quotient window)
      window.start window.stop enabled2 registers.phase1 = state registers.phase1
    rw [indexedQuotientSwapState_preserves (registers.quotient window)
      enabled2 hqLayout hphase1NeSign hphase1NotWork]
    simp [enabled2, enabled1, xorWireState, upd,
      hlayout.control_ne_phase1.symm]
  have hcontrolNePhase2 : registers.control ≠ registers.phase2 :=
    hlayout.aux_not_payload hlayout.control_mem_aux (by simp [indexedStepPayload])
  have hphase1NeControl : registers.phase1 ≠ registers.control :=
    Ne.symm hlayout.control_ne_phase1
  have hphase2NeControl : registers.phase2 ≠ registers.control :=
    Ne.symm hcontrolNePhase2
  have hchangedPhase2 : changed registers.phase2 = state registers.phase2 := by
    change indexedQuotientSwapState (registers.quotient window)
      window.start window.stop enabled2 registers.phase2 = state registers.phase2
    rw [indexedQuotientSwapState_preserves (registers.quotient window)
      enabled2 hqLayout hphase2NeSign hphase2NotWork]
    simp [enabled2, enabled1, xorWireState, upd, hcontrolNePhase2.symm]
  have hfinalControl : disabled1 registers.control = false := by
    change xorWireState registers.phase1 registers.control
      (xorWireState registers.phase2 registers.control changed)
        registers.control = false
    cases hp1 : state registers.phase1 <;> cases hp2 : state registers.phase2 <;>
      simp [xorWireState, upd, hphase1NeControl,
        hphase2NeControl, hchangedControl, hchangedPhase1, hchangedPhase2,
        enabled2, enabled1, hcontrolFalse, hp1, hp2]
  have hfinalSource : Clean registers.sourceScratch disabled1 := by
    intro wire hwire
    have hcontrol : wire ≠ registers.control := by
      intro equality
      subst wire
      exact hlayout.control_not_sourceScratch hwire
    simp [disabled1, disabled2, xorWireState, upd, hcontrol,
      hchangedSource wire hwire]
  have hrun : run (circuit! {
      quotientXorControl registers;
      quotientSwapUnitary (registers.quotient window) window.start window.stop;
      quotientXorControlInverse registers
    }) state = blockD2ForwardState registers window state := by
    simp only [Classical.run_append]
    rw [henabledRun, hchangedRun, hdisabledRun]
    rfl
  constructor
  · exact hrun
  · rw [hrun]
    intro wire hwire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons] at hwire
    rcases hwire with rfl | hsourceWire
    · exact hfinalControl
    · exact hfinalSource wire hsourceWire

private theorem blockD3Forward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state) :
    run (circuit! {
      phase3LengthControl registers;
      controlledDecrement registers.control registers.lengthQ (lengthCarries registers);
      phase3LengthControl registers
    }) state = blockD3ForwardState registers state ∧
      IndexedStepReady registers
        (run (circuit! {
          phase3LengthControl registers;
          controlledDecrement registers.control registers.lengthQ
            (lengthCarries registers);
          phase3LengthControl registers
        }) state) := by
  have hsource : Clean registers.sourceScratch state := by
    intro wire hwire
    exact hready wire (by
      simp [IndexedStepRegisters.sharedScratch, hwire])
  let enabled := matchXorState [registers.phase1, registers.phase2] 1
    registers.control state
  have henabled := run_computeControl_state [registers.phase1, registers.phase2] 1
    registers.control registers.sourceScratch state hlayout.phase3Length hsource
  have henabledRun : run (phase3LengthControl registers) state = enabled := by
    simpa [phase3LengthControl, enabled] using henabled.1
  have henabledSource : Clean registers.sourceScratch enabled := by
    simpa only [enabled] using henabled.2
  have hcarries : Clean (lengthCarries registers) enabled := by
    intro wire hwire
    exact henabledSource wire (List.mem_of_mem_take hwire)
  let changed := indexedDecrementWordState (enabled registers.control)
    registers.lengthQ enabled
  have hchangedRun : run
      (controlledDecrement registers.control registers.lengthQ
        (lengthCarries registers)) enabled = changed := by
    simpa only [changed] using run_controlledDecrement_indexedState
      registers.control registers.lengthQ (lengthCarries registers) enabled
      hlayout.lengthCarryCapacity hlayout.lengthCarryPhysical hcarries
  have hchangedSource : Clean registers.sourceScratch changed := by
    intro wire hwire
    have hnotLengthQ : wire ∉ registers.lengthQ := by
      intro hlength
      exact (hlayout.aux_not_payload
        (auxWire := wire) (payloadWire := wire)
        (hlayout.sourceScratch_mem_aux hwire)
        (by simp [indexedStepPayload, hlength])) rfl
    change changed wire = false
    rw [show changed wire = enabled wire by
      exact indexedDecrementWordState_preservesOutside _ _ _ hnotLengthQ]
    exact henabledSource wire hwire
  have hcleared := run_computeControl_state [registers.phase1, registers.phase2] 1
    registers.control registers.sourceScratch changed hlayout.phase3Length hchangedSource
  have hclearedRun : run (phase3LengthControl registers) changed =
      matchXorState [registers.phase1, registers.phase2] 1
        registers.control changed := by
    simpa [phase3LengthControl] using hcleared.1
  have hcontrolFalse : state registers.control = false :=
    hready registers.control (by simp [IndexedStepRegisters.sharedScratch])
  have hcontrolNePhase2 : registers.control ≠ registers.phase2 :=
    hlayout.aux_not_payload hlayout.control_mem_aux (by simp [indexedStepPayload])
  have hphase1NotQ : registers.phase1 ∉ registers.lengthQ := by
    intro hmem
    exact (hlayout.phase1_ne_after (by
      simp [indexedStepAfterPhase1, hmem])) rfl
  have hphase2NotQ : registers.phase2 ∉ registers.lengthQ := by
    intro hmem
    exact (hlayout.phase2_ne_after (by
      simp [indexedStepAfterPhase2, hmem])) rfl
  have hcontrolNotQ : registers.control ∉ registers.lengthQ := by
    intro hmem
    exact (hlayout.aux_not_payload
      (auxWire := registers.control) (payloadWire := registers.control)
      hlayout.control_mem_aux (by simp [indexedStepPayload, hmem])) rfl
  have henabledControl : enabled registers.control =
      registerMatches [registers.phase1, registers.phase2] 1 state := by
    simp [enabled, matchXorState, hcontrolFalse]
  have hchangedControl : changed registers.control = enabled registers.control := by
    exact indexedDecrementWordState_preservesOutside _ _ _ hcontrolNotQ
  have hpredicate : registerMatches [registers.phase1, registers.phase2] 1 changed =
      registerMatches [registers.phase1, registers.phase2] 1 state := by
    apply registerMatches_congr
    intro wire hwire
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
    rcases hwire with rfl | rfl
    · change indexedDecrementWordState (enabled registers.control)
        registers.lengthQ enabled registers.phase1 = state registers.phase1
      rw [indexedDecrementWordState_preservesOutside _ _ _ hphase1NotQ]
      simp [enabled, matchXorState, upd, hlayout.control_ne_phase1.symm]
    · change indexedDecrementWordState (enabled registers.control)
        registers.lengthQ enabled registers.phase2 = state registers.phase2
      rw [indexedDecrementWordState_preservesOutside _ _ _ hphase2NotQ]
      simp [enabled, matchXorState, upd, hcontrolNePhase2.symm]
  have hfinalControl : matchXorState [registers.phase1, registers.phase2] 1
      registers.control changed registers.control = false := by
    simp [matchXorState, hchangedControl, henabledControl, hpredicate]
  have hrun : run (circuit! {
      phase3LengthControl registers;
      controlledDecrement registers.control registers.lengthQ (lengthCarries registers);
      phase3LengthControl registers
    }) state = blockD3ForwardState registers state := by
    simp only [Classical.run_append]
    rw [henabledRun, hchangedRun, hclearedRun]
    rfl
  constructor
  · exact hrun
  · rw [hrun]
    intro wire hwire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons] at hwire
    rcases hwire with rfl | hsourceWire
    · exact hfinalControl
    · exact hcleared.2 wire hsourceWire

private theorem blockDForward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).quotientSwap)
    (hready : IndexedStepReady registers state) :
    run (blockDForward registers window) state =
        blockDForwardState registers window state ∧
      IndexedStepReady registers (run (blockDForward registers window) state) := by
  have hfirst := blockD1Forward_correct registers n T state hlayout hready
  have hfirstReady : IndexedStepReady registers
      (blockD1ForwardState registers state) := by
    rw [← hfirst.1]
    exact hfirst.2
  have hsecond := blockD2Forward_correct registers n T window
    (blockD1ForwardState registers state) hlayout hwindow hfirstReady
  have hsecondReady : IndexedStepReady registers
      (blockD2ForwardState registers window
        (blockD1ForwardState registers state)) := by
    rw [← hsecond.1]
    exact hsecond.2
  have hthird := blockD3Forward_correct registers n T
    (blockD2ForwardState registers window
      (blockD1ForwardState registers state)) hlayout hsecondReady
  have hrun : run (blockDForward registers window) state =
      blockDForwardState registers window state := by
    calc
      run (blockDForward registers window) state =
          run (circuit! {
            phase3LengthControl registers;
            controlledDecrement registers.control registers.lengthQ
              (lengthCarries registers);
            phase3LengthControl registers
          })
            (run (circuit! {
              quotientXorControl registers;
              quotientSwapUnitary (registers.quotient window)
                window.start window.stop;
              quotientXorControlInverse registers
            })
              (run (circuit! {
                phase2LengthControl registers;
                controlledIncrement registers.control registers.lengthQ
                  (lengthCarries registers);
                phase2LengthControl registers
              }) state)) := by
                simp [blockDForward, Classical.run_append]
      _ = blockDForwardState registers window state := by
        rw [hfirst.1, hsecond.1, hthird.1]
        rfl
  constructor
  · exact hrun
  · rw [hrun]
    change IndexedStepReady registers
      (blockD3ForwardState registers
        (blockD2ForwardState registers window
          (blockD1ForwardState registers state)))
    rw [← hthird.1]
    exact hthird.2

private theorem run_tBoundaryPrepareState
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hclean : Clean registers.blockScratch state) :
    run (prepareLatestPaperTBoundary registers.tBoundary n) state =
        tBoundaryPrepareState registers n state ∧
      Clean registers.blockScratch
        (run (prepareLatestPaperTBoundary registers.tBoundary n) state) := by
  have hlocalReady : TBoundaryReady registers.tBoundary state := by
    intro wire hwire
    exact hclean wire (hlayout.tBoundary_usedScratch_sub_block wire hwire)
  have hcorrect := prepareLatestPaperTBoundary_correct registers.tBoundary n state
    hlayout.tBoundary hlocalReady
  dsimp only at hcorrect
  let words := prepareLatestPaperTBoundaryWords (state registers.phase2)
    (wireValues registers.lengthT state)
    (wireValues registers.lengthRPrime state)
    (wireValues registers.tBoundary.lengthSLow state) n
  have hrun : run (prepareLatestPaperTBoundary registers.tBoundary n) state =
      indexedWriteWireValues (registers.lengthT ++ registers.lengthRPrime)
        (words.1 ++ words.2) state := by
    apply indexedState_eq_writeWireValues
    · exact hlayout.tBoundary_words_nodup
    · have hlength := congrArg
          (fun pair : List Bool × List Bool => pair.1.length + pair.2.length)
          hcorrect.1
      simpa [words, wireValues] using hlength.symm
    · have hvalues := congrArg
          (fun pair : List Bool × List Bool => pair.1 ++ pair.2) hcorrect.1
      simpa [words, wireValues] using hvalues
    · intro wire hwire
      simp only [List.mem_append, not_or] at hwire
      exact hcorrect.2.2 wire hwire.1 hwire.2
  constructor
  · simpa only [tBoundaryPrepareState, words] using hrun
  · intro wire hwire
    have haux := hlayout.blockScratch_mem_aux hwire
    have ht : wire ∉ registers.lengthT := by
      intro hlength
      exact (hlayout.aux_not_payload haux
        (by simp [indexedStepPayload, hlength])) rfl
    have hrp : wire ∉ registers.lengthRPrime := by
      intro hlength
      exact (hlayout.aux_not_payload haux
        (by simp [indexedStepPayload, hlength])) rfl
    rw [hcorrect.2.2 wire ht hrp]
    exact hclean wire hwire

private theorem run_tBoundaryRestoreState
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hclean : Clean registers.blockScratch state) :
    run (restoreLatestPaperTBoundary registers.tBoundary n) state =
        tBoundaryRestoreState registers n state ∧
      Clean registers.blockScratch
        (run (restoreLatestPaperTBoundary registers.tBoundary n) state) := by
  have hlocalReady : TBoundaryReady registers.tBoundary state := by
    intro wire hwire
    exact hclean wire (hlayout.tBoundary_usedScratch_sub_block wire hwire)
  have hcorrect := restoreLatestPaperTBoundary_correct registers.tBoundary n state
    hlayout.tBoundary hlocalReady
  dsimp only at hcorrect
  let words := restoreLatestPaperTBoundaryWords (state registers.phase2)
    (wireValues registers.lengthT state)
    (wireValues registers.lengthRPrime state)
    (wireValues registers.tBoundary.lengthSLow state) n
  have hrun : run (restoreLatestPaperTBoundary registers.tBoundary n) state =
      indexedWriteWireValues (registers.lengthT ++ registers.lengthRPrime)
        (words.1 ++ words.2) state := by
    apply indexedState_eq_writeWireValues
    · exact hlayout.tBoundary_words_nodup
    · have hlength := congrArg
          (fun pair : List Bool × List Bool => pair.1.length + pair.2.length)
          hcorrect.1
      simpa [words, wireValues] using hlength.symm
    · have hvalues := congrArg
          (fun pair : List Bool × List Bool => pair.1 ++ pair.2) hcorrect.1
      simpa [words, wireValues] using hvalues
    · intro wire hwire
      simp only [List.mem_append, not_or] at hwire
      exact hcorrect.2.2 wire hwire.1 hwire.2
  constructor
  · simpa only [tBoundaryRestoreState, words] using hrun
  · intro wire hwire
    have haux := hlayout.blockScratch_mem_aux hwire
    have ht : wire ∉ registers.lengthT := by
      intro hlength
      exact (hlayout.aux_not_payload haux
        (by simp [indexedStepPayload, hlength])) rfl
    have hrp : wire ∉ registers.lengthRPrime := by
      intro hlength
      exact (hlayout.aux_not_payload haux
        (by simp [indexedStepPayload, hlength])) rfl
    rw [hcorrect.2.2 wire ht hrp]
    exact hclean wire hwire

private theorem run_coefficientPrefixState_from_blockScratch
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (mode : RippleMode) (signUpdate : Bool) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient)
    (hclean : Clean registers.blockScratch state) :
    let circuit := coefficientPrefixUnitary (registers.coefficient window)
      window.start window.stop mode signUpdate .work2
    run circuit state = coefficientPrefixState (registers.coefficient window)
        window.start window.stop mode signUpdate .work2 state ∧
      Clean registers.blockScratch (run circuit state) ∧
      run circuit state registers.control = state registers.control ∧
      (signUpdate = false →
        run circuit state registers.sign = state registers.sign) := by
  have hcoefficientLayout : CoefficientPrefixLayout
      (registers.coefficient window) window.start window.stop := by
    subst window
    exact hlayout.coefficient
  have hlocalReady : CoefficientPrefixReady
      (registers.coefficient window) state := by
    intro wire hwire
    exact hclean wire (hlayout.coefficient_scratch_sub_block window wire hwire)
  let circuit := coefficientPrefixUnitary (registers.coefficient window)
    window.start window.stop mode signUpdate .work2
  have hrun : run circuit state = coefficientPrefixState
      (registers.coefficient window) window.start window.stop mode signUpdate
        .work2 state := by
    simpa only [circuit] using run_coefficientPrefixUnitary_state
      (registers.coefficient window) mode signUpdate .work2 state
      hcoefficientLayout hlocalReady
  have hlocalAfter : CoefficientPrefixReady (registers.coefficient window)
      (run circuit state) := by
    simpa only [circuit] using coefficientPrefixUnitary_clean
      (registers.coefficient window) mode signUpdate .work2 state
      hcoefficientLayout hlocalReady
  have hblockAfter : Clean registers.blockScratch (run circuit state) := by
    intro wire hwire
    by_cases hlocal : wire ∈ (registers.coefficient window).scratch
    · exact hlocalAfter wire hlocal
    · rw [show run circuit state wire = state wire by
        simpa only [circuit] using coefficientPrefixUnitary_preservesOutside
          (registers.coefficient window) mode signUpdate .work2 state
          hcoefficientLayout
          (hlayout.blockScratch_outside_coefficient window hwire hlocal)]
      exact hclean wire hwire
  have hcontrol : run circuit state registers.control = state registers.control := by
    simpa only [circuit] using coefficientPrefixUnitary_preserves_control
      (registers.coefficient window) mode signUpdate .work2 state
      hcoefficientLayout
  refine ⟨hrun, hblockAfter, hcontrol, ?_⟩
  intro hfalse
  subst signUpdate
  simpa only [circuit] using coefficientPrefixUnitary_preserves_sign_of_false
    (registers.coefficient window) mode .work2 state hcoefficientLayout

private theorem blockEForward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient)
    (hready : IndexedStepReady registers state) :
    run (blockEForward registers n window) state =
        blockEForwardState registers n window state ∧
      IndexedStepReady registers
        (run (blockEForward registers n window) state) := by
  have hcontrolFalse : state registers.control = false :=
    hready registers.control (by simp [IndexedStepRegisters.sharedScratch])
  have hterminalSource : registers.terminal ∈ registers.sourceScratch := by
    rw [← hlayout.scratch_view]
    simp
  have hterminalFalse : state registers.terminal = false :=
    hready registers.terminal (by
      simp [IndexedStepRegisters.sharedScratch, hterminalSource])
  have hblock : Clean registers.blockScratch state := by
    intro wire hwire
    exact hready wire (by
      simp only [IndexedStepRegisters.sharedScratch, List.mem_cons]
      exact Or.inr (List.mem_of_mem_drop hwire))
  have hterminalAux := hlayout.sourceScratch_mem_aux hterminalSource
  have hcontrolNePhase2 : registers.control ≠ registers.phase2 :=
    hlayout.aux_not_payload hlayout.control_mem_aux (by
      simp [indexedStepPayload])
  have hcontrolNeSign : registers.control ≠ registers.sign :=
    hlayout.aux_not_payload hlayout.control_mem_aux (by
      simp [indexedStepPayload])
  have hterminalNePhase1 : registers.terminal ≠ registers.phase1 :=
    hlayout.aux_not_payload hterminalAux (by simp [indexedStepPayload])
  have hterminalNePhase2 : registers.terminal ≠ registers.phase2 :=
    hlayout.aux_not_payload hterminalAux (by simp [indexedStepPayload])
  have hterminalNeSign : registers.terminal ≠ registers.sign :=
    hlayout.aux_not_payload hterminalAux (by simp [indexedStepPayload])
  have hfixedNotWords : ∀ wire ∈
      [registers.phase1, registers.phase2, registers.sign,
        registers.control, registers.terminal],
      wire ∉ registers.lengthT ∧ wire ∉ registers.lengthRPrime := by
    intro wire hwire
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
    rcases hwire with rfl | rfl | rfl | rfl | rfl
    · constructor
      · intro hmem
        exact (hlayout.phase1_ne_after (by
          simp [indexedStepAfterPhase1, hmem])) rfl
      · intro hmem
        exact (hlayout.phase1_ne_after (by
          simp [indexedStepAfterPhase1, hmem])) rfl
    · constructor
      · intro hmem
        exact (hlayout.phase2_ne_after (by
          simp [indexedStepAfterPhase2, hmem])) rfl
      · intro hmem
        exact (hlayout.phase2_ne_after (by
          simp [indexedStepAfterPhase2, hmem])) rfl
    · constructor
      · intro hmem
        exact (hlayout.sign_ne_after (by
          simp [indexedStepAfterSign, hmem])) rfl
      · intro hmem
        exact (hlayout.sign_ne_after (by
          simp [indexedStepAfterSign, hmem])) rfl
    · constructor
      · intro hmem
        exact (hlayout.aux_not_payload hlayout.control_mem_aux
          (by simp [indexedStepPayload, hmem])) rfl
      · intro hmem
        exact (hlayout.aux_not_payload hlayout.control_mem_aux
          (by simp [indexedStepPayload, hmem])) rfl
    · constructor
      · intro hmem
        exact (hlayout.aux_not_payload hterminalAux
          (by simp [indexedStepPayload, hmem])) rfl
      · intro hmem
        exact (hlayout.aux_not_payload hterminalAux
          (by simp [indexedStepPayload, hmem])) rfl
  have hcoefficientLayout : CoefficientPrefixLayout
      (registers.coefficient window) window.start window.stop := by
    subst window
    exact hlayout.coefficient
  let temporary1 := matchXorState [registers.phase2, registers.sign] 2
    registers.terminal state
  have htemporary1 := run_computeControl_state
    [registers.phase2, registers.sign] 2 registers.terminal
      registers.blockScratch state hlayout.coefficientTemporary hblock
  have htemporary1Run : run (coefficientTemporaryControl registers) state =
      temporary1 := by
    simpa [coefficientTemporaryControl, temporary1] using htemporary1.1
  have htemporary1Block : Clean registers.blockScratch temporary1 := by
    simpa only [temporary1] using htemporary1.2
  let subEnabled := matchXorState [registers.phase1, registers.terminal] 1
    registers.control temporary1
  have hsubEnabled := run_computeControl_state
    [registers.phase1, registers.terminal] 1 registers.control
      registers.blockScratch temporary1 hlayout.coefficientSub htemporary1Block
  have hsubEnabledRun : run (coefficientSubControl registers) temporary1 =
      subEnabled := by
    simpa [coefficientSubControl, subEnabled] using hsubEnabled.1
  have hsubEnabledBlock : Clean registers.blockScratch subEnabled := by
    simpa only [subEnabled] using hsubEnabled.2
  let temporaryCleared1 := matchXorState [registers.phase2, registers.sign] 2
    registers.terminal subEnabled
  have htemporaryCleared1 := run_computeControl_state
    [registers.phase2, registers.sign] 2 registers.terminal
      registers.blockScratch subEnabled hlayout.coefficientTemporary hsubEnabledBlock
  have htemporaryCleared1Run :
      run (coefficientTemporaryControl registers) subEnabled =
        temporaryCleared1 := by
    simpa [coefficientTemporaryControl, temporaryCleared1] using
      htemporaryCleared1.1
  have htemporaryCleared1Block : Clean registers.blockScratch
      temporaryCleared1 := by
    simpa only [temporaryCleared1] using htemporaryCleared1.2
  let prepared := tBoundaryPrepareState registers n temporaryCleared1
  have hprepared := run_tBoundaryPrepareState registers n T temporaryCleared1
    hlayout htemporaryCleared1Block
  have hpreparedBlock : Clean registers.blockScratch prepared := by
    simpa only [prepared, hprepared.1] using hprepared.2
  let subtracted := coefficientPrefixState (registers.coefficient window)
    window.start window.stop .sub false .work2 prepared
  have hsubtracted := run_coefficientPrefixState_from_blockScratch registers n T
    window .sub false prepared hlayout hwindow hpreparedBlock
  dsimp only at hsubtracted
  have hsubtractedBlock : Clean registers.blockScratch subtracted := by
    simpa only [subtracted, hsubtracted.1] using hsubtracted.2.1
  let temporary2 := matchXorState [registers.phase2, registers.sign] 2
    registers.terminal subtracted
  have htemporary2 := run_computeControl_state
    [registers.phase2, registers.sign] 2 registers.terminal
      registers.blockScratch subtracted hlayout.coefficientTemporary hsubtractedBlock
  have htemporary2Run : run (coefficientTemporaryControl registers) subtracted =
      temporary2 := by
    simpa [coefficientTemporaryControl, temporary2] using htemporary2.1
  have htemporary2Block : Clean registers.blockScratch temporary2 := by
    simpa only [temporary2] using htemporary2.2
  let subCleared := matchXorState [registers.phase1, registers.terminal] 1
    registers.control temporary2
  have hsubCleared := run_computeControl_state
    [registers.phase1, registers.terminal] 1 registers.control
      registers.blockScratch temporary2 hlayout.coefficientSub htemporary2Block
  have hsubClearedRun : run (coefficientSubControl registers) temporary2 =
      subCleared := by
    simpa [coefficientSubControl, subCleared] using hsubCleared.1
  have hsubClearedBlock : Clean registers.blockScratch subCleared := by
    simpa only [subCleared] using hsubCleared.2
  let temporaryCleared2 := matchXorState [registers.phase2, registers.sign] 2
    registers.terminal subCleared
  have htemporaryCleared2 := run_computeControl_state
    [registers.phase2, registers.sign] 2 registers.terminal
      registers.blockScratch subCleared hlayout.coefficientTemporary hsubClearedBlock
  have htemporaryCleared2Run :
      run (coefficientTemporaryControl registers) subCleared =
        temporaryCleared2 := by
    simpa [coefficientTemporaryControl, temporaryCleared2] using
      htemporaryCleared2.1
  have htemporaryCleared2Block : Clean registers.blockScratch
      temporaryCleared2 := by
    simpa only [temporaryCleared2] using htemporaryCleared2.2
  let signChanged := xorWireState registers.phase1 registers.sign temporaryCleared2
  have hsignChangedRun : run ([.CX registers.phase1 registers.sign] : Circuit)
      temporaryCleared2 = signChanged := by
    simpa only [signChanged] using
      run_xorWireState registers.phase1 registers.sign temporaryCleared2
  have hsignChangedBlock : Clean registers.blockScratch signChanged := by
    simpa [signChanged, xorWireState] using
      clean_upd_not_mem htemporaryCleared2Block
        (by
          intro hmem
          exact (hlayout.sign_ne_after (by
            simp [indexedStepAfterSign,
              hlayout.blockScratch_mem_aux hmem])) rfl)
  let addEnabled := matchXorState [registers.phase1] 1 registers.control signChanged
  have haddEnabled := run_computeControl_state [registers.phase1] 1
    registers.control registers.blockScratch signChanged hlayout.coefficientAdd
      hsignChangedBlock
  have haddEnabledRun : run (coefficientAddControl registers) signChanged =
      addEnabled := by
    simpa [coefficientAddControl, addEnabled] using haddEnabled.1
  have haddEnabledBlock : Clean registers.blockScratch addEnabled := by
    simpa only [addEnabled] using haddEnabled.2
  let added := coefficientPrefixState (registers.coefficient window)
    window.start window.stop .add true .work2 addEnabled
  have hadded := run_coefficientPrefixState_from_blockScratch registers n T window
    .add true addEnabled hlayout hwindow haddEnabledBlock
  dsimp only at hadded
  have haddedBlock : Clean registers.blockScratch added := by
    simpa only [added, hadded.1] using hadded.2.1
  let addCleared := matchXorState [registers.phase1] 1 registers.control added
  have haddCleared := run_computeControl_state [registers.phase1] 1
    registers.control registers.blockScratch added hlayout.coefficientAdd haddedBlock
  have haddClearedRun : run (coefficientAddControl registers) added =
      addCleared := by
    simpa [coefficientAddControl, addCleared] using haddCleared.1
  have haddClearedBlock : Clean registers.blockScratch addCleared := by
    simpa only [addCleared] using haddCleared.2
  let restored := tBoundaryRestoreState registers n addCleared
  have hrestored := run_tBoundaryRestoreState registers n T addCleared hlayout
    haddClearedBlock
  have hrun : run (blockEForward registers n window) state = restored := by
    simp only [blockEForward, Classical.run_append]
    rw [htemporary1Run, hsubEnabledRun, htemporaryCleared1Run,
      hprepared.1, hsubtracted.1, htemporary2Run, hsubClearedRun,
      htemporaryCleared2Run, hsignChangedRun, haddEnabledRun,
      hadded.1, haddClearedRun, hrestored.1]
  have hstate : restored = blockEForwardState registers n window state := by
    rfl
  have htemporary1Control : temporary1 registers.control = false := by
    calc
      temporary1 registers.control = state registers.control := by
        simpa only [temporary1] using
          matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal state hlayout.control_ne_terminal
      _ = false := hcontrolFalse
  have htemporary1Terminal : temporary1 registers.terminal =
      registerMatches [registers.phase2, registers.sign] 2 state := by
    simp [temporary1, matchXorState, hterminalFalse]
  have hsubEnabledTerminal : subEnabled registers.terminal =
      temporary1 registers.terminal :=
    matchXorState_preserves _ _ _ _ (Ne.symm hlayout.control_ne_terminal)
  have hsubEnabledControl : subEnabled registers.control =
      registerMatches [registers.phase1, registers.terminal] 1 temporary1 := by
    simp [subEnabled, matchXorState, htemporary1Control]
  have hsubEnabledControls : ∀ wire ∈ [registers.phase2, registers.sign],
      subEnabled wire = state wire := by
    intro wire hwire
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
    rcases hwire with rfl | rfl
    · calc
        subEnabled registers.phase2 = temporary1 registers.phase2 := by
          simpa only [subEnabled] using
            matchXorState_preserves [registers.phase1, registers.terminal] 1
              registers.control temporary1 (Ne.symm hcontrolNePhase2)
        _ = state registers.phase2 := by
          simpa only [temporary1] using
            matchXorState_preserves [registers.phase2, registers.sign] 2
              registers.terminal state (Ne.symm hterminalNePhase2)
    · calc
        subEnabled registers.sign = temporary1 registers.sign := by
          simpa only [subEnabled] using
            matchXorState_preserves [registers.phase1, registers.terminal] 1
              registers.control temporary1 (Ne.symm hcontrolNeSign)
        _ = state registers.sign := by
          simpa only [temporary1] using
            matchXorState_preserves [registers.phase2, registers.sign] 2
              registers.terminal state (Ne.symm hterminalNeSign)
  have htemporaryCleared1Terminal :
      temporaryCleared1 registers.terminal = false := by
    apply matchXorState_clears [registers.phase2, registers.sign] 2
      registers.terminal state subEnabled
    · exact hsubEnabledTerminal.trans htemporary1Terminal
    · exact hsubEnabledControls
  have htemporaryCleared1Control :
      temporaryCleared1 registers.control = subEnabled registers.control := by
    simpa only [temporaryCleared1] using
      matchXorState_preserves [registers.phase2, registers.sign] 2
        registers.terminal subEnabled hlayout.control_ne_terminal
  have htemporaryCleared1Phase1 :
      temporaryCleared1 registers.phase1 = state registers.phase1 := by
    calc
      temporaryCleared1 registers.phase1 = subEnabled registers.phase1 := by
        simpa only [temporaryCleared1] using
          matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal subEnabled (Ne.symm hterminalNePhase1)
      _ = temporary1 registers.phase1 := by
        simpa only [subEnabled] using
          matchXorState_preserves [registers.phase1, registers.terminal] 1
            registers.control temporary1 (Ne.symm hlayout.control_ne_phase1)
      _ = state registers.phase1 := by
        simpa only [temporary1] using
          matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal state (Ne.symm hterminalNePhase1)
  have htemporaryCleared1Phase2 :
      temporaryCleared1 registers.phase2 = state registers.phase2 := by
    calc
      temporaryCleared1 registers.phase2 = subEnabled registers.phase2 := by
        simpa only [temporaryCleared1] using
          matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal subEnabled (Ne.symm hterminalNePhase2)
      _ = state registers.phase2 := hsubEnabledControls _ (by simp)
  have htemporaryCleared1Sign :
      temporaryCleared1 registers.sign = state registers.sign := by
    calc
      temporaryCleared1 registers.sign = subEnabled registers.sign := by
        simpa only [temporaryCleared1] using
          matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal subEnabled (Ne.symm hterminalNeSign)
      _ = state registers.sign := hsubEnabledControls _ (by simp)
  have hpreparedFixed : ∀ wire ∈
      [registers.phase1, registers.phase2, registers.sign,
        registers.control, registers.terminal],
      prepared wire = temporaryCleared1 wire := by
    intro wire hwire
    simpa only [prepared] using
      tBoundaryPrepareState_preservesOutside registers n temporaryCleared1
        (hfixedNotWords wire hwire).1 (hfixedNotWords wire hwire).2
  have hsubtractedPhase1 : subtracted registers.phase1 = state registers.phase1 := by
    calc
      subtracted registers.phase1 =
          run (coefficientPrefixUnitary (registers.coefficient window)
            window.start window.stop .sub false .work2) prepared
              registers.phase1 := by
        simpa only [subtracted] using congrFun hsubtracted.1.symm registers.phase1
      _ = prepared registers.phase1 := by
        exact coefficientPrefixUnitary_preservesOutside
          (registers.coefficient window) .sub false .work2 prepared
            hcoefficientLayout (hlayout.phase1_not_coefficient window)
      _ = temporaryCleared1 registers.phase1 := hpreparedFixed _ (by simp)
      _ = state registers.phase1 := htemporaryCleared1Phase1
  have hsubtractedPhase2 : subtracted registers.phase2 = state registers.phase2 := by
    calc
      subtracted registers.phase2 =
          run (coefficientPrefixUnitary (registers.coefficient window)
            window.start window.stop .sub false .work2) prepared
              registers.phase2 := by
        simpa only [subtracted] using congrFun hsubtracted.1.symm registers.phase2
      _ = prepared registers.phase2 := by
        exact coefficientPrefixUnitary_preservesOutside
          (registers.coefficient window) .sub false .work2 prepared
            hcoefficientLayout (hlayout.phase2_not_coefficient window)
      _ = temporaryCleared1 registers.phase2 := hpreparedFixed _ (by simp)
      _ = state registers.phase2 := htemporaryCleared1Phase2
  have hsubtractedTerminal : subtracted registers.terminal = false := by
    calc
      subtracted registers.terminal =
          run (coefficientPrefixUnitary (registers.coefficient window)
            window.start window.stop .sub false .work2) prepared
              registers.terminal := by
        simpa only [subtracted] using congrFun hsubtracted.1.symm registers.terminal
      _ = prepared registers.terminal := by
        exact coefficientPrefixUnitary_preservesOutside
          (registers.coefficient window) .sub false .work2 prepared
            hcoefficientLayout (hlayout.terminal_not_coefficient window)
      _ = temporaryCleared1 registers.terminal := hpreparedFixed _ (by simp)
      _ = false := htemporaryCleared1Terminal
  have hsubtractedControl : subtracted registers.control =
      subEnabled registers.control := by
    calc
      subtracted registers.control =
          run (coefficientPrefixUnitary (registers.coefficient window)
            window.start window.stop .sub false .work2) prepared
              registers.control := by
        simpa only [subtracted] using congrFun hsubtracted.1.symm registers.control
      _ = prepared registers.control := hsubtracted.2.2.1
      _ = temporaryCleared1 registers.control := hpreparedFixed _ (by simp)
      _ = subEnabled registers.control := htemporaryCleared1Control
  have hsubtractedSign : subtracted registers.sign = state registers.sign := by
    calc
      subtracted registers.sign =
          run (coefficientPrefixUnitary (registers.coefficient window)
            window.start window.stop .sub false .work2) prepared
              registers.sign := by
        simpa only [subtracted] using congrFun hsubtracted.1.symm registers.sign
      _ = prepared registers.sign := hsubtracted.2.2.2 rfl
      _ = temporaryCleared1 registers.sign := hpreparedFixed _ (by simp)
      _ = state registers.sign := htemporaryCleared1Sign
  have htemporary2Control : temporary2 registers.control =
      subEnabled registers.control := by
    calc
      temporary2 registers.control = subtracted registers.control := by
        simpa only [temporary2] using
          matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal subtracted hlayout.control_ne_terminal
      _ = subEnabled registers.control := hsubtractedControl
  have htemporary2Phase1 : temporary2 registers.phase1 =
      temporary1 registers.phase1 := by
    calc
      temporary2 registers.phase1 = subtracted registers.phase1 := by
        simpa only [temporary2] using
          matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal subtracted (Ne.symm hterminalNePhase1)
      _ = state registers.phase1 := hsubtractedPhase1
      _ = temporary1 registers.phase1 := by
        symm
        simpa only [temporary1] using
          matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal state (Ne.symm hterminalNePhase1)
  have htemporary2Terminal : temporary2 registers.terminal =
      temporary1 registers.terminal := by
    have hpredicate : registerMatches [registers.phase2, registers.sign] 2
        subtracted = registerMatches [registers.phase2, registers.sign] 2 state := by
      apply registerMatches_congr
      intro wire hwire
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
      rcases hwire with rfl | rfl
      · exact hsubtractedPhase2
      · exact hsubtractedSign
    simp [temporary2, matchXorState, hsubtractedTerminal, hpredicate,
      htemporary1Terminal]
  have hsubClearedControl : subCleared registers.control = false := by
    apply matchXorState_clears [registers.phase1, registers.terminal] 1
      registers.control temporary1 temporary2
    · exact htemporary2Control.trans hsubEnabledControl
    · intro wire hwire
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
      rcases hwire with rfl | rfl
      · exact htemporary2Phase1
      · exact htemporary2Terminal
  have hsubClearedTerminal : subCleared registers.terminal =
      temporary2 registers.terminal := by
    simpa only [subCleared] using
      matchXorState_preserves [registers.phase1, registers.terminal] 1
        registers.control temporary2 (Ne.symm hlayout.control_ne_terminal)
  have hsubClearedPhase2 : subCleared registers.phase2 =
      subtracted registers.phase2 := by
    calc
      subCleared registers.phase2 = temporary2 registers.phase2 := by
        simpa only [subCleared] using
          matchXorState_preserves [registers.phase1, registers.terminal] 1
            registers.control temporary2 (Ne.symm hcontrolNePhase2)
      _ = subtracted registers.phase2 := by
        simpa only [temporary2] using
          matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal subtracted (Ne.symm hterminalNePhase2)
  have hsubClearedSign : subCleared registers.sign = subtracted registers.sign := by
    calc
      subCleared registers.sign = temporary2 registers.sign := by
        simpa only [subCleared] using
          matchXorState_preserves [registers.phase1, registers.terminal] 1
            registers.control temporary2 (Ne.symm hcontrolNeSign)
      _ = subtracted registers.sign := by
        simpa only [temporary2] using
          matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal subtracted (Ne.symm hterminalNeSign)
  have htemporaryCleared2Terminal :
      temporaryCleared2 registers.terminal = false := by
    apply matchXorState_clears [registers.phase2, registers.sign] 2
      registers.terminal subtracted subCleared
    · calc
        subCleared registers.terminal = temporary2 registers.terminal :=
          hsubClearedTerminal
        _ = temporary1 registers.terminal := htemporary2Terminal
        _ = registerMatches [registers.phase2, registers.sign] 2 state :=
          htemporary1Terminal
        _ = registerMatches [registers.phase2, registers.sign] 2 subtracted := by
          symm
          apply registerMatches_congr
          intro wire hwire
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
          rcases hwire with rfl | rfl
          · exact hsubtractedPhase2
          · exact hsubtractedSign
    · intro wire hwire
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
      rcases hwire with rfl | rfl
      · exact hsubClearedPhase2
      · exact hsubClearedSign
  have htemporaryCleared2Control : temporaryCleared2 registers.control = false := by
    calc
      temporaryCleared2 registers.control = subCleared registers.control := by
        simpa only [temporaryCleared2] using
          matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal subCleared hlayout.control_ne_terminal
      _ = false := hsubClearedControl
  have hsignChangedControl : signChanged registers.control = false := by
    simpa [signChanged, xorWireState, upd, hcontrolNeSign] using
      htemporaryCleared2Control
  have hsignChangedTerminal : signChanged registers.terminal = false := by
    simpa [signChanged, xorWireState, upd, hterminalNeSign] using
      htemporaryCleared2Terminal
  have haddEnabledControl : addEnabled registers.control =
      registerMatches [registers.phase1] 1 signChanged := by
    simp [addEnabled, matchXorState, hsignChangedControl]
  have haddedControl : added registers.control =
      registerMatches [registers.phase1] 1 signChanged := by
    calc
      added registers.control =
          run (coefficientPrefixUnitary (registers.coefficient window)
            window.start window.stop .add true .work2) addEnabled
              registers.control := by
        simpa only [added] using congrFun hadded.1.symm registers.control
      _ = addEnabled registers.control := hadded.2.2.1
      _ = _ := haddEnabledControl
  have haddedPhase1 : added registers.phase1 = signChanged registers.phase1 := by
    calc
      added registers.phase1 =
          run (coefficientPrefixUnitary (registers.coefficient window)
            window.start window.stop .add true .work2) addEnabled
              registers.phase1 := by
        simpa only [added] using congrFun hadded.1.symm registers.phase1
      _ = addEnabled registers.phase1 := by
        exact coefficientPrefixUnitary_preservesOutside
          (registers.coefficient window) .add true .work2 addEnabled
            hcoefficientLayout (hlayout.phase1_not_coefficient window)
      _ = signChanged registers.phase1 := by
        simpa only [addEnabled] using
          matchXorState_preserves [registers.phase1] 1 registers.control
            signChanged (Ne.symm hlayout.control_ne_phase1)
  have haddClearedControl : addCleared registers.control = false := by
    apply matchXorState_clears [registers.phase1] 1 registers.control
      signChanged added haddedControl
    intro wire hwire
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
    subst wire
    exact haddedPhase1
  have haddedTerminal : added registers.terminal = false := by
    calc
      added registers.terminal =
          run (coefficientPrefixUnitary (registers.coefficient window)
            window.start window.stop .add true .work2) addEnabled
              registers.terminal := by
        simpa only [added] using congrFun hadded.1.symm registers.terminal
      _ = addEnabled registers.terminal := by
        exact coefficientPrefixUnitary_preservesOutside
          (registers.coefficient window) .add true .work2 addEnabled
            hcoefficientLayout (hlayout.terminal_not_coefficient window)
      _ = signChanged registers.terminal := by
        simpa only [addEnabled] using
          matchXorState_preserves [registers.phase1] 1 registers.control
            signChanged (Ne.symm hlayout.control_ne_terminal)
      _ = false := hsignChangedTerminal
  have haddClearedTerminal : addCleared registers.terminal = false := by
    calc
      addCleared registers.terminal = added registers.terminal := by
        simpa only [addCleared] using
          matchXorState_preserves [registers.phase1] 1 registers.control added
            (Ne.symm hlayout.control_ne_terminal)
      _ = false := haddedTerminal
  have hrestoredControl : restored registers.control = false := by
    calc
      restored registers.control = addCleared registers.control := by
        simpa only [restored] using
          tBoundaryRestoreState_preservesOutside registers n addCleared
            (hfixedNotWords registers.control (by simp)).1
            (hfixedNotWords registers.control (by simp)).2
      _ = false := haddClearedControl
  have hrestoredTerminal : restored registers.terminal = false := by
    calc
      restored registers.terminal = addCleared registers.terminal := by
        simpa only [restored] using
          tBoundaryRestoreState_preservesOutside registers n addCleared
            (hfixedNotWords registers.terminal (by simp)).1
            (hfixedNotWords registers.terminal (by simp)).2
      _ = false := haddClearedTerminal
  have hrestoredBlock : Clean registers.blockScratch restored := by
    simpa only [restored, hrestored.1] using hrestored.2
  constructor
  · exact hrun.trans hstate
  · rw [hrun]
    intro wire hwire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons] at hwire
    rcases hwire with rfl | hsource
    · exact hrestoredControl
    · rw [← hlayout.scratch_view] at hsource
      simp only [List.mem_cons] at hsource
      rcases hsource with rfl | hblockWire
      · exact hrestoredTerminal
      · exact hrestoredBlock wire hblockWire

private theorem blockFForward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state) :
    run (blockFForward registers) state = blockFForwardState registers state ∧
      IndexedStepReady registers (run (blockFForward registers) state) := by
  have hlocalReady : ShiftReady registers.postShift state := by
    intro wire hwire
    apply hready wire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons]
    exact Or.inr (hlayout.postShift_scratch_sub_source wire hwire)
  have hrun := run_postShiftUnitary registers.postShift state
    hlayout.postShift hlocalReady
  have hlocalAfter := postShiftUnitary_ready registers.postShift state
    hlayout.postShift hlocalReady
  have hglobalAfter : Clean registers.sharedScratch
      (run (postShiftUnitary registers.postShift) state) :=
    clean_after_local_circuit hready hlocalAfter
      (postShiftUnitary_usesOnly registers.postShift)
      hlayout.postShift_support_intersection
  constructor
  · simpa only [blockFForward, blockFForwardState] using hrun
  · simpa only [blockFForward] using hglobalAfter

private theorem blockGForward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state) :
    run (blockGForward registers) state = blockGForwardState registers state ∧
      IndexedStepReady registers (run (blockGForward registers) state) := by
  have hlocalReady : PhaseUpdateReady registers.phaseUpdate state := by
    intro wire hwire
    apply hready wire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons]
    exact Or.inr (hlayout.phaseUpdate_scratch_sub_source wire hwire)
  have hrun := run_phaseUpdateEpochUnitary registers.phaseUpdate
    registers.shiftEpoch state hlayout.phaseUpdate hlocalReady
  have hlocalAfter := phaseUpdateEpochUnitary_ready registers.phaseUpdate
    registers.shiftEpoch state hlayout.phaseUpdate hlocalReady
  have hglobalAfter : Clean registers.sharedScratch
      (run (phaseUpdateEpochUnitary registers.phaseUpdate registers.shiftEpoch)
        state) :=
    clean_after_local_circuit hready hlocalAfter
      (phaseUpdateEpochUnitary_usesOnly registers.phaseUpdate registers.shiftEpoch)
      hlayout.phaseUpdate_support_intersection
  constructor
  · simpa only [blockGForward, blockGForwardState] using hrun
  · simpa only [blockGForward] using hglobalAfter

private theorem blockHForward_run
    (registers : IndexedStepRegisters) (n T boundary4 boundary5 : Nat)
    (hboundary4 : (endIterationWindowsAt n T).k4 ≤ boundary4 ∧
      boundary4 ≤ (endIterationWindowsAt n T).K4)
    (hboundary5 : (endIterationWindowsAt n T).k5 ≤ boundary5 ∧
      boundary5 ≤ (endIterationWindowsAt n T).K5Decode n)
    (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hroute4 : T % 4 = 0 →
      ((registers.endIteration n T).upperTree
        (endIterationWindowsAt n T)).routeLabel
        (run (constMinus (registers.endIteration n T).lengthRP
            (registers.endIteration n T).constants
            (registers.endIteration n T).carry (n + 2))
          (run (controlledWorkSwap (registers.endIteration n T).control
            (registers.endIteration n T).work1
            (registers.endIteration n T).work2)
            (blockHEndInputState registers state))) = boundary4)
    (hroute5 : T % 4 = 0 →
      ((registers.endIteration n T).lowerTree n
        (endIterationWindowsAt n T)).routeLabel
        (run (addConstant (registers.endIteration n T).lengthT
            (registers.endIteration n T).constants
            (registers.endIteration n T).carry 3)
          (run (lenUpdateLtUnary n (endIterationWindowsAt n T).k4
            (endIterationWindowsAt n T).K4
            ((registers.endIteration n T).upperTree (endIterationWindowsAt n T))
            (registers.endIteration n T).control
            ((registers.endIteration n T).rangeAccumulator
              (endIterationWindowsAt n T).k4 (endIterationWindowsAt n T).K4)
            ((registers.endIteration n T).temporary
              (endIterationWindowsAt n T).k4 (endIterationWindowsAt n T).K4)
            (registers.endIteration n T).carry
            ((registers.endIteration n T).path
              (endIterationWindowsAt n T).k4 (endIterationWindowsAt n T).K4)
            (registers.endIteration n T).work1At
            (registers.endIteration n T).work2At
            (registers.endIteration n T).lengthT
            (registers.endIteration n T).lengthRP
            (registers.endIteration n T).constants)
          (run (controlledWorkSwap (registers.endIteration n T).control
            (registers.endIteration n T).work1
            (registers.endIteration n T).work2)
            (blockHEndInputState registers state)))) = boundary5)
    (hready : IndexedStepReady registers state) :
    run (blockHForward registers n T) state =
      blockHForwardState registers n T boundary4 boundary5 state := by
  by_cases hstep : T % 4 = 0
  · let zeroQ := blockHZeroQState registers state
    let beforeS := blockHBeforeSState registers state
    let zeroS := blockHZeroSState registers state
    let restoredEpoch :=
      zeroS[registers.shiftEpoch ↦ !zeroS registers.shiftEpoch]
    let enabled := blockHEndInputState registers state
    let changed := endIterationForwardState registers n T boundary4 boundary5 enabled
    let iterated := xorWireState registers.control registers.iter changed
    let disabled := andXorWireState (registers.sourceScratch.getD 0 0)
      (registers.sourceScratch.getD 1 0) registers.control iterated
    let epochBeforeClear :=
      disabled[registers.shiftEpoch ↦ !disabled registers.shiftEpoch]
    let clearedS := andListXorState (registers.lengthS ++ [registers.shiftEpoch])
      (registers.sourceScratch.getD 1 0) epochBeforeClear
    let restoredEpochAgain :=
      clearedS[registers.shiftEpoch ↦ !clearedS registers.shiftEpoch]
    let after := andListXorState registers.lengthQ
      (registers.sourceScratch.getD 0 0) restoredEpochAgain
    have hcleanTail : Clean (registers.sourceScratch.drop 2) state := by
      intro wire hwire
      apply hready wire
      simp only [IndexedStepRegisters.sharedScratch, List.mem_cons]
      exact Or.inr (List.mem_of_mem_drop hwire)
    have hq := run_mcxVChain_andListXorState registers.lengthQ
      (registers.sourceScratch.getD 0 0) (registers.sourceScratch.drop 2)
      state hlayout.endQ.1 hlayout.endQ.2 hcleanTail
    have hqRun : run (mcxVChain registers.lengthQ
        (registers.sourceScratch.getD 0 0) (registers.sourceScratch.drop 2))
        state = zeroQ := by
      simpa only [zeroQ, blockHZeroQState] using hq.1
    have hzeroQClean : Clean (registers.sourceScratch.drop 2) zeroQ := by
      simpa only [zeroQ, blockHZeroQState] using hq.2
    have hepochNotTail : registers.shiftEpoch ∉ registers.sourceScratch.drop 2 := by
      intro hmem
      exact hlayout.shiftEpoch_not_sourceScratch (List.mem_of_mem_drop hmem)
    have hbeforeSClean : Clean (registers.sourceScratch.drop 2) beforeS := by
      intro wire hwire
      simp only [beforeS, blockHBeforeSState]
      rw [upd_other]
      · exact hzeroQClean wire hwire
      · intro equality
        subst wire
        exact hepochNotTail hwire
    have hs := run_mcxVChain_andListXorState
      (registers.lengthS ++ [registers.shiftEpoch])
      (registers.sourceScratch.getD 1 0) (registers.sourceScratch.drop 2)
      beforeS hlayout.endS.1 hlayout.endS.2 hbeforeSClean
    have hsRun : run (mcxVChain (registers.lengthS ++ [registers.shiftEpoch])
        (registers.sourceScratch.getD 1 0) (registers.sourceScratch.drop 2))
        beforeS = zeroS := by
      simpa only [zeroS, blockHZeroSState, beforeS, blockHBeforeSState]
        using hs.1
    have hzeroSClean : Clean (registers.sourceScratch.drop 2) zeroS := by
      simpa only [zeroS, blockHZeroSState] using hs.2
    have hrestoredEpochClean : Clean (registers.sourceScratch.drop 2)
        restoredEpoch := by
      intro wire hwire
      simp only [restoredEpoch]
      rw [upd_other]
      · exact hzeroSClean wire hwire
      · intro equality
        subst wire
        exact hepochNotTail hwire
    have hcontrolNotTail : registers.control ∉ registers.sourceScratch.drop 2 := by
      intro hmem
      exact hlayout.control_not_sourceScratch (List.mem_of_mem_drop hmem)
    have henabledClean : Clean (registers.sourceScratch.drop 2) enabled := by
      intro wire hwire
      simp only [enabled, blockHEndInputState]
      rw [andXorWireState_preserves _ _ _ _]
      · exact hrestoredEpochClean wire hwire
      · intro equality
        subst wire
        exact hcontrolNotTail hwire
    have hendReady : EndIterationReady (registers.endIteration n T) enabled := by
      intro wire hwire
      apply henabledClean wire
      exact List.mem_of_mem_take (by
        simpa [IndexedStepRegisters.endIteration] using hwire)
    have hend := run_endIterationForwardState registers n T boundary4 boundary5
      hboundary4 hboundary5 enabled hlayout hstep (hroute4 hstep)
      (hroute5 hstep) hendReady
    have hx1 : run ([.X registers.shiftEpoch] : Circuit) zeroQ = beforeS := by
      rfl
    have hx2 : run ([.X registers.shiftEpoch] : Circuit) zeroS = restoredEpoch := by
      rfl
    have hccx1 : run ([.CCX (registers.sourceScratch.getD 0 0)
        (registers.sourceScratch.getD 1 0) registers.control] : Circuit)
        restoredEpoch = enabled := by
      rfl
    have hgroup1 : run ([.X registers.shiftEpoch,
        .CCX (registers.sourceScratch.getD 0 0)
          (registers.sourceScratch.getD 1 0) registers.control] : Circuit)
        zeroS = enabled := by
      calc
        _ = run ([.CCX (registers.sourceScratch.getD 0 0)
            (registers.sourceScratch.getD 1 0) registers.control] : Circuit)
            (run ([.X registers.shiftEpoch] : Circuit) zeroS) := by rfl
        _ = enabled := by rw [hx2, hccx1]
    have hcx : run ([.CX registers.control registers.iter] : Circuit) changed =
        iterated := by
      rfl
    have hccx2 : run ([.CCX (registers.sourceScratch.getD 0 0)
        (registers.sourceScratch.getD 1 0) registers.control] : Circuit)
        iterated = disabled := by
      rfl
    have hx3 : run ([.X registers.shiftEpoch] : Circuit) disabled =
        epochBeforeClear := by
      rfl
    have hgroup2 : run ([.CX registers.control registers.iter,
        .CCX (registers.sourceScratch.getD 0 0)
          (registers.sourceScratch.getD 1 0) registers.control,
        .X registers.shiftEpoch] : Circuit) changed = epochBeforeClear := by
      calc
        _ = run ([.X registers.shiftEpoch] : Circuit)
            (run ([.CCX (registers.sourceScratch.getD 0 0)
              (registers.sourceScratch.getD 1 0) registers.control] : Circuit)
              (run ([.CX registers.control registers.iter] : Circuit) changed)) := by rfl
        _ = epochBeforeClear := by rw [hcx, hccx2, hx3]
    have hchangedTail : Clean (registers.sourceScratch.drop 2) changed := by
      intro wire hwire
      simp only [changed]
      rw [endIterationForwardState_preservesOutside]
      · exact henabledClean wire hwire
      · exact hlayout.aux_not_endIterationMutable
          (hlayout.sourceScratch_mem_aux (List.mem_of_mem_drop hwire))
    have hiterNotTail : registers.iter ∉ registers.sourceScratch.drop 2 := by
      intro hmem
      apply (hlayout.aux_not_payload
        (hlayout.sourceScratch_mem_aux (List.mem_of_mem_drop hmem)) (by
          simp [indexedStepPayload])) rfl
    have hiteratedTail : Clean (registers.sourceScratch.drop 2) iterated := by
      intro wire hwire
      simp only [iterated]
      rw [xorWireState_preserves _ _ _ _]
      · exact hchangedTail wire hwire
      · intro equality
        subst wire
        exact hiterNotTail hwire
    have hdisabledTail : Clean (registers.sourceScratch.drop 2) disabled := by
      intro wire hwire
      simp only [disabled]
      rw [andXorWireState_preserves _ _ _ _]
      · exact hiteratedTail wire hwire
      · intro equality
        subst wire
        exact hcontrolNotTail hwire
    have hepochBeforeClearTail : Clean (registers.sourceScratch.drop 2)
        epochBeforeClear := by
      intro wire hwire
      simp only [epochBeforeClear]
      rw [upd_other]
      · exact hdisabledTail wire hwire
      · intro equality
        subst wire
        exact hepochNotTail hwire
    have hsClear := run_mcxVChain_andListXorState
      (registers.lengthS ++ [registers.shiftEpoch])
      (registers.sourceScratch.getD 1 0) (registers.sourceScratch.drop 2)
      epochBeforeClear hlayout.endS.1 hlayout.endS.2 hepochBeforeClearTail
    have hsClearRun : run (mcxVChain
        (registers.lengthS ++ [registers.shiftEpoch])
        (registers.sourceScratch.getD 1 0) (registers.sourceScratch.drop 2))
        epochBeforeClear = clearedS := by
      simpa only [clearedS] using hsClear.1
    have hclearedSTail : Clean (registers.sourceScratch.drop 2) clearedS := by
      simpa only [clearedS] using hsClear.2
    have hrestoredAgainTail : Clean (registers.sourceScratch.drop 2)
        restoredEpochAgain := by
      intro wire hwire
      simp only [restoredEpochAgain]
      rw [upd_other]
      · exact hclearedSTail wire hwire
      · intro equality
        subst wire
        exact hepochNotTail hwire
    have hx4 : run ([.X registers.shiftEpoch] : Circuit) clearedS =
        restoredEpochAgain := by
      rfl
    have hqClear := run_mcxVChain_andListXorState registers.lengthQ
      (registers.sourceScratch.getD 0 0) (registers.sourceScratch.drop 2)
      restoredEpochAgain hlayout.endQ.1 hlayout.endQ.2 hrestoredAgainTail
    have hqClearRun : run (mcxVChain registers.lengthQ
        (registers.sourceScratch.getD 0 0) (registers.sourceScratch.drop 2))
        restoredEpochAgain = after := by
      simpa only [after] using hqClear.1
    simp only [blockHForward, hstep, if_pos, Classical.run_append]
    rw [hqRun, hx1, hsRun, hgroup1, hend.1, hgroup2,
      hsClearRun, hx4, hqClearRun]
    simp only [after, restoredEpochAgain, clearedS, epochBeforeClear,
      disabled, iterated, changed, enabled, blockHForwardState, hstep, if_pos]
  · simp [blockHForward, blockHForwardState, hstep]

private theorem blockHForwardState_ready
    (registers : IndexedStepRegisters) (n T boundary4 boundary5 : Nat)
    (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state) :
    IndexedStepReady registers
      (blockHForwardState registers n T boundary4 boundary5 state) := by
  by_cases hstep : T % 4 = 0
  · let q := registers.sourceScratch.getD 0 0
    let s := registers.sourceScratch.getD 1 0
    let epoch := registers.shiftEpoch
    let control := registers.control
    let iter := registers.iter
    let zeroQ := blockHZeroQState registers state
    let beforeS := blockHBeforeSState registers state
    let zeroS := blockHZeroSState registers state
    let restoredEpoch := zeroS[epoch ↦ !zeroS epoch]
    let enabled := blockHEndInputState registers state
    let changed := endIterationForwardState registers n T boundary4 boundary5 enabled
    let iterated := xorWireState control iter changed
    let disabled := andXorWireState q s control iterated
    let epochBeforeClear := disabled[epoch ↦ !disabled epoch]
    let clearedS := andListXorState (registers.lengthS ++ [epoch]) s
      epochBeforeClear
    let restoredEpochAgain := clearedS[epoch ↦ !clearedS epoch]
    let after := andListXorState registers.lengthQ q restoredEpochAgain
    have hview : q :: s :: registers.sourceScratch.drop 2 =
        registers.sourceScratch := by
      simpa only [q, s] using hlayout.sourceScratch_view2
    have hqMem : q ∈ registers.sourceScratch := by
      rw [← hview]
      simp
    have hsMem : s ∈ registers.sourceScratch := by
      rw [← hview]
      simp
    have hqAux := hlayout.sourceScratch_mem_aux hqMem
    have hsAux := hlayout.sourceScratch_mem_aux hsMem
    have hepochAux := hlayout.shiftEpoch_mem_aux
    have hcontrolAux := hlayout.control_mem_aux
    have hiterPayload : iter ∈ indexedStepPayload registers := by
      simp [iter, indexedStepPayload]
    have hendDistinct := hlayout.endControls
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hendDistinct
    have hqNeS : q ≠ s := by
      simpa only [q, s] using hendDistinct.1.1
    have hqNeControl : q ≠ control := by
      simpa only [q, control] using hendDistinct.1.2.1
    have hqNeIter : q ≠ iter := by
      simpa only [q, iter] using hendDistinct.1.2.2
    have hsNeControl : s ≠ control := by
      simpa only [s, control] using hendDistinct.2.1.1
    have hsNeIter : s ≠ iter := by
      simpa only [s, iter] using hendDistinct.2.1.2
    have hcontrolNeIter : control ≠ iter := by
      simpa only [control, iter] using hendDistinct.2.2.1
    have hqNeEpoch : q ≠ epoch := by
      intro equality
      apply hlayout.shiftEpoch_not_sourceScratch
      have hmem : epoch ∈ registers.sourceScratch := equality ▸ hqMem
      simpa only [epoch] using hmem
    have hsNeEpoch : s ≠ epoch := by
      intro equality
      apply hlayout.shiftEpoch_not_sourceScratch
      have hmem : epoch ∈ registers.sourceScratch := equality ▸ hsMem
      simpa only [epoch] using hmem
    have hcontrolNeEpoch : control ≠ epoch := by
      have hauxDistinct : (control :: epoch :: registers.sourceScratch).Nodup := by
        simpa only [control, epoch, List.cons_append, List.nil_append] using
          hlayout.aux_view_nodup
      intro equality
      apply (List.nodup_cons.mp hauxDistinct).1
      rw [equality]
      simp
    have hepochNeControl : epoch ≠ control := hcontrolNeEpoch.symm
    have hepochNeIter : epoch ≠ iter := by
      exact hlayout.aux_not_payload hepochAux hiterPayload
    have hqNotMutable : q ∉ endIterationMutableWires registers :=
      hlayout.aux_not_endIterationMutable hqAux
    have hsNotMutable : s ∉ endIterationMutableWires registers :=
      hlayout.aux_not_endIterationMutable hsAux
    have hepochNotMutable : epoch ∉ endIterationMutableWires registers :=
      hlayout.aux_not_endIterationMutable hepochAux
    have hcontrolNotMutable : control ∉ endIterationMutableWires registers :=
      hlayout.aux_not_endIterationMutable hcontrolAux
    have hqInitial : state q = false := by
      apply hready q
      simp [IndexedStepRegisters.sharedScratch, hqMem]
    have hsInitial : state s = false := by
      apply hready s
      simp [IndexedStepRegisters.sharedScratch, hsMem]
    have hcontrolInitial : state control = false := by
      apply hready control
      simp [IndexedStepRegisters.sharedScratch, control]
    have hbetween (wire : Wire)
        (hwireS : wire ≠ s) (hwireEpoch : wire ≠ epoch)
        (hwireControl : wire ≠ control) (hwireIter : wire ≠ iter)
        (hwireMutable : wire ∉ endIterationMutableWires registers) :
        epochBeforeClear wire = beforeS wire := by
      calc
        epochBeforeClear wire = disabled wire := by
          simp [epochBeforeClear, upd, hwireEpoch]
        _ = iterated wire :=
          andXorWireState_preserves q s control iterated hwireControl
        _ = changed wire :=
          xorWireState_preserves control iter changed hwireIter
        _ = enabled wire :=
          endIterationForwardState_preservesOutside registers n T boundary4
            boundary5 enabled hwireMutable
        _ = restoredEpoch wire :=
          andXorWireState_preserves q s control restoredEpoch hwireControl
        _ = zeroS wire := by
          simp [restoredEpoch, upd, hwireEpoch]
        _ = beforeS wire :=
          andListXorState_preserves (registers.lengthS ++ [epoch]) s
            beforeS hwireS
    have hfull (wire : Wire)
        (hwireQ : wire ≠ q) (hwireS : wire ≠ s)
        (hwireEpoch : wire ≠ epoch) (hwireControl : wire ≠ control)
        (hwireIter : wire ≠ iter)
        (hwireMutable : wire ∉ endIterationMutableWires registers) :
        restoredEpochAgain wire = state wire := by
      calc
        restoredEpochAgain wire = clearedS wire := by
          simp [restoredEpochAgain, upd, hwireEpoch]
        _ = epochBeforeClear wire :=
          andListXorState_preserves (registers.lengthS ++ [epoch]) s
            epochBeforeClear hwireS
        _ = beforeS wire := hbetween wire hwireS hwireEpoch hwireControl
          hwireIter hwireMutable
        _ = zeroQ wire := by
          simp [beforeS, blockHBeforeSState, zeroQ, epoch, upd, hwireEpoch]
        _ = state wire :=
          andListXorState_preserves registers.lengthQ q state hwireQ
    have hqAtRestored : restoredEpochAgain q =
        wireAnd registers.lengthQ state := by
      calc
        restoredEpochAgain q = clearedS q := by
          simp [restoredEpochAgain, upd, hqNeEpoch]
        _ = epochBeforeClear q :=
          andListXorState_preserves (registers.lengthS ++ [epoch]) s
            epochBeforeClear hqNeS
        _ = beforeS q := hbetween q hqNeS hqNeEpoch hqNeControl hqNeIter
          hqNotMutable
        _ = zeroQ q := by
          simp [beforeS, blockHBeforeSState, zeroQ, epoch, upd, hqNeEpoch]
        _ = wireAnd registers.lengthQ state := by
          change state[q ↦ Bool.xor (state q)
            (wireAnd registers.lengthQ state)] q =
              wireAnd registers.lengthQ state
          simp [hqInitial]
    have hlengthQ : ∀ wire ∈ registers.lengthQ,
        restoredEpochAgain wire = state wire := by
      intro wire hwire
      have hpayload : wire ∈ indexedStepPayload registers := by
        simp [indexedStepPayload, hwire]
      have hwireQ : wire ≠ q := (hlayout.aux_not_payload hqAux hpayload).symm
      have hwireS : wire ≠ s := (hlayout.aux_not_payload hsAux hpayload).symm
      have hwireEpoch : wire ≠ epoch :=
        (hlayout.aux_not_payload hepochAux hpayload).symm
      have hwireControl : wire ≠ control :=
        (hlayout.aux_not_payload hcontrolAux hpayload).symm
      have hwireIter : wire ≠ iter := by
        exact hlayout.lengthQ_ne_outside hwire (Or.inl (by
          simp [iter, indexedStepBeforeLengthQ]))
      exact hfull wire hwireQ hwireS hwireEpoch hwireControl hwireIter
        (hlayout.lengthQ_not_endIterationMutable hwire)
    have hqAfter : after q = false := by
      have hand := wireAnd_congr registers.lengthQ restoredEpochAgain state
        hlengthQ
      simp only [after, andListXorState, upd_same]
      rw [hqAtRestored, hand]
      simp
    have hsAtEpochBefore : epochBeforeClear s =
        wireAnd (registers.lengthS ++ [epoch]) beforeS := by
      calc
        epochBeforeClear s = disabled s := by
          simp [epochBeforeClear, upd, hsNeEpoch]
        _ = iterated s := andXorWireState_preserves q s control iterated
          hsNeControl
        _ = changed s := xorWireState_preserves control iter changed hsNeIter
        _ = enabled s := endIterationForwardState_preservesOutside registers n T
          boundary4 boundary5 enabled hsNotMutable
        _ = restoredEpoch s := andXorWireState_preserves q s control restoredEpoch
          hsNeControl
        _ = zeroS s := by
          simp [restoredEpoch, upd, hsNeEpoch]
        _ = wireAnd (registers.lengthS ++ [epoch]) beforeS := by
          have hbeforeS : beforeS s = false := by
            calc
              beforeS s = zeroQ s := by
                simp [beforeS, blockHBeforeSState, zeroQ, epoch, upd,
                  hsNeEpoch]
              _ = state s := andListXorState_preserves registers.lengthQ q
                state hqNeS.symm
              _ = false := hsInitial
          change beforeS[s ↦ Bool.xor (beforeS s)
            (wireAnd (registers.lengthS ++ [epoch]) beforeS)] s =
              wireAnd (registers.lengthS ++ [epoch]) beforeS
          simp [hbeforeS]
    have hlengthS : ∀ wire ∈ registers.lengthS,
        epochBeforeClear wire = beforeS wire := by
      intro wire hwire
      have hpayload : wire ∈ indexedStepPayload registers := by
        simp [indexedStepPayload, hwire]
      have hwireS : wire ≠ s := (hlayout.aux_not_payload hsAux hpayload).symm
      have hwireEpoch : wire ≠ epoch :=
        (hlayout.aux_not_payload hepochAux hpayload).symm
      have hwireControl : wire ≠ control :=
        (hlayout.aux_not_payload hcontrolAux hpayload).symm
      exact hbetween wire hwireS hwireEpoch hwireControl
        (by simpa only [iter] using hlayout.lengthS_ne_iter hwire)
        (hlayout.lengthS_not_endIterationMutable hwire)
    have hepochBetween : epochBeforeClear epoch = beforeS epoch := by
      calc
        epochBeforeClear epoch = !disabled epoch := by
          simp [epochBeforeClear]
        _ = !iterated epoch := by
          simp only [disabled]
          rw [andXorWireState_preserves q s control iterated hepochNeControl]
        _ = !changed epoch := by
          simp only [iterated]
          rw [xorWireState_preserves control iter changed hepochNeIter]
        _ = !enabled epoch := by
          simp only [changed]
          rw [endIterationForwardState_preservesOutside registers n T boundary4
            boundary5 enabled hepochNotMutable]
        _ = !restoredEpoch epoch := by
          simp only [enabled, blockHEndInputState, epoch]
          rw [andXorWireState_preserves q s control restoredEpoch hepochNeControl]
        _ = zeroS epoch := by
          simp [restoredEpoch]
        _ = beforeS epoch :=
          andListXorState_preserves (registers.lengthS ++ [epoch]) s beforeS
            hsNeEpoch.symm
    have hlengthSEpoch : ∀ wire ∈ registers.lengthS ++ [epoch],
        epochBeforeClear wire = beforeS wire := by
      intro wire hwire
      simp only [List.mem_append, List.mem_singleton] at hwire
      rcases hwire with hlength | rfl
      · exact hlengthS wire hlength
      · exact hepochBetween
    have hsCleared : clearedS s = false := by
      have hand := wireAnd_congr (registers.lengthS ++ [epoch])
        epochBeforeClear beforeS hlengthSEpoch
      simp only [clearedS, andListXorState, upd_same]
      rw [hsAtEpochBefore, hand]
      simp
    have hsAfter : after s = false := by
      calc
        after s = restoredEpochAgain s :=
          andListXorState_preserves registers.lengthQ q restoredEpochAgain
            hqNeS.symm
        _ = clearedS s := by
          simp [restoredEpochAgain, upd, hsNeEpoch]
        _ = false := hsCleared
    have hrestoredControl : restoredEpoch control = false := by
      calc
        restoredEpoch control = zeroS control := by
          simp [restoredEpoch, upd, hepochNeControl.symm]
        _ = beforeS control :=
          andListXorState_preserves (registers.lengthS ++ [epoch]) s beforeS
            hsNeControl.symm
        _ = zeroQ control := by
          simp [beforeS, blockHBeforeSState, zeroQ, epoch, upd,
            hepochNeControl.symm]
        _ = state control :=
          andListXorState_preserves registers.lengthQ q state
            hqNeControl.symm
        _ = false := hcontrolInitial
    have henabledControl : enabled control = (enabled q && enabled s) := by
      change (andXorWireState q s control restoredEpoch) control =
        ((andXorWireState q s control restoredEpoch) q &&
          (andXorWireState q s control restoredEpoch) s)
      simp [andXorWireState, upd, hrestoredControl, hqNeControl,
        hsNeControl]
    have hchangedControl : changed control = enabled control :=
      endIterationForwardState_preservesOutside registers n T boundary4 boundary5
        enabled hcontrolNotMutable
    have hchangedQ : changed q = enabled q :=
      endIterationForwardState_preservesOutside registers n T boundary4 boundary5
        enabled hqNotMutable
    have hchangedS : changed s = enabled s :=
      endIterationForwardState_preservesOutside registers n T boundary4 boundary5
        enabled hsNotMutable
    have hiteratedControl : iterated control = changed control :=
      xorWireState_preserves control iter changed hcontrolNeIter
    have hiteratedQ : iterated q = changed q :=
      xorWireState_preserves control iter changed hqNeIter
    have hiteratedS : iterated s = changed s :=
      xorWireState_preserves control iter changed hsNeIter
    have hdisabledControl : disabled control = false := by
      simp only [disabled, andXorWireState, upd_same]
      rw [hiteratedControl, hchangedControl, hiteratedQ, hchangedQ,
        hiteratedS, hchangedS, henabledControl]
      simp
    have hcontrolAfter : after control = false := by
      calc
        after control = restoredEpochAgain control :=
          andListXorState_preserves registers.lengthQ q restoredEpochAgain
            hqNeControl.symm
        _ = clearedS control := by
          simp [restoredEpochAgain, upd, hepochNeControl.symm]
        _ = epochBeforeClear control :=
          andListXorState_preserves (registers.lengthS ++ [epoch]) s
            epochBeforeClear hsNeControl.symm
        _ = disabled control := by
          simp [epochBeforeClear, upd, hepochNeControl.symm]
        _ = false := hdisabledControl
    have htailAfter : Clean (registers.sourceScratch.drop 2) after := by
      intro wire hwire
      have hsource : wire ∈ registers.sourceScratch := List.mem_of_mem_drop hwire
      have hwireQ : wire ≠ q := by
        have hnodup : (q :: s :: registers.sourceScratch.drop 2).Nodup := by
          rw [hview]
          exact hlayout.sourceScratch_nodup
        intro equality
        apply (List.nodup_cons.mp hnodup).1
        simp [← equality, hwire]
      have hwireS : wire ≠ s := by
        have hnodup : (q :: s :: registers.sourceScratch.drop 2).Nodup := by
          rw [hview]
          exact hlayout.sourceScratch_nodup
        intro equality
        apply (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).1
        rwa [← equality]
      have hwireEpoch : wire ≠ epoch := by
        intro equality
        apply hlayout.shiftEpoch_not_sourceScratch
        have hmem : epoch ∈ registers.sourceScratch := equality ▸ hsource
        simpa only [epoch] using hmem
      have hwireControl : wire ≠ control := by
        intro equality
        apply hlayout.control_not_sourceScratch
        have hmem : control ∈ registers.sourceScratch := equality ▸ hsource
        simpa only [control] using hmem
      have hwireIter : wire ≠ iter := by
        exact hlayout.aux_not_payload (hlayout.sourceScratch_mem_aux hsource)
          hiterPayload
      have hpreserved := hfull wire hwireQ hwireS hwireEpoch hwireControl
        hwireIter (hlayout.aux_not_endIterationMutable
          (hlayout.sourceScratch_mem_aux hsource))
      calc
        after wire = restoredEpochAgain wire :=
          andListXorState_preserves registers.lengthQ q restoredEpochAgain hwireQ
        _ = state wire := hpreserved
        _ = false := hready wire (by
          simp [IndexedStepRegisters.sharedScratch, hsource])
    have hafterReady : IndexedStepReady registers after := by
      intro wire hwire
      simp only [IndexedStepRegisters.sharedScratch, List.mem_cons] at hwire
      rcases hwire with rfl | hsource
      · exact hcontrolAfter
      · rw [← hview] at hsource
        simp only [List.mem_cons] at hsource
        rcases hsource with rfl | rfl | htail
        · exact hqAfter
        · exact hsAfter
        · exact htailAfter wire htail
    simpa only [blockHForwardState, hstep, if_pos, after, restoredEpochAgain,
      clearedS, epochBeforeClear, disabled, iterated, changed, enabled,
      control, iter, q, s, epoch] using hafterReady
  · simpa [blockHForwardState, hstep] using hready

private theorem blockHForward_correct
    (registers : IndexedStepRegisters) (n T boundary4 boundary5 : Nat)
    (hboundary4 : (endIterationWindowsAt n T).k4 ≤ boundary4 ∧
      boundary4 ≤ (endIterationWindowsAt n T).K4)
    (hboundary5 : (endIterationWindowsAt n T).k5 ≤ boundary5 ∧
      boundary5 ≤ (endIterationWindowsAt n T).K5Decode n)
    (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hroute4 : T % 4 = 0 →
      ((registers.endIteration n T).upperTree
        (endIterationWindowsAt n T)).routeLabel
        (run (constMinus (registers.endIteration n T).lengthRP
            (registers.endIteration n T).constants
            (registers.endIteration n T).carry (n + 2))
          (run (controlledWorkSwap (registers.endIteration n T).control
            (registers.endIteration n T).work1
            (registers.endIteration n T).work2)
            (blockHEndInputState registers state))) = boundary4)
    (hroute5 : T % 4 = 0 →
      ((registers.endIteration n T).lowerTree n
        (endIterationWindowsAt n T)).routeLabel
        (run (addConstant (registers.endIteration n T).lengthT
            (registers.endIteration n T).constants
            (registers.endIteration n T).carry 3)
          (run (lenUpdateLtUnary n (endIterationWindowsAt n T).k4
            (endIterationWindowsAt n T).K4
            ((registers.endIteration n T).upperTree (endIterationWindowsAt n T))
            (registers.endIteration n T).control
            ((registers.endIteration n T).rangeAccumulator
              (endIterationWindowsAt n T).k4 (endIterationWindowsAt n T).K4)
            ((registers.endIteration n T).temporary
              (endIterationWindowsAt n T).k4 (endIterationWindowsAt n T).K4)
            (registers.endIteration n T).carry
            ((registers.endIteration n T).path
              (endIterationWindowsAt n T).k4 (endIterationWindowsAt n T).K4)
            (registers.endIteration n T).work1At
            (registers.endIteration n T).work2At
            (registers.endIteration n T).lengthT
            (registers.endIteration n T).lengthRP
            (registers.endIteration n T).constants)
          (run (controlledWorkSwap (registers.endIteration n T).control
            (registers.endIteration n T).work1
            (registers.endIteration n T).work2)
            (blockHEndInputState registers state)))) = boundary5)
    (hready : IndexedStepReady registers state) :
    run (blockHForward registers n T) state =
        blockHForwardState registers n T boundary4 boundary5 state ∧
      IndexedStepReady registers (run (blockHForward registers n T) state) := by
  have hrun := blockHForward_run registers n T boundary4 boundary5 hboundary4
    hboundary5 state hlayout hroute4 hroute5 hready
  constructor
  · exact hrun
  · rw [hrun]
    exact blockHForwardState_ready registers n T boundary4 boundary5 state
      hlayout hready

private theorem toggleTerminal_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (toggleTerminal registers) := by
  exact computeControl_wellFormed _ _ _ _ hlayout.terminalControl

private theorem blockAForward_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (blockAForward registers) := by
  simp only [blockAForward, circuitWellFormed_append]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact toggleTerminal_wellFormed registers n T hlayout
  · exact terminalPaddingForward_wellFormed _ hlayout.terminalPadding
  · simpa [CircuitWellFormed, Gate.WellFormed] using hlayout.terminalPhase
  · exact preShiftUnitary_wellFormed _ hlayout.preShift
  · simpa [CircuitWellFormed, Gate.WellFormed] using hlayout.terminalPhase
  · exact terminalEpochSpill_wellFormed _ _ _ hlayout.terminalEpoch
  · exact toggleTerminal_wellFormed registers n T hlayout

private theorem blockAInverse_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (blockAInverse registers) := by
  simp only [blockAInverse, circuitWellFormed_append]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact toggleTerminal_wellFormed registers n T hlayout
  · exact terminalEpochRestore_wellFormed _ _ _ hlayout.terminalEpoch
  · simpa [CircuitWellFormed, Gate.WellFormed] using hlayout.terminalPhase
  · exact (circuitWellFormed_adjoint _).mpr
      (preShiftUnitary_wellFormed _ hlayout.preShift)
  · simpa [CircuitWellFormed, Gate.WellFormed] using hlayout.terminalPhase
  · exact terminalPaddingInverse_wellFormed _ hlayout.terminalPadding
  · exact toggleTerminal_wellFormed registers n T hlayout

private theorem remainderSubControl_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (remainderSubControl registers) := by
  exact rControlNonterminal_wellFormed _ _ _ _ _ _ hlayout.remainderSub

private theorem remainderPhase2Control_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (remainderPhase2Control registers) := by
  exact rControlNonterminal_wellFormed _ _ _ _ _ _ hlayout.remainderPhase2

private theorem remainderRestoreControl_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (remainderRestoreControl registers) := by
  have hmiddle := rControlNonterminal_wellFormed
    [registers.phase1, registers.terminal] 0 registers.control
    registers.lengthRPrime (registers.blockScratch.getD 0 0)
    (registers.blockScratch.drop 1) hlayout.remainderRestore
  have hccx : Gate.WellFormed
      (.CCX registers.phase2 registers.sign registers.terminal) := by
    have hphysical := hlayout.remainderRestoreCCX
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hphysical
    exact ⟨hphysical.1.1, hphysical.1.2, hphysical.2.1⟩
  intro gate hgate
  simp only [remainderRestoreControl, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hgate
  rcases hgate with (rfl | hgate) | rfl
  · exact hccx
  · exact hmiddle gate hgate
  · exact hccx

private theorem blockB1Forward_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder) :
    CircuitWellFormed (blockB1Forward registers n window) := by
  subst window
  simp only [blockB1Forward, circuitWellFormed_append]
  exact ⟨⟨remainderSubControl_wellFormed registers n T hlayout,
    intervalAddSubUnitary_wellFormed _ _ _ _ _ _ _ hlayout.remainder⟩,
    remainderSubControl_wellFormed registers n T hlayout⟩

private theorem blockB1Inverse_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder) :
    CircuitWellFormed (blockB1Inverse registers n window) := by
  subst window
  simp only [blockB1Inverse, circuitWellFormed_append]
  exact ⟨⟨remainderSubControl_wellFormed registers n T hlayout,
    intervalAddSubInverseUnitary_wellFormed _ _ _ _ _ _ _ hlayout.remainder⟩,
    remainderSubControl_wellFormed registers n T hlayout⟩

private theorem blockB2_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (blockB2 registers) := by
  simp only [blockB2, circuitWellFormed_append]
  refine ⟨⟨remainderPhase2Control_wellFormed registers n T hlayout, ?_⟩,
    remainderPhase2Control_wellFormed registers n T hlayout⟩
  simpa [CircuitWellFormed, Gate.WellFormed] using hlayout.controlSign

private theorem blockB3Forward_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder) :
    CircuitWellFormed (blockB3Forward registers n window) := by
  subst window
  simp only [blockB3Forward, circuitWellFormed_append]
  exact ⟨⟨remainderRestoreControl_wellFormed registers n T hlayout,
    intervalAddSubUnitary_wellFormed _ _ _ _ _ _ _ hlayout.remainder⟩,
    remainderRestoreControl_wellFormed registers n T hlayout⟩

private theorem blockB3Inverse_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder) :
    CircuitWellFormed (blockB3Inverse registers n window) := by
  subst window
  simp only [blockB3Inverse, circuitWellFormed_append]
  exact ⟨⟨remainderRestoreControl_wellFormed registers n T hlayout,
    intervalAddSubInverseUnitary_wellFormed _ _ _ _ _ _ _ hlayout.remainder⟩,
    remainderRestoreControl_wellFormed registers n T hlayout⟩

private theorem blockBForward_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder) :
    CircuitWellFormed (blockBForward registers n window) := by
  simp only [blockBForward, circuitWellFormed_append]
  exact ⟨⟨blockB1Forward_wellFormed registers n T window hlayout hwindow,
    blockB2_wellFormed registers n T hlayout⟩,
    blockB3Forward_wellFormed registers n T window hlayout hwindow⟩

private theorem adaptiveUnitary_wellFormed
    (circuit : Circuit) (hwellFormed : CircuitWellFormed circuit) :
    (adaptiveUnitary circuit).WellFormed := by
  exact ⟨hwellFormed, trivial⟩

private theorem blockB1Adaptive_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder) :
    (blockB1Adaptive registers n window).WellFormed := by
  subst window
  rw [blockB1Adaptive]
  exact Quantum.AdaptiveCircuit.WellFormed.seq
    (adaptiveUnitary_wellFormed _
      (remainderSubControl_wellFormed registers n T hlayout))
    (Quantum.AdaptiveCircuit.WellFormed.seq
      (intervalAddSub_wellFormed _ _ _ _ _ _ _ hlayout.remainder)
      (adaptiveUnitary_wellFormed _
        (remainderSubControl_wellFormed registers n T hlayout)))

private theorem blockB3Adaptive_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder) :
    (blockB3Adaptive registers n window).WellFormed := by
  subst window
  rw [blockB3Adaptive]
  exact Quantum.AdaptiveCircuit.WellFormed.seq
    (adaptiveUnitary_wellFormed _
      (remainderRestoreControl_wellFormed registers n T hlayout))
    (Quantum.AdaptiveCircuit.WellFormed.seq
      (intervalAddSub_wellFormed _ _ _ _ _ _ _ hlayout.remainder)
      (adaptiveUnitary_wellFormed _
        (remainderRestoreControl_wellFormed registers n T hlayout)))

private theorem blockBAdaptive_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder) :
    (blockBAdaptive registers n window).WellFormed := by
  rw [blockBAdaptive]
  exact Quantum.AdaptiveCircuit.WellFormed.seq
    (blockB1Adaptive_wellFormed registers n T window hlayout hwindow)
    (Quantum.AdaptiveCircuit.WellFormed.seq
      (adaptiveUnitary_wellFormed _ (blockB2_wellFormed registers n T hlayout))
      (blockB3Adaptive_wellFormed registers n T window hlayout hwindow))

private theorem blockBInverse_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder) :
    CircuitWellFormed (blockBInverse registers n window) := by
  simp only [blockBInverse, circuitWellFormed_append]
  exact ⟨⟨blockB3Inverse_wellFormed registers n T window hlayout hwindow,
    blockB2_wellFormed registers n T hlayout⟩,
    blockB1Inverse_wellFormed registers n T window hlayout hwindow⟩

private theorem blockCForward_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (blockCForward registers) := by
  simp only [blockCForward, circuitWellFormed_append]
  exact ⟨⟨toggleTerminal_wellFormed registers n T hlayout,
    terminalEpochRestore_wellFormed _ _ _ hlayout.terminalEpoch⟩,
    toggleTerminal_wellFormed registers n T hlayout⟩

private theorem blockCInverse_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (blockCInverse registers) := by
  simp only [blockCInverse, circuitWellFormed_append]
  exact ⟨⟨toggleTerminal_wellFormed registers n T hlayout,
    terminalEpochSpill_wellFormed _ _ _ hlayout.terminalEpoch⟩,
    toggleTerminal_wellFormed registers n T hlayout⟩

private theorem phase2LengthControl_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (phase2LengthControl registers) := by
  exact computeControl_wellFormed _ _ _ _ hlayout.phase2Length

private theorem phase3LengthControl_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (phase3LengthControl registers) := by
  exact computeControl_wellFormed _ _ _ _ hlayout.phase3Length

private theorem quotientXorControl_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (quotientXorControl registers) := by
  have hphysical := hlayout.quotientControls
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or] at hphysical
  simp [quotientXorControl, CircuitWellFormed, Gate.WellFormed, hphysical]

private theorem quotientXorControlInverse_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (quotientXorControlInverse registers) := by
  have hphysical := hlayout.quotientControls
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or] at hphysical
  simp [quotientXorControlInverse, CircuitWellFormed, Gate.WellFormed, hphysical]

private theorem blockDForward_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).quotientSwap) :
    CircuitWellFormed (blockDForward registers window) := by
  subst window
  simp only [blockDForward, circuitWellFormed_append]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact phase2LengthControl_wellFormed registers n T hlayout
  · exact controlledIncrement_wellFormed _ _ _ hlayout.lengthCarryPhysical
  · exact phase2LengthControl_wellFormed registers n T hlayout
  · exact quotientXorControl_wellFormed registers n T hlayout
  · exact quotientSwapUnitary_wellFormed _ hlayout.quotient
  · exact quotientXorControlInverse_wellFormed registers n T hlayout
  · exact phase3LengthControl_wellFormed registers n T hlayout
  · exact controlledDecrement_wellFormed _ _ _ hlayout.lengthCarryPhysical
  · exact phase3LengthControl_wellFormed registers n T hlayout

private theorem blockDInverse_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).quotientSwap) :
    CircuitWellFormed (blockDInverse registers window) := by
  subst window
  simp only [blockDInverse, circuitWellFormed_append]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact phase3LengthControl_wellFormed registers n T hlayout
  · exact controlledIncrement_wellFormed _ _ _ hlayout.lengthCarryPhysical
  · exact phase3LengthControl_wellFormed registers n T hlayout
  · exact quotientXorControl_wellFormed registers n T hlayout
  · exact quotientSwapUnitary_wellFormed _ hlayout.quotient
  · exact quotientXorControlInverse_wellFormed registers n T hlayout
  · exact phase2LengthControl_wellFormed registers n T hlayout
  · exact controlledDecrement_wellFormed _ _ _ hlayout.lengthCarryPhysical
  · exact phase2LengthControl_wellFormed registers n T hlayout

private theorem coefficientTemporaryControl_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (coefficientTemporaryControl registers) := by
  exact computeControl_wellFormed _ _ _ _ hlayout.coefficientTemporary

private theorem coefficientSubControl_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (coefficientSubControl registers) := by
  exact computeControl_wellFormed _ _ _ _ hlayout.coefficientSub

private theorem coefficientAddControl_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (coefficientAddControl registers) := by
  exact computeControl_wellFormed _ _ _ _ hlayout.coefficientAdd

private theorem coefficientSign_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed ([.CX registers.phase1 registers.sign] : Circuit) := by
  simpa [CircuitWellFormed, Gate.WellFormed] using hlayout.coefficientSign

private theorem blockEForward_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient) :
    CircuitWellFormed (blockEForward registers n window) := by
  subst window
  simp only [blockEForward, circuitWellFormed_append]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact coefficientTemporaryControl_wellFormed registers n T hlayout
  · exact coefficientSubControl_wellFormed registers n T hlayout
  · exact coefficientTemporaryControl_wellFormed registers n T hlayout
  · exact prepareLatestPaperTBoundary_wellFormed _ n hlayout.tBoundary
  · exact coefficientPrefixUnitary_wellFormed _ _ _ _ hlayout.coefficient
  · exact coefficientTemporaryControl_wellFormed registers n T hlayout
  · exact coefficientSubControl_wellFormed registers n T hlayout
  · exact coefficientTemporaryControl_wellFormed registers n T hlayout
  · exact coefficientSign_wellFormed registers n T hlayout
  · exact coefficientAddControl_wellFormed registers n T hlayout
  · exact coefficientPrefixUnitary_wellFormed _ _ _ _ hlayout.coefficient
  · exact coefficientAddControl_wellFormed registers n T hlayout
  · exact restoreLatestPaperTBoundary_wellFormed _ n hlayout.tBoundary

private theorem blockEPrefix_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (blockEPrefix registers n) := by
  simp only [blockEPrefix, circuitWellFormed_append]
  exact ⟨⟨⟨
    coefficientTemporaryControl_wellFormed registers n T hlayout,
    coefficientSubControl_wellFormed registers n T hlayout⟩,
    coefficientTemporaryControl_wellFormed registers n T hlayout⟩,
    prepareLatestPaperTBoundary_wellFormed _ n hlayout.tBoundary⟩

private theorem blockEMiddle_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (blockEMiddle registers) := by
  simp only [blockEMiddle, circuitWellFormed_append]
  exact ⟨⟨⟨⟨
    coefficientTemporaryControl_wellFormed registers n T hlayout,
    coefficientSubControl_wellFormed registers n T hlayout⟩,
    coefficientTemporaryControl_wellFormed registers n T hlayout⟩,
    coefficientSign_wellFormed registers n T hlayout⟩,
    coefficientAddControl_wellFormed registers n T hlayout⟩

private theorem blockESuffix_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (blockESuffix registers n) := by
  simp only [blockESuffix, circuitWellFormed_append]
  exact ⟨coefficientAddControl_wellFormed registers n T hlayout,
    restoreLatestPaperTBoundary_wellFormed _ n hlayout.tBoundary⟩

private theorem blockEFirstAdaptive_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient) :
    (blockEFirstAdaptive registers n window).WellFormed := by
  subst window
  rw [blockEFirstAdaptive]
  exact Quantum.AdaptiveCircuit.WellFormed.seq
    (adaptiveUnitary_wellFormed _ (blockEPrefix_wellFormed registers n T hlayout))
    (coefficientPrefixAdaptive_wellFormed _ _ _ _ hlayout.coefficient)

private theorem blockETailAdaptive_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient) :
    (blockETailAdaptive registers n window).WellFormed := by
  subst window
  rw [blockETailAdaptive]
  exact Quantum.AdaptiveCircuit.WellFormed.seq
    (adaptiveUnitary_wellFormed _ (blockEMiddle_wellFormed registers n T hlayout))
    (Quantum.AdaptiveCircuit.WellFormed.seq
      (coefficientPrefixAdaptive_wellFormed _ _ _ _ hlayout.coefficient)
      (adaptiveUnitary_wellFormed _ (blockESuffix_wellFormed registers n T hlayout)))

private theorem blockEAdaptive_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient) :
    (blockEAdaptive registers n window).WellFormed := by
  rw [blockEAdaptive]
  exact Quantum.AdaptiveCircuit.WellFormed.seq
    (blockEFirstAdaptive_wellFormed registers n T window hlayout hwindow)
    (blockETailAdaptive_wellFormed registers n T window hlayout hwindow)

private theorem blockEInverse_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient) :
    CircuitWellFormed (blockEInverse registers n window) := by
  subst window
  simp only [blockEInverse, circuitWellFormed_append]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact prepareLatestPaperTBoundary_wellFormed _ n hlayout.tBoundary
  · exact coefficientAddControl_wellFormed registers n T hlayout
  · exact coefficientPrefixInverseUnitary_wellFormed _ _ _ _ hlayout.coefficient
  · exact coefficientAddControl_wellFormed registers n T hlayout
  · exact coefficientSign_wellFormed registers n T hlayout
  · exact coefficientTemporaryControl_wellFormed registers n T hlayout
  · exact coefficientSubControl_wellFormed registers n T hlayout
  · exact coefficientTemporaryControl_wellFormed registers n T hlayout
  · exact coefficientPrefixInverseUnitary_wellFormed _ _ _ _ hlayout.coefficient
  · exact coefficientTemporaryControl_wellFormed registers n T hlayout
  · exact coefficientSubControl_wellFormed registers n T hlayout
  · exact coefficientTemporaryControl_wellFormed registers n T hlayout
  · exact restoreLatestPaperTBoundary_wellFormed _ n hlayout.tBoundary

private theorem blockFForward_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (blockFForward registers) :=
  postShiftUnitary_wellFormed _ hlayout.postShift

private theorem blockFInverse_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (blockFInverse registers) := by
  exact (circuitWellFormed_adjoint _).mpr
    (postShiftUnitary_wellFormed _ hlayout.postShift)

private theorem blockGForward_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (blockGForward registers) :=
  phaseUpdateEpochUnitary_wellFormed _ _ hlayout.phaseUpdate

private theorem blockGInverse_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (blockGInverse registers) :=
  phaseUpdateEpochInverseUnitary_wellFormed _ _ hlayout.phaseUpdate

private theorem blockHEndGate_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    Gate.WellFormed (.CCX (registers.sourceScratch.getD 0 0)
      (registers.sourceScratch.getD 1 0) registers.control) := by
  have hphysical := hlayout.endControls
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or] at hphysical
  exact ⟨hphysical.1.1, hphysical.1.2.1, hphysical.2.1.1⟩

private theorem blockHIterGate_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    Gate.WellFormed (.CX registers.control registers.iter) := by
  have hphysical := hlayout.endControls
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or] at hphysical
  simpa only [Gate.WellFormed] using hphysical.2.2.1

private theorem blockHForward_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (blockHForward registers n T) := by
  by_cases hstep : T % 4 = 0
  · have hq := mcxVChain_wellFormed registers.lengthQ
      (registers.sourceScratch.getD 0 0) (registers.sourceScratch.drop 2)
      hlayout.endQ.1 hlayout.endQ.2
    have hs := mcxVChain_wellFormed (registers.lengthS ++ [registers.shiftEpoch])
      (registers.sourceScratch.getD 1 0) (registers.sourceScratch.drop 2)
      hlayout.endS.1 hlayout.endS.2
    have hswap := swapWorkAndLengthUnaryShared_wellFormed
      (registers.endIteration n T) n (endIterationWindowsAt n T)
      (hlayout.endIteration hstep)
    have hend := blockHEndGate_wellFormed registers n T hlayout
    have hiter := blockHIterGate_wellFormed registers n T hlayout
    have hx : Gate.WellFormed (.X registers.shiftEpoch) := by
      simp [Gate.WellFormed]
    unfold CircuitWellFormed at hq hs hswap ⊢
    intro gate hgate
    simp only [blockHForward, hstep, if_pos, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hgate
    aesop
  · simp [blockHForward, hstep]

private theorem blockHInverse_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (blockHInverse registers n T) := by
  by_cases hstep : T % 4 = 0
  · have hq := mcxVChain_wellFormed registers.lengthQ
      (registers.sourceScratch.getD 0 0) (registers.sourceScratch.drop 2)
      hlayout.endQ.1 hlayout.endQ.2
    have hs := mcxVChain_wellFormed (registers.lengthS ++ [registers.shiftEpoch])
      (registers.sourceScratch.getD 1 0) (registers.sourceScratch.drop 2)
      hlayout.endS.1 hlayout.endS.2
    have hswap := swapWorkAndLengthUnarySharedInverse_wellFormed
      (registers.endIteration n T) n (endIterationWindowsAt n T)
      (hlayout.endIteration hstep)
    have hend := blockHEndGate_wellFormed registers n T hlayout
    have hiter := blockHIterGate_wellFormed registers n T hlayout
    have hx : Gate.WellFormed (.X registers.shiftEpoch) := by
      simp [Gate.WellFormed]
    unfold CircuitWellFormed at hq hs hswap ⊢
    intro gate hgate
    simp only [blockHInverse, hstep, if_pos, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hgate
    aesop
  · simp [blockHInverse, hstep]

private theorem indexedStep_hpFree_adjoint
    {circuit : Circuit} (hfree : HPFree circuit) :
    HPFree circuit.adjoint := by
  induction circuit with
  | nil => simp
  | cons gate circuit ih =>
      have hparts := (hpFree_cons gate circuit).mp hfree
      rw [circuit_adjoint_cons, hpFree_append]
      constructor
      · exact ih hparts.2
      · cases gate <;> simp_all

@[simp]
private theorem blockHForward_HPFree
    (registers : IndexedStepRegisters) (n T : Nat) :
    HPFree (blockHForward registers n T) := by
  by_cases hstep : T % 4 = 0 <;> simp [blockHForward, hstep]

@[simp]
private theorem blockHInverse_HPFree
    (registers : IndexedStepRegisters) (n T : Nat) :
    HPFree (blockHInverse registers n T) := by
  by_cases hstep : T % 4 = 0 <;> simp [blockHInverse, hstep]

/-! ## Blockwise coherent refinement -/

private theorem indexedStep_coherent_seq_circuits
    {first second : Quantum.AdaptiveCircuit}
    {firstCircuit secondCircuit : Circuit}
    {FirstValid SecondValid : BasisState → Prop}
    (hfirst : Quantum.CoherentlyImplementsOn first
      (Quantum.run firstCircuit) FirstValid)
    (hsecond : Quantum.CoherentlyImplementsOn second
      (Quantum.run secondCircuit) SecondValid)
    (hfirstClassical : HPFree firstCircuit)
    (hvalid : ∀ state, FirstValid state →
      SecondValid (Classical.run firstCircuit state)) :
    Quantum.CoherentlyImplementsOn (first.seq second)
      (Quantum.run (firstCircuit ++ secondCircuit)) FirstValid := by
  have hseq := hfirst.seq hsecond (by
    intro state hstate
    rw [Quantum.run_ket_agrees_classical firstCircuit state hfirstClassical]
    exact Quantum.supportedOn_ket SecondValid _ (hvalid state hstate))
  apply hseq.congrIdeal
  intro state _
  exact (Quantum.run_append firstCircuit secondCircuit (Quantum.ket state)).symm

private theorem indexedStep_coherent_strengthen
    {program : Quantum.AdaptiveCircuit} {ideal : State →ₗ[ℂ] State}
    {Valid Stronger : BasisState → Prop}
    (hrefines : Quantum.CoherentlyImplementsOn program ideal Valid)
    (hsub : ∀ state, Stronger state → Valid state) :
    Quantum.CoherentlyImplementsOn program ideal Stronger := by
  rcases hrefines with ⟨coefficients, haligned, hmass⟩
  refine ⟨coefficients, ?_, hmass⟩
  exact haligned.imp fun branch coefficient hbranch state hstate ↦
    hbranch state (hsub state hstate)

private theorem remainderSubControl_intervalReady
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder)
    (hready : IndexedStepBorrowedReady registers state) :
    IntervalReady (registers.remainder window)
      (run (remainderSubControl registers) state) := by
  have hsourceClean : Clean (registers.terminal :: registers.blockScratch) state := by
    intro wire hwire
    apply hready wire
    apply hlayout.sourceScratch_mem_aux
    rw [← hlayout.scratch_view]
    exact hwire
  have hrun := run_rControlNonterminal [registers.phase1] 0 registers.control
    registers.lengthRPrime registers.terminal registers.blockScratch state
    hlayout.remainderSub hsourceClean
  intro wire hwire
  rw [show run (remainderSubControl registers) state =
      rControlState [registers.phase1] 0 registers.control
        registers.lengthRPrime registers.terminal state by
    simpa [remainderSubControl, toggleRControl, rControlState] using hrun]
  rw [rControlState_preserves _ _ _ _ _ _ (by
    intro equality
    subst wire
    exact hlayout.control_not_remainder_scratch window hwindow hwire)]
  exact hready wire (hlayout.remainder_scratch_sub_aux window wire hwire)

private theorem remainderRestoreControl_intervalReady
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder)
    (hready : IndexedStepBorrowedReady registers state) :
    IntervalReady (registers.remainder window)
      (run (remainderRestoreControl registers) state) := by
  have haway : ∀ wire ∈ registers.aux, wire ≠ registers.control →
      state wire = false := by
    intro wire hwire _
    exact hready wire hwire
  have hcorrect := remainderRestoreControl_correct registers n T state hlayout haway
  intro wire hwire
  rw [hcorrect.1]
  exact hcorrect.2 wire (hlayout.remainder_scratch_sub_aux window wire hwire) (by
    intro equality
    subst wire
    exact hlayout.control_not_remainder_scratch window hwindow hwire)

private theorem blockB1Adaptive_coherent
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder) :
    Quantum.CoherentlyImplementsOn
      (blockB1Adaptive registers n window)
      (Quantum.run (blockB1Forward registers n window))
      (IndexedStepBorrowedReady registers) := by
  have hprefix := Quantum.CoherentlyImplementsOn.unitary
    (remainderSubControl registers) (IndexedStepBorrowedReady registers)
  have hinterval := intervalAddSub_coherent (registers.remainder window) n
    window.start window.stop .sub true .work1 (by
      subst window
      exact hlayout.remainder)
  have hprefixInterval := indexedStep_coherent_seq_circuits hprefix hinterval
    (by simp [remainderSubControl, toggleRControl])
    (fun state hready ↦ remainderSubControl_intervalReady registers n T window
      state hlayout hwindow hready)
  have hsuffix := Quantum.CoherentlyImplementsOn.unitary
    (remainderSubControl registers) (fun _ ↦ True)
  have hall := indexedStep_coherent_seq_circuits hprefixInterval hsuffix
    (by simp [remainderSubControl, toggleRControl]) (fun _ _ ↦ trivial)
  simpa [blockB1Adaptive, blockB1Forward, adaptiveUnitary,
    List.append_assoc] using hall

private theorem blockB3Adaptive_coherent
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder) :
    Quantum.CoherentlyImplementsOn
      (blockB3Adaptive registers n window)
      (Quantum.run (blockB3Forward registers n window))
      (IndexedStepBorrowedReady registers) := by
  have hprefix := Quantum.CoherentlyImplementsOn.unitary
    (remainderRestoreControl registers) (IndexedStepBorrowedReady registers)
  have hinterval := intervalAddSub_coherent (registers.remainder window) n
    window.start window.stop .add false .work1 (by
      subst window
      exact hlayout.remainder)
  have hprefixInterval := indexedStep_coherent_seq_circuits hprefix hinterval
    (by simp [remainderRestoreControl, toggleRControl])
    (fun state hready ↦ remainderRestoreControl_intervalReady registers n T window
      state hlayout hwindow hready)
  have hsuffix := Quantum.CoherentlyImplementsOn.unitary
    (remainderRestoreControl registers) (fun _ ↦ True)
  have hall := indexedStep_coherent_seq_circuits hprefixInterval hsuffix
    (by simp [remainderRestoreControl, toggleRControl]) (fun _ _ ↦ trivial)
  simpa [blockB3Adaptive, blockB3Forward, adaptiveUnitary,
    List.append_assoc] using hall

private theorem blockBAdaptive_coherent
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder) :
    Quantum.CoherentlyImplementsOn
      (blockBAdaptive registers n window)
      (Quantum.run (blockBForward registers n window))
      (IndexedStepBorrowedReady registers) := by
  have hfirst := blockB1Adaptive_coherent registers n T window hlayout hwindow
  have hmiddle := Quantum.CoherentlyImplementsOn.unitary
    (blockB2 registers) (IndexedStepBorrowedReady registers)
  have hlast := blockB3Adaptive_coherent registers n T window hlayout hwindow
  have hmiddleLast := indexedStep_coherent_seq_circuits hmiddle hlast
    (by simp [blockB2, remainderPhase2Control, toggleRControl])
    (fun state hready ↦ (blockB2_correct registers n T state hlayout hready).2)
  have hall := indexedStep_coherent_seq_circuits hfirst hmiddleLast
    (by simp [blockB1Forward, remainderSubControl, toggleRControl])
    (fun state hready ↦
      (blockB1Forward_correct registers n T window state hlayout hwindow hready).2)
  simpa [blockBAdaptive, blockBForward, List.append_assoc] using hall

private theorem blockEPrefix_cleanBlockScratch
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state) :
    Clean registers.blockScratch (run (blockEPrefix registers n) state) := by
  have hblock : Clean registers.blockScratch state := by
    intro wire hwire
    exact hready wire (by
      simp only [IndexedStepRegisters.sharedScratch, List.mem_cons]
      exact Or.inr (List.mem_of_mem_drop hwire))
  let temporary1 := matchXorState [registers.phase2, registers.sign] 2
    registers.terminal state
  have htemporary1 := run_computeControl_state
    [registers.phase2, registers.sign] 2 registers.terminal
      registers.blockScratch state hlayout.coefficientTemporary hblock
  let subEnabled := matchXorState [registers.phase1, registers.terminal] 1
    registers.control temporary1
  have hsubEnabled := run_computeControl_state
    [registers.phase1, registers.terminal] 1 registers.control
      registers.blockScratch temporary1 hlayout.coefficientSub (by
        simpa only [temporary1] using htemporary1.2)
  let temporaryCleared := matchXorState [registers.phase2, registers.sign] 2
    registers.terminal subEnabled
  have htemporaryCleared := run_computeControl_state
    [registers.phase2, registers.sign] 2 registers.terminal
      registers.blockScratch subEnabled hlayout.coefficientTemporary (by
        simpa only [subEnabled] using hsubEnabled.2)
  have hprepared := run_tBoundaryPrepareState registers n T temporaryCleared
    hlayout (by simpa only [temporaryCleared] using htemporaryCleared.2)
  simp only [blockEPrefix, Classical.run_append]
  rw [show run (coefficientTemporaryControl registers) state = temporary1 by
      simpa [coefficientTemporaryControl, temporary1] using htemporary1.1,
    show run (coefficientSubControl registers) temporary1 = subEnabled by
      simpa [coefficientSubControl, subEnabled] using hsubEnabled.1,
    show run (coefficientTemporaryControl registers) subEnabled = temporaryCleared by
      simpa [coefficientTemporaryControl, temporaryCleared] using
        htemporaryCleared.1]
  exact hprepared.2

private theorem blockEMiddle_preservesBlockScratch
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hclean : Clean registers.blockScratch state) :
    Clean registers.blockScratch (run (blockEMiddle registers) state) := by
  let temporary1 := matchXorState [registers.phase2, registers.sign] 2
    registers.terminal state
  have htemporary1 := run_computeControl_state
    [registers.phase2, registers.sign] 2 registers.terminal
      registers.blockScratch state hlayout.coefficientTemporary hclean
  let subCleared := matchXorState [registers.phase1, registers.terminal] 1
    registers.control temporary1
  have hsubCleared := run_computeControl_state
    [registers.phase1, registers.terminal] 1 registers.control
      registers.blockScratch temporary1 hlayout.coefficientSub (by
        simpa only [temporary1] using htemporary1.2)
  let temporaryCleared := matchXorState [registers.phase2, registers.sign] 2
    registers.terminal subCleared
  have htemporaryCleared := run_computeControl_state
    [registers.phase2, registers.sign] 2 registers.terminal
      registers.blockScratch subCleared hlayout.coefficientTemporary (by
        simpa only [subCleared] using hsubCleared.2)
  let signChanged := xorWireState registers.phase1 registers.sign temporaryCleared
  have hsignChanged : Clean registers.blockScratch signChanged := by
    apply clean_upd_not_mem (by
      simpa only [temporaryCleared] using htemporaryCleared.2)
    intro hsign
    exact (hlayout.sign_ne_after (by
      simp [indexedStepAfterSign, hlayout.blockScratch_mem_aux hsign])) rfl
  let addEnabled := matchXorState [registers.phase1] 1 registers.control signChanged
  have haddEnabled := run_computeControl_state [registers.phase1] 1
    registers.control registers.blockScratch signChanged hlayout.coefficientAdd
      hsignChanged
  simp only [blockEMiddle, Classical.run_append]
  rw [show run (coefficientTemporaryControl registers) state = temporary1 by
      simpa [coefficientTemporaryControl, temporary1] using htemporary1.1,
    show run (coefficientSubControl registers) temporary1 = subCleared by
      simpa [coefficientSubControl, subCleared] using hsubCleared.1,
    show run (coefficientTemporaryControl registers) subCleared = temporaryCleared by
      simpa [coefficientTemporaryControl, temporaryCleared] using
        htemporaryCleared.1,
    show run ([.CX registers.phase1 registers.sign] : Circuit) temporaryCleared =
        signChanged by exact run_xorWireState _ _ _]
  rw [show run (coefficientAddControl registers) signChanged = addEnabled by
    simpa [coefficientAddControl, addEnabled] using haddEnabled.1]
  simpa only [addEnabled] using haddEnabled.2

private theorem coefficientPrefix_coherent_on_blockScratch
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (mode : RippleMode) (signUpdate : Bool)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient) :
    Quantum.CoherentlyImplementsOn
      (coefficientPrefixAdaptive (registers.coefficient window)
        window.start window.stop mode signUpdate .work2)
      (Quantum.run (coefficientPrefixUnitary (registers.coefficient window)
        window.start window.stop mode signUpdate .work2))
      (Clean registers.blockScratch) := by
  apply indexedStep_coherent_strengthen
    (coefficientPrefixAdaptive_coherent (registers.coefficient window)
      mode signUpdate .work2 (by
        subst window
        exact hlayout.coefficient))
  intro state hclean wire hwire
  exact hclean wire (hlayout.coefficient_scratch_sub_block window wire hwire)

private theorem coefficientPrefix_preservesBlockScratch
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (mode : RippleMode) (signUpdate : Bool) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient)
    (hclean : Clean registers.blockScratch state) :
    Clean registers.blockScratch
      (run (coefficientPrefixUnitary (registers.coefficient window)
        window.start window.stop mode signUpdate .work2) state) := by
  exact (run_coefficientPrefixState_from_blockScratch registers n T window
    mode signUpdate state hlayout hwindow hclean).2.1

private theorem blockEFirstAdaptive_coherent
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient) :
    Quantum.CoherentlyImplementsOn
      (blockEFirstAdaptive registers n window)
      (Quantum.run (blockEPrefix registers n ++
        coefficientPrefixUnitary (registers.coefficient window)
          window.start window.stop .sub false .work2))
      (IndexedStepReady registers) := by
  let subCircuit := coefficientPrefixUnitary (registers.coefficient window)
    window.start window.stop .sub false .work2
  have hprefix := Quantum.CoherentlyImplementsOn.unitary
    (blockEPrefix registers n) (IndexedStepReady registers)
  have hsub : Quantum.CoherentlyImplementsOn
      (coefficientPrefixAdaptive (registers.coefficient window)
        window.start window.stop .sub false .work2)
      (Quantum.run subCircuit) (Clean registers.blockScratch) := by
    simpa only [subCircuit] using coefficientPrefix_coherent_on_blockScratch
      registers n T window .sub false hlayout hwindow
  have hprefixSub := indexedStep_coherent_seq_circuits hprefix hsub
    (by simp [blockEPrefix, coefficientTemporaryControl,
      coefficientSubControl])
    (fun state hready ↦
      blockEPrefix_cleanBlockScratch registers n T state hlayout hready)
  simpa only [blockEFirstAdaptive, adaptiveUnitary, subCircuit] using hprefixSub

private theorem blockETailAdaptive_coherent
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient) :
    Quantum.CoherentlyImplementsOn
      (blockETailAdaptive registers n window)
      (Quantum.run (blockEMiddle registers ++
        coefficientPrefixUnitary (registers.coefficient window)
          window.start window.stop .add true .work2 ++
        blockESuffix registers n))
      (Clean registers.blockScratch) := by
  let addCircuit := coefficientPrefixUnitary (registers.coefficient window)
    window.start window.stop .add true .work2
  have hmiddle := Quantum.CoherentlyImplementsOn.unitary
    (blockEMiddle registers) (Clean registers.blockScratch)
  have hadd : Quantum.CoherentlyImplementsOn
      (coefficientPrefixAdaptive (registers.coefficient window)
        window.start window.stop .add true .work2)
      (Quantum.run addCircuit) (Clean registers.blockScratch) := by
    simpa only [addCircuit] using coefficientPrefix_coherent_on_blockScratch
      registers n T window .add true hlayout hwindow
  have hmiddleAdd := indexedStep_coherent_seq_circuits hmiddle hadd
    (by simp [blockEMiddle,
      coefficientTemporaryControl, coefficientSubControl,
      coefficientAddControl]) (by
        intro state hclean
        exact blockEMiddle_preservesBlockScratch registers n T state hlayout hclean)
  have hsuffix := Quantum.CoherentlyImplementsOn.unitary
    (blockESuffix registers n) (fun _ ↦ True)
  have hall := indexedStep_coherent_seq_circuits hmiddleAdd hsuffix
    (by simp [blockEMiddle, addCircuit,
      coefficientTemporaryControl, coefficientSubControl,
      coefficientAddControl]) (fun _ _ ↦ trivial)
  simpa only [blockETailAdaptive, adaptiveUnitary, addCircuit,
    List.append_assoc] using hall

private theorem blockEAdaptive_coherent
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient) :
    Quantum.CoherentlyImplementsOn
      (blockEAdaptive registers n window)
      (Quantum.run (blockEForward registers n window))
      (IndexedStepReady registers) := by
  let subCircuit := coefficientPrefixUnitary (registers.coefficient window)
    window.start window.stop .sub false .work2
  let firstCircuit := blockEPrefix registers n ++ subCircuit
  let tailCircuit := blockEMiddle registers ++
    coefficientPrefixUnitary (registers.coefficient window)
      window.start window.stop .add true .work2 ++ blockESuffix registers n
  have hfirst : Quantum.CoherentlyImplementsOn
      (blockEFirstAdaptive registers n window) (Quantum.run firstCircuit)
      (IndexedStepReady registers) := by
    simpa only [firstCircuit, subCircuit] using
      blockEFirstAdaptive_coherent registers n T window hlayout hwindow
  have htail : Quantum.CoherentlyImplementsOn
      (blockETailAdaptive registers n window) (Quantum.run tailCircuit)
      (Clean registers.blockScratch) := by
    simpa only [tailCircuit] using
      blockETailAdaptive_coherent registers n T window hlayout hwindow
  have hall := indexedStep_coherent_seq_circuits hfirst htail
    (by simp [firstCircuit, subCircuit, blockEPrefix,
      coefficientTemporaryControl, coefficientSubControl]) (by
        intro state hready
        rw [show firstCircuit = blockEPrefix registers n ++ subCircuit by rfl,
          Classical.run_append]
        exact coefficientPrefix_preservesBlockScratch registers n T window .sub false
          _ hlayout hwindow
          (blockEPrefix_cleanBlockScratch registers n T state hlayout hready))
  simpa [blockEAdaptive, blockEForward, firstCircuit, tailCircuit,
    blockEPrefix, blockEMiddle, blockESuffix, subCircuit,
    List.append_assoc] using hall

/-! ## Complete coherent source terms -/

/-- Literal coherent `append_one_step_T`, using the certified active windows. -/
def indexedStepUnitary
    (registers : IndexedStepRegisters) (n T : Nat) : Circuit :=
  let windows := certifiedActiveWindows n T
  circuit! {
    blockAForward registers;
    blockBForward registers n windows.remainder;
    blockCForward registers;
    blockDForward registers windows.quotientSwap;
    blockEForward registers n windows.coefficient;
    blockFForward registers;
    blockGForward registers;
    blockHForward registers n T
  }

/-- Literal explicit reverse `append_one_step_T_inverse`. -/
def indexedStepInverseUnitary
    (registers : IndexedStepRegisters) (n T : Nat) : Circuit :=
  let windows := certifiedActiveWindows n T
  circuit! {
    blockHInverse registers n T;
    blockGInverse registers;
    blockFInverse registers;
    blockEInverse registers n windows.coefficient;
    blockDInverse registers windows.quotientSwap;
    blockCInverse registers;
    blockBInverse registers n windows.remainder;
    blockAInverse registers
  }

/-- Measurement-uncomputed realization of the same literal forward step.  Only the two remainder
intervals, two coefficient-prefix traversals, and epoch-aware phase update use adaptive cleanup;
all surrounding source blocks remain ordinary unitary circuits. -/
def indexedStepAdaptive
    (registers : IndexedStepRegisters) (n T : Nat) : Quantum.AdaptiveCircuit :=
  let windows := certifiedActiveWindows n T
  (adaptiveUnitary (blockAForward registers)).seq
    ((blockBAdaptive registers n windows.remainder).seq
      ((adaptiveUnitary (blockCForward registers ++
        blockDForward registers windows.quotientSwap)).seq
        ((blockEAdaptive registers n windows.coefficient).seq
          ((adaptiveUnitary (blockFForward registers)).seq
            ((phaseUpdateEpochAdaptive registers.phaseUpdate registers.shiftEpoch).seq
              (adaptiveUnitary (blockHForward registers n T)))))))

/-- The complete coherent source step is physically well formed under the explicit composition
contract. -/
theorem indexedStepUnitary_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (indexedStepUnitary registers n T) := by
  simp only [indexedStepUnitary, circuitWellFormed_append]
  exact ⟨⟨⟨⟨⟨⟨⟨
    blockAForward_wellFormed registers n T hlayout,
    blockBForward_wellFormed registers n T _ hlayout rfl⟩,
    blockCForward_wellFormed registers n T hlayout⟩,
    blockDForward_wellFormed registers n T _ hlayout rfl⟩,
    blockEForward_wellFormed registers n T _ hlayout rfl⟩,
    blockFForward_wellFormed registers n T hlayout⟩,
    blockGForward_wellFormed registers n T hlayout⟩,
    blockHForward_wellFormed registers n T hlayout⟩

/-- The explicit reverse source stream is physically well formed under the same allocation. -/
theorem indexedStepInverseUnitary_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (indexedStepInverseUnitary registers n T) := by
  simp only [indexedStepInverseUnitary, circuitWellFormed_append]
  exact ⟨⟨⟨⟨⟨⟨⟨
    blockHInverse_wellFormed registers n T hlayout,
    blockGInverse_wellFormed registers n T hlayout⟩,
    blockFInverse_wellFormed registers n T hlayout⟩,
    blockEInverse_wellFormed registers n T _ hlayout rfl⟩,
    blockDInverse_wellFormed registers n T _ hlayout rfl⟩,
    blockCInverse_wellFormed registers n T hlayout⟩,
    blockBInverse_wellFormed registers n T _ hlayout rfl⟩,
    blockAInverse_wellFormed registers n T hlayout⟩

/-- Every branch of the measurement-uncomputed indexed step is physically well formed under the
same source allocation. -/
theorem indexedStepAdaptive_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    (indexedStepAdaptive registers n T).WellFormed := by
  rw [indexedStepAdaptive]
  exact Quantum.AdaptiveCircuit.WellFormed.seq
    (adaptiveUnitary_wellFormed _
      (blockAForward_wellFormed registers n T hlayout))
    (Quantum.AdaptiveCircuit.WellFormed.seq
      (blockBAdaptive_wellFormed registers n T _ hlayout rfl)
      (Quantum.AdaptiveCircuit.WellFormed.seq
        (adaptiveUnitary_wellFormed _ (by
          rw [circuitWellFormed_append]
          exact ⟨blockCForward_wellFormed registers n T hlayout,
            blockDForward_wellFormed registers n T _ hlayout rfl⟩))
        (Quantum.AdaptiveCircuit.WellFormed.seq
          (blockEAdaptive_wellFormed registers n T _ hlayout rfl)
          (Quantum.AdaptiveCircuit.WellFormed.seq
            (adaptiveUnitary_wellFormed _
              (blockFForward_wellFormed registers n T hlayout))
            (Quantum.AdaptiveCircuit.WellFormed.seq
              (phaseUpdateEpochAdaptive_wellFormed _ _ hlayout.phaseUpdate)
              (adaptiveUnitary_wellFormed _
                (blockHForward_wellFormed registers n T hlayout)))))))

@[simp]
theorem indexedStepUnitary_HPFree
    (registers : IndexedStepRegisters) (n T : Nat) :
    HPFree (indexedStepUnitary registers n T) := by
  simp [indexedStepUnitary, blockAForward, blockBForward, blockB1Forward,
    blockB2, blockB3Forward, blockCForward, blockDForward, blockEForward,
    blockFForward, blockGForward, toggleTerminal,
    remainderSubControl, remainderPhase2Control, remainderRestoreControl,
    toggleRControl, phase2LengthControl, phase3LengthControl,
    quotientXorControl, quotientXorControlInverse,
    coefficientTemporaryControl, coefficientSubControl, coefficientAddControl]

@[simp]
theorem indexedStepInverseUnitary_HPFree
    (registers : IndexedStepRegisters) (n T : Nat) :
    HPFree (indexedStepInverseUnitary registers n T) := by
  simp [indexedStepInverseUnitary, blockAInverse, blockBInverse, blockB1Inverse,
    blockB2, blockB3Inverse, blockCInverse, blockDInverse, blockEInverse,
    blockFInverse, blockGInverse, toggleTerminal,
    remainderSubControl, remainderPhase2Control, remainderRestoreControl,
    toggleRControl, phase2LengthControl, phase3LengthControl,
    quotientXorControl, quotientXorControlInverse,
    coefficientTemporaryControl, coefficientSubControl, coefficientAddControl,
    indexedStep_hpFree_adjoint (preShiftUnitary_HPFree registers.preShift),
    indexedStep_hpFree_adjoint (postShiftUnitary_HPFree registers.postShift)]

private theorem phaseUpdateAdaptive_coherent_of_indexedReady
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    Quantum.CoherentlyImplementsOn
      (phaseUpdateEpochAdaptive registers.phaseUpdate registers.shiftEpoch)
      (Quantum.run (blockGForward registers))
      (IndexedStepReady registers) := by
  apply indexedStep_coherent_strengthen
    (phaseUpdateEpochAdaptive_coherent registers.phaseUpdate registers.shiftEpoch
      hlayout.phaseUpdate)
  intro state hready wire hwire
  exact hready wire (by
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons]
    exact Or.inr (hlayout.phaseUpdate_scratch_sub_source wire hwire))

private theorem blockCDForward_ready
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepBorrowedReady registers state) :
    IndexedStepReady registers
      (run (blockCForward registers ++
        blockDForward registers (certifiedActiveWindows n T).quotientSwap) state) := by
  rw [Classical.run_append]
  have hC := blockCForward_correct registers n T state hlayout hready
  exact (blockDForward_correct registers n T _
    (run (blockCForward registers) state) hlayout rfl hC.2).2

private theorem indexedStepAdaptive_GH_coherent
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    Quantum.CoherentlyImplementsOn
      ((phaseUpdateEpochAdaptive registers.phaseUpdate registers.shiftEpoch).seq
        (adaptiveUnitary (blockHForward registers n T)))
      (Quantum.run (blockGForward registers ++ blockHForward registers n T))
      (IndexedStepReady registers) := by
  have hphase := phaseUpdateAdaptive_coherent_of_indexedReady registers n T hlayout
  have hend := Quantum.CoherentlyImplementsOn.unitary
    (blockHForward registers n T) (fun _ ↦ True)
  simpa [adaptiveUnitary] using indexedStep_coherent_seq_circuits hphase hend
    (by simp [blockGForward]) (fun _ _ ↦ trivial)

private theorem indexedStepAdaptive_FGH_coherent
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    Quantum.CoherentlyImplementsOn
      ((adaptiveUnitary (blockFForward registers)).seq
        ((phaseUpdateEpochAdaptive registers.phaseUpdate registers.shiftEpoch).seq
          (adaptiveUnitary (blockHForward registers n T))))
      (Quantum.run (blockFForward registers ++ blockGForward registers ++
        blockHForward registers n T))
      (IndexedStepReady registers) := by
  have hshift := Quantum.CoherentlyImplementsOn.unitary
    (blockFForward registers) (IndexedStepReady registers)
  have htail := indexedStepAdaptive_GH_coherent registers n T hlayout
  have hall := indexedStep_coherent_seq_circuits hshift htail
    (by simp [blockFForward])
    (fun state hready ↦ (blockFForward_correct registers n T state hlayout hready).2)
  simpa [adaptiveUnitary, List.append_assoc] using hall

private theorem indexedStepAdaptive_EFGH_coherent
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    let windows := certifiedActiveWindows n T
    Quantum.CoherentlyImplementsOn
      ((blockEAdaptive registers n windows.coefficient).seq
        ((adaptiveUnitary (blockFForward registers)).seq
          ((phaseUpdateEpochAdaptive registers.phaseUpdate registers.shiftEpoch).seq
            (adaptiveUnitary (blockHForward registers n T)))))
      (Quantum.run (blockEForward registers n windows.coefficient ++
        blockFForward registers ++ blockGForward registers ++
        blockHForward registers n T))
      (IndexedStepReady registers) := by
  let windows := certifiedActiveWindows n T
  have hcoefficient := blockEAdaptive_coherent registers n T windows.coefficient
    hlayout rfl
  have htail := indexedStepAdaptive_FGH_coherent registers n T hlayout
  have hall := indexedStep_coherent_seq_circuits hcoefficient htail
    (by simp [blockEForward, coefficientTemporaryControl,
      coefficientSubControl, coefficientAddControl])
    (fun state hready ↦
      (blockEForward_correct registers n T windows.coefficient state
        hlayout rfl hready).2)
  simpa [windows, List.append_assoc] using hall

private theorem indexedStepAdaptive_CDEFGH_coherent
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    let windows := certifiedActiveWindows n T
    Quantum.CoherentlyImplementsOn
      ((adaptiveUnitary (blockCForward registers ++
          blockDForward registers windows.quotientSwap)).seq
        ((blockEAdaptive registers n windows.coefficient).seq
          ((adaptiveUnitary (blockFForward registers)).seq
            ((phaseUpdateEpochAdaptive registers.phaseUpdate registers.shiftEpoch).seq
              (adaptiveUnitary (blockHForward registers n T))))))
      (Quantum.run (blockCForward registers ++
        blockDForward registers windows.quotientSwap ++
        blockEForward registers n windows.coefficient ++
        blockFForward registers ++ blockGForward registers ++
        blockHForward registers n T))
      (IndexedStepBorrowedReady registers) := by
  let windows := certifiedActiveWindows n T
  have hprefix := Quantum.CoherentlyImplementsOn.unitary
    (blockCForward registers ++ blockDForward registers windows.quotientSwap)
    (IndexedStepBorrowedReady registers)
  have htail := indexedStepAdaptive_EFGH_coherent registers n T hlayout
  have hall := indexedStep_coherent_seq_circuits hprefix htail
    (by simp [blockCForward, blockDForward, toggleTerminal,
      phase2LengthControl, phase3LengthControl, quotientXorControl,
      quotientXorControlInverse])
    (fun state hready ↦ blockCDForward_ready registers n T state hlayout hready)
  simpa [windows, adaptiveUnitary, List.append_assoc] using hall

private theorem indexedStepAdaptive_BCDEFGH_coherent
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    let windows := certifiedActiveWindows n T
    Quantum.CoherentlyImplementsOn
      ((blockBAdaptive registers n windows.remainder).seq
        ((adaptiveUnitary (blockCForward registers ++
            blockDForward registers windows.quotientSwap)).seq
          ((blockEAdaptive registers n windows.coefficient).seq
            ((adaptiveUnitary (blockFForward registers)).seq
              ((phaseUpdateEpochAdaptive registers.phaseUpdate registers.shiftEpoch).seq
                (adaptiveUnitary (blockHForward registers n T)))))))
      (Quantum.run (blockBForward registers n windows.remainder ++
        blockCForward registers ++ blockDForward registers windows.quotientSwap ++
        blockEForward registers n windows.coefficient ++
        blockFForward registers ++ blockGForward registers ++
        blockHForward registers n T))
      (IndexedStepBorrowedReady registers) := by
  let windows := certifiedActiveWindows n T
  have hremainder := blockBAdaptive_coherent registers n T windows.remainder
    hlayout rfl
  have htail := indexedStepAdaptive_CDEFGH_coherent registers n T hlayout
  have hall := indexedStep_coherent_seq_circuits hremainder htail
    (by simp [blockBForward, blockB1Forward, blockB2, blockB3Forward,
      remainderSubControl, remainderPhase2Control, remainderRestoreControl,
      toggleRControl])
    (fun state hready ↦
      (blockBForward_correct registers n T windows.remainder state
        hlayout rfl hready).2)
  simpa [windows, List.append_assoc] using hall

/-- Replacing every eligible reverse v-chain in the full indexed source step by X-basis
measurement/reset preserves the exact coherent step on all encoded, clean-scratch inputs. -/
theorem indexedStepAdaptive_coherent
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    Quantum.CoherentlyImplementsOn
      (indexedStepAdaptive registers n T)
      (Quantum.run (indexedStepUnitary registers n T))
      (fun state ↦ IndexedStepReady registers state ∧
        IndexedStepEpochEncoded registers state) := by
  let Valid := fun state ↦ IndexedStepReady registers state ∧
    IndexedStepEpochEncoded registers state
  have hfirst := Quantum.CoherentlyImplementsOn.unitary
    (blockAForward registers) Valid
  have htail := indexedStepAdaptive_BCDEFGH_coherent registers n T hlayout
  have hall := indexedStep_coherent_seq_circuits hfirst htail
    (by simp [blockAForward, toggleTerminal]) (by
      intro state hvalid
      exact blockAForward_borrowedReady registers n T state hlayout
        hvalid.1 hvalid.2)
  simpa [indexedStepAdaptive, indexedStepUnitary, Valid, adaptiveUnitary,
    List.append_assoc] using hall

/-! ## Circuit-free full-step semantics -/

/-- State immediately before the optional iteration-end block, expressed only through the
gate-independent recurrences of Blocks A--G. -/
def indexedStepBeforeEndState
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState) : BasisState :=
  let windows := certifiedActiveWindows n T
  blockGForwardState registers
    (blockFForwardState registers
      (blockEForwardState registers n windows.coefficient
        (blockDForwardState registers windows.quotientSwap
          (blockCForwardState registers
            (blockBForwardState registers n windows.remainder
              (blockAForwardState registers state))))))

/-- Gate-independent recurrence of one literal indexed Algorithm-3 microstep.  The two boundary
arguments are the decoded end-of-iteration routes and are ignored away from `T % 4 = 0`. -/
def indexedStepForwardState
    (registers : IndexedStepRegisters) (n T boundary4 boundary5 : Nat)
    (state : BasisState) : BasisState :=
  blockHForwardState registers n T boundary4 boundary5
    (indexedStepBeforeEndState registers n T state)

/-- Actual pair of unary routes consumed by the optional iteration-end aggregate. -/
def indexedStepEndRoutes
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState) : Nat × Nat :=
  let inner := registers.endIteration n T
  let windows := endIterationWindowsAt n T
  let beforeEnd := indexedStepBeforeEndState registers n T state
  let enabled := blockHEndInputState registers beforeEnd
  let swapped := run (controlledWorkSwap inner.control inner.work1 inner.work2) enabled
  let afterUpper := run (lenUpdateLtUnary n windows.k4 windows.K4
    (inner.upperTree windows) inner.control
    (inner.rangeAccumulator windows.k4 windows.K4)
    (inner.temporary windows.k4 windows.K4) inner.carry
    (inner.path windows.k4 windows.K4) inner.work1At inner.work2At
    inner.lengthT inner.lengthRP inner.constants) swapped
  ((inner.upperTree windows).routeLabel
      (run (constMinus inner.lengthRP inner.constants inner.carry (n + 2)) swapped),
    (inner.lowerTree n windows).routeLabel
      (run (addConstant inner.lengthT inner.constants inner.carry 3) afterUpper))

/-- The literal coherent source stream implements the circuit-free indexed recurrence, restores
every step-local temporary, and leaves the borrowed epoch as persistent padding state. -/
theorem indexedStepUnitary_correct
    (registers : IndexedStepRegisters) (n T boundary4 boundary5 : Nat)
    (hboundary4 : (endIterationWindowsAt n T).k4 ≤ boundary4 ∧
      boundary4 ≤ (endIterationWindowsAt n T).K4)
    (hboundary5 : (endIterationWindowsAt n T).k5 ≤ boundary5 ∧
      boundary5 ≤ (endIterationWindowsAt n T).K5Decode n)
    (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state)
    (hencoded : IndexedStepEpochEncoded registers state)
    (hroutes : T % 4 = 0 →
      indexedStepEndRoutes registers n T state = (boundary4, boundary5)) :
    run (indexedStepUnitary registers n T) state =
        indexedStepForwardState registers n T boundary4 boundary5 state ∧
      IndexedStepReady registers (run (indexedStepUnitary registers n T) state) := by
  let windows := certifiedActiveWindows n T
  let afterA := blockAForwardState registers state
  let afterB := blockBForwardState registers n windows.remainder afterA
  let afterC := blockCForwardState registers afterB
  let afterD := blockDForwardState registers windows.quotientSwap afterC
  let afterE := blockEForwardState registers n windows.coefficient afterD
  let afterF := blockFForwardState registers afterE
  let beforeEnd := blockGForwardState registers afterF
  have hA := blockAForward_correct registers n T state hlayout hready
  have hABorrowed : IndexedStepBorrowedReady registers afterA := by
    have h := blockAForward_borrowedReady registers n T state hlayout hready
      hencoded
    rw [hA.1] at h
    simpa only [afterA] using h
  have hB := blockBForward_correct registers n T windows.remainder afterA
    hlayout (by rfl) hABorrowed
  have hBBorrowed : IndexedStepBorrowedReady registers afterB := by
    have h := hB.2
    rw [hB.1] at h
    simpa only [afterB] using h
  have hC := blockCForward_correct registers n T afterB hlayout hBBorrowed
  have hCReady : IndexedStepReady registers afterC := by
    have h := hC.2
    rw [hC.1] at h
    simpa only [afterC] using h
  have hD := blockDForward_correct registers n T windows.quotientSwap afterC
    hlayout (by rfl) hCReady
  have hDReady : IndexedStepReady registers afterD := by
    have h := hD.2
    rw [hD.1] at h
    simpa only [afterD] using h
  have hE := blockEForward_correct registers n T windows.coefficient afterD
    hlayout (by rfl) hDReady
  have hEReady : IndexedStepReady registers afterE := by
    have h := hE.2
    rw [hE.1] at h
    simpa only [afterE] using h
  have hF := blockFForward_correct registers n T afterE hlayout hEReady
  have hFReady : IndexedStepReady registers afterF := by
    have h := hF.2
    rw [hF.1] at h
    simpa only [afterF] using h
  have hG := blockGForward_correct registers n T afterF hlayout hFReady
  have hGReady : IndexedStepReady registers beforeEnd := by
    have h := hG.2
    rw [hG.1] at h
    simpa only [beforeEnd] using h
  have hroute4 : T % 4 = 0 →
      ((registers.endIteration n T).upperTree
        (endIterationWindowsAt n T)).routeLabel
        (run (constMinus (registers.endIteration n T).lengthRP
            (registers.endIteration n T).constants
            (registers.endIteration n T).carry (n + 2))
          (run (controlledWorkSwap (registers.endIteration n T).control
            (registers.endIteration n T).work1
            (registers.endIteration n T).work2)
            (blockHEndInputState registers beforeEnd))) = boundary4 := by
    intro hstep
    have hr := congrArg Prod.fst (hroutes hstep)
    simpa only [indexedStepEndRoutes, beforeEnd, afterF, afterE, afterD,
      afterC, afterB, afterA, windows] using hr
  have hroute5 : T % 4 = 0 →
      ((registers.endIteration n T).lowerTree n
        (endIterationWindowsAt n T)).routeLabel
        (run (addConstant (registers.endIteration n T).lengthT
            (registers.endIteration n T).constants
            (registers.endIteration n T).carry 3)
          (run (lenUpdateLtUnary n (endIterationWindowsAt n T).k4
            (endIterationWindowsAt n T).K4
            ((registers.endIteration n T).upperTree (endIterationWindowsAt n T))
            (registers.endIteration n T).control
            ((registers.endIteration n T).rangeAccumulator
              (endIterationWindowsAt n T).k4 (endIterationWindowsAt n T).K4)
            ((registers.endIteration n T).temporary
              (endIterationWindowsAt n T).k4 (endIterationWindowsAt n T).K4)
            (registers.endIteration n T).carry
            ((registers.endIteration n T).path
              (endIterationWindowsAt n T).k4 (endIterationWindowsAt n T).K4)
            (registers.endIteration n T).work1At
            (registers.endIteration n T).work2At
            (registers.endIteration n T).lengthT
            (registers.endIteration n T).lengthRP
            (registers.endIteration n T).constants)
          (run (controlledWorkSwap (registers.endIteration n T).control
            (registers.endIteration n T).work1
            (registers.endIteration n T).work2)
            (blockHEndInputState registers beforeEnd)))) = boundary5 := by
    intro hstep
    have hr := congrArg Prod.snd (hroutes hstep)
    simpa only [indexedStepEndRoutes, beforeEnd, afterF, afterE, afterD,
      afterC, afterB, afterA, windows] using hr
  have hH := blockHForward_correct registers n T boundary4 boundary5
    hboundary4 hboundary5 beforeEnd hlayout hroute4 hroute5 hGReady
  have hrun : run (indexedStepUnitary registers n T) state =
      indexedStepForwardState registers n T boundary4 boundary5 state := by
    simp only [indexedStepUnitary, Classical.run_append]
    rw [hA.1, hB.1, hC.1, hD.1, hE.1, hF.1, hG.1, hH.1]
    rfl
  constructor
  · exact hrun
  · rw [hrun]
    have h := hH.2
    rw [hH.1] at h
    simpa only [indexedStepForwardState, indexedStepBeforeEndState,
      beforeEnd, afterF, afterE, afterD, afterC, afterB, afterA, windows]
      using h

/-! ## Constructor-derived resources -/

/-- Exact measurement count of the adaptive full step.  The surrounding source blocks are
unitary, so only the two interval traversals, two coefficient traversals, and phase update
contribute measurements. -/
def indexedStepAdaptiveMeasurementFormula
    (registers : IndexedStepRegisters) (n T : Nat) : Nat :=
  let windows := certifiedActiveWindows n T
  let remainder := registers.remainder windows.remainder
  let coefficient := registers.coefficient windows.coefficient
  2 * intervalMeasurementFormula remainder
      windows.remainder.start windows.remainder.stop +
    4 * (coefficientPrefixTree coefficient windows.coefficient.start
      windows.coefficient.stop).leaves +
    4 * (coefficientPrefixTree coefficient windows.coefficient.start
      windows.coefficient.stop).internalNodes +
    2 * (mcxVChainMeasurementCost registers.phaseUpdate.lengthQ.length +
      mcxVChainMeasurementCost registers.phaseUpdate.lengthRPrime.length +
      mcxVChainMeasurementCost (registers.phaseUpdate.lengthS.length + 1))

/-- Exact worst-branch T count of the adaptive full step, split into literal unitary source
blocks and the five measurement-uncomputed substitutions. -/
def indexedStepAdaptiveTFormula
    (registers : IndexedStepRegisters) (n T : Nat) : Nat :=
  let windows := certifiedActiveWindows n T
  let remainder := registers.remainder windows.remainder
  let coefficient := registers.coefficient windows.coefficient
  ShorECDLP.tCount (blockAForward registers) +
    2 * ShorECDLP.tCount (remainderSubControl registers) +
    intervalAdaptiveTFormula remainder windows.remainder.start
      windows.remainder.stop .sub +
    ShorECDLP.tCount (blockB2 registers) +
    2 * ShorECDLP.tCount (remainderRestoreControl registers) +
    intervalAdaptiveTFormula remainder windows.remainder.start
      windows.remainder.stop .add +
    ShorECDLP.tCount (blockCForward registers) +
    ShorECDLP.tCount (blockDForward registers windows.quotientSwap) +
    ShorECDLP.tCount (blockEPrefix registers n) +
    70 * (coefficientPrefixTree coefficient windows.coefficient.start
      windows.coefficient.stop).leaves +
    28 * (coefficientPrefixTree coefficient windows.coefficient.start
      windows.coefficient.stop).internalNodes +
    ShorECDLP.tCount (blockEMiddle registers) +
    ShorECDLP.tCount (blockESuffix registers n) +
    ShorECDLP.tCount (blockFForward registers) +
    7 * (2 * (mcxVChainAdaptiveToffoliCost
        registers.phaseUpdate.lengthQ.length +
      mcxVChainAdaptiveToffoliCost registers.phaseUpdate.lengthRPrime.length +
      mcxVChainAdaptiveToffoliCost
        (registers.phaseUpdate.lengthS.length + 1)) + 4) +
    ShorECDLP.tCount (blockHForward registers n T)

private theorem indexedStepAdaptive_measurementCount_seq
    (first second : Quantum.AdaptiveCircuit) :
    (first.seq second).measurementCount =
      first.measurementCount + second.measurementCount := by
  induction first with
  | done => simp [Quantum.AdaptiveCircuit.seq,
      Quantum.AdaptiveCircuit.measurementCount]
  | unitary circuit next ih =>
      simp [Quantum.AdaptiveCircuit.seq,
        Quantum.AdaptiveCircuit.measurementCount, ih]
  | xMeasureReset target onFalse onTrue ihFalse ihTrue =>
      simp [Quantum.AdaptiveCircuit.seq,
        Quantum.AdaptiveCircuit.measurementCount, ihFalse, ihTrue,
        Nat.add_max_add_right, Nat.add_assoc]

private theorem indexedStepAdaptive_tCount_seq
    (first second : Quantum.AdaptiveCircuit) :
    (first.seq second).tCount = first.tCount + second.tCount := by
  induction first with
  | done => simp [Quantum.AdaptiveCircuit.seq, Quantum.AdaptiveCircuit.tCount]
  | unitary circuit next ih =>
      simp [Quantum.AdaptiveCircuit.seq, Quantum.AdaptiveCircuit.tCount,
        ih, Nat.add_assoc]
  | xMeasureReset target onFalse onTrue ihFalse ihTrue =>
      simp [Quantum.AdaptiveCircuit.seq, Quantum.AdaptiveCircuit.tCount,
        ihFalse, ihTrue, Nat.add_max_add_right]

/-- Eight-block Toffoli formula for the coherent forward source step. -/
def indexedStepUnitaryToffoliFormula
    (registers : IndexedStepRegisters) (n T : Nat) : Nat :=
  eeaToffoliCount (blockAForward registers) +
    eeaToffoliCount
      (blockBForward registers n (certifiedActiveWindows n T).remainder) +
    eeaToffoliCount (blockCForward registers) +
    eeaToffoliCount
      (blockDForward registers (certifiedActiveWindows n T).quotientSwap) +
    eeaToffoliCount
      (blockEForward registers n (certifiedActiveWindows n T).coefficient) +
    eeaToffoliCount (blockFForward registers) +
    eeaToffoliCount (blockGForward registers) +
    eeaToffoliCount (blockHForward registers n T)

/-- Eight-block CNOT formula for the coherent forward source step. -/
def indexedStepUnitaryCnotFormula
    (registers : IndexedStepRegisters) (n T : Nat) : Nat :=
  eeaCnotCount (blockAForward registers) +
    eeaCnotCount
      (blockBForward registers n (certifiedActiveWindows n T).remainder) +
    eeaCnotCount (blockCForward registers) +
    eeaCnotCount
      (blockDForward registers (certifiedActiveWindows n T).quotientSwap) +
    eeaCnotCount
      (blockEForward registers n (certifiedActiveWindows n T).coefficient) +
    eeaCnotCount (blockFForward registers) +
    eeaCnotCount (blockGForward registers) +
    eeaCnotCount (blockHForward registers n T)

/-- Eight-block standalone-X formula for the coherent forward source step. -/
def indexedStepUnitaryXFormula
    (registers : IndexedStepRegisters) (n T : Nat) : Nat :=
  eeaXCount (blockAForward registers) +
    eeaXCount
      (blockBForward registers n (certifiedActiveWindows n T).remainder) +
    eeaXCount (blockCForward registers) +
    eeaXCount
      (blockDForward registers (certifiedActiveWindows n T).quotientSwap) +
    eeaXCount
      (blockEForward registers n (certifiedActiveWindows n T).coefficient) +
    eeaXCount (blockFForward registers) +
    eeaXCount (blockGForward registers) +
    eeaXCount (blockHForward registers n T)

/-- Eight-block Framework-T formula for the coherent forward source step. -/
def indexedStepUnitaryTFormula
    (registers : IndexedStepRegisters) (n T : Nat) : Nat :=
  ShorECDLP.tCount (blockAForward registers) +
    ShorECDLP.tCount
      (blockBForward registers n (certifiedActiveWindows n T).remainder) +
    ShorECDLP.tCount (blockCForward registers) +
    ShorECDLP.tCount
      (blockDForward registers (certifiedActiveWindows n T).quotientSwap) +
    ShorECDLP.tCount
      (blockEForward registers n (certifiedActiveWindows n T).coefficient) +
    ShorECDLP.tCount (blockFForward registers) +
    ShorECDLP.tCount (blockGForward registers) +
    ShorECDLP.tCount (blockHForward registers n T)

/-- Eight-block Toffoli formula for the explicit reverse source step. -/
def indexedStepInverseUnitaryToffoliFormula
    (registers : IndexedStepRegisters) (n T : Nat) : Nat :=
  eeaToffoliCount (blockHInverse registers n T) +
    eeaToffoliCount (blockGInverse registers) +
    eeaToffoliCount (blockFInverse registers) +
    eeaToffoliCount
      (blockEInverse registers n (certifiedActiveWindows n T).coefficient) +
    eeaToffoliCount
      (blockDInverse registers (certifiedActiveWindows n T).quotientSwap) +
    eeaToffoliCount (blockCInverse registers) +
    eeaToffoliCount
      (blockBInverse registers n (certifiedActiveWindows n T).remainder) +
    eeaToffoliCount (blockAInverse registers)

/-- Eight-block CNOT formula for the explicit reverse source step. -/
def indexedStepInverseUnitaryCnotFormula
    (registers : IndexedStepRegisters) (n T : Nat) : Nat :=
  eeaCnotCount (blockHInverse registers n T) +
    eeaCnotCount (blockGInverse registers) +
    eeaCnotCount (blockFInverse registers) +
    eeaCnotCount
      (blockEInverse registers n (certifiedActiveWindows n T).coefficient) +
    eeaCnotCount
      (blockDInverse registers (certifiedActiveWindows n T).quotientSwap) +
    eeaCnotCount (blockCInverse registers) +
    eeaCnotCount
      (blockBInverse registers n (certifiedActiveWindows n T).remainder) +
    eeaCnotCount (blockAInverse registers)

/-- Eight-block standalone-X formula for the explicit reverse source step. -/
def indexedStepInverseUnitaryXFormula
    (registers : IndexedStepRegisters) (n T : Nat) : Nat :=
  eeaXCount (blockHInverse registers n T) +
    eeaXCount (blockGInverse registers) +
    eeaXCount (blockFInverse registers) +
    eeaXCount
      (blockEInverse registers n (certifiedActiveWindows n T).coefficient) +
    eeaXCount
      (blockDInverse registers (certifiedActiveWindows n T).quotientSwap) +
    eeaXCount (blockCInverse registers) +
    eeaXCount
      (blockBInverse registers n (certifiedActiveWindows n T).remainder) +
    eeaXCount (blockAInverse registers)

/-- Eight-block Framework-T formula for the explicit reverse source step. -/
def indexedStepInverseUnitaryTFormula
    (registers : IndexedStepRegisters) (n T : Nat) : Nat :=
  ShorECDLP.tCount (blockHInverse registers n T) +
    ShorECDLP.tCount (blockGInverse registers) +
    ShorECDLP.tCount (blockFInverse registers) +
    ShorECDLP.tCount
      (blockEInverse registers n (certifiedActiveWindows n T).coefficient) +
    ShorECDLP.tCount
      (blockDInverse registers (certifiedActiveWindows n T).quotientSwap) +
    ShorECDLP.tCount (blockCInverse registers) +
    ShorECDLP.tCount
      (blockBInverse registers n (certifiedActiveWindows n T).remainder) +
    ShorECDLP.tCount (blockAInverse registers)

/-- The coherent source term's Toffoli count is exactly its eight-block formula. -/
theorem indexedStepUnitary_toffoliCount
    (registers : IndexedStepRegisters) (n T : Nat) :
    eeaToffoliCount (indexedStepUnitary registers n T) =
      indexedStepUnitaryToffoliFormula registers n T := by
  simp [indexedStepUnitary, indexedStepUnitaryToffoliFormula,
    eeaToffoliCount_append, Nat.add_assoc]

/-- The coherent source term's CNOT count is exactly its eight-block formula. -/
theorem indexedStepUnitary_cnotCount
    (registers : IndexedStepRegisters) (n T : Nat) :
    eeaCnotCount (indexedStepUnitary registers n T) =
      indexedStepUnitaryCnotFormula registers n T := by
  simp [indexedStepUnitary, indexedStepUnitaryCnotFormula,
    eeaCnotCount_append, Nat.add_assoc]

/-- The coherent source term's X count is exactly its eight-block formula. -/
theorem indexedStepUnitary_xCount
    (registers : IndexedStepRegisters) (n T : Nat) :
    eeaXCount (indexedStepUnitary registers n T) =
      indexedStepUnitaryXFormula registers n T := by
  simp [indexedStepUnitary, indexedStepUnitaryXFormula,
    eeaXCount_append, Nat.add_assoc]

/-- The coherent source term's Framework T count is exactly its eight-block formula. -/
theorem indexedStepUnitary_tCount
    (registers : IndexedStepRegisters) (n T : Nat) :
    ShorECDLP.tCount (indexedStepUnitary registers n T) =
      indexedStepUnitaryTFormula registers n T := by
  simp [indexedStepUnitary, indexedStepUnitaryTFormula, tCount_append,
    Nat.add_assoc]

/-- The explicit reverse term's Toffoli count is exactly its eight-block formula. -/
theorem indexedStepInverseUnitary_toffoliCount
    (registers : IndexedStepRegisters) (n T : Nat) :
    eeaToffoliCount (indexedStepInverseUnitary registers n T) =
      indexedStepInverseUnitaryToffoliFormula registers n T := by
  simp [indexedStepInverseUnitary, indexedStepInverseUnitaryToffoliFormula,
    eeaToffoliCount_append, Nat.add_assoc]

/-- The explicit reverse term's CNOT count is exactly its eight-block formula. -/
theorem indexedStepInverseUnitary_cnotCount
    (registers : IndexedStepRegisters) (n T : Nat) :
    eeaCnotCount (indexedStepInverseUnitary registers n T) =
      indexedStepInverseUnitaryCnotFormula registers n T := by
  simp [indexedStepInverseUnitary, indexedStepInverseUnitaryCnotFormula,
    eeaCnotCount_append, Nat.add_assoc]

/-- The explicit reverse term's X count is exactly its eight-block formula. -/
theorem indexedStepInverseUnitary_xCount
    (registers : IndexedStepRegisters) (n T : Nat) :
    eeaXCount (indexedStepInverseUnitary registers n T) =
      indexedStepInverseUnitaryXFormula registers n T := by
  simp [indexedStepInverseUnitary, indexedStepInverseUnitaryXFormula,
    eeaXCount_append, Nat.add_assoc]

/-- The explicit reverse term's Framework T count is exactly its eight-block formula. -/
theorem indexedStepInverseUnitary_tCount
    (registers : IndexedStepRegisters) (n T : Nat) :
    ShorECDLP.tCount (indexedStepInverseUnitary registers n T) =
      indexedStepInverseUnitaryTFormula registers n T := by
  simp [indexedStepInverseUnitary, indexedStepInverseUnitaryTFormula,
    tCount_append, Nat.add_assoc]

/-- Exact constructor-derived measurement count of the adaptive full step. -/
theorem indexedStepAdaptive_measurementCount
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    (indexedStepAdaptive registers n T).measurementCount =
      indexedStepAdaptiveMeasurementFormula registers n T := by
  simp only [indexedStepAdaptive, blockBAdaptive, blockB1Adaptive,
    blockB3Adaptive, blockEAdaptive, blockEFirstAdaptive,
    blockETailAdaptive, indexedStepAdaptive_measurementCount_seq,
    adaptiveUnitary, Quantum.AdaptiveCircuit.measurementCount]
  rw [intervalAddSub_measurementCount _ _ _ _ .sub true .work1
      hlayout.remainder,
    intervalAddSub_measurementCount _ _ _ _ .add false .work1
      hlayout.remainder,
    coefficientPrefixAdaptive_measurementCount _ .sub false .work2
      hlayout.coefficient,
    coefficientPrefixAdaptive_measurementCount _ .add true .work2
      hlayout.coefficient,
    phaseUpdateEpochAdaptive_measurementCount _ _ hlayout.phaseUpdate]
  simp only [indexedStepAdaptiveMeasurementFormula]
  omega

/-- Exact constructor-derived worst-branch T count of the adaptive full step. -/
theorem indexedStepAdaptive_tCount
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    (indexedStepAdaptive registers n T).tCount =
      indexedStepAdaptiveTFormula registers n T := by
  simp only [indexedStepAdaptive, blockBAdaptive, blockB1Adaptive,
    blockB3Adaptive, blockEAdaptive, blockEFirstAdaptive,
    blockETailAdaptive, indexedStepAdaptive_tCount_seq,
    adaptiveUnitary, Quantum.AdaptiveCircuit.tCount, tCount_append]
  rw [intervalAddSub_tCount _ _ _ _ .sub true .work1 hlayout.remainder,
    intervalAddSub_tCount _ _ _ _ .add false .work1 hlayout.remainder,
    coefficientPrefixAdaptive_tCount _ .sub false .work2 hlayout.coefficient,
    coefficientPrefixAdaptive_tCount _ .add true .work2 hlayout.coefficient,
    phaseUpdateEpochAdaptive_tCount _ _ hlayout.phaseUpdate]
  simp only [indexedStepAdaptiveTFormula]
  omega

end

end ShorECDLP.Paper2607_13816
