import ShorECDLP.Submission.«2607_13816».EEA.CoefficientArithmetic
import ShorECDLP.Submission.«2607_13816».EEA.CoefficientPrefixInverse
import ShorECDLP.Submission.«2607_13816».EEA.EndIteration
import ShorECDLP.Submission.«2607_13816».EEA.PhaseUpdate
import ShorECDLP.Submission.«2607_13816».EEA.StepControl
import ShorECDLP.Submission.«2607_13816».EEA.TBoundary
import ShorECDLP.Submission.«2607_13816».EEA.ShiftCounter

/-!
# One indexed Algorithm-3 microstep

This module composes the source-exact Phase-5 building blocks into the literal forward and
explicit reverse bodies of `append_one_step_T` from the pinned arXiv:2607.13816v2 supplement.
The scheduler uses `certifiedActiveWindows`: in particular the remainder block keeps the proved
one-lane conservative repair, while the other four windows agree with Appendix A.2.

The certified implementation uses twenty-two serially shared auxiliary wires.  `Aux[0]` is the
temporary control, `Aux[1]` is the borrowed shift epoch, and `Aux[2:]` supplies the block-local
scratch views below.  The final two wires are the explicit capacity repair required when the
certified remainder window widens the pinned 257-lane source interval to 258 lanes.

Consequently the untouched generator remains a 578-internal / 579-with-external-control source
artifact, while the presently verified repaired step has 580 internal roles and 581 after adding
that control.  Recovering the paper's 579-role target requires either tightening the remainder
window proof or proving a safe allocator reuse; this module claims neither.
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

/-- `Aux[2:20]`, called `scratch` by the pinned source. -/
def sourceScratch (registers : IndexedStepRegisters) : List Wire :=
  (registers.aux.take 20).drop 2

/-- Two repair-only ancillas appended after the pinned source's twenty-wire `Aux` bank. -/
def remainderRepairScratch (registers : IndexedStepRegisters) : List Wire :=
  registers.aux.drop 20

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
  phase1IsZero := registers.sourceScratch.getD registers.lengthS.length 0
  both := registers.sourceScratch.getD 0 0
  carries := (registers.sourceScratch.drop 1).take (registers.lengthS.length - 1)
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
borrowed epoch has been spilled and cleared, and ends with the two certified-window repair
ancillas. -/
def remainder
    (registers : IndexedStepRegisters) (window : ActiveWindow) : IntervalRegisters :=
  { registers.remainderBase window with
    scratch := (registers.shiftEpoch :: (registers.sourceScratch ++
      registers.remainderRepairScratch)).take
        (registers.remainderScratchSize window) }

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

def blockB1Forward
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

def blockB2 (registers : IndexedStepRegisters) : Circuit :=
  circuit! {
    remainderPhase2Control registers;
    gate! Gate.CX registers.control registers.sign;
    remainderPhase2Control registers
  }

def blockB3Forward
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

def blockBForward
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

def blockCForward (registers : IndexedStepRegisters) : Circuit :=
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

/-- Phase-2 quotient-length increment at the start of Block D. -/
def blockD1Forward (registers : IndexedStepRegisters) : Circuit :=
  circuit! {
    phase2LengthControl registers;
    controlledIncrement registers.control registers.lengthQ (lengthCarries registers);
    phase2LengthControl registers
  }

/-- Phase-3 quotient-length decrement at the end of Block D. -/
def blockD3Forward (registers : IndexedStepRegisters) : Circuit :=
  circuit! {
    phase3LengthControl registers;
    controlledDecrement registers.control registers.lengthQ (lengthCarries registers);
    phase3LengthControl registers
  }

/-- Phase-controlled quotient/sign selector used by the source Block D. -/
def blockD2Forward (registers : IndexedStepRegisters) (window : ActiveWindow) : Circuit :=
  circuit! {
    quotientXorControl registers;
    quotientSwapUnitary (registers.quotient window) window.start window.stop;
    quotientXorControlInverse registers
  }

def blockDForward
    (registers : IndexedStepRegisters) (window : ActiveWindow) : Circuit :=
  circuit! {
    blockD1Forward registers;
    blockD2Forward registers window;
    blockD3Forward registers
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

/-- The source subtraction-control sandwich, shared by preparation and cleanup. -/
def coefficientSubtractControl (r : IndexedStepRegisters) : Circuit :=
  coefficientTemporaryControl r ++ coefficientSubControl r ++ coefficientTemporaryControl r

/-- Block E up to the prepared coefficient boundary, before either arithmetic scan. -/
def blockEPrepareForward (r : IndexedStepRegisters) (n : Nat) : Circuit :=
  coefficientSubtractControl r ++ prepareLatestPaperTBoundary r.tBoundary n

/-- Block E through coefficient subtraction and its control cleanup. -/
def blockESubtractForward (r : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) : Circuit :=
  blockEPrepareForward r n ++
    coefficientPrefixUnitary (r.coefficient window) window.start window.stop .sub false .work2 ++
    coefficientTemporaryControl r ++ coefficientSubControl r ++ coefficientTemporaryControl r

/-- The source sign flip, coefficient addition, control cleanup and boundary restore. -/
def blockEFinishForward (r : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) : Circuit :=
  [.CX r.phase1 r.sign] ++ coefficientAddControl r ++
    coefficientPrefixUnitary (r.coefficient window) window.start window.stop .add true .work2 ++
    coefficientAddControl r ++ restoreLatestPaperTBoundary r.tBoundary n

private def blockEForward
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) : Circuit :=
  blockESubtractForward registers n window ++ blockEFinishForward registers n window

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
  aux_length : registers.aux.length = 22
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

/-! The closed production witness below uses executable checks only to discharge the finite
decoder trees.  The soundness lemmas turn those checks back into the ordinary inductive layout
judgments; no executable checker enters the public contract. -/

private def dualTreeLayoutCheck :
    DualUnaryActionTree → Wire → Wire → List Wire → List Wire → Bool
  | .leaf label, controlA, controlB, pathsA, pathsB =>
      decide
        (DualUnaryActionTree.decoderWires (.leaf label)
          controlA controlB pathsA pathsB).Nodup
  | .node indexA indexB zero one, controlA, controlB,
      pathA :: restA, pathB :: restB =>
      decide
          (DualUnaryActionTree.decoderWires
            (.node indexA indexB zero one) controlA controlB
              (pathA :: restA) (pathB :: restB)).Nodup &&
        dualTreeLayoutCheck zero pathA pathB restA restB &&
          dualTreeLayoutCheck one pathA pathB restA restB
  | .node _ _ _ _, _, _, _, _ => false

private theorem dualTreeLayoutCheck_sound
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (pathsA pathsB : List Wire)
    (hcheck : dualTreeLayoutCheck tree controlA controlB pathsA pathsB = true) :
    tree.Layout controlA controlB pathsA pathsB := by
  induction tree generalizing controlA controlB pathsA pathsB with
  | leaf label =>
      simp only [dualTreeLayoutCheck, decide_eq_true_eq] at hcheck
      exact .leaf label controlA controlB pathsA pathsB hcheck
  | node indexA indexB zero one ihZero ihOne =>
      cases pathsA with
      | nil => simp [dualTreeLayoutCheck] at hcheck
      | cons pathA restA =>
          cases pathsB with
          | nil => simp [dualTreeLayoutCheck] at hcheck
          | cons pathB restB =>
              simp only [dualTreeLayoutCheck, Bool.and_eq_true,
                decide_eq_true_eq] at hcheck
              exact .node indexA indexB controlA controlB pathA pathB zero one
                restA restB hcheck.1.1
                (ihZero pathA pathB restA restB hcheck.1.2)
                (ihOne pathA pathB restA restB hcheck.2)

private def intervalTraversalLeavesCheck
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire) : Bool :=
  tree.labels.all fun label =>
    decide
        [rightTop, leftTop, accumulator, targetAt label, addendAt label,
          carry, scratch].Nodup &&
      (tree.decoderWires rightRoot leftRoot rightPaths leftPaths).all fun wire =>
        decide (wire ∉
          [rightTop, leftTop, accumulator, targetAt label, addendAt label,
            carry, scratch])

private theorem intervalTraversalLeavesCheck_sound
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (hcheck : intervalTraversalLeavesCheck tree rightRoot leftRoot
      rightPaths leftPaths rightTop leftTop accumulator carry scratch
        targetAt addendAt = true) :
    ∀ label, label ∈ tree.labels →
      [rightTop, leftTop, accumulator, targetAt label, addendAt label,
        carry, scratch].Nodup ∧
      DecoderOutsideIntervalRoles
        (tree.decoderWires rightRoot leftRoot rightPaths leftPaths)
        rightTop leftTop accumulator (targetAt label) (addendAt label) carry scratch := by
  intro label hlabel
  have hlabelCheck := (List.all_eq_true.mp hcheck) label hlabel
  simp only [Bool.and_eq_true] at hlabelCheck
  refine ⟨of_decide_eq_true hlabelCheck.1, ?_⟩
  rw [DecoderOutsideIntervalRoles, List.disjoint_left]
  intro wire hdecoder harithmetic
  have hwire := (List.all_eq_true.mp hlabelCheck.2) wire hdecoder
  exact (of_decide_eq_true hwire) harithmetic

/-! ## Closed nonterminal layout witness -/

/-- A compact repaired allocation for the first nonterminal step at `n = T = 1`.
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
  aux := List.range' 24 22

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

/-- The full indexed-step physical contract is inhabited by a compact 46-role repaired
allocation.  The theorem keeps the concrete fixture private while making non-vacuity explicit. -/
theorem indexedStepLayout_inhabited :
    ∃ registers : IndexedStepRegisters,
      registers.allWires.length = 46 ∧ IndexedStepLayout registers 1 1 := by
  exact ⟨indexedStepSmallRegisters, by decide, indexedStepSmall_layout⟩

/-! ## Closed production layout witness -/

/-- Dense physical allocation for the first secp256k1 microstep.  The first 578 roles are the
pinned source allocation; wires 578 and 579 are the certified-remainder repair suffix. -/
def indexedStepProductionRegisters : IndexedStepRegisters where
  phase1 := 0
  phase2 := 1
  iter := 2
  sign := 3
  work1 := List.range' 4 259
  work2 := List.range' 263 259
  lengthT := List.range' 522 9
  lengthQ := List.range' 531 9
  lengthS := List.range' 540 9
  lengthRPrime := List.range' 549 9
  aux := List.range' 558 22

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem indexedStepProduction_remainder_layout :
    IntervalLayout
      (indexedStepProductionRegisters.remainder
        (certifiedActiveWindows 256 1).remainder)
      (certifiedActiveWindows 256 1).remainder.start
      (certifiedActiveWindows 256 1).remainder.stop .work1 := by
  let registers := indexedStepProductionRegisters.remainder
    (certifiedActiveWindows 256 1).remainder
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
      change IntervalEndpointLayout (List.range' 522 9)
        (List.range' 531 9) (List.range' 540 9)
        (List.range' 559 9) 577
      norm_num [IntervalEndpointLayout]
      decide
    traversal := ?_
    topSpecial := by
      intro hspecial
      have hnotSpecial : intervalHasTopSpecial
          (certifiedActiveWindows 256 1).remainder.start
          (certifiedActiveWindows 256 1).remainder.stop = false := by
        decide
      rw [hnotSpecial] at hspecial
      contradiction
  }
  rw [IntervalTraversalLayout]
  constructor
  · apply dualTreeLayoutCheck_sound
    decide
  · apply intervalTraversalLeavesCheck_sound
    decide

private theorem indexedStepProduction_quotient_tree :
    quotientSwapTree
      (indexedStepProductionRegisters.quotient
        (certifiedActiveWindows 256 1).quotientSwap) 2 2 = .leaf 2 := by
  rfl

private theorem indexedStepProduction_quotient_layout :
    QuotientSwapLayout
      (indexedStepProductionRegisters.quotient
        (certifiedActiveWindows 256 1).quotientSwap) 2 2 := by
  refine {
    k_le_K := by decide
    work1_length := by decide
    lengthT_eq_lengthQ := by decide
    index_width := by decide
    scratch_length := by decide
    physical := by decide
    tree := ?_
  }
  rw [indexedStepProduction_quotient_tree]
  change UnaryActionTree.Layout (.leaf 2) 558 ([] : List Wire)
  exact UnaryActionTree.Layout.leaf 2 558 ([] : List Wire) (by decide)

private theorem indexedStepProduction_coefficient_tree :
    coefficientPrefixTree
      (indexedStepProductionRegisters.coefficient
        (certifiedActiveWindows 256 1).coefficient) 1 2 =
      .node 523 (.leaf 1) (.leaf 2) := by
  rfl

private theorem indexedStepProduction_coefficient_layout :
    CoefficientPrefixLayout
      (indexedStepProductionRegisters.coefficient
        (certifiedActiveWindows 256 1).coefficient) 1 2 := by
  refine {
    k_le_K := by decide
    work1_length := by decide
    work2_length := by decide
    index_width := by decide
    scratch_length := by decide
    physical := by decide
    tree := ?_
  }
  rw [indexedStepProduction_coefficient_tree]
  change UnaryActionTree.Layout
    (.node 523 (.leaf 1) (.leaf 2)) 558 ([561] : List Wire)
  exact .node 523 558 561 (.leaf 1) (.leaf 2) ([] : List Wire) (by decide)
    (.leaf 1 561 ([] : List Wire) (by decide))
    (.leaf 2 561 ([] : List Wire) (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem indexedStepProduction_layout :
    IndexedStepLayout indexedStepProductionRegisters 256 1 := by
  refine {
    aux_length := by decide
    work1_length := by decide
    work2_length := by decide
    physical := by decide
    terminalControl := by
      change 8 ≤ 17 ∧
        (((0 :: List.range' 549 9) : List Wire) ++
          560 :: List.range' 561 17).Nodup
      decide
    terminalPaddingCapacity := by decide
    terminalPadding := ⟨by decide, by decide⟩
    terminalPhase := by decide
    terminalEpoch := by decide
    preShift := ⟨by decide, by decide, by decide⟩
    remainderSub := by
      refine ⟨?_, ?_, by decide⟩
      · change 7 ≤ 17 ∧
          ((List.range' 549 9 : List Wire) ++
            560 :: List.range' 561 17).Nodup
        decide
      · change 0 ≤ 17 ∧
          (([0, 560] : List Wire) ++
            558 :: List.range' 561 17).Nodup
        decide
    remainderPhase2 := by
      refine ⟨?_, ?_, by decide⟩
      · change 7 ≤ 17 ∧
          ((List.range' 549 9 : List Wire) ++
            560 :: List.range' 561 17).Nodup
        decide
      · change 1 ≤ 17 ∧
          (([0, 1, 560] : List Wire) ++
            558 :: List.range' 561 17).Nodup
        decide
    remainderRestoreCCX := by decide
    controlSign := by decide
    remainderRestore := by
      refine ⟨?_, ?_, by decide⟩
      · change 7 ≤ 16 ∧
          ((List.range' 549 9 : List Wire) ++
            561 :: List.range' 562 16).Nodup
        decide
      · change 1 ≤ 16 ∧
          (([0, 560, 561] : List Wire) ++
            558 :: List.range' 562 16).Nodup
        decide
    remainder := indexedStepProduction_remainder_layout
    lengthQ_positive := by decide
    phase2Length := by
      change 0 ≤ 18 ∧
        (([0, 1] : List Wire) ++ 558 :: List.range' 560 18).Nodup
      decide
    phase3Length := by
      change 0 ≤ 18 ∧
        (([0, 1] : List Wire) ++ 558 :: List.range' 560 18).Nodup
      decide
    lengthCarryCapacity := by decide
    lengthCarryPhysical := by decide
    quotientControls := by decide
    quotient := by
      simpa using indexedStepProduction_quotient_layout
    coefficientTemporary := by
      change 0 ≤ 17 ∧
        (([1, 3] : List Wire) ++ 560 :: List.range' 561 17).Nodup
      decide
    coefficientSub := by
      change 0 ≤ 17 ∧
        (([0, 560] : List Wire) ++ 558 :: List.range' 561 17).Nodup
      decide
    coefficientAdd := by
      change 0 ≤ 17 ∧
        (([0] : List Wire) ++ 558 :: List.range' 561 17).Nodup
      decide
    coefficientSign := by decide
    tBoundary := ⟨by decide, by decide, by decide, by decide, by decide⟩
    coefficient := by
      simpa using indexedStepProduction_coefficient_layout
    postShift := ⟨by decide, by decide, by decide⟩
    phaseUpdate := ⟨by decide, by decide, by decide, by decide, by decide⟩
    endQ := by
      change 7 ≤ 16 ∧
        ((List.range' 531 9 : List Wire) ++
          560 :: List.range' 562 16).Nodup
      decide
    endS := by
      change 8 ≤ 16 ∧
        (((List.range' 540 9 : List Wire) ++ [559]) ++
          561 :: List.range' 562 16).Nodup
      decide
    endControls := by decide
    endIteration := by norm_num
  }

set_option maxRecDepth 100000 in
/-- The complete repaired first-step layout is inhabited by exactly 580 internal roles.  A
caller that adds the external point-add control therefore allocates 581 roles. -/
theorem indexedStepProduction_layout_inhabited :
    ∃ registers : IndexedStepRegisters,
      registers.allWires.length = 580 ∧
        IndexedStepLayout registers 256 1 := by
  exact ⟨indexedStepProductionRegisters, by decide,
    indexedStepProduction_layout⟩

/-- Scratch that is genuinely temporary at an indexed step boundary.  The borrowed epoch is
deliberately excluded: it is persistent padding state, not a clean ancilla. -/
def IndexedStepRegisters.sharedScratch
    (registers : IndexedStepRegisters) : List Wire :=
  registers.control ::
    (registers.sourceScratch ++ registers.remainderRepairScratch)

/-- Every temporary source role is clean at a step boundary. -/
def IndexedStepReady
    (registers : IndexedStepRegisters) (state : BasisState) : Prop :=
  Clean registers.sharedScratch state

/-- During remainder arithmetic the borrowed epoch has been spilled, so the entire auxiliary
bank—including `Aux[1]`—is a clean serial workspace. -/
private def IndexedStepBorrowedReady
    (registers : IndexedStepRegisters) (state : BasisState) : Prop :=
  Clean registers.aux state

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

private theorem wireValues_congr_indexedStep
    (wires : List Wire) (left right : BasisState)
    (hagrees : ∀ wire ∈ wires, left wire = right wire) :
    wireValues wires left = wireValues wires right := by
  induction wires with
  | nil => rfl
  | cons wire wires ih =>
      simp only [wireValues, List.map_cons, List.cons.injEq]
      exact ⟨hagrees wire (by simp), ih (fun next hnext ↦
        hagrees next (by simp [hnext]))⟩

private theorem matchXorState_update_commute
    (controls : List Wire) (value : Nat) (target updated : Wire)
    (bit : Bool) (state : BasisState)
    (htarget : target ≠ updated) (hupdated : updated ∉ controls) :
    (matchXorState controls value target state)[updated ↦ bit] =
      matchXorState controls value target state[updated ↦ bit] := by
  have hmatches :
      registerMatches controls value state[updated ↦ bit] =
        registerMatches controls value state := by
    apply registerMatches_congr
    intro wire hwire
    rw [upd_other]
    intro equality
    subst wire
    exact hupdated hwire
  funext wire
  by_cases hwireUpdated : wire = updated
  · subst wire
    simp [matchXorState, upd, Ne.symm htarget]
  · by_cases hwireTarget : wire = target
    · subst wire
      simp [matchXorState, upd, hwireUpdated, hmatches]
    · simp [matchXorState, upd, hwireUpdated, hwireTarget]

private theorem indexedWriteWireValues_matchXorState_commute
    (wires : List Wire) (bits : List Bool) (controls : List Wire)
    (value : Nat) (target : Wire) (state : BasisState)
    (htarget : target ∉ wires)
    (hcontrols : ∀ control ∈ controls, control ∉ wires) :
    indexedWriteWireValues wires bits
        (matchXorState controls value target state) =
      matchXorState controls value target
        (indexedWriteWireValues wires bits state) := by
  induction wires generalizing bits state with
  | nil => simp [indexedWriteWireValues]
  | cons wire wires ih =>
      cases bits with
      | nil => simp [indexedWriteWireValues]
      | cons bit bits =>
          simp only [List.mem_cons, not_or] at htarget
          have hcontrolsTail : ∀ control ∈ controls, control ∉ wires := by
            intro control hcontrol hwire
            exact hcontrols control hcontrol (by simp [hwire])
          have hwireOutside : wire ∉ controls := by
            intro hwire
            exact hcontrols wire hwire (by simp)
          rw [indexedWriteWireValues,
            ih bits (state := state) htarget.2 hcontrolsTail]
          exact matchXorState_update_commute controls value target wire bit
            (indexedWriteWireValues wires bits state) htarget.1 hwireOutside

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
  exact List.mem_of_mem_take (List.mem_of_mem_drop hwire)

private theorem IndexedStepLayout.remainderRepairScratch_mem_aux
    {registers : IndexedStepRegisters} {n T : Nat}
    (_hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ registers.remainderRepairScratch) :
    wire ∈ registers.aux := by
  exact List.mem_of_mem_drop hwire

private theorem IndexedStepLayout.blockScratch_mem_aux
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ registers.blockScratch) :
    wire ∈ registers.aux := by
  exact hlayout.sourceScratch_mem_aux (List.mem_of_mem_drop hwire)

private theorem IndexedStepLayout.sourceScratch_mem_sharedScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (_hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ registers.sourceScratch) :
    wire ∈ registers.sharedScratch := by
  simp [IndexedStepRegisters.sharedScratch, hwire]

private theorem IndexedStepLayout.remainderRepairScratch_mem_sharedScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (_hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ registers.remainderRepairScratch) :
    wire ∈ registers.sharedScratch := by
  simp [IndexedStepRegisters.sharedScratch, hwire]

private theorem IndexedStepLayout.blockScratch_mem_sharedScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ registers.blockScratch) :
    wire ∈ registers.sharedScratch := by
  exact hlayout.sourceScratch_mem_sharedScratch (List.mem_of_mem_drop hwire)

private theorem IndexedStepLayout.aux_view
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    [registers.control, registers.shiftEpoch] ++
        (registers.sourceScratch ++ registers.remainderRepairScratch) =
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
          have hsplit := List.take_append_drop 18 rest
          simp [IndexedStepRegisters.control, IndexedStepRegisters.shiftEpoch,
            IndexedStepRegisters.sourceScratch,
            IndexedStepRegisters.remainderRepairScratch,
            haux, htail, hsplit]

private theorem IndexedStepLayout.sourceScratch_length
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.sourceScratch.length = 18 := by
  simp [IndexedStepRegisters.sourceScratch, hlayout.aux_length]

private theorem IndexedStepLayout.scratch_view
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.terminal :: registers.blockScratch =
      registers.sourceScratch := by
  cases hscratch : registers.sourceScratch with
  | nil =>
      have hlength := hlayout.sourceScratch_length
      simp [hscratch] at hlength
  | cons terminal rest =>
      simp [IndexedStepRegisters.terminal, IndexedStepRegisters.blockScratch,
        hscratch]

private theorem IndexedStepLayout.aux_view_nodup
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ([registers.control, registers.shiftEpoch] ++
      (registers.sourceScratch ++ registers.remainderRepairScratch)).Nodup := by
  rw [hlayout.aux_view]
  exact hlayout.aux_nodup

private theorem IndexedStepLayout.sourceAux_view_nodup
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ([registers.control, registers.shiftEpoch] ++
      registers.sourceScratch).Nodup := by
  have hfull := hlayout.aux_view_nodup
  rw [← List.append_assoc] at hfull
  exact (List.nodup_append.mp hfull).1

private theorem IndexedStepLayout.remainderRepairScratch_not_sourceAux
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hrepair : wire ∈ registers.remainderRepairScratch) :
    wire ∉ [registers.control, registers.shiftEpoch] ++
      registers.sourceScratch := by
  have hfull := hlayout.aux_view_nodup
  rw [← List.append_assoc] at hfull
  have hcross := (List.nodup_append.mp hfull).2.2
  intro hsource
  exact hcross wire hsource wire hrepair rfl

private theorem IndexedStepLayout.remainderRepairScratch_not_sourceScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hrepair : wire ∈ registers.remainderRepairScratch) :
    wire ∉ registers.sourceScratch := by
  intro hsource
  exact hlayout.remainderRepairScratch_not_sourceAux hrepair (by simp [hsource])

private theorem IndexedStepLayout.remainderRepairScratch_ne_control
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hrepair : wire ∈ registers.remainderRepairScratch) :
    wire ≠ registers.control := by
  intro equality
  exact hlayout.remainderRepairScratch_not_sourceAux hrepair (by simp [equality])

private theorem IndexedStepLayout.remainderRepairScratch_ne_shiftEpoch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hrepair : wire ∈ registers.remainderRepairScratch) :
    wire ≠ registers.shiftEpoch := by
  intro equality
  exact hlayout.remainderRepairScratch_not_sourceAux hrepair (by simp [equality])

private theorem IndexedStepLayout.remainderRepairScratch_not_payload
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hrepair : wire ∈ registers.remainderRepairScratch) :
    wire ∉ indexedStepPayload registers := by
  intro hpayload
  exact (hlayout.aux_not_payload
    (hlayout.remainderRepairScratch_mem_aux hrepair) hpayload) rfl

private theorem IndexedStepLayout.control_ne_shiftEpoch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.control ≠ registers.shiftEpoch := by
  have hnodup :
      (registers.control :: registers.shiftEpoch ::
        registers.sourceScratch).Nodup := by
    simpa only [List.cons_append, List.nil_append] using
      hlayout.sourceAux_view_nodup
  intro equality
  exact (List.nodup_cons.mp hnodup).1 (by simp [equality])

private theorem IndexedStepLayout.shiftEpoch_not_sharedScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.shiftEpoch ∉ registers.sharedScratch := by
  have hfull :
      (registers.control :: registers.shiftEpoch ::
        (registers.sourceScratch ++ registers.remainderRepairScratch)).Nodup := by
    simpa only [List.cons_append, List.nil_append] using hlayout.aux_view_nodup
  have hshiftNotTail := (List.nodup_cons.mp (List.nodup_cons.mp hfull).2).1
  simp only [IndexedStepRegisters.sharedScratch, List.mem_cons, List.mem_append,
    not_or]
  exact ⟨hlayout.control_ne_shiftEpoch.symm, by
    simpa only [List.mem_append, not_or] using hshiftNotTail⟩

private theorem IndexedStepLayout.control_not_sourceScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.control ∉ registers.sourceScratch := by
  have hcross := (List.nodup_append.mp hlayout.aux_view_nodup).2.2
  intro hmem
  exact hcross registers.control (by simp) registers.control
    (by simp [hmem]) rfl

private theorem IndexedStepLayout.shiftEpoch_not_sourceScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.shiftEpoch ∉ registers.sourceScratch := by
  have hcross := (List.nodup_append.mp hlayout.aux_view_nodup).2.2
  intro hmem
  exact hcross registers.shiftEpoch (by simp) registers.shiftEpoch
    (by simp [hmem]) rfl

private theorem IndexedStepLayout.sourceScratch_nodup
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.sourceScratch.Nodup := by
  have htail :
      (registers.sourceScratch ++ registers.remainderRepairScratch).Nodup :=
    (List.nodup_append.mp hlayout.aux_view_nodup).2.1
  exact (List.nodup_append.mp htail).1

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
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow) :
    ∀ wire ∈ (registers.remainder window).scratch, wire ∈ registers.aux := by
  intro wire hwire
  have hsource := List.mem_of_mem_take hwire
  simp only [List.mem_cons, List.mem_append] at hsource
  rcases hsource with hshift | hsource | hrepair
  · rw [hshift]
    exact hlayout.shiftEpoch_mem_aux
  · exact hlayout.sourceScratch_mem_aux hsource
  · exact hlayout.remainderRepairScratch_mem_aux hrepair

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
    [registers.sourceScratch.getD registers.lengthS.length 0,
      registers.sourceScratch.getD 0 0] ++
      (registers.sourceScratch.drop 1).take (registers.lengthS.length - 1) ++
        (registers.sourceScratch.drop (registers.lengthS.length + 1)).take 3 at hwire
  rcases List.mem_append.mp hwire with hprefix | hreservedWire
  · rcases List.mem_append.mp hprefix with hflag | hcarry
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hflag
      rcases hflag with hzero | hboth
      · rw [hzero]
        exact indexedStep_getD_mem registers.sourceScratch
          registers.lengthS.length 0 (by omega)
      · rw [hboth]
        exact indexedStep_getD_mem registers.sourceScratch 0 0 (by omega)
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
      simp only [IndexedStepRegisters.sharedScratch, List.mem_cons,
        List.mem_append] at hshared
      rcases hshared with rfl | hsource | hrepair
      · exact hlayout.control_mem_aux
      · exact hlayout.sourceScratch_mem_aux hsource
      · exact hlayout.remainderRepairScratch_mem_aux hrepair
    have hpayload : wire ∈ indexedStepPayload registers := by
      change wire ∈
        [registers.phase1, registers.phase2,
          registers.sourceScratch.getD 0 0] ++
          registers.work2 ++ registers.lengthS ++
            (registers.sourceScratch.drop 1).take
              (registers.lengthS.length - 1) at hsupport
      change wire ∉
        [registers.sourceScratch.getD registers.lengthS.length 0,
          registers.sourceScratch.getD 0 0] ++
          (registers.sourceScratch.drop 1).take
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
      simp only [IndexedStepRegisters.sharedScratch, List.mem_cons,
        List.mem_append] at hshared
      rcases hshared with rfl | hsource | hrepair
      · exact hlayout.control_mem_aux
      · exact hlayout.sourceScratch_mem_aux hsource
      · exact hlayout.remainderRepairScratch_mem_aux hrepair
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
      exact (hlayout.shiftEpoch_not_sharedScratch hshared).elim

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

private theorem IndexedStepLayout.remainderRepairScratch_not_coefficient
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow)
    {wire : Wire} (hrepair : wire ∈ registers.remainderRepairScratch) :
    wire ∉ (registers.coefficient window).allWires := by
  intro hused
  have hnotPayload := hlayout.remainderRepairScratch_not_payload hrepair
  have hnotSource := hlayout.remainderRepairScratch_not_sourceScratch hrepair
  change wire ∈
    [registers.control, registers.sign] ++
      (IndexedStepRegisters.windowSlice registers.work1 window ++
        (IndexedStepRegisters.windowSlice registers.work2 window ++
          (registers.lengthT ++ (registers.coefficient window).scratch))) at hused
  rcases List.mem_append.mp hused with hfixed | hrest
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfixed
    rcases hfixed with hcontrol | hsign
    · exact (hlayout.remainderRepairScratch_ne_control hrepair hcontrol).elim
    · exact hnotPayload (by simp [indexedStepPayload, hsign])
  · rcases List.mem_append.mp hrest with hwork1 | hrest
    · exact hnotPayload (by simp [indexedStepPayload,
        windowSlice_mem registers.work1 window hwork1])
    · rcases List.mem_append.mp hrest with hwork2 | hrest
      · exact hnotPayload (by simp [indexedStepPayload,
          windowSlice_mem registers.work2 window hwork2])
      · rcases List.mem_append.mp hrest with hlengthT | hscratch
        · exact hnotPayload (by simp [indexedStepPayload, hlengthT])
        · exact hnotSource (List.mem_of_mem_drop
            (hlayout.coefficient_scratch_sub_block window wire hscratch))

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

private theorem IndexedStepLayout.remainderRepairScratch_not_preShift
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hrepair : wire ∈ registers.remainderRepairScratch) :
    wire ∉ registers.preShift.preUsedWires := by
  intro hused
  rcases hlayout.preShift_used_payload_or_scratch hused with hpayload | hscratch
  · apply hlayout.remainderRepairScratch_not_payload hrepair
    simp only [indexedStepShiftPayload, indexedStepPayload,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hpayload ⊢
    aesop
  · apply hlayout.remainderRepairScratch_not_sourceScratch hrepair
    exact List.mem_of_mem_drop
      (hlayout.preShift_scratch_sub_block wire hscratch)

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

theorem terminalPaddingForwardState_preserves
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

private theorem tBoundaryRestoreState_matchXorState_commute
    (registers : IndexedStepRegisters) (n : Nat)
    (controls : List Wire) (value : Nat) (target : Wire)
    (state : BasisState)
    (htargetPhase : target ≠ registers.phase2)
    (htargetT : target ∉ registers.lengthT)
    (htargetRP : target ∉ registers.lengthRPrime)
    (htargetS : target ∉ registers.tBoundary.lengthSLow)
    (hcontrolsT : ∀ control ∈ controls, control ∉ registers.lengthT)
    (hcontrolsRP : ∀ control ∈ controls,
      control ∉ registers.lengthRPrime) :
    tBoundaryRestoreState registers n
        (matchXorState controls value target state) =
      matchXorState controls value target
        (tBoundaryRestoreState registers n state) := by
  have hphase :
      matchXorState controls value target state registers.phase2 =
        state registers.phase2 :=
    matchXorState_preserves controls value target state
      (Ne.symm htargetPhase)
  have ht : wireValues registers.lengthT
      (matchXorState controls value target state) =
      wireValues registers.lengthT state := by
    apply wireValues_congr_indexedStep
    intro wire hwire
    exact matchXorState_preserves controls value target state (by
      intro equality
      subst wire
      exact htargetT hwire)
  have hrp : wireValues registers.lengthRPrime
      (matchXorState controls value target state) =
      wireValues registers.lengthRPrime state := by
    apply wireValues_congr_indexedStep
    intro wire hwire
    exact matchXorState_preserves controls value target state (by
      intro equality
      subst wire
      exact htargetRP hwire)
  have hs : wireValues registers.tBoundary.lengthSLow
      (matchXorState controls value target state) =
      wireValues registers.tBoundary.lengthSLow state := by
    apply wireValues_congr_indexedStep
    intro wire hwire
    exact matchXorState_preserves controls value target state (by
      intro equality
      subst wire
      exact htargetS hwire)
  unfold tBoundaryRestoreState
  rw [hphase, ht, hrp, hs]
  apply indexedWriteWireValues_matchXorState_commute
  · simp [htargetT, htargetRP]
  · intro control hcontrol
    simp [hcontrolsT control hcontrol, hcontrolsRP control hcontrol]

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
    exact hlayout.blockScratch_mem_sharedScratch hwire
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
    exact hlayout.blockScratch_mem_sharedScratch hwire
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
  have hrepairFinal : ∀ wire ∈ registers.remainderRepairScratch,
      blockAForwardState registers state wire = false := by
    intro wire hrepair
    have hnotPayload := hlayout.remainderRepairScratch_not_payload hrepair
    have hnotSource := hlayout.remainderRepairScratch_not_sourceScratch hrepair
    have hterminal : wire ≠ registers.terminal := by
      intro equality
      apply hnotSource
      rw [equality, ← hlayout.scratch_view]
      simp
    have hphase1 : wire ≠ registers.phase1 := by
      intro equality
      apply hnotPayload
      simp [indexedStepPayload, equality]
    have hshift : wire ≠ registers.shiftEpoch :=
      hlayout.remainderRepairScratch_ne_shiftEpoch hrepair
    have hquotient : wire ≠ registers.quotientLow := by
      intro equality
      apply hnotPayload
      simp [indexedStepPayload, equality, hlayout.quotientLow_mem_lengthQ]
    have hwork2 : wire ∉ registers.work2 := by
      intro hmem
      exact hnotPayload (by simp [indexedStepPayload, hmem])
    have hlengthS : wire ∉ registers.lengthS := by
      intro hmem
      exact hnotPayload (by simp [indexedStepPayload, hmem])
    calc
      blockAForwardState registers state wire = spilled wire := by
        change matchXorState (terminalConditionWires registers)
          (terminalConditionValue registers) registers.terminal spilled wire =
            spilled wire
        exact matchXorState_preserves _ _ _ _ hterminal
      _ = restoredPhase wire := terminalEpochSpillState_preserves _ _ _ _
        hshift hquotient hterminalQuotient
      _ = shifted wire := xorWireState_preserves _ _ _ hphase1
      _ = disabled wire := by
        rw [← hpreRun]
        exact preShiftUnitary_preservesOutside registers.preShift disabled
          (hlayout.remainderRepairScratch_not_preShift hrepair)
      _ = padded wire := xorWireState_preserves _ _ _ hphase1
      _ = marked wire := terminalPaddingForwardState_preserves
        registers.terminalPadding marked hwork2 hlengthS hshift
      _ = state wire := matchXorState_preserves _ _ _ _ hterminal
      _ = false := hready wire
        (hlayout.remainderRepairScratch_mem_sharedScratch hrepair)
  intro wire hwire
  rw [← hlayout.aux_view] at hwire
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hwire
  by_cases hcontrol : wire = registers.control
  · rw [hcontrol, hcorrect.1]
    exact hfinalControl
  by_cases hepoch : wire = registers.shiftEpoch
  · rw [hepoch, hcorrect.1]
    exact hfinalEpoch
  have htail :
      wire ∈ registers.sourceScratch ++ registers.remainderRepairScratch := by
    simpa [hcontrol, hepoch] using hwire
  rcases List.mem_append.mp htail with hsource | hrepair
  · rw [← hlayout.scratch_view] at hsource
    simp only [List.mem_cons] at hsource
    by_cases hterminal : wire = registers.terminal
    · rw [hterminal, hcorrect.1]
      exact hfinalTerminal
    · have hblockWire : wire ∈ registers.blockScratch := by
        simpa [hterminal] using hsource
      exact hcorrect.2 wire hblockWire
  · rw [hcorrect.1]
    exact hrepairFinal wire hrepair

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
  have hrepairFinal : ∀ wire ∈ registers.remainderRepairScratch,
      blockCForwardState registers state wire = false := by
    intro wire hrepair
    have hnotPayload := hlayout.remainderRepairScratch_not_payload hrepair
    have hnotSource := hlayout.remainderRepairScratch_not_sourceScratch hrepair
    have hterminal : wire ≠ registers.terminal := by
      intro equality
      apply hnotSource
      rw [equality, ← hlayout.scratch_view]
      simp
    have hshift := hlayout.remainderRepairScratch_ne_shiftEpoch hrepair
    have hquotient : wire ≠ registers.quotientLow := by
      intro equality
      apply hnotPayload
      simp [indexedStepPayload, equality, hlayout.quotientLow_mem_lengthQ]
    calc
      blockCForwardState registers state wire = restored wire := by
        change matchXorState (terminalConditionWires registers)
          (terminalConditionValue registers) registers.terminal restored wire =
            restored wire
        exact matchXorState_preserves _ _ _ _ hterminal
      _ = marked wire := terminalEpochRestoreState_preserves _ _ _ _
        hshift hquotient
      _ = state wire := matchXorState_preserves _ _ _ _ hterminal
      _ = false := hready wire
        (hlayout.remainderRepairScratch_mem_aux hrepair)
  constructor
  · exact hrun
  · rw [hrun]
    intro wire hwire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons,
      List.mem_append] at hwire
    rcases hwire with rfl | hsource | hrepair
    · exact hfinalControl
    · rw [← hlayout.scratch_view] at hsource
      simp only [List.mem_cons] at hsource
      rcases hsource with rfl | hblockWire
      · exact hfinalTerminal
      · exact hfinalBlock wire hblockWire
    · exact hrepairFinal wire hrepair

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

private theorem blockCForward_epochEncoded
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepBorrowedReady registers state) :
    IndexedStepEpochEncoded registers (blockCForwardState registers state) := by
  have hdist := hlayout.terminalEpoch
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hdist
  have ht : state registers.terminal = false := hready _
    (hlayout.sourceScratch_mem_aux (by rw [← hlayout.scratch_view]; simp))
  have he : state registers.shiftEpoch = false := hready _ hlayout.shiftEpoch_mem_aux
  have hcondition : registerMatches (terminalConditionWires registers)
      (terminalConditionValue registers) (blockCForwardState registers state) =
      registerMatches (terminalConditionWires registers) (terminalConditionValue registers) state := by
    apply registerMatches_congr
    intro wire hw
    have hnt : wire ≠ registers.terminal := by
      intro h; subst wire; exact hlayout.terminal_not_condition hw
    have hne : wire ≠ registers.shiftEpoch := by
      intro h; subst wire; exact hlayout.shiftEpoch_not_condition hw
    have hnq : wire ≠ registers.quotientLow := by
      intro h; subst wire; exact hlayout.quotientLow_not_condition hw
    simp only [blockCForwardState, matchXorState_preserves _ _ _ _ hnt,
      terminalEpochRestoreState_preserves _ _ _ _ hne hnq]
  unfold IndexedStepEpochEncoded
  rw [hcondition]
  cases hm : registerMatches (terminalConditionWires registers)
      (terminalConditionValue registers) state <;>
    simp [blockCForwardState, matchXorState, terminalEpochRestoreState, controlledSwapState,
      swapWireState, xorWireState, upd, ht, he, hm, hdist.1.1, hdist.1.2,
      hdist.2.1, Ne.symm hdist.1.1, Ne.symm hdist.1.2]

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
  have hrepairFinal : ∀ wire ∈ registers.remainderRepairScratch,
      blockD1ForwardState registers state wire = false := by
    intro wire hrepair
    have hcontrol := hlayout.remainderRepairScratch_ne_control hrepair
    have hnotPayload := hlayout.remainderRepairScratch_not_payload hrepair
    have hnotLengthQ : wire ∉ registers.lengthQ := by
      intro hmem
      exact hnotPayload (by simp [indexedStepPayload, hmem])
    calc
      blockD1ForwardState registers state wire = changed wire := by
        change matchXorState [registers.phase1, registers.phase2] 2
          registers.control changed wire = changed wire
        exact matchXorState_preserves _ _ _ _ hcontrol
      _ = enabled wire := indexedIncrementWordState_preservesOutside _ _ _
        hnotLengthQ
      _ = state wire := matchXorState_preserves _ _ _ _ hcontrol
      _ = false := hready wire
        (hlayout.remainderRepairScratch_mem_sharedScratch hrepair)
  constructor
  · exact hrun
  · rw [hrun]
    intro wire hwire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons,
      List.mem_append] at hwire
    rcases hwire with rfl | hsourceWire | hrepair
    · exact hfinalControl
    · exact hcleared.2 wire hsourceWire
    · exact hrepairFinal wire hrepair

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
  have hrepairFinal : ∀ wire ∈ registers.remainderRepairScratch,
      blockD2ForwardState registers window state wire = false := by
    intro wire hrepair
    have hcontrol := hlayout.remainderRepairScratch_ne_control hrepair
    have hnotPayload := hlayout.remainderRepairScratch_not_payload hrepair
    have hsign : wire ≠ registers.sign := by
      intro equality
      exact hnotPayload (by simp [indexedStepPayload, equality])
    have hwork : wire ∉ (registers.quotient window).work1 := by
      intro hwindowWire
      apply hnotPayload
      simp [indexedStepPayload,
        windowSlice_mem registers.work1 window hwindowWire]
    calc
      blockD2ForwardState registers window state wire = disabled1 wire := by rfl
      _ = disabled2 wire := xorWireState_preserves _ _ _ hcontrol
      _ = changed wire := xorWireState_preserves _ _ _ hcontrol
      _ = enabled2 wire := indexedQuotientSwapState_preserves
        (registers.quotient window) enabled2 hqLayout hsign hwork
      _ = enabled1 wire := xorWireState_preserves _ _ _ hcontrol
      _ = state wire := xorWireState_preserves _ _ _ hcontrol
      _ = false := hready wire
        (hlayout.remainderRepairScratch_mem_sharedScratch hrepair)
  constructor
  · exact hrun
  · rw [hrun]
    intro wire hwire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons,
      List.mem_append] at hwire
    rcases hwire with rfl | hsourceWire | hrepair
    · exact hfinalControl
    · exact hfinalSource wire hsourceWire
    · exact hrepairFinal wire hrepair

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
  have hrepairFinal : ∀ wire ∈ registers.remainderRepairScratch,
      blockD3ForwardState registers state wire = false := by
    intro wire hrepair
    have hcontrol := hlayout.remainderRepairScratch_ne_control hrepair
    have hnotPayload := hlayout.remainderRepairScratch_not_payload hrepair
    have hnotLengthQ : wire ∉ registers.lengthQ := by
      intro hmem
      exact hnotPayload (by simp [indexedStepPayload, hmem])
    calc
      blockD3ForwardState registers state wire = changed wire := by
        change matchXorState [registers.phase1, registers.phase2] 1
          registers.control changed wire = changed wire
        exact matchXorState_preserves _ _ _ _ hcontrol
      _ = enabled wire := indexedDecrementWordState_preservesOutside _ _ _
        hnotLengthQ
      _ = state wire := matchXorState_preserves _ _ _ _ hcontrol
      _ = false := hready wire
        (hlayout.remainderRepairScratch_mem_sharedScratch hrepair)
  constructor
  · exact hrun
  · rw [hrun]
    intro wire hwire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons,
      List.mem_append] at hwire
    rcases hwire with rfl | hsourceWire | hrepair
    · exact hfinalControl
    · exact hcleared.2 wire hsourceWire
    · exact hrepairFinal wire hrepair

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
                simp [blockDForward, blockD1Forward, blockD2Forward, blockD3Forward, Classical.run_append]
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
    exact hready wire (hlayout.blockScratch_mem_sharedScratch hwire)
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
    simp only [blockEForward, blockEFinishForward, blockESubtractForward, blockEPrepareForward, coefficientSubtractControl, Classical.run_append]
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
  have hrepairFinal : ∀ wire ∈ registers.remainderRepairScratch,
      restored wire = false := by
    intro wire hrepair
    have hnotPayload := hlayout.remainderRepairScratch_not_payload hrepair
    have hnotSource := hlayout.remainderRepairScratch_not_sourceScratch hrepair
    have hcontrol := hlayout.remainderRepairScratch_ne_control hrepair
    have hterminal : wire ≠ registers.terminal := by
      intro equality
      apply hnotSource
      rw [equality, ← hlayout.scratch_view]
      simp
    have hsign : wire ≠ registers.sign := by
      intro equality
      exact hnotPayload (by simp [indexedStepPayload, equality])
    have hlengthT : wire ∉ registers.lengthT := by
      intro hmem
      exact hnotPayload (by simp [indexedStepPayload, hmem])
    have hlengthRPrime : wire ∉ registers.lengthRPrime := by
      intro hmem
      exact hnotPayload (by simp [indexedStepPayload, hmem])
    have hcoefficient :=
      hlayout.remainderRepairScratch_not_coefficient window hrepair
    calc
      restored wire = addCleared wire :=
        tBoundaryRestoreState_preservesOutside registers n addCleared
          hlengthT hlengthRPrime
      _ = added wire := matchXorState_preserves _ _ _ _ hcontrol
      _ = addEnabled wire := by
        calc
          added wire = run
              (coefficientPrefixUnitary (registers.coefficient window)
                window.start window.stop .add true .work2) addEnabled wire := by
            simpa only [added] using congrFun hadded.1.symm wire
          _ = addEnabled wire := coefficientPrefixUnitary_preservesOutside
            (registers.coefficient window) .add true .work2 addEnabled
              hcoefficientLayout hcoefficient
      _ = signChanged wire := matchXorState_preserves _ _ _ _ hcontrol
      _ = temporaryCleared2 wire := xorWireState_preserves _ _ _ hsign
      _ = subCleared wire := matchXorState_preserves _ _ _ _ hterminal
      _ = temporary2 wire := matchXorState_preserves _ _ _ _ hcontrol
      _ = subtracted wire := matchXorState_preserves _ _ _ _ hterminal
      _ = prepared wire := by
        calc
          subtracted wire = run
              (coefficientPrefixUnitary (registers.coefficient window)
                window.start window.stop .sub false .work2) prepared wire := by
            simpa only [subtracted] using congrFun hsubtracted.1.symm wire
          _ = prepared wire := coefficientPrefixUnitary_preservesOutside
            (registers.coefficient window) .sub false .work2 prepared
              hcoefficientLayout hcoefficient
      _ = temporaryCleared1 wire :=
        tBoundaryPrepareState_preservesOutside registers n temporaryCleared1
          hlengthT hlengthRPrime
      _ = subEnabled wire := matchXorState_preserves _ _ _ _ hterminal
      _ = temporary1 wire := matchXorState_preserves _ _ _ _ hcontrol
      _ = state wire := matchXorState_preserves _ _ _ _ hterminal
      _ = false := hready wire
        (hlayout.remainderRepairScratch_mem_sharedScratch hrepair)
  have hrestoredBlock : Clean registers.blockScratch restored := by
    simpa only [restored, hrestored.1] using hrestored.2
  constructor
  · exact hrun.trans hstate
  · rw [hrun]
    intro wire hwire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons,
      List.mem_append] at hwire
    rcases hwire with rfl | hsource | hrepair
    · exact hrestoredControl
    · rw [← hlayout.scratch_view] at hsource
      simp only [List.mem_cons] at hsource
      rcases hsource with rfl | hblockWire
      · exact hrestoredTerminal
      · exact hrestoredBlock wire hblockWire
    · exact hrepairFinal wire hrepair

private theorem blockFForward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state) :
    run (blockFForward registers) state = blockFForwardState registers state ∧
      IndexedStepReady registers (run (blockFForward registers) state) := by
  have hlocalReady : ShiftReady registers.postShift state := by
    intro wire hwire
    apply hready wire
    exact hlayout.sourceScratch_mem_sharedScratch
      (hlayout.postShift_scratch_sub_source wire hwire)
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
    exact hlayout.sourceScratch_mem_sharedScratch
      (hlayout.phaseUpdate_scratch_sub_source wire hwire)
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
      exact hlayout.sourceScratch_mem_sharedScratch (List.mem_of_mem_drop hwire)
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
          hlayout.sourceAux_view_nodup
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
    have hrepairAfter : Clean registers.remainderRepairScratch after := by
      intro wire hrepair
      have hnotSource := hlayout.remainderRepairScratch_not_sourceScratch hrepair
      have hwireQ : wire ≠ q := by
        intro equality
        apply hnotSource
        exact equality ▸ hqMem
      have hwireS : wire ≠ s := by
        intro equality
        apply hnotSource
        exact equality ▸ hsMem
      have hwireEpoch : wire ≠ epoch := by
        simpa only [epoch] using
          hlayout.remainderRepairScratch_ne_shiftEpoch hrepair
      have hwireControl : wire ≠ control := by
        simpa only [control] using
          hlayout.remainderRepairScratch_ne_control hrepair
      have hwireIter : wire ≠ iter := by
        intro equality
        apply hlayout.remainderRepairScratch_not_payload hrepair
        simpa only [equality] using hiterPayload
      have hpreserved := hfull wire hwireQ hwireS hwireEpoch hwireControl
        hwireIter (hlayout.aux_not_endIterationMutable
          (hlayout.remainderRepairScratch_mem_aux hrepair))
      calc
        after wire = restoredEpochAgain wire :=
          andListXorState_preserves registers.lengthQ q restoredEpochAgain hwireQ
        _ = state wire := hpreserved
        _ = false := hready wire
          (hlayout.remainderRepairScratch_mem_sharedScratch hrepair)
    have hafterReady : IndexedStepReady registers after := by
      intro wire hwire
      simp only [IndexedStepRegisters.sharedScratch, List.mem_cons,
        List.mem_append] at hwire
      rcases hwire with rfl | hsource | hrepair
      · exact hcontrolAfter
      · rw [← hview] at hsource
        simp only [List.mem_cons] at hsource
        rcases hsource with rfl | rfl | htail
        · exact hqAfter
        · exact hsAfter
        · exact htailAfter wire htail
      · exact hrepairAfter wire hrepair
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
  simp only [blockDForward, blockD1Forward, blockD2Forward, blockD3Forward, circuitWellFormed_append, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  simp only [blockEForward, blockEFinishForward, blockESubtractForward, blockEPrepareForward, coefficientSubtractControl, circuitWellFormed_append]
  repeat' apply And.intro
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
    exact hready wire (hlayout.blockScratch_mem_sharedScratch hwire)
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
  simpa [blockEAdaptive, blockEForward, blockEFinishForward, blockESubtractForward, blockEPrepareForward, coefficientSubtractControl, firstCircuit, tailCircuit,
    blockEPrefix, blockEMiddle, blockESuffix, subCircuit,
    List.append_assoc] using hall

/-! ## Literal forward/reverse cancellation -/

private theorem IndexedStepLayout.coefficientFixed_not_words
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ∀ wire ∈ [registers.phase1, registers.phase2, registers.sign,
      registers.control, registers.terminal],
      wire ∉ registers.lengthT ∧ wire ∉ registers.lengthRPrime := by
  have hterminalSource : registers.terminal ∈ registers.sourceScratch := by
    rw [← hlayout.scratch_view]
    simp
  have hterminalAux := hlayout.sourceScratch_mem_aux hterminalSource
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

private def coefficientSubWrapper
    (registers : IndexedStepRegisters) : Circuit :=
  circuit! {
    coefficientTemporaryControl registers;
    coefficientSubControl registers;
    coefficientTemporaryControl registers
  }

private def coefficientSubWrapperState
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  matchXorState [registers.phase2, registers.sign] 2 registers.terminal
    (matchXorState [registers.phase1, registers.terminal] 1 registers.control
      (matchXorState [registers.phase2, registers.sign] 2 registers.terminal state))

private theorem run_coefficientSubWrapper_state
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hclean : Clean registers.blockScratch state) :
    run (coefficientSubWrapper registers) state =
        coefficientSubWrapperState registers state ∧
      Clean registers.blockScratch
        (run (coefficientSubWrapper registers) state) := by
  let temporary := matchXorState [registers.phase2, registers.sign] 2
    registers.terminal state
  have htemporary := run_computeControl_state
    [registers.phase2, registers.sign] 2 registers.terminal
      registers.blockScratch state hlayout.coefficientTemporary hclean
  let enabled := matchXorState [registers.phase1, registers.terminal] 1
    registers.control temporary
  have henabled := run_computeControl_state
    [registers.phase1, registers.terminal] 1 registers.control
      registers.blockScratch temporary hlayout.coefficientSub (by
        simpa only [temporary] using htemporary.2)
  let cleared := matchXorState [registers.phase2, registers.sign] 2
    registers.terminal enabled
  have hcleared := run_computeControl_state
    [registers.phase2, registers.sign] 2 registers.terminal
      registers.blockScratch enabled hlayout.coefficientTemporary (by
        simpa only [enabled] using henabled.2)
  have hrun : run (coefficientSubWrapper registers) state = cleared := by
    simp only [coefficientSubWrapper, Classical.run_append]
    rw [show run (coefficientTemporaryControl registers) state = temporary by
        simpa [coefficientTemporaryControl, temporary] using htemporary.1,
      show run (coefficientSubControl registers) temporary = enabled by
        simpa [coefficientSubControl, enabled] using henabled.1,
      show run (coefficientTemporaryControl registers) enabled = cleared by
        simpa [coefficientTemporaryControl, cleared] using hcleared.1]
  constructor
  · simpa only [coefficientSubWrapperState, temporary, enabled, cleared] using hrun
  · rw [hrun]
    simpa only [cleared] using hcleared.2

private theorem coefficientSubWrapper_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (coefficientSubWrapper registers) := by
  simp only [coefficientSubWrapper, circuitWellFormed_append]
  exact ⟨⟨coefficientTemporaryControl_wellFormed registers n T hlayout,
    coefficientSubControl_wellFormed registers n T hlayout⟩,
    coefficientTemporaryControl_wellFormed registers n T hlayout⟩

private theorem coefficientSubWrapper_selfAdjoint
    (registers : IndexedStepRegisters) :
    (coefficientSubWrapper registers).adjoint =
      coefficientSubWrapper registers := by
  simp [coefficientSubWrapper, circuit_adjoint_append,
    coefficientTemporaryControl, coefficientSubControl,
    computeControl_selfAdjoint]

private theorem tBoundaryRestoreState_coefficientSubWrapperState_commute
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T) :
    tBoundaryRestoreState registers n
        (coefficientSubWrapperState registers state) =
      coefficientSubWrapperState registers
        (tBoundaryRestoreState registers n state) := by
  have hfixed := hlayout.coefficientFixed_not_words
  have hterminalT := (hfixed registers.terminal (by simp)).1
  have hterminalRP := (hfixed registers.terminal (by simp)).2
  have hcontrolT := (hfixed registers.control (by simp)).1
  have hcontrolRP := (hfixed registers.control (by simp)).2
  have htemporaryControlsT : ∀ wire ∈ [registers.phase2, registers.sign],
      wire ∉ registers.lengthT := by
    intro wire hwire
    exact (hfixed wire (by simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hwire ⊢; aesop)).1
  have htemporaryControlsRP : ∀ wire ∈ [registers.phase2, registers.sign],
      wire ∉ registers.lengthRPrime := by
    intro wire hwire
    exact (hfixed wire (by simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hwire ⊢; aesop)).2
  have hsubControlsT : ∀ wire ∈ [registers.phase1, registers.terminal],
      wire ∉ registers.lengthT := by
    intro wire hwire
    exact (hfixed wire (by simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hwire ⊢; aesop)).1
  have hsubControlsRP : ∀ wire ∈ [registers.phase1, registers.terminal],
      wire ∉ registers.lengthRPrime := by
    intro wire hwire
    exact (hfixed wire (by simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hwire ⊢; aesop)).2
  have hterminalPhase : registers.terminal ≠ registers.phase2 := by
    have hterminalSource : registers.terminal ∈ registers.sourceScratch := by
      rw [← hlayout.scratch_view]
      simp
    exact hlayout.aux_not_payload
      (hlayout.sourceScratch_mem_aux hterminalSource)
      (by simp [indexedStepPayload])
  have hcontrolPhase : registers.control ≠ registers.phase2 :=
    hlayout.aux_not_payload hlayout.control_mem_aux
      (by simp [indexedStepPayload])
  have hterminalS : registers.terminal ∉ registers.tBoundary.lengthSLow := by
    intro hmem
    exact hlayout.terminal_not_lengthS (List.mem_of_mem_take hmem)
  have hcontrolS : registers.control ∉ registers.tBoundary.lengthSLow := by
    intro hmem
    exact hlayout.control_not_lengthS (List.mem_of_mem_take hmem)
  have htemporary (current : BasisState) :=
    tBoundaryRestoreState_matchXorState_commute registers n
      ([registers.phase2, registers.sign]) 2 registers.terminal current
      hterminalPhase hterminalT hterminalRP hterminalS
      htemporaryControlsT htemporaryControlsRP
  have hsub (current : BasisState) :=
    tBoundaryRestoreState_matchXorState_commute registers n
      ([registers.phase1, registers.terminal]) 1 registers.control current
      hcontrolPhase hcontrolT hcontrolRP hcontrolS
      hsubControlsT hsubControlsRP
  simp only [coefficientSubWrapperState]
  rw [htemporary, hsub, htemporary]

private theorem run_tBoundaryRestore_after_coefficientSubWrapper
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hclean : Clean registers.blockScratch state) :
    run (restoreLatestPaperTBoundary registers.tBoundary n)
        (run (coefficientSubWrapper registers) state) =
      run (coefficientSubWrapper registers)
        (run (restoreLatestPaperTBoundary registers.tBoundary n) state) := by
  have hwrapper := run_coefficientSubWrapper_state registers n T state
    hlayout hclean
  have hleft := run_tBoundaryRestoreState registers n T
    (run (coefficientSubWrapper registers) state) hlayout hwrapper.2
  have hright := run_tBoundaryRestoreState registers n T state hlayout hclean
  have hwrapperRight := run_coefficientSubWrapper_state registers n T
    (run (restoreLatestPaperTBoundary registers.tBoundary n) state)
    hlayout hright.2
  calc
    run (restoreLatestPaperTBoundary registers.tBoundary n)
        (run (coefficientSubWrapper registers) state) =
        tBoundaryRestoreState registers n
          (run (coefficientSubWrapper registers) state) := hleft.1
    _ = tBoundaryRestoreState registers n
          (coefficientSubWrapperState registers state) :=
      congrArg (tBoundaryRestoreState registers n) hwrapper.1
    _ = coefficientSubWrapperState registers
          (tBoundaryRestoreState registers n state) :=
      tBoundaryRestoreState_coefficientSubWrapperState_commute
        registers n T state hlayout
    _ = coefficientSubWrapperState registers
          (run (restoreLatestPaperTBoundary registers.tBoundary n) state) :=
      congrArg (coefficientSubWrapperState registers) hright.1.symm
    _ = run (coefficientSubWrapper registers)
          (run (restoreLatestPaperTBoundary registers.tBoundary n) state) :=
      hwrapperRight.1.symm

private theorem run_cx_twice
    (control target : Wire) (state : BasisState) (hne : control ≠ target) :
    run ([.CX control target] : Circuit)
        (run ([.CX control target] : Circuit) state) = state := by
  simpa [Circuit.adjoint] using
    (run_adjoint_run_classical ([.CX control target] : Circuit)
      (by simp [CircuitWellFormed, Gate.WellFormed, hne]) state)

private theorem run_selfAdjoint_twice
    (circuit : Circuit) (state : BasisState)
    (hself : circuit.adjoint = circuit)
    (hwellFormed : CircuitWellFormed circuit) :
    run circuit (run circuit state) = state := by
  simpa only [hself] using
    run_adjoint_run_classical circuit hwellFormed state

set_option maxHeartbeats 1000000 in
private theorem blockEInverse_after_forward
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient)
    (hready : IndexedStepReady registers state) :
    run (blockEInverse registers n window)
        (run (blockEForward registers n window) state) = state := by
  subst window
  let wrapper := coefficientSubWrapper registers
  let prepareCircuit := prepareLatestPaperTBoundary registers.tBoundary n
  let restoreCircuit := restoreLatestPaperTBoundary registers.tBoundary n
  let subForward := coefficientPrefixUnitary
    (registers.coefficient (certifiedActiveWindows n T).coefficient)
    (certifiedActiveWindows n T).coefficient.start
    (certifiedActiveWindows n T).coefficient.stop .sub false .work2
  let subInverse := coefficientPrefixInverseUnitary
    (registers.coefficient (certifiedActiveWindows n T).coefficient)
    (certifiedActiveWindows n T).coefficient.start
    (certifiedActiveWindows n T).coefficient.stop .sub false .work2
  let signCircuit : Circuit := [.CX registers.phase1 registers.sign]
  let addControlCircuit := coefficientAddControl registers
  let addForward := coefficientPrefixUnitary
    (registers.coefficient (certifiedActiveWindows n T).coefficient)
    (certifiedActiveWindows n T).coefficient.start
    (certifiedActiveWindows n T).coefficient.stop .add true .work2
  let addInverse := coefficientPrefixInverseUnitary
    (registers.coefficient (certifiedActiveWindows n T).coefficient)
    (certifiedActiveWindows n T).coefficient.start
    (certifiedActiveWindows n T).coefficient.stop .add true .work2
  let afterW1 := run wrapper state
  let afterPrepare := run prepareCircuit afterW1
  let afterSub := run subForward afterPrepare
  let afterW2 := run wrapper afterSub
  let afterSign := run signCircuit afterW2
  let afterAddControl := run addControlCircuit afterSign
  let afterAdd := run addForward afterAddControl
  let beforeRestore := run addControlCircuit afterAdd
  have hblock : Clean registers.blockScratch state := by
    intro wire hwire
    exact hready wire (hlayout.blockScratch_mem_sharedScratch hwire)
  have hafterW1 := run_coefficientSubWrapper_state registers n T state
    hlayout hblock
  have hafterW1Clean : Clean registers.blockScratch afterW1 := by
    simpa only [afterW1, wrapper] using hafterW1.2
  have hafterPrepare := run_tBoundaryPrepareState registers n T afterW1
    hlayout hafterW1Clean
  have hafterPrepareClean : Clean registers.blockScratch afterPrepare := by
    simpa only [afterPrepare, prepareCircuit] using hafterPrepare.2
  have hafterSubClean : Clean registers.blockScratch afterSub := by
    simpa only [afterSub, subForward] using
      coefficientPrefix_preservesBlockScratch registers n T
        (certifiedActiveWindows n T).coefficient .sub false afterPrepare hlayout
        rfl hafterPrepareClean
  have hafterW2 := run_coefficientSubWrapper_state registers n T afterSub
    hlayout hafterSubClean
  have hafterW2Clean : Clean registers.blockScratch afterW2 := by
    simpa only [afterW2, wrapper] using hafterW2.2
  have hsignOutside : registers.sign ∉ registers.blockScratch := by
    intro hmem
    exact (hlayout.sign_ne_after (by
      simp [indexedStepAfterSign, hlayout.blockScratch_mem_aux hmem])) rfl
  have hafterSignClean : Clean registers.blockScratch afterSign := by
    simpa [afterSign, signCircuit, xorWireState, Classical.run,
      Classical.applyGate] using
      clean_upd_not_mem hafterW2Clean hsignOutside
  have hafterAddControl := run_computeControl_state [registers.phase1] 1
    registers.control registers.blockScratch afterSign hlayout.coefficientAdd
      hafterSignClean
  have hafterAddControlClean : Clean registers.blockScratch afterAddControl := by
    rw [show afterAddControl =
        matchXorState [registers.phase1] 1 registers.control afterSign by
      simpa only [afterAddControl, addControlCircuit, coefficientAddControl] using
        hafterAddControl.1]
    exact hafterAddControl.2
  have hafterAddClean : Clean registers.blockScratch afterAdd := by
    simpa only [afterAdd, addForward] using
      coefficientPrefix_preservesBlockScratch registers n T
        (certifiedActiveWindows n T).coefficient .add true afterAddControl hlayout
        rfl hafterAddControlClean
  have hbeforeRestore := run_computeControl_state [registers.phase1] 1
    registers.control registers.blockScratch afterAdd hlayout.coefficientAdd
      hafterAddClean
  have hbeforeRestoreClean : Clean registers.blockScratch beforeRestore := by
    rw [show beforeRestore =
        matchXorState [registers.phase1] 1 registers.control afterAdd by
      simpa only [beforeRestore, addControlCircuit, coefficientAddControl] using
        hbeforeRestore.1]
    exact hbeforeRestore.2
  have hbeforeRestoreReady : TBoundaryReady registers.tBoundary beforeRestore := by
    intro wire hwire
    exact hbeforeRestoreClean wire
      (hlayout.tBoundary_usedScratch_sub_block wire hwire)
  have hmiddleBoundary :
      run prepareCircuit (run restoreCircuit beforeRestore) = beforeRestore := by
    simpa only [prepareCircuit, restoreCircuit] using
      run_prepareLatestPaperTBoundary_after_restore registers.tBoundary n
        beforeRestore hlayout.tBoundary hbeforeRestoreReady
  have hshape :
      run (blockEInverse registers n (certifiedActiveWindows n T).coefficient)
          (run (blockEForward registers n
            (certifiedActiveWindows n T).coefficient) state) =
        run restoreCircuit
          (run wrapper
            (run subInverse
              (run wrapper
                (run signCircuit
                  (run addControlCircuit
                    (run addInverse
                      (run addControlCircuit
                        (run prepareCircuit
                          (run restoreCircuit beforeRestore))))))))) := by
    simp [blockEInverse, blockEForward, blockEFinishForward, blockESubtractForward, blockEPrepareForward, coefficientSubtractControl, wrapper, coefficientSubWrapper,
      prepareCircuit, restoreCircuit, subForward, subInverse, signCircuit,
      addControlCircuit, addForward, addInverse, beforeRestore, afterAdd,
      afterAddControl, afterSign, afterW2, afterSub, afterPrepare, afterW1,
      Classical.run_append]
  rw [hshape, hmiddleBoundary]
  rw [show run addControlCircuit beforeRestore = afterAdd by
    simpa only [beforeRestore, addControlCircuit, coefficientAddControl] using
      run_computeControl_twice [registers.phase1] 1 registers.control
        registers.blockScratch afterAdd hlayout.coefficientAdd]
  rw [show run addInverse afterAdd = afterAddControl by
    simpa only [addInverse, afterAdd, addForward] using
      run_coefficientPrefixInverseUnitary_after_forward
        (registers.coefficient (certifiedActiveWindows n T).coefficient)
        .add true .work2 afterAddControl hlayout.coefficient]
  rw [show run addControlCircuit afterAddControl = afterSign by
    simpa only [afterAddControl, addControlCircuit, coefficientAddControl] using
      run_computeControl_twice [registers.phase1] 1 registers.control
        registers.blockScratch afterSign hlayout.coefficientAdd]
  rw [show run signCircuit afterSign = afterW2 by
    simpa only [afterSign, signCircuit] using
      run_cx_twice registers.phase1 registers.sign afterW2 (by
        have hphysical := hlayout.coefficientSign
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
          or_false] at hphysical
        exact hphysical.1)]
  rw [show run wrapper afterW2 = afterSub by
    simpa only [afterW2, wrapper] using
      run_selfAdjoint_twice (coefficientSubWrapper registers) afterSub
        (coefficientSubWrapper_selfAdjoint registers)
        (coefficientSubWrapper_wellFormed registers n T hlayout)]
  rw [show run subInverse afterSub = afterPrepare by
    simpa only [subInverse, afterSub, subForward] using
      run_coefficientPrefixInverseUnitary_after_forward
        (registers.coefficient (certifiedActiveWindows n T).coefficient)
        .sub false .work2 afterPrepare hlayout.coefficient]
  rw [show run restoreCircuit (run wrapper afterPrepare) =
      run wrapper (run restoreCircuit afterPrepare) by
    simpa only [restoreCircuit, wrapper] using
      run_tBoundaryRestore_after_coefficientSubWrapper registers n T
        afterPrepare hlayout hafterPrepareClean]
  have hafterW1Ready : TBoundaryReady registers.tBoundary afterW1 := by
    intro wire hwire
    exact hafterW1Clean wire
      (hlayout.tBoundary_usedScratch_sub_block wire hwire)
  rw [show run restoreCircuit afterPrepare = afterW1 by
    simpa only [restoreCircuit, afterPrepare, prepareCircuit] using
      run_restoreLatestPaperTBoundary_after_prepare registers.tBoundary n
        afterW1 hlayout.tBoundary hafterW1Ready]
  simpa only [afterW1, wrapper] using
    run_selfAdjoint_twice (coefficientSubWrapper registers) state
      (coefficientSubWrapper_selfAdjoint registers)
      (coefficientSubWrapper_wellFormed registers n T hlayout)

private theorem run_run_adjoint_classical_indexedStep
    (circuit : Circuit) (state : BasisState)
    (hwellFormed : CircuitWellFormed circuit) :
    run circuit (run circuit.adjoint state) = state := by
  simpa using run_adjoint_run_classical circuit.adjoint
    ((circuitWellFormed_adjoint circuit).2 hwellFormed) state

private theorem mcxVChainTail_indexedStep_selfAdjoint
    (accumulator : Wire) (controls : List Wire) (target : Wire)
    (scratches : List Wire) :
    (mcxVChainTail accumulator controls target scratches).adjoint =
      mcxVChainTail accumulator controls target scratches := by
  induction controls generalizing accumulator scratches with
  | nil => simp [mcxVChainTail]
  | cons control controls ih =>
      cases controls with
      | nil => simp [mcxVChainTail, Circuit.adjoint]
      | cons nextControl controls =>
          cases scratches with
          | nil => simp [mcxVChainTail]
          | cons scratch scratches =>
              simp [mcxVChainTail, circuit_adjoint_append, ih]

private theorem mcxVChain_indexedStep_selfAdjoint
    (controls : List Wire) (target : Wire) (scratches : List Wire) :
    (mcxVChain controls target scratches).adjoint =
      mcxVChain controls target scratches := by
  cases controls with
  | nil => simp [mcxVChain, Circuit.adjoint]
  | cons first controls =>
      cases controls with
      | nil => simp [mcxVChain, Circuit.adjoint]
      | cons second controls =>
          simp [mcxVChain, mcxVChainTail_indexedStep_selfAdjoint]

private theorem indexedStep_decrementBits_incrementBits
    (carry : Bool) (bits : List Bool) :
    decrementBits carry (incrementBits carry bits) = bits := by
  induction bits generalizing carry with
  | nil => rfl
  | cons bit bits ih =>
      cases carry <;> cases bit <;>
        simp [incrementBits, decrementBits, ih]

private theorem indexedStep_incrementBits_decrementBits
    (carry : Bool) (bits : List Bool) :
    incrementBits carry (decrementBits carry bits) = bits := by
  induction bits generalizing carry with
  | nil => rfl
  | cons bit bits ih =>
      cases carry <;> cases bit <;>
        simp [incrementBits, decrementBits, ih]

private theorem indexedStep_basisState_eq_of_word
    (wires : List Wire) (left right : BasisState)
    (hvalues : wireValues wires left = wireValues wires right)
    (houtside : ∀ wire, wire ∉ wires → left wire = right wire) :
    left = right := by
  induction wires with
  | nil =>
      funext wire
      exact houtside wire (by simp)
  | cons head tail ih =>
      have hhead : left head = right head := by
        have h := congrArg List.head? hvalues
        simpa [wireValues] using h
      have htail : wireValues tail left = wireValues tail right := by
        have h := congrArg List.tail hvalues
        simpa [wireValues] using h
      apply ih htail
      intro wire hwire
      by_cases heq : wire = head
      · subst wire
        exact hhead
      · exact houtside wire (by simp [heq, hwire])

private theorem indexedStep_run_decrement_after_increment
    (control : Wire) (register carries : List Wire) (state : BasisState)
    (hlength : register.length = carries.length + 1)
    (hnd : (control :: register ++ carries).Nodup)
    (hclean : Clean carries state) :
    run (controlledDecrement control register carries)
        (run (controlledIncrement control register carries) state) = state := by
  let increased := run (controlledIncrement control register carries) state
  have hinc := controlledIncrement_correct control register carries state
    hlength hnd hclean
  have hcontrol := controlledIncrement_control control register carries state
    hlength hnd hclean
  have hcleanIncreased := controlledIncrement_clean control register carries state
    hlength hnd hclean
  have hdec := controlledDecrement_correct control register carries increased
    hlength hnd hcleanIncreased
  apply indexedStep_basisState_eq_of_word register _ state
  · rw [hdec.1]
    rw [show increased control = state control by exact hcontrol, hinc.1,
      indexedStep_decrementBits_incrementBits]
  · intro wire hwire
    rw [hdec.2 wire hwire]
    exact hinc.2 wire hwire

private theorem indexedStep_run_increment_after_decrement
    (control : Wire) (register carries : List Wire) (state : BasisState)
    (hlength : register.length = carries.length + 1)
    (hnd : (control :: register ++ carries).Nodup)
    (hclean : Clean carries state) :
    run (controlledIncrement control register carries)
        (run (controlledDecrement control register carries) state) = state := by
  let decreased := run (controlledDecrement control register carries) state
  have hdec := controlledDecrement_correct control register carries state
    hlength hnd hclean
  have hcontrol := controlledDecrement_control control register carries state
    hlength hnd hclean
  have hcleanDecreased := controlledDecrement_clean control register carries state
    hlength hnd hclean
  have hinc := controlledIncrement_correct control register carries decreased
    hlength hnd hcleanDecreased
  apply indexedStep_basisState_eq_of_word register _ state
  · rw [hinc.1]
    rw [show decreased control = state control by exact hcontrol, hdec.1,
      indexedStep_incrementBits_decrementBits]
  · intro wire hwire
    rw [hinc.2 wire hwire]
    exact hdec.2 wire hwire

private theorem remainderRestoreControl_selfAdjoint
    (registers : IndexedStepRegisters) :
    (remainderRestoreControl registers).adjoint =
      remainderRestoreControl registers := by
  simp [remainderRestoreControl, toggleRControl, circuit_adjoint_append,
    rControlNonterminal_selfAdjoint]

private theorem blockB2_selfAdjoint
    (registers : IndexedStepRegisters) :
    (blockB2 registers).adjoint = blockB2 registers := by
  have hcontrol : (remainderPhase2Control registers).adjoint =
      remainderPhase2Control registers := by
    exact rControlNonterminal_selfAdjoint _ _ _ _ _ _
  simp [blockB2, circuit_adjoint_append, hcontrol]

private theorem blockAInverse_after_forward
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state) :
    run (blockAInverse registers) (run (blockAForward registers) state) = state := by
  have hblock : Clean registers.blockScratch state := by
    apply clean_mono hready
    intro wire hwire
    exact hlayout.blockScratch_mem_sharedScratch hwire
  let marked := run (toggleTerminal registers) state
  have hmarkedBlock : Clean registers.blockScratch marked := by
    rw [show marked =
        state[registers.terminal ↦ Bool.xor (state registers.terminal)
          (registerMatches (terminalConditionWires registers)
            (terminalConditionValue registers) state)] by
      simpa only [marked, toggleTerminal] using
        run_computeControl (terminalConditionWires registers)
          (terminalConditionValue registers) registers.terminal
          registers.blockScratch state hlayout.terminalControl hblock]
    exact clean_upd_not_mem hblock hlayout.terminal_not_blockScratch
  have hpadding : Clean registers.terminalPadding.scratch marked :=
    clean_mono hmarkedBlock hlayout.terminalPadding_scratch_sub_block
  simp only [blockAInverse, blockAForward, toggleTerminal,
    Classical.run_append]
  rw [run_computeControl_twice (terminalConditionWires registers)
      (terminalConditionValue registers) registers.terminal registers.blockScratch
      _ hlayout.terminalControl]
  rw [run_terminalEpochRestore_after_spill _ _ _ _ hlayout.terminalEpoch]
  rw [run_cx_twice registers.terminal registers.phase1 _ (by
    simpa [List.nodup_cons] using hlayout.terminalPhase)]
  rw [run_preShiftUnitary_adjoint_after _ _ hlayout.preShift]
  rw [run_cx_twice registers.terminal registers.phase1 _ (by
    simpa [List.nodup_cons] using hlayout.terminalPhase)]
  rw [show run (terminalPaddingInverse registers.terminalPadding)
      (run (terminalPaddingForward registers.terminalPadding)
        (run (computeControl (terminalConditionWires registers)
          (terminalConditionValue registers) registers.terminal
          registers.blockScratch) state)) =
      run (computeControl (terminalConditionWires registers)
        (terminalConditionValue registers) registers.terminal
        registers.blockScratch) state by
    simpa only [marked, toggleTerminal] using
      run_terminalPaddingInverse_after_forward registers.terminalPadding marked
        hlayout.terminalPadding hpadding]
  exact run_computeControl_twice (terminalConditionWires registers)
    (terminalConditionValue registers) registers.terminal registers.blockScratch
    state hlayout.terminalControl

private theorem blockB1Inverse_after_forward
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder)
    (hready : IndexedStepBorrowedReady registers state) :
    run (blockB1Inverse registers n window)
        (run (blockB1Forward registers n window) state) = state := by
  have hinterval := remainderSubControl_intervalReady registers n T window state
    hlayout hwindow hready
  simp only [blockB1Inverse, blockB1Forward, Classical.run_append]
  rw [show Classical.run (remainderSubControl registers)
      (Classical.run (remainderSubControl registers)
        (run (intervalAddSubUnitary (registers.remainder window) n
          window.start window.stop .sub true .work1)
          (run (remainderSubControl registers) state))) =
      run (intervalAddSubUnitary (registers.remainder window) n
        window.start window.stop .sub true .work1)
        (run (remainderSubControl registers) state) by
    simpa [remainderSubControl, toggleRControl] using
      run_rControlNonterminal_twice [registers.phase1] 0 registers.control
        registers.lengthRPrime registers.terminal registers.blockScratch
        (run (intervalAddSubUnitary (registers.remainder window) n
          window.start window.stop .sub true .work1)
          (run (remainderSubControl registers) state)) hlayout.remainderSub]
  rw [run_intervalAddSubInverseUnitary_after_forward
    (registers.remainder window) n window.start window.stop .sub true .work1
    (run (remainderSubControl registers) state) (by simpa [hwindow] using hlayout.remainder)
    hinterval]
  simpa [remainderSubControl, toggleRControl] using
    run_rControlNonterminal_twice [registers.phase1] 0 registers.control
      registers.lengthRPrime registers.terminal registers.blockScratch state
      hlayout.remainderSub

private theorem blockB3Inverse_after_forward
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder)
    (hready : IndexedStepBorrowedReady registers state) :
    run (blockB3Inverse registers n window)
        (run (blockB3Forward registers n window) state) = state := by
  have hinterval := remainderRestoreControl_intervalReady registers n T window state
    hlayout hwindow hready
  simp only [blockB3Inverse, blockB3Forward, Classical.run_append]
  rw [run_selfAdjoint_twice (remainderRestoreControl registers) _
    (remainderRestoreControl_selfAdjoint registers)
    (remainderRestoreControl_wellFormed registers n T hlayout)]
  rw [run_intervalAddSubInverseUnitary_after_forward
    (registers.remainder window) n window.start window.stop .add false .work1
    (run (remainderRestoreControl registers) state)
    (by simpa [hwindow] using hlayout.remainder) hinterval]
  exact run_selfAdjoint_twice (remainderRestoreControl registers) state
    (remainderRestoreControl_selfAdjoint registers)
    (remainderRestoreControl_wellFormed registers n T hlayout)

private theorem blockBInverse_after_forward
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder)
    (hready : IndexedStepBorrowedReady registers state) :
    run (blockBInverse registers n window)
        (run (blockBForward registers n window) state) = state := by
  let afterB1 := run (blockB1Forward registers n window) state
  let afterB2 := run (blockB2 registers) afterB1
  have hfirst := blockB1Forward_correct registers n T window state hlayout hwindow hready
  have hreadyB1 : IndexedStepBorrowedReady registers afterB1 := by
    simpa only [afterB1] using hfirst.2
  have hsecond := blockB2_correct registers n T afterB1 hlayout hreadyB1
  have hreadyB2 : IndexedStepBorrowedReady registers afterB2 := by
    simpa only [afterB2] using hsecond.2
  simp only [blockBInverse, blockBForward, Classical.run_append]
  rw [show run (blockB3Inverse registers n window)
      (run (blockB3Forward registers n window) afterB2) = afterB2 by
    exact blockB3Inverse_after_forward registers n T window afterB2 hlayout
      hwindow hreadyB2]
  rw [run_selfAdjoint_twice (blockB2 registers) afterB1
    (blockB2_selfAdjoint registers) (blockB2_wellFormed registers n T hlayout)]
  exact blockB1Inverse_after_forward registers n T window state hlayout hwindow hready

private theorem blockCInverse_after_forward
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T) :
    run (blockCInverse registers) (run (blockCForward registers) state) = state := by
  simp only [blockCInverse, blockCForward, toggleTerminal,
    Classical.run_append]
  rw [run_computeControl_twice (terminalConditionWires registers)
    (terminalConditionValue registers) registers.terminal registers.blockScratch
    _ hlayout.terminalControl]
  rw [run_terminalEpochSpill_after_restore _ _ _ _ hlayout.terminalEpoch]
  exact run_computeControl_twice (terminalConditionWires registers)
    (terminalConditionValue registers) registers.terminal registers.blockScratch
    state hlayout.terminalControl

private theorem run_phase2LengthControl_twice
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T) :
    run (phase2LengthControl registers)
        (run (phase2LengthControl registers) state) = state := by
  simpa only [phase2LengthControl] using
    run_computeControl_twice [registers.phase1, registers.phase2] 2
      registers.control registers.sourceScratch state hlayout.phase2Length

private theorem run_phase3LengthControl_twice
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T) :
    run (phase3LengthControl registers)
        (run (phase3LengthControl registers) state) = state := by
  simpa only [phase3LengthControl] using
    run_computeControl_twice [registers.phase1, registers.phase2] 1
      registers.control registers.sourceScratch state hlayout.phase3Length

private theorem blockD1Inverse_after_forward
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state) :
    run (circuit! {
      phase2LengthControl registers;
      controlledDecrement registers.control registers.lengthQ (lengthCarries registers);
      phase2LengthControl registers
    })
      (run (circuit! {
        phase2LengthControl registers;
        controlledIncrement registers.control registers.lengthQ (lengthCarries registers);
        phase2LengthControl registers
      }) state) = state := by
  have hsource : Clean registers.sourceScratch state := by
    intro wire hwire
    exact hready wire (by simp [IndexedStepRegisters.sharedScratch, hwire])
  have henabled := run_computeControl_state [registers.phase1, registers.phase2] 2
    registers.control registers.sourceScratch state hlayout.phase2Length hsource
  have henabledRun : run (phase2LengthControl registers) state =
      matchXorState [registers.phase1, registers.phase2] 2
        registers.control state := by
    simpa only [phase2LengthControl] using henabled.1
  have hcarries : Clean (lengthCarries registers)
      (run (phase2LengthControl registers) state) := by
    rw [henabledRun]
    intro wire hwire
    exact henabled.2 wire (List.mem_of_mem_take hwire)
  simp only [Classical.run_append]
  rw [run_phase2LengthControl_twice registers n T _ hlayout]
  rw [indexedStep_run_decrement_after_increment registers.control registers.lengthQ
    (lengthCarries registers) (run (phase2LengthControl registers) state)
    hlayout.lengthCarryCapacity hlayout.lengthCarryPhysical hcarries]
  exact run_phase2LengthControl_twice registers n T state hlayout

private theorem blockD3Inverse_after_forward
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state) :
    run (circuit! {
      phase3LengthControl registers;
      controlledIncrement registers.control registers.lengthQ (lengthCarries registers);
      phase3LengthControl registers
    })
      (run (circuit! {
        phase3LengthControl registers;
        controlledDecrement registers.control registers.lengthQ (lengthCarries registers);
        phase3LengthControl registers
      }) state) = state := by
  have hsource : Clean registers.sourceScratch state := by
    intro wire hwire
    exact hready wire (by simp [IndexedStepRegisters.sharedScratch, hwire])
  have henabled := run_computeControl_state [registers.phase1, registers.phase2] 1
    registers.control registers.sourceScratch state hlayout.phase3Length hsource
  have henabledRun : run (phase3LengthControl registers) state =
      matchXorState [registers.phase1, registers.phase2] 1
        registers.control state := by
    simpa only [phase3LengthControl] using henabled.1
  have hcarries : Clean (lengthCarries registers)
      (run (phase3LengthControl registers) state) := by
    rw [henabledRun]
    intro wire hwire
    exact henabled.2 wire (List.mem_of_mem_take hwire)
  simp only [Classical.run_append]
  rw [run_phase3LengthControl_twice registers n T _ hlayout]
  rw [indexedStep_run_increment_after_decrement registers.control registers.lengthQ
    (lengthCarries registers) (run (phase3LengthControl registers) state)
    hlayout.lengthCarryCapacity hlayout.lengthCarryPhysical hcarries]
  exact run_phase3LengthControl_twice registers n T state hlayout

private theorem quotientXorControlInverse_eq_adjoint
    (registers : IndexedStepRegisters) :
    quotientXorControlInverse registers =
      (quotientXorControl registers).adjoint := by
  rfl

private theorem blockD2_after_forward
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).quotientSwap)
    (hready : IndexedStepReady registers state) :
    run (circuit! {
      quotientXorControl registers;
      quotientSwapUnitary (registers.quotient window) window.start window.stop;
      quotientXorControlInverse registers
    })
      (run (circuit! {
        quotientXorControl registers;
        quotientSwapUnitary (registers.quotient window) window.start window.stop;
        quotientXorControlInverse registers
      }) state) = state := by
  have hqLayout : QuotientSwapLayout (registers.quotient window)
      window.start window.stop := by
    subst window
    exact hlayout.quotient
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
  have hxorWellFormed := quotientXorControl_wellFormed registers n T hlayout
  simp only [Classical.run_append]
  rw [show run (quotientXorControl registers)
      (run (quotientXorControlInverse registers)
        (run (quotientSwapUnitary (registers.quotient window)
          window.start window.stop)
          (run (quotientXorControl registers) state))) =
      run (quotientSwapUnitary (registers.quotient window)
        window.start window.stop)
        (run (quotientXorControl registers) state) by
    rw [quotientXorControlInverse_eq_adjoint]
    exact run_run_adjoint_classical_indexedStep (quotientXorControl registers)
      _ hxorWellFormed]
  rw [show run (quotientSwapUnitary (registers.quotient window)
      window.start window.stop)
      (run (quotientSwapUnitary (registers.quotient window)
        window.start window.stop)
        (run (quotientXorControl registers) state)) =
      run (quotientXorControl registers) state by
    rw [henabledRun]
    exact run_quotientSwapUnitary_after_forward
      (registers.quotient window) enabled2 hqLayout hqReady]
  rw [quotientXorControlInverse_eq_adjoint]
  exact run_adjoint_run_classical (quotientXorControl registers)
    hxorWellFormed state

private theorem blockDInverse_after_forward
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).quotientSwap)
    (hready : IndexedStepReady registers state) :
    run (blockDInverse registers window)
        (run (blockDForward registers window) state) = state := by
  let firstForward : Circuit := circuit! {
    phase2LengthControl registers;
    controlledIncrement registers.control registers.lengthQ (lengthCarries registers);
    phase2LengthControl registers
  }
  let middle : Circuit := circuit! {
    quotientXorControl registers;
    quotientSwapUnitary (registers.quotient window) window.start window.stop;
    quotientXorControlInverse registers
  }
  let lastForward : Circuit := circuit! {
    phase3LengthControl registers;
    controlledDecrement registers.control registers.lengthQ (lengthCarries registers);
    phase3LengthControl registers
  }
  let firstInverse : Circuit := circuit! {
    phase3LengthControl registers;
    controlledIncrement registers.control registers.lengthQ (lengthCarries registers);
    phase3LengthControl registers
  }
  let lastInverse : Circuit := circuit! {
    phase2LengthControl registers;
    controlledDecrement registers.control registers.lengthQ (lengthCarries registers);
    phase2LengthControl registers
  }
  have hfirst := blockD1Forward_correct registers n T state hlayout hready
  have hfirstReady : IndexedStepReady registers (run firstForward state) := by
    simpa only [firstForward] using hfirst.2
  have hmiddle := blockD2Forward_correct registers n T window
    (run firstForward state) hlayout hwindow hfirstReady
  have hmiddleReady : IndexedStepReady registers
      (run middle (run firstForward state)) := by
    simpa only [middle] using hmiddle.2
  rw [show run (blockDInverse registers window)
      (run (blockDForward registers window) state) =
      run lastInverse
        (run middle
          (run firstInverse
            (run lastForward
              (run middle (run firstForward state))))) by
    simp [blockDInverse, blockDForward, blockD1Forward, blockD2Forward, blockD3Forward, firstForward, middle,
      lastForward, firstInverse, lastInverse, Classical.run_append]]
  rw [show run firstInverse
      (run lastForward (run middle (run firstForward state))) =
      run middle (run firstForward state) by
    exact blockD3Inverse_after_forward registers n T
      (run middle (run firstForward state)) hlayout hmiddleReady]
  rw [show run middle (run middle (run firstForward state)) =
      run firstForward state by
    exact blockD2_after_forward registers n T window
      (run firstForward state) hlayout hwindow hfirstReady]
  exact blockD1Inverse_after_forward registers n T state hlayout hready

private theorem blockFInverse_after_forward
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T) :
    run (blockFInverse registers) (run (blockFForward registers) state) = state := by
  exact run_postShiftUnitary_adjoint_after registers.postShift state hlayout.postShift

private theorem blockGInverse_after_forward
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T) :
    run (blockGInverse registers) (run (blockGForward registers) state) = state := by
  exact run_phaseUpdateEpochInverseUnitary_after_forward registers.phaseUpdate
    registers.shiftEpoch state hlayout.phaseUpdate

private def blockHPrefix (registers : IndexedStepRegisters) : Circuit :=
  circuit! {
    mcxVChain registers.lengthQ (registers.sourceScratch.getD 0 0)
      (registers.sourceScratch.drop 2);
    gate! Gate.X registers.shiftEpoch;
    mcxVChain (registers.lengthS ++ [registers.shiftEpoch])
      (registers.sourceScratch.getD 1 0) (registers.sourceScratch.drop 2);
    gate! Gate.X registers.shiftEpoch;
    gate! Gate.CCX (registers.sourceScratch.getD 0 0)
      (registers.sourceScratch.getD 1 0) registers.control
  }

private def blockHSuffix (registers : IndexedStepRegisters) : Circuit :=
  circuit! {
    gate! Gate.CCX (registers.sourceScratch.getD 0 0)
      (registers.sourceScratch.getD 1 0) registers.control;
    gate! Gate.X registers.shiftEpoch;
    mcxVChain (registers.lengthS ++ [registers.shiftEpoch])
      (registers.sourceScratch.getD 1 0) (registers.sourceScratch.drop 2);
    gate! Gate.X registers.shiftEpoch;
    mcxVChain registers.lengthQ (registers.sourceScratch.getD 0 0)
      (registers.sourceScratch.drop 2)
  }

private theorem blockHSuffix_eq_adjoint_blockHPrefix
    (registers : IndexedStepRegisters) :
    blockHSuffix registers = (blockHPrefix registers).adjoint := by
  simp [blockHPrefix, blockHSuffix, circuit_adjoint_append,
    mcxVChain_indexedStep_selfAdjoint]

private theorem blockHPrefix_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (blockHPrefix registers) := by
  have hq := mcxVChain_wellFormed registers.lengthQ
    (registers.sourceScratch.getD 0 0) (registers.sourceScratch.drop 2)
    hlayout.endQ.1 hlayout.endQ.2
  have hs := mcxVChain_wellFormed (registers.lengthS ++ [registers.shiftEpoch])
    (registers.sourceScratch.getD 1 0) (registers.sourceScratch.drop 2)
    hlayout.endS.1 hlayout.endS.2
  have hend := blockHEndGate_wellFormed registers n T hlayout
  have hx : Gate.WellFormed (.X registers.shiftEpoch) := by
    simp [Gate.WellFormed]
  unfold CircuitWellFormed at hq hs ⊢
  intro gate hgate
  simp only [blockHPrefix, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hgate
  aesop

private theorem blockHPrefix_run
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state) :
    run (blockHPrefix registers) state = blockHEndInputState registers state ∧
      EndIterationReady (registers.endIteration n T)
        (run (blockHPrefix registers) state) := by
  let zeroQ := blockHZeroQState registers state
  let beforeS := blockHBeforeSState registers state
  let zeroS := blockHZeroSState registers state
  let restoredEpoch :=
    zeroS[registers.shiftEpoch ↦ !zeroS registers.shiftEpoch]
  let enabled := blockHEndInputState registers state
  have hcleanTail : Clean (registers.sourceScratch.drop 2) state := by
    intro wire hwire
    apply hready wire
    exact hlayout.sourceScratch_mem_sharedScratch (List.mem_of_mem_drop hwire)
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
  have hx1 : run ([.X registers.shiftEpoch] : Circuit) zeroQ = beforeS := by
    rfl
  have hx2 : run ([.X registers.shiftEpoch] : Circuit) zeroS = restoredEpoch := by
    rfl
  have hccx : run ([.CCX (registers.sourceScratch.getD 0 0)
      (registers.sourceScratch.getD 1 0) registers.control] : Circuit)
      restoredEpoch = enabled := by
    rfl
  have hgroup : run ([.X registers.shiftEpoch,
      .CCX (registers.sourceScratch.getD 0 0)
        (registers.sourceScratch.getD 1 0) registers.control] : Circuit)
      zeroS = enabled := by
    change run ([.CCX (registers.sourceScratch.getD 0 0)
      (registers.sourceScratch.getD 1 0) registers.control] : Circuit)
      (run ([.X registers.shiftEpoch] : Circuit) zeroS) = enabled
    rw [hx2, hccx]
  have hrun : run (blockHPrefix registers) state = enabled := by
    simp only [blockHPrefix, Classical.run_append]
    rw [hqRun, hx1, hsRun, hgroup]
  constructor
  · simpa only [enabled] using hrun
  · rw [hrun]
    exact hendReady

private theorem blockHInverse_after_forward_of_step
    (registers : IndexedStepRegisters) (n T boundary4 boundary5 : Nat)
    (hboundary4 : (endIterationWindowsAt n T).k4 ≤ boundary4 ∧
      boundary4 ≤ (endIterationWindowsAt n T).K4)
    (hboundary5 : (endIterationWindowsAt n T).k5 ≤ boundary5 ∧
      boundary5 ≤ (endIterationWindowsAt n T).K5Decode n)
    (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hstep : T % 4 = 0)
    (hroute4 :
      ((registers.endIteration n T).upperTree
        (endIterationWindowsAt n T)).routeLabel
        (run (constMinus (registers.endIteration n T).lengthRP
            (registers.endIteration n T).constants
            (registers.endIteration n T).carry (n + 2))
          (run (controlledWorkSwap (registers.endIteration n T).control
            (registers.endIteration n T).work1
            (registers.endIteration n T).work2)
            (blockHEndInputState registers state))) = boundary4)
    (hroute5 :
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
    run (blockHInverse registers n T)
        (run (blockHForward registers n T) state) = state := by
  let headCircuit := blockHPrefix registers
  let tailCircuit := blockHSuffix registers
  let endForward := swapWorkAndLengthUnaryShared (registers.endIteration n T) n
    (endIterationWindowsAt n T)
  let endInverse := swapWorkAndLengthUnarySharedInverse
    (registers.endIteration n T) n (endIterationWindowsAt n T)
  let iterGate : Circuit := [.CX registers.control registers.iter]
  have hprefix := blockHPrefix_run registers n T state hlayout hready
  have hroute4' :
      ((registers.endIteration n T).upperTree
        (endIterationWindowsAt n T)).routeLabel
        (run (constMinus (registers.endIteration n T).lengthRP
            (registers.endIteration n T).constants
            (registers.endIteration n T).carry (n + 2))
          (run (controlledWorkSwap (registers.endIteration n T).control
            (registers.endIteration n T).work1
            (registers.endIteration n T).work2)
            (run headCircuit state))) = boundary4 := by
    rw [show run headCircuit state = blockHEndInputState registers state by
      simpa only [headCircuit] using hprefix.1]
    exact hroute4
  have hroute5' :
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
            (run headCircuit state)))) = boundary5 := by
    rw [show run headCircuit state = blockHEndInputState registers state by
      simpa only [headCircuit] using hprefix.1]
    exact hroute5
  have hendCancel : run endInverse (run endForward (run headCircuit state)) =
      run headCircuit state := by
    exact swapWorkAndLengthUnaryShared_roundTrip_auto
      (registers.endIteration n T) n (endIterationWindowsAt n T)
      boundary4 boundary5 hboundary4 hboundary5 (run headCircuit state)
      (hlayout.endIteration hstep) hroute4' hroute5'
      (by simpa only [headCircuit] using hprefix.2)
  have hprefixWellFormed : CircuitWellFormed headCircuit := by
    simpa only [headCircuit] using blockHPrefix_wellFormed registers n T hlayout
  have hiterDistinct : registers.control ≠ registers.iter := by
    simpa only [Gate.WellFormed] using
      blockHIterGate_wellFormed registers n T hlayout
  rw [show run (blockHInverse registers n T)
      (run (blockHForward registers n T) state) =
      run tailCircuit
        (run endInverse
          (run iterGate
            (run headCircuit
              (run tailCircuit
                (run iterGate (run endForward (run headCircuit state))))))) by
    simp [blockHInverse, blockHForward, hstep, headCircuit, tailCircuit,
      endForward, endInverse, iterGate, blockHPrefix, blockHSuffix,
      Classical.run_append]]
  rw [show run headCircuit
      (run tailCircuit (run iterGate (run endForward (run headCircuit state)))) =
      run iterGate (run endForward (run headCircuit state)) by
    rw [show tailCircuit = headCircuit.adjoint by
      simpa only [headCircuit, tailCircuit] using
        blockHSuffix_eq_adjoint_blockHPrefix registers]
    exact run_run_adjoint_classical_indexedStep headCircuit _ hprefixWellFormed]
  rw [show run iterGate (run iterGate (run endForward (run headCircuit state))) =
      run endForward (run headCircuit state) by
    simpa only [iterGate] using run_cx_twice registers.control registers.iter
      (run endForward (run headCircuit state)) hiterDistinct]
  rw [hendCancel]
  rw [show tailCircuit = headCircuit.adjoint by
    simpa only [headCircuit, tailCircuit] using
      blockHSuffix_eq_adjoint_blockHPrefix registers]
  exact run_adjoint_run_classical headCircuit hprefixWellFormed state

private theorem blockHInverse_after_forward
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
    run (blockHInverse registers n T)
        (run (blockHForward registers n T) state) = state := by
  by_cases hstep : T % 4 = 0
  · exact blockHInverse_after_forward_of_step registers n T boundary4 boundary5
      hboundary4 hboundary5 state hlayout hstep (hroute4 hstep) (hroute5 hstep) hready
  · simp [blockHInverse, blockHForward, hstep]

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
    blockB2, blockB3Forward, blockCForward, blockDForward, blockD1Forward, blockD2Forward, blockD3Forward, blockEForward, blockEFinishForward, blockESubtractForward, blockEPrepareForward, coefficientSubtractControl,
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
  exact hready wire (hlayout.sourceScratch_mem_sharedScratch
    (hlayout.phaseUpdate_scratch_sub_source wire hwire))

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
    (by simp [blockEForward, blockEFinishForward, blockESubtractForward, blockEPrepareForward, coefficientSubtractControl, coefficientTemporaryControl,
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
    (by simp [blockCForward, blockDForward, blockD1Forward, blockD2Forward, blockD3Forward, toggleTerminal,
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

/-- Replacing the five selected cleanup sites—two remainder intervals, two coefficient prefixes,
and the phase update—by X-basis measurement/reset preserves the exact coherent step on all
encoded, clean-scratch inputs. -/
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

/-! ## Direct blockwise full-step semantics -/

/-- State immediately before the optional iteration-end block, expressed through the direct
block recurrences of A--G.  The full composition does not appeal to its own circuit execution;
Block B deliberately retains the interval layer's `intervalAddSubState`, whose endpoint
preparation and restoration are still tied to the proved interval circuit. -/
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

/-- The actual A--C prefix: pre-shift/padding, remainder arithmetic and epoch restoration. -/
def indexedStepRemainderPrefix (registers : IndexedStepRegisters) (n T : Nat) : Circuit :=
  blockAForward registers ++
    blockBForward registers n (certifiedActiveWindows n T).remainder ++
    blockCForward registers

/-- The complete remainder prefix preserves both operational encoding premises.
The later quotient/coefficient, phase and iteration-end blocks are not included. -/
theorem indexedStepRemainderPrefix_correct
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state)
    (hencoded : IndexedStepEpochEncoded registers state) :
    (indexedStepRemainderPrefix registers n T).IsPrefix (indexedStepUnitary registers n T) ∧
    IndexedStepReady registers (run (indexedStepRemainderPrefix registers n T) state) ∧
    IndexedStepEpochEncoded registers (run (indexedStepRemainderPrefix registers n T) state) := by
  constructor
  · refine ⟨blockDForward registers (certifiedActiveWindows n T).quotientSwap ++
      blockEForward registers n (certifiedActiveWindows n T).coefficient ++
      blockFForward registers ++ blockGForward registers ++ blockHForward registers n T, ?_⟩
    simp only [indexedStepRemainderPrefix, indexedStepUnitary, List.append_assoc]
  ·
    let afterA := blockAForwardState registers state
    let afterB := blockBForwardState registers n (certifiedActiveWindows n T).remainder afterA
    have hA := blockAForward_correct registers n T state hlayout hready
    have hABorrowed : IndexedStepBorrowedReady registers afterA := by
      have h := blockAForward_borrowedReady registers n T state hlayout hready hencoded
      rw [hA.1] at h
      exact h
    have hB := blockBForward_correct registers n T (certifiedActiveWindows n T).remainder
      afterA hlayout rfl hABorrowed
    have hBBorrowed : IndexedStepBorrowedReady registers afterB := by
      have h := hB.2
      rw [hB.1] at h
      exact h
    have hC := blockCForward_correct registers n T afterB hlayout hBBorrowed
    have hCE := blockCForward_epochEncoded registers n T afterB hlayout hBBorrowed
    simp only [indexedStepRemainderPrefix, Classical.run_append]
    rw [hA.1, hB.1]
    exact ⟨hC.2, by rw [hC.1]; exact hCE⟩

/-- Direct blockwise recurrence of one literal indexed Algorithm-3 microstep.  It is noncircular
relative to the complete indexed circuit, while inheriting Block B's circuit-bound endpoint
semantics.  The two boundary arguments are the decoded end-of-iteration routes and are ignored
away from `T % 4 = 0`. -/
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

/-- The literal coherent source stream implements the direct blockwise indexed recurrence,
restores every step-local temporary, and leaves the borrowed epoch as persistent padding state. -/
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

/-- The pinned explicit reverse step cancels the literal forward step on every encoded routed
basis state.  In particular, the inverse decoder routes are derived from the forward routes by
the component round-trip theorems rather than assumed separately. -/
theorem indexedStepInverseUnitary_after_forward
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
    run (indexedStepInverseUnitary registers n T)
        (run (indexedStepUnitary registers n T) state) = state := by
  let windows := certifiedActiveWindows n T
  let afterA := run (blockAForward registers) state
  let afterB := run (blockBForward registers n windows.remainder) afterA
  let afterC := run (blockCForward registers) afterB
  let afterD := run (blockDForward registers windows.quotientSwap) afterC
  let afterE := run (blockEForward registers n windows.coefficient) afterD
  let afterF := run (blockFForward registers) afterE
  let beforeEnd := run (blockGForward registers) afterF
  have hA := blockAForward_correct registers n T state hlayout hready
  have hABorrowed : IndexedStepBorrowedReady registers afterA := by
    simpa only [afterA] using
      blockAForward_borrowedReady registers n T state hlayout hready hencoded
  have hB := blockBForward_correct registers n T windows.remainder afterA
    hlayout rfl hABorrowed
  have hBBorrowed : IndexedStepBorrowedReady registers afterB := by
    simpa only [afterB] using hB.2
  have hC := blockCForward_correct registers n T afterB hlayout hBBorrowed
  have hCReady : IndexedStepReady registers afterC := by
    simpa only [afterC] using hC.2
  have hD := blockDForward_correct registers n T windows.quotientSwap afterC
    hlayout rfl hCReady
  have hDReady : IndexedStepReady registers afterD := by
    simpa only [afterD] using hD.2
  have hE := blockEForward_correct registers n T windows.coefficient afterD
    hlayout rfl hDReady
  have hEReady : IndexedStepReady registers afterE := by
    simpa only [afterE] using hE.2
  have hF := blockFForward_correct registers n T afterE hlayout hEReady
  have hFReady : IndexedStepReady registers afterF := by
    simpa only [afterF] using hF.2
  have hG := blockGForward_correct registers n T afterF hlayout hFReady
  have hGReady : IndexedStepReady registers beforeEnd := by
    simpa only [beforeEnd] using hG.2
  have hbeforeEnd :
      beforeEnd = indexedStepBeforeEndState registers n T state := by
    simp only [beforeEnd]
    rw [hG.1]
    simp only [afterF]
    rw [hF.1]
    simp only [afterE]
    rw [hE.1]
    simp only [afterD]
    rw [hD.1]
    simp only [afterC]
    rw [hC.1]
    simp only [afterB]
    rw [hB.1]
    simp only [afterA]
    rw [hA.1]
    rfl
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
    rw [hbeforeEnd]
    have hr := congrArg Prod.fst (hroutes hstep)
    simpa only [indexedStepEndRoutes] using hr
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
    rw [hbeforeEnd]
    have hr := congrArg Prod.snd (hroutes hstep)
    simpa only [indexedStepEndRoutes] using hr
  have hshape :
      run (indexedStepInverseUnitary registers n T)
          (run (indexedStepUnitary registers n T) state) =
        run (blockAInverse registers)
          (run (blockBInverse registers n windows.remainder)
            (run (blockCInverse registers)
              (run (blockDInverse registers windows.quotientSwap)
                (run (blockEInverse registers n windows.coefficient)
                  (run (blockFInverse registers)
                    (run (blockGInverse registers)
                      (run (blockHInverse registers n T)
                        (run (blockHForward registers n T) beforeEnd)))))))) := by
    simp only [indexedStepInverseUnitary, indexedStepUnitary,
      Classical.run_append, windows, beforeEnd, afterF, afterE, afterD,
      afterC, afterB, afterA]
  rw [hshape]
  rw [show run (blockHInverse registers n T)
      (run (blockHForward registers n T) beforeEnd) = beforeEnd by
    exact blockHInverse_after_forward registers n T boundary4 boundary5
      hboundary4 hboundary5 beforeEnd hlayout hroute4 hroute5 hGReady]
  rw [show run (blockGInverse registers)
      (run (blockGForward registers) afterF) = afterF by
    exact blockGInverse_after_forward registers n T afterF hlayout]
  rw [show run (blockFInverse registers)
      (run (blockFForward registers) afterE) = afterE by
    exact blockFInverse_after_forward registers n T afterE hlayout]
  rw [show run (blockEInverse registers n windows.coefficient)
      (run (blockEForward registers n windows.coefficient) afterD) = afterD by
    exact blockEInverse_after_forward registers n T windows.coefficient afterD
      hlayout rfl hDReady]
  rw [show run (blockDInverse registers windows.quotientSwap)
      (run (blockDForward registers windows.quotientSwap) afterC) = afterC by
    exact blockDInverse_after_forward registers n T windows.quotientSwap afterC
      hlayout rfl hCReady]
  rw [show run (blockCInverse registers)
      (run (blockCForward registers) afterB) = afterB by
    exact blockCInverse_after_forward registers n T afterB hlayout]
  rw [show run (blockBInverse registers n windows.remainder)
      (run (blockBForward registers n windows.remainder) afterA) = afterA by
    exact blockBInverse_after_forward registers n T windows.remainder afterA
      hlayout rfl hABorrowed]
  exact blockAInverse_after_forward registers n T state hlayout hready

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


private theorem terminal_write_read (wires : List Wire) (state : BasisState) :
    indexedWriteWireValues wires (wireValues wires state) state = state := by
  induction wires with
  | nil => rfl
  | cons wire wires ih =>
    simp only [wireValues, List.map_cons, indexedWriteWireValues] at ih ⊢
    rw [ih]
    funext w
    by_cases hw : w = wire
    · subst w; simp [upd]
    · simp [upd, hw]

private theorem terminal_increment_false (bits : List Bool) : incrementBits false bits = bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [incrementBits, ih]

private theorem terminal_decrement_false (bits : List Bool) : decrementBits false bits = bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [decrementBits, ih]

private theorem terminal_increment_idle (wires : List Wire) (state : BasisState) :
    indexedIncrementWordState false wires state = state := by
  rw [indexedIncrementWordState, terminal_increment_false, terminal_write_read]

private theorem terminal_decrement_idle (wires : List Wire) (state : BasisState) :
    indexedDecrementWordState false wires state = state := by
  rw [indexedDecrementWordState, terminal_decrement_false, terminal_write_read]

private theorem terminal_match_idle (wires : List Wire) (value : Nat) (target : Wire)
    (state : BasisState) (ht : state target = false) (hm : registerMatches wires value state = false) :
    matchXorState wires value target state = state := by
  funext wire
  by_cases hw : wire = target
  · subst wire; simp [matchXorState, hm, ht, upd]
  · simp [matchXorState, upd, hw]

private theorem terminal_xor_idle (control target : Wire) (state : BasisState)
    (hc : state control = false) : xorWireState control target state = state := by
  funext wire
  by_cases hw : wire = target
  · subst wire; simp [xorWireState, hc, upd]
  · simp [xorWireState, upd, hw]

private theorem terminal_blockD_idle (registers : IndexedStepRegisters) (window : ActiveWindow)
    (state : BasisState) (hc : state registers.control = false)
    (h1 : state registers.phase1 = false) (h2 : state registers.phase2 = false) :
    blockDForwardState registers window state = state := by
  have hm2 : registerMatches [registers.phase1, registers.phase2] 2 state = false := by
    simp [registerMatches, registerMatchesFrom, h1, h2]
    decide
  have hm1 : registerMatches [registers.phase1, registers.phase2] 1 state = false := by
    simp [registerMatches, registerMatchesFrom, h1, h2]
  have hm2idle := terminal_match_idle _ _ _ state hc hm2
  have hm1idle := terminal_match_idle _ _ _ state hc hm1
  have hd1 : blockD1ForwardState registers state = state := by
    simp only [blockD1ForwardState, hm2idle, hc, terminal_increment_idle]
  have hd3 : blockD3ForwardState registers state = state := by
    simp only [blockD3ForwardState, hm1idle, hc, terminal_decrement_idle]
  have hx1 := terminal_xor_idle registers.phase1 registers.control state h1
  have hx2 := terminal_xor_idle registers.phase2 registers.control state h2
  have hs : indexedQuotientSwapState (registers.quotient window) window.start window.stop state = state := by
    simp [indexedQuotientSwapState, quotientSwapState, IndexedStepRegisters.quotient, hc]
  have hd2 : blockD2ForwardState registers window state = state := by
    simp only [blockD2ForwardState, hx1, hx2, hs]
  rw [blockDForwardState, hd1, hd2, hd3]

private theorem terminal_boundary_restore_prepare
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hclean : Clean registers.blockScratch state) :
    tBoundaryRestoreState registers n (tBoundaryPrepareState registers n state) = state := by
  have hp := run_tBoundaryPrepareState registers n T state hlayout hclean
  have hr := run_tBoundaryRestoreState registers n T
    (run (prepareLatestPaperTBoundary registers.tBoundary n) state) hlayout hp.2
  rw [← hp.1, ← hr.1]
  apply run_restoreLatestPaperTBoundary_after_prepare registers.tBoundary n state hlayout.tBoundary
  intro wire hwire
  exact hclean wire (hlayout.tBoundary_usedScratch_sub_block wire hwire)

private theorem terminal_match_twice (controls : List Wire) (value : Nat) (target : Wire)
    (state : BasisState) (hne : target ∉ controls) :
    matchXorState controls value target (matchXorState controls value target state) = state := by
  have hm : registerMatches controls value (matchXorState controls value target state) =
      registerMatches controls value state := by
    apply registerMatches_congr
    intro wire hw
    have h : wire ≠ target := by intro he; subst wire; exact hne hw
    simp [matchXorState, upd, h]
  funext wire
  by_cases hw : wire = target
  · subst wire
    rw [matchXorState]
    simp only [upd]
    rw [hm]
    simp [matchXorState, upd]
  · simp [matchXorState, upd, hw]

private theorem terminal_coefficient_controls_idle (registers : IndexedStepRegisters)
    (state : BasisState) (h1 : state registers.phase1 = false)
    (hc : state registers.control = false)
    (hp : registers.phase1 ≠ registers.terminal)
    (hct : registers.control ≠ registers.terminal)
    (ht : registers.terminal ∉ [registers.phase2, registers.sign]) :
    matchXorState [registers.phase2, registers.sign] 2 registers.terminal
      (matchXorState [registers.phase1, registers.terminal] 1 registers.control
        (matchXorState [registers.phase2, registers.sign] 2 registers.terminal state)) = state := by
  let temporary := matchXorState [registers.phase2, registers.sign] 2 registers.terminal state
  have hc' : temporary registers.control = false := by simp [temporary, matchXorState, upd, hct, hc]
  have hp' : temporary registers.phase1 = false := by simp [temporary, matchXorState, upd, hp, h1]
  have hm : registerMatches [registers.phase1, registers.terminal] 1 temporary = false := by
    simp [registerMatches, registerMatchesFrom, hp']
  rw [terminal_match_idle _ _ _ temporary hc' hm]
  exact terminal_match_twice _ _ _ state ht

private theorem terminal_blockE_reduced (registers : IndexedStepRegisters) (n : Nat)
    (window : ActiveWindow) (state : BasisState)
    (h1 : state registers.phase1 = false) (hc : state registers.control = false)
    (hp : registers.phase1 ≠ registers.terminal)
    (hct : registers.control ≠ registers.terminal)
    (ht : registers.terminal ∉ [registers.phase2, registers.sign])
    (hp1 : (tBoundaryPrepareState registers n state) registers.phase1 = false)
    (hpc : (tBoundaryPrepareState registers n state) registers.control = false)
    (hsub : coefficientPrefixState (registers.coefficient window) window.start window.stop
      .sub false .work2 (tBoundaryPrepareState registers n state) = tBoundaryPrepareState registers n state)
    (hadd : coefficientPrefixState (registers.coefficient window) window.start window.stop
      .add true .work2 (tBoundaryPrepareState registers n state) = tBoundaryPrepareState registers n state) :
    blockEForwardState registers n window state =
      tBoundaryRestoreState registers n (tBoundaryPrepareState registers n state) := by
  have hsandwich := terminal_coefficient_controls_idle registers state h1 hc hp hct ht
  let prepared := tBoundaryPrepareState registers n state
  have hsandwichP := terminal_coefficient_controls_idle registers prepared hp1 hpc hp hct ht
  have hx := terminal_xor_idle registers.phase1 registers.sign prepared hp1
  have hm : registerMatches [registers.phase1] 1 prepared = false := by
    simp [registerMatches, registerMatchesFrom, show prepared registers.phase1 = false from hp1]
  have hmIdle := terminal_match_idle _ _ _ prepared hpc hm
  dsimp only [prepared] at hsandwichP hx hmIdle
  simp only [blockEForwardState, hsandwich, hsub, hsandwichP, hx, hmIdle, hadd]

private theorem terminal_blockE_idle (registers : IndexedStepRegisters) (n T : Nat)
    (window : ActiveWindow) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient)
    (hready : IndexedStepReady registers state)
    (h1 : state registers.phase1 = false) :
    blockEForwardState registers n window state = state := by
  have hc : state registers.control = false :=
    hready registers.control (by simp [IndexedStepRegisters.sharedScratch])
  have hclean : Clean registers.blockScratch state := by
    intro wire hw
    exact hready wire (hlayout.blockScratch_mem_sharedScratch hw)
  have hts : registers.terminal ∈ registers.sourceScratch := by
    rw [← hlayout.scratch_view]
    simp
  have hta := hlayout.sourceScratch_mem_aux hts
  have hp : registers.phase1 ≠ registers.terminal :=
    Ne.symm (hlayout.aux_not_payload hta (by simp [indexedStepPayload]))
  have hct : registers.control ≠ registers.terminal := by
    have hnodup := hlayout.control_not_sourceScratch
    intro he
    exact hnodup (he ▸ hts)
  have ht : registers.terminal ∉ [registers.phase2, registers.sign] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hlayout.aux_not_payload hta (by simp [indexedStepPayload]),
      hlayout.aux_not_payload hta (by simp [indexedStepPayload])⟩
  let prepared := tBoundaryPrepareState registers n state
  have hprep := run_tBoundaryPrepareState registers n T state hlayout hclean
  have hcleanP : Clean registers.blockScratch prepared := by
    simpa only [prepared, hprep.1] using hprep.2
  have hp1 : prepared registers.phase1 = false := by
    dsimp only [prepared]
    rw [tBoundaryPrepareState_preservesOutside]
    · exact h1
    · intro hm
      exact (hlayout.phase1_ne_after (by simp [indexedStepAfterPhase1, hm])) rfl
    · intro hm
      exact (hlayout.phase1_ne_after (by simp [indexedStepAfterPhase1, hm])) rfl
  have hpc : prepared registers.control = false := by
    dsimp only [prepared]
    rw [tBoundaryPrepareState_preservesOutside]
    · exact hc
    · intro hm
      exact (hlayout.aux_not_payload hlayout.control_mem_aux (by simp [indexedStepPayload, hm])) rfl
    · intro hm
      exact (hlayout.aux_not_payload hlayout.control_mem_aux (by simp [indexedStepPayload, hm])) rfl
  have hcoefficient : CoefficientPrefixLayout (registers.coefficient window) window.start window.stop := by
    subst window
    exact hlayout.coefficient
  have hlocal : CoefficientPrefixReady (registers.coefficient window) prepared := by
    intro wire hw
    exact hcleanP wire (hlayout.coefficient_scratch_sub_block window wire hw)
  have hidle (mode : RippleMode) (signUpdate : Bool) :
      coefficientPrefixState (registers.coefficient window) window.start window.stop
        mode signUpdate .work2 prepared = prepared := by
    rw [← run_coefficientPrefixUnitary_state (registers.coefficient window)
      mode signUpdate .work2 prepared hcoefficient hlocal]
    exact coefficientPrefixUnitary_idle (registers.coefficient window)
      mode signUpdate .work2 prepared hcoefficient hlocal hpc
  rw [terminal_blockE_reduced registers n window state h1 hc hp hct ht hp1 hpc
    (hidle .sub false) (hidle .add true)]
  exact terminal_boundary_restore_prepare registers n T state hlayout hclean

/-- The literal A--F prefix, through quotient/coefficient arithmetic and post-shift. -/
def indexedStepShiftPrefix (registers : IndexedStepRegisters) (n T : Nat) : Circuit :=
  indexedStepRemainderPrefix registers n T ++
    blockDForward registers (certifiedActiveWindows n T).quotientSwap ++
    blockEForward registers n (certifiedActiveWindows n T).coefficient ++
    blockFForward registers

/-- In the terminal phase after A--C, quotient and coefficient arithmetic are inactive on the
complete state. This extends operational encoding preservation through F; it does not establish
that the phase premises hold on every reachable trace, or cover G--H. -/
theorem indexedStepShiftPrefix_terminal_correct
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state)
    (hencoded : IndexedStepEpochEncoded registers state)
    (hphase1 : run (indexedStepRemainderPrefix registers n T) state registers.phase1 = false)
    (hphase2 : run (indexedStepRemainderPrefix registers n T) state registers.phase2 = false) :
    (indexedStepShiftPrefix registers n T).IsPrefix (indexedStepUnitary registers n T) ∧
      run (indexedStepShiftPrefix registers n T) state =
        run (indexedStepRemainderPrefix registers n T) state ∧
      IndexedStepReady registers (run (indexedStepShiftPrefix registers n T) state) ∧
      IndexedStepEpochEncoded registers (run (indexedStepShiftPrefix registers n T) state) := by
  have hprefix := indexedStepRemainderPrefix_correct registers n T state hlayout hready hencoded
  let afterC := run (indexedStepRemainderPrefix registers n T) state
  have hcontrol : afterC registers.control = false :=
    hprefix.2.1 registers.control (by simp [IndexedStepRegisters.sharedScratch])
  have hD := (blockDForward_correct registers n T (certifiedActiveWindows n T).quotientSwap
    afterC hlayout rfl hprefix.2.1).1
  rw [terminal_blockD_idle registers _ afterC hcontrol hphase1 hphase2] at hD
  have hE := (blockEForward_correct registers n T (certifiedActiveWindows n T).coefficient
    afterC hlayout rfl hprefix.2.1).1
  rw [terminal_blockE_idle registers n T _ afterC hlayout rfl hprefix.2.1 hphase1] at hE
  have hlocal : ShiftReady registers.postShift afterC := by
    intro wire hw
    exact hprefix.2.1 wire (hlayout.sourceScratch_mem_sharedScratch
      (hlayout.postShift_scratch_sub_source wire hw))
  have hF : run (blockFForward registers) afterC = afterC := by
    exact postShiftUnitary_idle registers.postShift afterC hlayout.postShift hlocal hphase1
  have heq : run (indexedStepShiftPrefix registers n T) state = afterC := by
    simp only [indexedStepShiftPrefix, Classical.run_append]
    dsimp only [afterC] at hD hE hF
    rw [hD, hE, hF]
  refine ⟨?_, heq, ?_⟩
  · refine ⟨blockGForward registers ++ blockHForward registers n T, ?_⟩
    simp only [indexedStepShiftPrefix, indexedStepRemainderPrefix,
      indexedStepUnitary, List.append_assoc]
  · rw [heq]
    exact hprefix.2

private theorem endIdle_lengths (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows) (b4 b5 : Nat) (state : BasisState)
    (hc : state registers.control = false) :
    endIterationLengthWords registers n windows b4 b5 state =
      (wireValues registers.lengthT state, wireValues registers.lengthRP state) := by
  have hu (bits : List Bool) :
      endIterationUpperRangeBits false b4 (zeroMapLabels windows.k4 windows.K4) bits =
        (zeroMapLabels windows.k4 windows.K4).map (fun _ => false) := by
    simp [endIterationUpperRangeBits]
  have hl (bits : List Bool) :
      endIterationLowerRangeBits false b5 (zeroMapLabels windows.k5 (windows.K5Decode n)) bits =
        (zeroMapLabels windows.k5 (windows.K5Decode n)).map (fun _ => false) := by
    simp [endIterationLowerRangeBits]
  simp only [endIterationLengthWords, hc, hu, hl]
  rw [highestPositionWordAction_involutive _ _ _ _ _ _ (by simp),
    rightLengthWordAction_involutive _ _ _ _ _ _ _ (by simp)]
private theorem endIdle_state (registers : IndexedStepRegisters) (n T b4 b5 : Nat)
    (state : BasisState) (hc : state registers.control = false) :
    endIterationForwardState registers n T b4 b5 state = state := by
  have hl := endIdle_lengths (registers.endIteration n T) n (endIterationWindowsAt n T)
    b4 b5 state hc
  rw [endIterationForwardState, endIterationForwardBits]
  rw [hl]
  simp only [endIterationSwappedWorkWords, IndexedStepRegisters.endIteration, hc, Bool.false_eq_true,
    ↓reduceIte, endIterationMutableWires]
  simpa only [wireValues, List.map_append] using
    terminal_write_read (registers.work1 ++ registers.work2 ++ registers.lengthT ++ registers.lengthRPrime) state
private theorem endIdle_toggle_twice (wire : Wire) (state : BasisState) :
    (state[wire ↦ !state wire])[wire ↦ !(state[wire ↦ !state wire]) wire] = state := by
  funext w
  by_cases h : w = wire
  · subst w; simp [upd]
  · simp [upd, h]

private theorem endIdle_and_twice (first second target : Wire) (state : BasisState)
    (hf : first ≠ target) (hs : second ≠ target) :
    andXorWireState first second target (andXorWireState first second target state) = state := by
  funext w
  by_cases h : w = target
  · subst w; simp [andXorWireState, upd, hf, hs]
  · simp [andXorWireState, upd, h]

private theorem endIdle_andList_twice (wires : List Wire) (target : Wire) (state : BasisState)
    (hne : target ∉ wires) :
    andListXorState wires target (andListXorState wires target state) = state := by
  have hm : wireAnd wires (andListXorState wires target state) = wireAnd wires state := by
    apply wireAnd_congr
    intro wire hw
    have h : wire ≠ target := by intro he; subst wire; exact hne hw
    simp [andListXorState, upd, h]
  funext w
  by_cases h : w = target
  · subst w
    rw [andListXorState]
    simp only [upd]
    rw [hm]
    simp [andListXorState, upd]
  · simp [andListXorState, upd, h]
private theorem endIdle_block (registers : IndexedStepRegisters) (n T b4 b5 : Nat)
    (state : BasisState)
    (hq : registers.sourceScratch.getD 0 0 ∉ registers.lengthQ)
    (hs : registers.sourceScratch.getD 1 0 ∉ registers.lengthS ++ [registers.shiftEpoch])
    (hqc : registers.sourceScratch.getD 0 0 ≠ registers.control)
    (hsc : registers.sourceScratch.getD 1 0 ≠ registers.control)
    (hc : (blockHEndInputState registers state) registers.control = false) :
    blockHForwardState registers n T b4 b5 state = state := by
  by_cases hT : T % 4 = 0
  · simp only [blockHForwardState, hT, ↓reduceIte]
    rw [endIdle_state registers n T b4 b5 _ hc]
    rw [terminal_xor_idle registers.control registers.iter _ hc]
    simp only [blockHEndInputState, blockHZeroSState, blockHBeforeSState, blockHZeroQState]
    rw [endIdle_and_twice _ _ _ _ hqc hsc]
    rw [endIdle_toggle_twice]
    rw [endIdle_andList_twice _ _ _ hs]
    rw [endIdle_toggle_twice]
    exact endIdle_andList_twice _ _ state hq
  · simp only [blockHForwardState, hT, ↓reduceIte]

private theorem endIdle_update_read (state : BasisState) (wire : Wire) :
    state[wire ↦ state wire] = state := by
  funext w
  by_cases h : w = wire
  · subst w; simp [upd]
  · simp [upd, h]
private theorem endIdle_wireAnd_append (wires : List Wire) (wire : Wire) (state : BasisState) :
    wireAnd (wires ++ [wire]) state = (wireAnd wires state && state wire) := by
  induction wires with
  | nil => simp [wireAnd]
  | cons w ws ih => simp only [List.cons_append, wireAnd, ih, Bool.and_assoc]
private theorem endIdle_wireAnd_update (wires : List Wire) (target : Wire)
    (bit : Bool) (state : BasisState) (hn : target ∉ wires) :
    wireAnd wires state[target ↦ bit] = wireAnd wires state := by
  apply wireAnd_congr
  intro wire hw
  have h : wire ≠ target := by intro he; subst wire; exact hn hw
  simp [upd, h]
private theorem endIdle_input_control (registers : IndexedStepRegisters) (state : BasisState)
    (hc : state registers.control = false)
    (hscratch : state (registers.sourceScratch.getD 1 0) = false)
    (hcq : registers.control ≠ registers.sourceScratch.getD 0 0)
    (hsq : registers.sourceScratch.getD 1 0 ≠ registers.sourceScratch.getD 0 0)
    (heq : registers.shiftEpoch ≠ registers.sourceScratch.getD 0 0)
    (hqS : registers.sourceScratch.getD 0 0 ∉ registers.lengthS)
    (heS : registers.shiftEpoch ∉ registers.lengthS)
    (hz : (wireAnd registers.lengthS state && !state registers.shiftEpoch) = false) :
    (blockHEndInputState registers state) registers.control = false := by
  have hpred : wireAnd (registers.lengthS ++ [registers.shiftEpoch])
      (blockHBeforeSState registers state) = false := by
    rw [endIdle_wireAnd_append]
    simp only [blockHBeforeSState, blockHZeroQState, andListXorState]
    rw [endIdle_wireAnd_update _ _ _ _ heS, endIdle_wireAnd_update _ _ _ _ hqS]
    simpa only [upd, heq, ↓reduceIte] using hz
  have hzeroS : blockHZeroSState registers state = blockHBeforeSState registers state := by
    rw [blockHZeroSState, andListXorState]
    rw [hpred]
    simp only [Bool.xor_false, endIdle_update_read]
  have hsQ : (blockHZeroQState registers state) (registers.sourceScratch.getD 1 0) = false := by
    simp only [blockHZeroQState, andListXorState, upd, hsq, ↓reduceIte, hscratch]
  rw [blockHEndInputState, hzeroS, blockHBeforeSState, endIdle_toggle_twice]
  simp only [andXorWireState, hsQ, Bool.and_false, Bool.xor_false, endIdle_update_read]
  simp only [blockHZeroQState, andListXorState, upd, hcq, ↓reduceIte, hc]
private theorem phaseIdle (registers : PhaseUpdateRegisters) (epoch : Wire)
    (state : BasisState) (hlayout : PhaseUpdateEpochLayout registers epoch)
    (hrp : wireAnd registers.lengthRPrime state = true)
    (hs : (wireAnd registers.lengthS state && !state epoch) = false) :
    phaseUpdateEpochState registers epoch state = state := by
  rw [phaseUpdateEpochState_spec registers epoch state hlayout]
  simp only [hrp, hs, Bool.not_true, Bool.and_false, Bool.false_and,
    Bool.xor_false, endIdle_update_read]
private theorem terminal_blockH_idle (registers : IndexedStepRegisters) (n T b4 b5 : Nat)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state)
    (hz : (wireAnd registers.lengthS state && !state registers.shiftEpoch) = false) :
    blockHForwardState registers n T b4 b5 state = state := by
  have hqmem : registers.sourceScratch.getD 0 0 ∈ registers.sourceScratch :=
    indexedStep_getD_mem _ _ _ (by rw [hlayout.sourceScratch_length]; decide)
  have hsmem : registers.sourceScratch.getD 1 0 ∈ registers.sourceScratch :=
    indexedStep_getD_mem _ _ _ (by rw [hlayout.sourceScratch_length]; decide)
  have hqaux := hlayout.sourceScratch_mem_aux hqmem
  have hsaux := hlayout.sourceScratch_mem_aux hsmem
  have hcq : registers.control ≠ registers.sourceScratch.getD 0 0 := by
    intro he
    exact hlayout.control_not_sourceScratch (he ▸ hqmem)
  have hcs : registers.control ≠ registers.sourceScratch.getD 1 0 := by
    intro he
    exact hlayout.control_not_sourceScratch (he ▸ hsmem)
  have heq : registers.shiftEpoch ≠ registers.sourceScratch.getD 0 0 := by
    intro he
    exact hlayout.shiftEpoch_not_sourceScratch (he ▸ hqmem)
  have hes : registers.shiftEpoch ≠ registers.sourceScratch.getD 1 0 := by
    intro he
    exact hlayout.shiftEpoch_not_sourceScratch (he ▸ hsmem)
  have hnodup : (registers.sourceScratch.getD 0 0 :: registers.sourceScratch.getD 1 0 ::
      registers.sourceScratch.drop 2).Nodup := by
    rw [hlayout.sourceScratch_view2]
    exact hlayout.sourceScratch_nodup
  have hsq : registers.sourceScratch.getD 1 0 ≠ registers.sourceScratch.getD 0 0 := by
    intro he
    exact (List.nodup_cons.mp hnodup).1 (by simp only [List.mem_cons]; exact Or.inl he.symm)
  have hqQ : registers.sourceScratch.getD 0 0 ∉ registers.lengthQ := by
    intro hm
    exact (hlayout.aux_not_payload hqaux (by simp only [indexedStepPayload, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto)) rfl
  have hqS : registers.sourceScratch.getD 0 0 ∉ registers.lengthS := by
    intro hm
    exact (hlayout.aux_not_payload hqaux (by simp only [indexedStepPayload, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto)) rfl
  have hsS : registers.sourceScratch.getD 1 0 ∉ registers.lengthS ++ [registers.shiftEpoch] := by
    simp only [List.mem_append, List.mem_singleton, not_or]
    refine ⟨?_, Ne.symm hes⟩
    intro hm
    exact (hlayout.aux_not_payload hsaux (by simp only [indexedStepPayload, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto)) rfl
  have hc := endIdle_input_control registers state
    (hready registers.control (by simp [IndexedStepRegisters.sharedScratch]))
    (hready _ (hlayout.sourceScratch_mem_sharedScratch hsmem))
    hcq hsq heq hqS hlayout.shiftEpoch_not_lengthS hz
  exact endIdle_block registers n T b4 b5 state hqQ hsS (Ne.symm hcq) (Ne.symm hcs) hc

private theorem terminal_remainder_state
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state)
    (hencoded : IndexedStepEpochEncoded registers state) :
    run (indexedStepRemainderPrefix registers n T) state =
      blockCForwardState registers (blockBForwardState registers n
        (certifiedActiveWindows n T).remainder (blockAForwardState registers state)) := by
  have hA := blockAForward_correct registers n T state hlayout hready
  have hborrow := blockAForward_borrowedReady registers n T state hlayout hready hencoded
  rw [hA.1] at hborrow
  have hB := blockBForward_correct registers n T (certifiedActiveWindows n T).remainder
    (blockAForwardState registers state) hlayout rfl hborrow
  have hborrowB := hB.2
  rw [hB.1] at hborrowB
  have hC := blockCForward_correct registers n T _ hlayout hborrowB
  simp only [indexedStepRemainderPrefix, Classical.run_append]
  rw [hA.1, hB.1, hC.1]

/-- On a routed step whose A--C output has phase 00, terminal remainder length and nonzero
extended shift counter, every remaining block D--H is inactive on the complete state. The phase
and counter conditions are premises here; their preservation along reachable traces is separate. -/
theorem indexedStepUnitary_terminal_correct
    (registers : IndexedStepRegisters) (n T boundary4 boundary5 : Nat)
    (hboundary4 : (endIterationWindowsAt n T).k4 ≤ boundary4 ∧
      boundary4 ≤ (endIterationWindowsAt n T).K4)
    (hboundary5 : (endIterationWindowsAt n T).k5 ≤ boundary5 ∧
      boundary5 ≤ (endIterationWindowsAt n T).K5Decode n)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state)
    (hencoded : IndexedStepEpochEncoded registers state)
    (hroutes : T % 4 = 0 → indexedStepEndRoutes registers n T state = (boundary4, boundary5))
    (hphase1 : run (indexedStepRemainderPrefix registers n T) state registers.phase1 = false)
    (hphase2 : run (indexedStepRemainderPrefix registers n T) state registers.phase2 = false)
    (hrp : wireAnd registers.lengthRPrime (run (indexedStepRemainderPrefix registers n T) state) = true)
    (hs : (wireAnd registers.lengthS (run (indexedStepRemainderPrefix registers n T) state) &&
      !(run (indexedStepRemainderPrefix registers n T) state registers.shiftEpoch)) = false) :
    run (indexedStepUnitary registers n T) state = run (indexedStepRemainderPrefix registers n T) state ∧
      IndexedStepReady registers (run (indexedStepUnitary registers n T) state) ∧
      IndexedStepEpochEncoded registers (run (indexedStepUnitary registers n T) state) := by
  have hprefix := indexedStepRemainderPrefix_correct registers n T state hlayout hready hencoded
  let afterC := run (indexedStepRemainderPrefix registers n T) state
  have hcontrol : afterC registers.control = false :=
    hprefix.2.1 registers.control (by simp [IndexedStepRegisters.sharedScratch])
  have hD := terminal_blockD_idle registers (certifiedActiveWindows n T).quotientSwap
    afterC hcontrol hphase1 hphase2
  have hE := terminal_blockE_idle registers n T (certifiedActiveWindows n T).coefficient
    afterC hlayout rfl hprefix.2.1 hphase1
  have hlocal : ShiftReady registers.postShift afterC := by
    intro wire hw
    exact hprefix.2.1 wire (hlayout.sourceScratch_mem_sharedScratch
      (hlayout.postShift_scratch_sub_source wire hw))
  have hF : blockFForwardState registers afterC = afterC := by
    rw [blockFForwardState, ← run_postShiftUnitary registers.postShift afterC hlayout.postShift hlocal]
    exact postShiftUnitary_idle registers.postShift afterC hlayout.postShift hlocal hphase1
  have hG : blockGForwardState registers afterC = afterC :=
    phaseIdle registers.phaseUpdate registers.shiftEpoch afterC hlayout.phaseUpdate hrp hs
  have hbefore : indexedStepBeforeEndState registers n T state = afterC := by
    rw [indexedStepBeforeEndState, ← terminal_remainder_state registers n T state hlayout hready hencoded]
    dsimp only [afterC] at hD hE hF hG
    rw [hD, hE, hF, hG]
  have heq : run (indexedStepUnitary registers n T) state = afterC := by
    rw [(indexedStepUnitary_correct registers n T boundary4 boundary5 hboundary4 hboundary5
      state hlayout hready hencoded hroutes).1, indexedStepForwardState, hbefore]
    exact terminal_blockH_idle registers n T boundary4 boundary5 afterC hlayout hprefix.2.1 hs
  refine ⟨heq, ?_⟩
  rw [heq]
  exact hprefix.2

private theorem terminal_rControl_idle (conditions : List Wire) (value : Nat)
    (control : Wire) (lengthRP : List Wire) (zeroWire : Wire) (scratch : List Wire)
    (state : BasisState) (hlayout : RControlNonterminalLayout conditions control lengthRP zeroWire scratch)
    (hrp : wireAnd lengthRP state = true) :
    rControlState conditions value control lengthRP zeroWire state = state := by
  have hn : (conditions ++ [zeroWire]).Nodup :=
    (List.nodup_append.mp hlayout.conditionLayout.2).1
  have hzeroWire : zeroWire ∉ conditions := by
    intro hm
    exact (List.nodup_append.mp hn).2.2 zeroWire hm zeroWire (by simp) rfl
  rw [rControlState, rControlNonterminalPredicate_eq _ _ _ _ _ hzeroWire]
  simp only [hrp, Bool.not_true, Bool.and_false, Bool.xor_false, endIdle_update_read]

private theorem terminal_restoreControl_idle (registers : IndexedStepRegisters) (n T : Nat)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hrp : wireAnd registers.lengthRPrime state = true) :
    remainderRestoreControlState registers state = state := by
  have hts : registers.terminal ∈ registers.sourceScratch := by rw [← hlayout.scratch_view]; simp
  have hta := hlayout.sourceScratch_mem_aux hts
  have hmarked : wireAnd registers.lengthRPrime
      (andXorWireState registers.phase2 registers.sign registers.terminal state) = true := by
    rw [← hrp]
    apply wireAnd_congr
    intro wire hw
    exact andXorWireState_preserves _ _ _ _ (Ne.symm
      (hlayout.aux_not_payload hta (by simp [indexedStepPayload, hw])))
  have hp := hlayout.remainderRestoreCCX
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hp
  rw [remainderRestoreControlState,
    terminal_rControl_idle _ 0 _ _ _ _ _ hlayout.remainderRestore hmarked]
  exact endIdle_and_twice _ _ _ state hp.1.2 hp.2.1

private theorem terminal_blockB_idle (registers : IndexedStepRegisters) (n T : Nat)
    (window : ActiveWindow) (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder)
    (hready : IndexedStepBorrowedReady registers state)
    (hrp : wireAnd registers.lengthRPrime state = true) :
    blockBForwardState registers n window state = state := by
  have hc : state registers.control = false := hready _ hlayout.control_mem_aux
  have hlocal : IntervalReady (registers.remainder window) state := by
    intro wire hw
    exact hready wire (hlayout.remainder_scratch_sub_aux window wire hw)
  have hinterval : IntervalLayout (registers.remainder window) window.start window.stop .work1 := by
    subst window
    exact hlayout.remainder
  have hi (mode : RippleMode) (signUpdate : Bool) :
      intervalAddSubState (registers.remainder window) n window.start window.stop mode signUpdate .work1 state = state := by
    rw [← run_intervalAddSubUnitary_state (registers.remainder window) n window.start window.stop
      mode signUpdate .work1 state hinterval hlocal]
    exact intervalAddSubUnitary_idle (registers.remainder window) n window.start window.stop
      mode signUpdate .work1 state hinterval hlocal hc
  have hsub := terminal_rControl_idle _ 0 _ _ _ _ state hlayout.remainderSub hrp
  have hphase := terminal_rControl_idle _ 2 _ _ _ _ state hlayout.remainderPhase2 hrp
  have hrestore := terminal_restoreControl_idle registers n T state hlayout hrp
  have hx := terminal_xor_idle registers.control registers.sign state hc
  simp only [blockBForwardState, blockB1ForwardState, hsub, hi, blockB2State, hphase, hx,
    blockB3ForwardState, hrestore]

private theorem terminal_padding_condition_frame (registers : IndexedStepRegisters) (n T : Nat)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hw : wire ∈ terminalConditionWires registers) :
    terminalPaddingForwardState registers.terminalPadding state wire = state wire := by
  simp only [terminalConditionWires, List.mem_cons] at hw
  rcases hw with rfl | hw
  · exact terminalPaddingForwardState_preserves _ _ hlayout.phase1_not_work2
      hlayout.phase1_not_lengthS hlayout.phase1_ne_shiftEpoch
  · exact terminalPaddingForwardState_preserves _ _ (hlayout.lengthRPrime_not_work2 hw)
      (hlayout.lengthRPrime_not_lengthS hw) (hlayout.lengthRPrime_ne_shiftEpoch hw)

private theorem terminal_blockA_padding (registers : IndexedStepRegisters) (n T : Nat)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state) (hphase : state registers.phase1 = false)
    (hmatch : registerMatches (terminalConditionWires registers)
      (terminalConditionValue registers) state = true) :
    blockAForwardState registers state =
      matchXorState (terminalConditionWires registers) (terminalConditionValue registers)
        registers.terminal (terminalEpochSpillState registers.terminal registers.shiftEpoch
          registers.quotientLow (terminalPaddingForwardState registers.terminalPadding
            (matchXorState (terminalConditionWires registers) (terminalConditionValue registers)
              registers.terminal state))) := by
  let marked := matchXorState (terminalConditionWires registers)
    (terminalConditionValue registers) registers.terminal state
  let padded := terminalPaddingForwardState registers.terminalPadding marked
  let disabled := xorWireState registers.terminal registers.phase1 padded
  have ht : state registers.terminal = false := hready _
    (hlayout.sourceScratch_mem_sharedScratch (by rw [← hlayout.scratch_view]; simp))
  have htp : registers.terminal ≠ registers.phase1 := by
    intro he
    exact hlayout.terminal_not_condition (by simp [terminalConditionWires, he])
  have hmt : marked registers.terminal = true := by simp [marked, matchXorState, ht, hmatch]
  have hpt : padded registers.terminal = true := by
    exact (terminalPaddingForwardState_terminal registers n T marked hlayout).trans hmt
  have hpp : padded registers.phase1 = false := by
    dsimp only [padded]
    rw [terminal_padding_condition_frame registers n T marked hlayout
      (by simp [terminalConditionWires])]
    simp [marked, matchXorState, upd, Ne.symm htp, hphase]
  have hblock : Clean registers.blockScratch state :=
    clean_mono hready (fun _ hw ↦ hlayout.blockScratch_mem_sharedScratch hw)
  have hmarkedBlock : Clean registers.blockScratch marked := by
    simpa [marked, matchXorState] using clean_upd_not_mem hblock hlayout.terminal_not_blockScratch
  have hpReady := clean_mono hmarkedBlock hlayout.terminalPadding_scratch_sub_block
  have hpRun : run (terminalPaddingForward registers.terminalPadding) marked = padded :=
    run_terminalPaddingForward _ _ hlayout.terminalPadding hpReady
  have hpLocal : Clean registers.terminalPadding.scratch padded := by
    rw [← hpRun]
    exact terminalPaddingForward_clean _ _ hlayout.terminalPadding hpReady
  have hpBlock : Clean registers.blockScratch padded := by
    rw [← hpRun]
    exact clean_after_local_circuit hmarkedBlock (by simpa only [hpRun] using hpLocal)
      (terminalPaddingForward_usesOnly _) hlayout.terminalPadding_support_intersection
  have hdBlock : Clean registers.blockScratch disabled := by
    simpa [disabled, xorWireState] using clean_upd_not_mem hpBlock hlayout.phase1_not_blockScratch
  have hdReady := clean_mono hdBlock hlayout.preShift_scratch_sub_block
  have hdPhase : disabled registers.preShift.phase1 = true := by
    change disabled registers.phase1 = true
    simp [disabled, xorWireState, hpp, hpt]
  have hi : preShiftState registers.preShift disabled = disabled := by
    rw [← run_preShiftUnitary _ _ hlayout.preShift hdReady]
    exact preShiftUnitary_idle _ _ hlayout.preShift hdReady hdPhase
  have hcancel : xorWireState registers.terminal registers.phase1 disabled = padded := by
    funext wire
    by_cases hw : wire = registers.phase1
    · subst wire
      simp [disabled, xorWireState, upd, htp]
    · simp [disabled, xorWireState, upd, hw]
  change matchXorState _ _ _ (terminalEpochSpillState _ _ _
    (xorWireState _ _ (preShiftState registers.preShift disabled))) = _
  rw [hi, hcancel]

private theorem terminal_epoch_cancel (registers : IndexedStepRegisters) (n T : Nat)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T) :
    terminalEpochRestoreState registers.terminal registers.shiftEpoch registers.quotientLow
      (terminalEpochSpillState registers.terminal registers.shiftEpoch registers.quotientLow state) = state := by
  rw [← run_terminalEpochRestoreState _ _ _ _ hlayout.terminalEpoch,
    ← run_terminalEpochSpillState _ _ _ _ hlayout.terminalEpoch]
  exact run_terminalEpochRestore_after_spill _ _ _ _ hlayout.terminalEpoch

private theorem terminal_matches_ones (wires : List Wire) (value bit : Nat) (state : BasisState)
    (hbits : ∀ i, bit ≤ i → i < bit + wires.length → value.testBit i = true) :
    registerMatchesFrom wires value bit state = wireAnd wires state := by
  induction wires generalizing bit with
  | nil => rfl
  | cons wire wires ih =>
    have hb := hbits bit (by omega) (by simp)
    simp only [registerMatchesFrom, wireAnd, hb, Bool.decide_eq_true]
    rw [ih (bit + 1) (by intro i hi hj; apply hbits i <;> simp_all <;> omega)]
private theorem terminal_detection (phase : Wire) (wires : List Wire) (state : BasisState) :
    registerMatches (phase :: wires) (2 ^ (wires.length + 1) - 2) state =
      (!state phase && wireAnd wires state) := by
  have hpow : 1 < 2 ^ (wires.length + 1) := by
    rw [Nat.pow_succ]; have := Nat.two_pow_pos wires.length; omega
  have hb (i : Nat) : (2 ^ (wires.length + 1) - 2).testBit i =
      (decide (i < wires.length + 1) && !Nat.testBit 1 i) :=
    Nat.testBit_two_pow_sub_succ hpow i
  simp only [registerMatches, registerMatchesFrom]
  rw [terminal_matches_ones wires _ 1 state (by
    intro i hi hj
    rw [hb]
    have hbit : Nat.testBit 1 i = false := by
      change Nat.testBit (2^0) i = false
      simp only [Nat.testBit_two_pow, show (0 = i) = False by simp [show 0 ≠ i by omega], decide_false]
    simp [show i < wires.length + 1 by omega, hbit])]
  rw [hb 0]
  cases state phase <;> simp

/-- On a terminal-marked input, the actual A--C circuit reduces to the terminal padding
state with its marker cleaned. Phase1=false and the all-ones remainder-length sentinel
compute the terminal predicate; their preservation on reachable traces is separate. -/
theorem indexedStepRemainderPrefix_terminal_padding
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T) (hready : IndexedStepReady registers state)
    (hencoded : IndexedStepEpochEncoded registers state)
    (hphase : state registers.phase1 = false)
    (hrp : wireAnd registers.lengthRPrime state = true) :
    run (indexedStepRemainderPrefix registers n T) state =
      (terminalPaddingForwardState registers.terminalPadding
        state[registers.terminal ↦ true])[registers.terminal ↦ false] := by
  have hmatch : registerMatches (registers.phase1 :: registers.lengthRPrime)
      (2 ^ (registers.lengthRPrime.length + 1) - 2) state = true := by
    rw [terminal_detection, hphase, hrp]
    rfl
  let marked := matchXorState (terminalConditionWires registers)
    (terminalConditionValue registers) registers.terminal state
  let padded := terminalPaddingForwardState registers.terminalPadding marked
  let spilled := terminalEpochSpillState registers.terminal registers.shiftEpoch
    registers.quotientLow padded
  have ha := terminal_blockA_padding registers n T state hlayout hready hphase hmatch
  have hframe (wire : Wire) (hw : wire ∈ terminalConditionWires registers) :
      padded wire = state wire := by
    dsimp only [padded]
    rw [terminal_padding_condition_frame registers n T marked hlayout hw]
    have hn : wire ≠ registers.terminal := by
      intro he; subst wire; exact hlayout.terminal_not_condition hw
    simp [marked, matchXorState, upd, hn]
  have htq : registers.terminal ≠ registers.quotientLow := by
    have h := hlayout.terminalEpoch
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    exact h.1.2
  have hspilled (wire : Wire) (hw : wire ∈ terminalConditionWires registers) :
      spilled wire = state wire := by
    have he : wire ≠ registers.shiftEpoch := by
      intro he; subst wire; exact hlayout.shiftEpoch_not_condition hw
    have hq : wire ≠ registers.quotientLow := by
      intro he; subst wire; exact hlayout.quotientLow_not_condition hw
    exact (terminalEpochSpillState_preserves _ _ _ _ he hq htq).trans (hframe wire hw)
  have har : wireAnd registers.lengthRPrime (blockAForwardState registers state) = true := by
    rw [← hrp]
    apply wireAnd_congr
    intro wire hw
    have hcond : wire ∈ terminalConditionWires registers := by simp [terminalConditionWires, hw]
    have hn : wire ≠ registers.terminal := by
      intro he; subst wire; exact hlayout.terminal_not_condition hcond
    rw [ha]
    change matchXorState _ _ _ spilled wire = state wire
    simpa [matchXorState, upd, hn] using hspilled wire hcond
  have hborrow := blockAForward_borrowedReady registers n T state hlayout hready hencoded
  rw [(blockAForward_correct registers n T state hlayout hready).1] at hborrow
  rw [terminal_remainder_state registers n T state hlayout hready hencoded,
    terminal_blockB_idle registers n T _ _ hlayout rfl hborrow har, ha]
  change matchXorState _ _ _ (terminalEpochRestoreState _ _ _
    (matchXorState _ _ _ (matchXorState _ _ _ spilled))) = _
  rw [terminal_match_twice _ _ _ spilled hlayout.terminal_not_condition]
  change matchXorState _ _ _ (terminalEpochRestoreState _ _ _
    (terminalEpochSpillState _ _ _ padded)) = _
  rw [terminal_epoch_cancel registers n T padded hlayout]
  have ht : state registers.terminal = false := hready _
    (hlayout.sourceScratch_mem_sharedScratch (by rw [← hlayout.scratch_view]; simp))
  have hm : marked = state[registers.terminal ↦ true] := by
    simp only [marked, matchXorState, terminalConditionWires, terminalConditionValue, ht, hmatch,
      Bool.false_xor]
  have hp : registerMatches (terminalConditionWires registers)
      (terminalConditionValue registers) padded = true :=
    (registerMatches_congr _ _ _ _ hframe).trans hmatch
  have hpt : padded registers.terminal = true := by
    dsimp only [padded]
    rw [terminalPaddingForwardState_terminal registers n T marked hlayout]
    simp [hm]
  simp only [matchXorState, hp, hpt, Bool.xor_self]
  rw [show padded = terminalPaddingForwardState registers.terminalPadding
    state[registers.terminal ↦ true] by rw [← hm]]

private theorem terminal_padding_clean_frame (registers : IndexedStepRegisters)
    (state : BasisState)
    {wire : Wire} (ht : wire ≠ registers.terminal)
    (hw : wire ∉ registers.work2) (hs : wire ∉ registers.lengthS)
    (he : wire ≠ registers.shiftEpoch) :
    (terminalPaddingForwardState registers.terminalPadding
      state[registers.terminal ↦ true])[registers.terminal ↦ false] wire = state wire := by
  rw [upd_other _ _ _ ht, terminalPaddingForwardState_preserves _ _ hw hs he,
    upd_other _ _ _ ht]

/-- A routed terminal step performs only terminal padding, with clean scratch and preserved
entry encoding. The nonzero extended-counter premise is on the explicit padding result;
reachable traces must still establish that bound. -/
theorem indexedStepUnitary_terminal_padding
    (registers : IndexedStepRegisters) (n T boundary4 boundary5 : Nat)
    (hboundary4 : (endIterationWindowsAt n T).k4 ≤ boundary4 ∧
      boundary4 ≤ (endIterationWindowsAt n T).K4)
    (hboundary5 : (endIterationWindowsAt n T).k5 ≤ boundary5 ∧
      boundary5 ≤ (endIterationWindowsAt n T).K5Decode n)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state)
    (hencoded : IndexedStepEpochEncoded registers state)
    (hroutes : T % 4 = 0 → indexedStepEndRoutes registers n T state = (boundary4, boundary5))
    (hphase1 : state registers.phase1 = false)
    (hphase2 : state registers.phase2 = false)
    (hrp : wireAnd registers.lengthRPrime state = true)
    (hs : let padded := (terminalPaddingForwardState registers.terminalPadding
        state[registers.terminal ↦ true])[registers.terminal ↦ false]
      (wireAnd registers.lengthS padded && !padded registers.shiftEpoch) = false) :
    run (indexedStepUnitary registers n T) state =
      (terminalPaddingForwardState registers.terminalPadding
        state[registers.terminal ↦ true])[registers.terminal ↦ false] ∧
    IndexedStepReady registers
      (run (indexedStepUnitary registers n T) state) ∧
    IndexedStepEpochEncoded registers
      (run (indexedStepUnitary registers n T) state) := by
  let padded := (terminalPaddingForwardState registers.terminalPadding
    state[registers.terminal ↦ true])[registers.terminal ↦ false]
  have hp := indexedStepRemainderPrefix_terminal_padding registers n T state hlayout hready
    hencoded hphase1 hrp
  have hf (wire : Wire) (hw : wire ∈ terminalConditionWires registers) :
      padded wire = state wire := by
    have ht : wire ≠ registers.terminal := by
      intro he; subst wire; exact hlayout.terminal_not_condition hw
    dsimp only [padded]
    rw [upd_other _ _ _ ht, terminal_padding_condition_frame registers n T _ hlayout hw,
      upd_other _ _ _ ht]
  have hp1 : padded registers.phase1 = false :=
    (hf _ (by simp [terminalConditionWires])).trans hphase1
  have hp2 : padded registers.phase2 = false := by
    apply Eq.trans ?_ hphase2
    apply terminal_padding_clean_frame registers state
    · exact hlayout.phase2_ne_after (by simp [indexedStepAfterPhase2,
        hlayout.sourceScratch_mem_aux (show registers.terminal ∈ registers.sourceScratch by
          rw [← hlayout.scratch_view]; simp)])
    · intro hm; exact hlayout.phase2_ne_after (by simp [indexedStepAfterPhase2, hm]) rfl
    · intro hm; exact hlayout.phase2_ne_after (by simp [indexedStepAfterPhase2, hm]) rfl
    · exact hlayout.phase2_ne_after (by simp [indexedStepAfterPhase2, hlayout.shiftEpoch_mem_aux])
  have hpr : wireAnd registers.lengthRPrime padded = true := by
    rw [← hrp]
    exact wireAnd_congr _ _ _ (fun wire hw ↦ hf wire (by simp [terminalConditionWires, hw]))
  have hfull := indexedStepUnitary_terminal_correct registers n T boundary4 boundary5
    hboundary4 hboundary5 state hlayout hready hencoded hroutes
    (by rw [hp]; exact hp1) (by rw [hp]; exact hp2)
    (by rw [hp]; exact hpr) (by rw [hp]; exact hs)
  exact ⟨hfull.1.trans hp, hfull.2⟩


/-- A terminal routed step has the explicit padding transition under an input-side modular
bound on its extended counter. No condition on an intermediate circuit state is required. -/
theorem indexedStepUnitary_terminal_counter_correct
    (registers : IndexedStepRegisters) (n T boundary4 boundary5 : Nat)
    (hboundary4 : (endIterationWindowsAt n T).k4 ≤ boundary4 ∧
      boundary4 ≤ (endIterationWindowsAt n T).K4)
    (hboundary5 : (endIterationWindowsAt n T).k5 ≤ boundary5 ∧
      boundary5 ≤ (endIterationWindowsAt n T).K5Decode n)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state)
    (hencoded : IndexedStepEpochEncoded registers state)
    (hroutes : T % 4 = 0 → indexedStepEndRoutes registers n T state = (boundary4, boundary5))
    (hphase1 : state registers.phase1 = false)
    (hphase2 : state registers.phase2 = false)
    (hrp : wireAnd registers.lengthRPrime state = true)
    (hbound : (1 + (boolWordToNat (wireValues registers.lengthS state) +
        2^registers.lengthS.length * (state registers.shiftEpoch).toNat)) %
          2^(registers.lengthS.length + 1) ≠ 2^registers.lengthS.length - 1) :
    run (indexedStepUnitary registers n T) state =
      (terminalPaddingForwardState registers.terminalPadding
        state[registers.terminal ↦ true])[registers.terminal ↦ false] ∧
    IndexedStepReady registers (run (indexedStepUnitary registers n T) state) ∧
    IndexedStepEpochEncoded registers (run (indexedStepUnitary registers n T) state) := by
  have hta := hlayout.sourceScratch_mem_aux
    (show registers.terminal ∈ registers.sourceScratch by rw [← hlayout.scratch_view]; simp)
  have htS : registers.terminal ∉ registers.lengthS := by
    intro hm
    exact hlayout.aux_not_payload hta (by simp [indexedStepPayload, hm]) rfl
  have he : registers.shiftEpoch ≠ registers.terminal := by
    have h := hlayout.terminalEpoch
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    exact Ne.symm h.1.1
  have hvalues : wireValues registers.lengthS state[registers.terminal ↦ true] =
      wireValues registers.lengthS state := by
    apply List.map_congr_left
    intro wire hw
    exact upd_other _ _ _ (by intro h; subst wire; exact htS hw)
  have hmarked : (1 + (boolWordToNat
      (wireValues registers.terminalPadding.lengthS state[registers.terminal ↦ true]) +
      2^registers.terminalPadding.lengthS.length *
        (state[registers.terminal ↦ true] registers.terminalPadding.shiftEpoch).toNat)) %
      2^(registers.terminalPadding.lengthS.length + 1) ≠
        2^registers.terminalPadding.lengthS.length - 1 := by
    change (1 + (boolWordToNat (wireValues registers.lengthS state[registers.terminal ↦ true]) +
      2^registers.lengthS.length * (state[registers.terminal ↦ true] registers.shiftEpoch).toNat)) %
      2^(registers.lengthS.length + 1) ≠ 2^registers.lengthS.length - 1
    rw [hvalues, upd_other _ _ _ he]
    exact hbound
  have hs := terminalPaddingForwardState_counter_nonzero registers.terminalPadding
    state[registers.terminal ↦ true] hlayout.terminalPadding (by simp [IndexedStepRegisters.terminalPadding]) hmarked
  apply indexedStepUnitary_terminal_padding registers n T boundary4 boundary5 hboundary4 hboundary5
    state hlayout hready hencoded hroutes hphase1 hphase2 hrp
  dsimp only
  rw [upd_other _ _ _ he]
  rw [show wireAnd registers.lengthS
      ((terminalPaddingForwardState registers.terminalPadding state[registers.terminal ↦ true])
        [registers.terminal ↦ false]) =
      wireAnd registers.lengthS
        (terminalPaddingForwardState registers.terminalPadding state[registers.terminal ↦ true]) by
    apply wireAnd_congr
    intro wire hw
    exact upd_other _ _ _ (by intro h; subst wire; exact htS hw)]
  exact hs


private theorem active_shift_prefix (registers : IndexedStepRegisters) (n T : Nat)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state) (hencoded : IndexedStepEpochEncoded registers state) :
    blockGForwardState registers (run (indexedStepShiftPrefix registers n T) state) =
      indexedStepBeforeEndState registers n T state ∧
    IndexedStepReady registers (run (indexedStepShiftPrefix registers n T) state) := by
  let afterC := run (indexedStepRemainderPrefix registers n T) state
  have hc := (indexedStepRemainderPrefix_correct registers n T state hlayout hready hencoded).2.1
  have hd := blockDForward_correct registers n T _ afterC hlayout rfl hc
  have hdReady := hd.2
  rw [hd.1] at hdReady
  have he := blockEForward_correct registers n T _ _ hlayout rfl hdReady
  have heReady := he.2
  rw [he.1] at heReady
  have hf := blockFForward_correct registers n T _ hlayout heReady
  constructor
  · simp only [indexedStepShiftPrefix, Classical.run_append]
    rw [hd.1, he.1, hf.1]
    dsimp only [afterC]
    rw [terminal_remainder_state registers n T state hlayout hready hencoded]
    rfl
  · simp only [indexedStepShiftPrefix, Classical.run_append]
    rw [hd.1, he.1]
    exact hf.2

private theorem active_phase_frame (registers : IndexedStepRegisters) (n T : Nat)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hw : wire ∈ indexedStepAfterSign registers) :
    blockGForwardState registers state wire = state wire := by
  have h1 : wire ≠ registers.phase1 := Ne.symm (hlayout.phase1_ne_after (by
    simp only [indexedStepAfterSign, indexedStepAfterPhase1, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at *
    tauto))
  have h2 : wire ≠ registers.phase2 := Ne.symm (hlayout.phase2_ne_after (by
    simp only [indexedStepAfterSign, indexedStepAfterPhase2, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at *
    tauto))
  have hs : wire ≠ registers.sign := Ne.symm (hlayout.sign_ne_after hw)
  rw [blockGForwardState, phaseUpdateEpochState_spec _ _ _ hlayout.phaseUpdate]
  simp only [IndexedStepRegisters.phaseUpdate, upd_other _ _ _ hs,
    upd_other _ _ _ h2, upd_other _ _ _ h1]

/-- After A--F, a nonterminal remainder length and a nonzero shift counter disable H.
The actual remaining transition is the source phase update, and the borrowed-epoch
encoding is restored. These prefix-state conditions still need active arithmetic refinement. -/
theorem indexedStepUnitary_active_tail_correct
    (registers : IndexedStepRegisters) (n T boundary4 boundary5 : Nat)
    (hboundary4 : (endIterationWindowsAt n T).k4 ≤ boundary4 ∧
      boundary4 ≤ (endIterationWindowsAt n T).K4)
    (hboundary5 : (endIterationWindowsAt n T).k5 ≤ boundary5 ∧
      boundary5 ≤ (endIterationWindowsAt n T).K5Decode n)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state) (hencoded : IndexedStepEpochEncoded registers state)
    (hroutes : T % 4 = 0 → indexedStepEndRoutes registers n T state = (boundary4, boundary5))
    (hrp : wireAnd registers.lengthRPrime (run (indexedStepShiftPrefix registers n T) state) = false)
    (hepoch : run (indexedStepShiftPrefix registers n T) state registers.shiftEpoch = false)
    (hs : T % 4 = 0 →
      wireAnd registers.lengthS (run (indexedStepShiftPrefix registers n T) state) = false) :
    run (indexedStepUnitary registers n T) state =
      phaseUpdateEpochState registers.phaseUpdate registers.shiftEpoch
        (run (indexedStepShiftPrefix registers n T) state) ∧
    IndexedStepReady registers (run (indexedStepUnitary registers n T) state) ∧
    IndexedStepEpochEncoded registers (run (indexedStepUnitary registers n T) state) := by
  let afterF := run (indexedStepShiftPrefix registers n T) state
  let afterG := blockGForwardState registers afterF
  have hprefix := active_shift_prefix registers n T state hlayout hready hencoded
  have hg := blockGForward_correct registers n T afterF hlayout hprefix.2
  have hgReady := hg.2
  rw [hg.1] at hgReady
  have hrpG : wireAnd registers.lengthRPrime afterG = false := by
    rw [← hrp]
    apply wireAnd_congr
    intro wire hw
    exact active_phase_frame registers n T afterF hlayout (by simp [indexedStepAfterSign, hw])
  have heG : afterG registers.shiftEpoch = false := by
    exact (active_phase_frame registers n T afterF hlayout (by
      simp [indexedStepAfterSign, hlayout.shiftEpoch_mem_aux])).trans hepoch
  have hh : blockHForwardState registers n T boundary4 boundary5 afterG = afterG := by
    by_cases hT : T % 4 = 0
    · have hsG : wireAnd registers.lengthS afterG = false := by
        rw [← hs hT]
        apply wireAnd_congr
        intro wire hw
        exact active_phase_frame registers n T afterF hlayout (by simp [indexedStepAfterSign, hw])
      exact terminal_blockH_idle registers n T boundary4 boundary5 afterG hlayout hgReady
        (by simp only [hsG, Bool.false_and])
    · simp only [blockHForwardState, hT, ↓reduceIte]
  have hfull := indexedStepUnitary_correct registers n T boundary4 boundary5 hboundary4 hboundary5
    state hlayout hready hencoded hroutes
  have hout : run (indexedStepUnitary registers n T) state = afterG := by
    rw [hfull.1, indexedStepForwardState, ← hprefix.1]
    exact hh
  refine ⟨hout, hfull.2, ?_⟩
  rw [hout]
  have hmatch : registerMatches (terminalConditionWires registers)
      (terminalConditionValue registers) afterG = false := by
    rw [terminalConditionWires, terminalConditionValue, terminal_detection, hrpG]
    simp only [Bool.and_false]
  simp only [IndexedStepEpochEncoded, hmatch, Bool.false_eq_true, if_false]
  exact heG

private theorem active_interval_frame (r : IndexedStepRegisters) (n T : Nat)
    (window : ActiveWindow) (mode : RippleMode) (signUpdate : Bool)
    (state : BasisState) (hlayout : IndexedStepLayout r n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder)
    (hclean : ∀ wire ∈ r.aux, wire ≠ r.control → state wire = false)
    {wire : Wire} (hwire : wire ∉ r.sign :: r.work1 ++ r.work2) :
    intervalAddSubState (r.remainder window) n window.start window.stop mode signUpdate .work1
      state wire = state wire := by
  have hr : IntervalReady (r.remainder window) state := by
    intro w hw
    exact hclean w (hlayout.remainder_scratch_sub_aux window w hw) (by
      intro he; subst w; exact hlayout.control_not_remainder_scratch window hwindow hw)
  have hl : IntervalLayout (r.remainder window) window.start window.stop .work1 := by
    subst window; exact hlayout.remainder
  rw [← run_intervalAddSubUnitary_state _ _ _ _ _ _ _ _ hl hr]
  apply intervalAddSubUnitary_frame _ _ _ _ _ _ _ _ hl hr wire
  intro hm
  apply hwire
  change wire ∈ r.sign :: IndexedStepRegisters.windowSlice r.work1 window ++
    IndexedStepRegisters.windowSlice r.work2 window at hm
  rcases List.mem_cons.mp hm with he | he
  · exact List.mem_cons.mpr (Or.inl he)
  · rcases List.mem_append.mp he with he | he
    · exact List.mem_cons.mpr (Or.inr (List.mem_append_left _ (windowSlice_mem _ _ he)))
    · exact List.mem_cons.mpr (Or.inr (List.mem_append_right _ (windowSlice_mem _ _ he)))

private theorem active_B1_frame (r : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout r n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder)
    (hready : IndexedStepBorrowedReady r state) {wire : Wire}
    (hwire : wire ∉ r.sign :: r.work1 ++ r.work2) (hc : wire ≠ r.control) :
    blockB1ForwardState r n window state wire = state wire := by
  unfold blockB1ForwardState
  rw [rControlState_preserves _ _ _ _ _ _ hc]
  rw [active_interval_frame r n T window .sub true _ hlayout hwindow (by
    intro w hw hne
    rw [rControlState_preserves _ _ _ _ _ _ hne]
    exact hready w hw) hwire]
  exact rControlState_preserves _ _ _ _ _ _ hc

private theorem active_restore_aux (r : IndexedStepRegisters) (n T : Nat)
    (state : BasisState) (hlayout : IndexedStepLayout r n T)
    (hready : IndexedStepBorrowedReady r state) :
    ∀ wire ∈ r.aux, wire ≠ r.control →
      remainderRestoreControlState r state wire = false := by
  intro wire hw hc
  by_cases ht : wire = r.terminal
  · subst wire
    have htc : r.terminal ≠ r.control := hlayout.control_ne_terminal.symm
    simp only [remainderRestoreControlState, andXorWireState, rControlState,
      upd_same, upd_other _ _ _ htc]
    have h1 : r.phase2 ≠ r.terminal := by
      exact Ne.symm (hlayout.aux_not_payload (hlayout.sourceScratch_mem_aux (by rw [← hlayout.scratch_view]; simp)) (by simp [indexedStepPayload]))
    have h2 : r.sign ≠ r.terminal := by
      exact Ne.symm (hlayout.aux_not_payload (hlayout.sourceScratch_mem_aux (by rw [← hlayout.scratch_view]; simp)) (by simp [indexedStepPayload]))
    have h3 : r.phase2 ≠ r.control := by
      exact Ne.symm (hlayout.aux_not_payload hlayout.control_mem_aux (by simp [indexedStepPayload]))
    have h4 : r.sign ≠ r.control := by
      exact Ne.symm (hlayout.aux_not_payload hlayout.control_mem_aux (by simp [indexedStepPayload]))
    simp only [upd_other _ _ _ h1, upd_other _ _ _ h2,
      upd_other _ _ _ h3, upd_other _ _ _ h4]
    rw [hready r.terminal (hlayout.sourceScratch_mem_aux (by rw [← hlayout.scratch_view]; simp))]
    simp
  · rw [remainderRestoreControlState_preserves _ _ ht hc]
    exact hready wire hw

private theorem active_B3_frame (r : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout r n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder)
    (hready : IndexedStepBorrowedReady r state) {wire : Wire}
    (hwire : wire ∉ r.sign :: r.work1 ++ r.work2) (hc : wire ≠ r.control)
    (ht : wire ≠ r.terminal) : blockB3ForwardState r n window state wire = state wire := by
  unfold blockB3ForwardState
  rw [remainderRestoreControlState_preserves _ _ ht hc]
  rw [active_interval_frame r n T window .add false _ hlayout hwindow
    (active_restore_aux r n T state hlayout hready) hwire]
  exact remainderRestoreControlState_preserves _ _ ht hc

private theorem active_B_frame (r : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout r n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder)
    (hready : IndexedStepBorrowedReady r state) {wire : Wire}
    (hwire : wire ∉ r.sign :: r.work1 ++ r.work2) (hc : wire ≠ r.control)
    (ht : wire ≠ r.terminal) : blockBForwardState r n window state wire = state wire := by
  have h1 := blockB1Forward_correct r n T window state hlayout hwindow hready
  have hr1 := h1.2
  rw [h1.1] at hr1
  have h2 := blockB2_correct r n T (blockB1ForwardState r n window state) hlayout hr1
  have hr2 := h2.2
  rw [h2.1] at hr2
  rw [blockBForwardState, active_B3_frame r n T window _ hlayout hwindow hr2 hwire hc ht]
  unfold blockB2State
  rw [rControlState_preserves _ _ _ _ _ _ hc,
    xorWireState_preserves _ _ _ (by intro he; exact hwire (by simp [he])),
    rControlState_preserves _ _ _ _ _ _ hc]
  exact active_B1_frame r n T window state hlayout hwindow hready hwire hc

private theorem active_quotient_frame (r : IndexedStepRegisters) (n T : Nat)
    (window : ActiveWindow) (state : BasisState) (hlayout : IndexedStepLayout r n T)
    (hwindow : window = (certifiedActiveWindows n T).quotientSwap)
    {wire : Wire} (hs : wire ≠ r.sign) (hw : wire ∉ r.work1) :
    indexedQuotientSwapState (r.quotient window) window.start window.stop state wire = state wire := by
  have hl : QuotientSwapLayout (r.quotient window) window.start window.stop := by
    subst window; exact hlayout.quotient
  unfold indexedQuotientSwapState quotientSwapState
  split
  · rw [upd_other _ _ _ (by
      intro he
      apply hw
      exact he ▸ windowSlice_mem _ _ (indexedQuotientWorkAt_mem_any _ hl _))]
    exact upd_other _ _ _ hs
  · rfl

private theorem active_D_frame (r : IndexedStepRegisters) (n T : Nat)
    (window : ActiveWindow) (state : BasisState) (hlayout : IndexedStepLayout r n T)
    (hwindow : window = (certifiedActiveWindows n T).quotientSwap)
    {wire : Wire} (hs : wire ≠ r.sign) (hw : wire ∉ r.work1)
    (hq : wire ∉ r.lengthQ) (hc : wire ≠ r.control) :
    blockDForwardState r window state wire = state wire := by
  unfold blockDForwardState blockD3ForwardState
  rw [matchXorState_preserves _ _ _ _ hc]
  unfold indexedDecrementWordState
  rw [indexedWriteWireValues_preservesOutside _ _ _ hq,
    matchXorState_preserves _ _ _ _ hc]
  unfold blockD2ForwardState
  rw [xorWireState_preserves _ _ _ hc, xorWireState_preserves _ _ _ hc,
    active_quotient_frame r n T window _ hlayout hwindow hs hw,
    xorWireState_preserves _ _ _ hc, xorWireState_preserves _ _ _ hc]
  unfold blockD1ForwardState
  rw [matchXorState_preserves _ _ _ _ hc]
  unfold indexedIncrementWordState
  rw [indexedWriteWireValues_preservesOutside _ _ _ hq,
    matchXorState_preserves _ _ _ _ hc]

private theorem active_coefficient_frame (r : IndexedStepRegisters) (n T : Nat)
    (window : ActiveWindow) (mode : RippleMode) (signUpdate : Bool) (state : BasisState)
    (hlayout : IndexedStepLayout r n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient)
    (hclean : Clean r.blockScratch state) :
    AgreesOutside (r.sign :: r.work1 ++ r.work2)
      (coefficientPrefixState (r.coefficient window) window.start window.stop
        mode signUpdate .work2 state) state ∧
    Clean r.blockScratch (coefficientPrefixState (r.coefficient window) window.start window.stop
      mode signUpdate .work2 state) := by
  have hr := run_coefficientPrefixState_from_blockScratch r n T window mode signUpdate state
    hlayout hwindow hclean
  dsimp only at hr
  have hl : CoefficientPrefixLayout (r.coefficient window) window.start window.stop := by
    subst window; exact hlayout.coefficient
  constructor
  · rw [← hr.1]
    intro wire hw
    apply coefficientPrefixUnitary_frame _ _ _ _ _ hl wire
    intro hm
    apply hw
    change wire ∈ r.sign :: IndexedStepRegisters.windowSlice r.work1 window ++
      IndexedStepRegisters.windowSlice r.work2 window at hm
    rcases List.mem_cons.mp hm with he | he
    · exact List.mem_cons.mpr (Or.inl he)
    · rcases List.mem_append.mp he with he | he
      · exact List.mem_cons.mpr (Or.inr (List.mem_append_left _ (windowSlice_mem _ _ he)))
      · exact List.mem_cons.mpr (Or.inr (List.mem_append_right _ (windowSlice_mem _ _ he)))
  · rw [← hr.1]
    exact hr.2.1

private theorem active_match_clean (r : IndexedStepRegisters) (controls : List Wire)
    (value : Nat) (target : Wire) (state : BasisState)
    (hclean : Clean r.blockScratch state) (hn : target ∉ r.blockScratch) :
    Clean r.blockScratch (matchXorState controls value target state) := by
  exact clean_upd_not_mem hclean hn

private theorem active_write_agrees (ws : List Wire) (bits : List Bool)
    (a b : BasisState) {wire : Wire} (h : a wire = b wire) :
    indexedWriteWireValues ws bits a wire = indexedWriteWireValues ws bits b wire := by
  induction ws generalizing bits with
  | nil => exact h
  | cons w ws ih =>
    cases bits with
    | nil => exact h
    | cons bit bits =>
      by_cases he : wire = w
      · simp [indexedWriteWireValues, upd, he]
      · simp [indexedWriteWireValues, upd, he, ih]

private theorem active_boundary_transport (r : IndexedStepRegisters) (n : Nat)
    (a b : BasisState)
    (hm : ∀ w ∈ [r.phase2] ++ r.lengthT ++ r.lengthRPrime ++ r.tBoundary.lengthSLow,
      a w = b w) {wire : Wire} (hw : a wire = b wire) :
    tBoundaryRestoreState r n a wire = tBoundaryRestoreState r n b wire := by
  have hp := hm r.phase2 (by simp)
  have ht : wireValues r.lengthT a = wireValues r.lengthT b :=
    wireValues_congr_indexedStep _ _ _ (fun w h => hm w (by simp [h]))
  have hr : wireValues r.lengthRPrime a = wireValues r.lengthRPrime b :=
    wireValues_congr_indexedStep _ _ _ (fun w h => hm w (by simp [h]))
  have hs : wireValues r.tBoundary.lengthSLow a = wireValues r.tBoundary.lengthSLow b :=
    wireValues_congr_indexedStep _ _ _ (fun w h => hm w (by simp [h]))
  unfold tBoundaryRestoreState
  rw [hp, ht, hr, hs]
  exact active_write_agrees _ _ a b hw

private theorem active_boundary_geometry (r : IndexedStepRegisters) (n T : Nat)
    (hl : IndexedStepLayout r n T) {w : Wire}
    (hm : w ∈ [r.phase2] ++ r.lengthT ++ r.lengthRPrime ++ r.tBoundary.lengthSLow) :
    w ∉ r.sign :: r.work1 ++ r.work2 ∧ w ≠ r.control ∧ w ≠ r.terminal := by
  have hsmall : w ∈ [r.phase2] ++ r.lengthT ++ r.lengthRPrime ++ r.lengthS := by
    simp only [List.mem_append, List.mem_singleton] at hm ⊢
    rcases hm with ((h | h) | h) | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr (List.mem_of_mem_take h)
  have hpay : w ∈ indexedStepPayload r := by
    simp only [List.mem_append, List.mem_singleton] at hsmall
    rcases hsmall with ((h | h) | h) | h <;> simp [indexedStepPayload, h]
  have hc := (hl.aux_not_payload hl.control_mem_aux hpay).symm
  have ht : w ≠ r.terminal := (hl.aux_not_payload (hl.sourceScratch_mem_aux (by
    rw [← hl.scratch_view]; simp)) hpay).symm
  refine ⟨?_, hc, ht⟩
  have hp := hl.physical
  simp only [IndexedStepRegisters.allWires, List.append_assoc, List.cons_append,
    List.nil_append, List.nodup_cons] at hp
  have hdis : ∀ a ∈ r.sign :: r.work1 ++ r.work2,
      ∀ b ∈ r.lengthT ++ r.lengthQ ++ r.lengthS ++ r.lengthRPrime ++ r.aux, a ≠ b := by
    have hd : ((r.sign :: r.work1 ++ r.work2) ++
        (r.lengthT ++ r.lengthQ ++ r.lengthS ++ r.lengthRPrime ++ r.aux)).Nodup := by
      simpa only [List.cons_append, List.append_assoc, List.nodup_cons] using hp.2.2.2
    exact (List.nodup_append.mp hd).2.2
  simp only [List.mem_append, List.mem_singleton] at hsmall
  rcases hsmall with ((h | h) | h) | h
  · subst w
    intro hw
    exact hp.2.1 (by simp only [List.mem_cons, List.mem_append] at hw ⊢; tauto)
  · exact fun hw => hdis w hw w (by simp [h]) rfl
  · exact fun hw => hdis w hw w (by simp [h]) rfl
  · exact fun hw => hdis w hw w (by simp [h]) rfl

private theorem active_E_frame (r : IndexedStepRegisters) (n T : Nat)
    (window : ActiveWindow) (state : BasisState) (hlayout : IndexedStepLayout r n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient)
    (hclean : Clean r.blockScratch state) {wire : Wire}
    (hw : wire ∉ r.sign :: r.work1 ++ r.work2) (hc : wire ≠ r.control)
    (hf : wire ≠ r.terminal) :
    blockEForwardState r n window state wire = state wire := by
  have hcn : r.control ∉ r.blockScratch := fun hm =>
    hlayout.control_not_sourceScratch (List.mem_of_mem_drop hm)
  have hsn : r.sign ∉ r.blockScratch := by
    intro hm
    exact (hlayout.aux_not_payload
      (hlayout.sourceScratch_mem_aux (List.mem_of_mem_drop hm)) (by simp [indexedStepPayload])) rfl
  let t1 := matchXorState [r.phase2, r.sign] 2 r.terminal state
  let e1 := matchXorState [r.phase1, r.terminal] 1 r.control t1
  let t2 := matchXorState [r.phase2, r.sign] 2 r.terminal e1
  have hc1 : Clean r.blockScratch t1 := active_match_clean r _ _ _ state hclean hlayout.terminal_not_blockScratch
  have hc2 : Clean r.blockScratch e1 := active_match_clean r _ _ _ t1 hc1 hcn
  have hc3 : Clean r.blockScratch t2 := active_match_clean r _ _ _ e1 hc2 hlayout.terminal_not_blockScratch
  let prepared := tBoundaryPrepareState r n t2
  have hp := run_tBoundaryPrepareState r n T t2 hlayout hc3
  have hpc := hp.2
  rw [hp.1] at hpc
  let subtracted := coefficientPrefixState (r.coefficient window) window.start window.stop
    .sub false .work2 prepared
  have hsub := active_coefficient_frame r n T window .sub false prepared hlayout hwindow hpc
  let t3 := matchXorState [r.phase2, r.sign] 2 r.terminal subtracted
  let c1 := matchXorState [r.phase1, r.terminal] 1 r.control t3
  let t4 := matchXorState [r.phase2, r.sign] 2 r.terminal c1
  have hc4 : Clean r.blockScratch t3 := active_match_clean r _ _ _ subtracted hsub.2 hlayout.terminal_not_blockScratch
  have hc5 : Clean r.blockScratch c1 := active_match_clean r _ _ _ t3 hc4 hcn
  have hc6 : Clean r.blockScratch t4 := active_match_clean r _ _ _ c1 hc5 hlayout.terminal_not_blockScratch
  let signChanged := xorWireState r.phase1 r.sign t4
  have hsc : Clean r.blockScratch signChanged := clean_upd_not_mem hc6 hsn
  let e2 := matchXorState [r.phase1] 1 r.control signChanged
  have hc7 : Clean r.blockScratch e2 := active_match_clean r _ _ _ signChanged hsc hcn
  let added := coefficientPrefixState (r.coefficient window) window.start window.stop
    .add true .work2 e2
  have hadd := active_coefficient_frame r n T window .add true e2 hlayout hwindow hc7
  have hmiddle : ∀ w, w ∉ r.sign :: r.work1 ++ r.work2 → w ≠ r.control →
      w ≠ r.terminal → matchXorState [r.phase1] 1 r.control added w = prepared w := by
    intro w hw hc hf
    rw [matchXorState_preserves _ _ _ _ hc]
    dsimp only [added]
    rw [hadd.1 w hw]
    dsimp only [e2, signChanged, t4, c1, t3]
    rw [matchXorState_preserves _ _ _ _ hc,
      xorWireState_preserves _ _ _ (by intro he; exact hw (by simp [he])),
      matchXorState_preserves _ _ _ _ hf, matchXorState_preserves _ _ _ _ hc,
      matchXorState_preserves _ _ _ _ hf]
    exact hsub.1 w hw
  change tBoundaryRestoreState r n (matchXorState [r.phase1] 1 r.control added) wire = state wire
  have htransport := active_boundary_transport r n
    (matchXorState [r.phase1] 1 r.control added) prepared (by
      intro w hm
      have hg := active_boundary_geometry r n T hlayout hm
      exact hmiddle w hg.1 hg.2.1 hg.2.2) (hmiddle wire hw hc hf)
  rw [htransport]
  change tBoundaryRestoreState r n (tBoundaryPrepareState r n t2) wire = state wire
  rw [terminal_boundary_restore_prepare r n T t2 hlayout hc3]
  dsimp only [t2, e1, t1]
  rw [matchXorState_preserves _ _ _ _ hf, matchXorState_preserves _ _ _ _ hc,
    matchXorState_preserves _ _ _ _ hf]

private theorem active_read_write (ws : List Wire) (s : BasisState) :
    writeReg ws (boolWordToNat (wireValues ws s)) s = s := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hb : (Bool.toNat (s w) + 2 * boolWordToNat (wireValues ws s)).testBit 0 = s w := by
      rw [Nat.testBit_zero]
      cases s w <;> simp [Nat.add_mod]
    have hd : (Bool.toNat (s w) + 2 * boolWordToNat (wireValues ws s)) / 2 =
        boolWordToNat (wireValues ws s) := by
      cases s w <;> simp
      omega
    have hu : s[w ↦ s w] = s := by funext i; by_cases h : i = w <;> simp [upd, h]
    change writeReg ws ((Bool.toNat (s w) + 2 * boolWordToNat (wireValues ws s)) / 2)
      (s[w ↦ (Bool.toNat (s w) + 2 * boolWordToNat (wireValues ws s)).testBit 0]) = s
    rw [hb, hd, hu]
    exact ih
private theorem active_inc_false (xs : List Bool) : incrementBits false xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [incrementBits, ih]
private theorem active_padding_idle (r : TerminalPaddingRegisters) (s : BasisState) (ht : s r.terminal = false) :
    terminalPaddingForwardState r s = s := by
  unfold terminalPaddingForwardState
  simp only [ht, Bool.false_eq_true, ↓reduceIte, active_read_write, active_inc_false,
    Bool.false_and, Bool.xor_false]
  funext i
  by_cases h : i = r.shiftEpoch <;> simp [upd, h]

private theorem active_A_shift (r : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout r n T) (hready : IndexedStepBorrowedReady r state)
    (hcondition : registerMatches (terminalConditionWires r) (terminalConditionValue r) state = false) :
    blockAForwardState r state = run (preShiftUnitary r.preShift) state := by
  have htaux : r.terminal ∈ r.aux := hlayout.sourceScratch_mem_aux (by
    rw [← hlayout.scratch_view]; simp)
  have ht : state r.terminal = false := hready _ htaux
  have hpReady : ShiftReady r.preShift state := by
    intro wire hw
    exact hready wire (hlayout.sourceScratch_mem_aux
      (List.mem_of_mem_drop (hlayout.preShift_scratch_sub_block wire hw)))
  let shifted := preShiftState r.preShift state
  have hp := run_preShiftUnitary r.preShift state hlayout.preShift hpReady
  have hst : shifted r.terminal = false := by
    dsimp only [shifted]
    rw [← hp]
    exact (preShiftUnitary_preservesOutside _ _ hlayout.terminal_not_preShift).trans ht
  have hsc : registerMatches (terminalConditionWires r) (terminalConditionValue r) shifted = false := by
    rw [← hcondition]
    apply registerMatches_congr
    intro wire hw
    change wire ∈ r.phase1 :: r.lengthRPrime at hw
    dsimp only [shifted]
    rw [← hp]
    rcases List.mem_cons.mp hw with heq | hm
    · subst wire
      exact preShiftUnitary_preserves_phase1 _ _ hlayout.preShift hpReady
    · exact preShiftUnitary_preservesOutside _ _ (hlayout.lengthRPrime_not_preShift hm)
  have hm : matchXorState (terminalConditionWires r) (terminalConditionValue r) r.terminal state = state := by
    simp only [matchXorState, hcondition, Bool.xor_false, endIdle_update_read]
  have hd : xorWireState r.terminal r.phase1 state = state := by
    simp only [xorWireState, ht, Bool.xor_false, endIdle_update_read]
  have hrestore : xorWireState r.terminal r.phase1 shifted = shifted := by
    simp only [xorWireState, hst, Bool.xor_false, endIdle_update_read]
  have hspill : terminalEpochSpillState r.terminal r.shiftEpoch r.quotientLow shifted = shifted := by
    simp only [terminalEpochSpillState, xorWireState, Bool.xor_false,
      endIdle_update_read, controlledSwapState, hst, Bool.false_eq_true, ↓reduceIte]
  rw [blockAForwardState, hm, active_padding_idle _ _ ht, hd]
  change matchXorState (terminalConditionWires r) (terminalConditionValue r) r.terminal
    (terminalEpochSpillState r.terminal r.shiftEpoch r.quotientLow
      (xorWireState r.terminal r.phase1 shifted)) = _
  rw [hrestore, hspill]
  simp only [matchXorState, hsc, Bool.xor_false, endIdle_update_read]
  exact hp.symm

private theorem active_metadata_geometry (r : IndexedStepRegisters) (n T : Nat) (hl : IndexedStepLayout r n T) :
    List.Disjoint ([r.phase1, r.phase2] ++ r.lengthS)
      (r.sign :: r.work1 ++ r.work2 ++ r.lengthT ++ r.lengthQ ++ r.lengthRPrime ++ r.aux) := by
  have hp := hl.physical
  simp only [IndexedStepRegisters.allWires, List.append_assoc, List.cons_append,
    List.nil_append, List.nodup_cons, List.nodup_append] at hp
  rw [List.disjoint_left]
  intro w hm hn
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm hn
  rcases hm with ((h1 | h2) | hs)
  · subst w
    aesop
  · subst w
    aesop
  · have h1 := hp.2.2.2.2
    have h2 := h1.2.1
    have ht := h2.2.1
    have hq := ht.2.1
    have hS := hq.2.1
    rcases hn with (((((h | h) | h) | h) | h) | h) | h
    · subst w
      exact hp.2.2.2.1 (by simp [hs])
    · exact h1.2.2 w h w (by simp [hs]) rfl
    · exact h2.2.2 w h w (by simp [hs]) rfl
    · exact ht.2.2 w h w (by simp [hs]) rfl
    · exact hq.2.2 w h w (by simp [hs]) rfl
    · exact hS.2.2 w hs w (by simp [h]) rfl
    · exact hS.2.2 w hs w (by simp [h]) rfl

/-- Across the actual A--F prefix, a nonterminal input shifts the counter exactly
once, with direction selected by phase two. Scratch starts fully clear; active
arithmetic reachability must still establish this input encoding. -/
theorem indexedStepShiftPrefix_counter (r : IndexedStepRegisters) (n T : Nat)
    (state : BasisState) (hlayout : IndexedStepLayout r n T) (hclean : Clean r.aux state)
    (hrp : wireAnd r.lengthRPrime state = false) :
    boolWordToNat (wireValues r.lengthS (run (indexedStepShiftPrefix r n T) state)) =
      if state r.phase2 then
        (boolWordToNat (wireValues r.lengthS state) + 2^r.lengthS.length - 1) % 2^r.lengthS.length
      else (1 + boolWordToNat (wireValues r.lengthS state)) % 2^r.lengthS.length := by
  have hready : IndexedStepReady r state := by
    intro wire hw
    apply hclean wire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons, List.mem_append] at hw
    rcases hw with he | he | he
    · subst wire; exact hlayout.control_mem_aux
    · exact hlayout.sourceScratch_mem_aux he
    · exact hlayout.remainderRepairScratch_mem_aux he
  have hcondition : registerMatches (terminalConditionWires r) (terminalConditionValue r) state = false := by
    rw [terminalConditionWires, terminalConditionValue, terminal_detection, hrp]
    simp
  have hencoded : IndexedStepEpochEncoded r state := by
    simp only [IndexedStepEpochEncoded, hcondition, Bool.false_eq_true, if_false]
    exact hclean _ hlayout.shiftEpoch_mem_aux
  let a := run (blockAForward r) state
  have ha := blockAForward_correct r n T state hlayout hready
  have har := blockAForward_borrowedReady r n T state hlayout hready hencoded
  have hap : a = run (preShiftUnitary r.preShift) state :=
    ha.1.trans (active_A_shift r n T state hlayout hclean hcondition)
  let b := run (blockBForward r n (certifiedActiveWindows n T).remainder) a
  have hb := blockBForward_correct r n T _ a hlayout rfl har
  let c := run (blockCForward r) b
  have hc := blockCForward_correct r n T b hlayout hb.2
  let d := run (blockDForward r (certifiedActiveWindows n T).quotientSwap) c
  have hd := blockDForward_correct r n T _ c hlayout rfl hc.2
  let e := run (blockEForward r n (certifiedActiveWindows n T).coefficient) d
  have he := blockEForward_correct r n T _ d hlayout rfl hd.2
  have hmeta : ∀ wire ∈ [r.phase1, r.phase2] ++ r.lengthS,
      e wire = run (preShiftUnitary r.preShift) state wire := by
    intro wire hw
    have hn := List.disjoint_left.mp (active_metadata_geometry r n T hlayout) hw
    have hdata : wire ∉ r.sign :: r.work1 ++ r.work2 := by
      intro hm
      exact hn (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ hm))))
    have hQ : wire ∉ r.lengthQ := fun hm => hn (by simp [hm])
    have haux : ∀ v ∈ r.aux, wire ≠ v := by
      intro v hv hvw; apply hn; simp [hvw, hv]
    have hcontrol := haux _ hlayout.control_mem_aux
    have hterminal := haux r.terminal (hlayout.sourceScratch_mem_aux (by rw [← hlayout.scratch_view]; simp))
    have hepoch := haux _ hlayout.shiftEpoch_mem_aux
    have hqlow : wire ≠ r.quotientLow := by
      intro h; subst wire; exact hQ hlayout.quotientLow_mem_lengthQ
    have hsign : wire ≠ r.sign := by intro h; exact hdata (by simp [h])
    have hwork : wire ∉ r.work1 := fun hm => hdata (by simp [hm])
    dsimp only [e]
    rw [he.1, active_E_frame r n T _ d hlayout rfl
      (fun w hw => hd.2 w (hlayout.blockScratch_mem_sharedScratch hw))
      hdata hcontrol hterminal]
    dsimp only [d]
    rw [hd.1, active_D_frame r n T _ c hlayout rfl hsign hwork hQ hcontrol]
    dsimp only [c]
    rw [hc.1]
    simp only [blockCForwardState, matchXorState_preserves _ _ _ _ hterminal,
      terminalEpochRestoreState_preserves _ _ _ _ hepoch hqlow]
    dsimp only [b]
    rw [hb.1, active_B_frame r n T _ a hlayout rfl har hdata hcontrol hterminal]
    exact congrFun hap wire
  have hpReady : ShiftReady r.preShift state := by
    intro wire hw
    exact hclean wire (hlayout.blockScratch_mem_aux (hlayout.preShift_scratch_sub_block wire hw))
  have hfReady : ShiftReady r.postShift e := by
    intro wire hw
    exact he.2 wire (hlayout.sourceScratch_mem_sharedScratch (hlayout.postShift_scratch_sub_source wire hw))
  have hp1 : e r.phase1 = state r.phase1 :=
    (hmeta _ (by simp)).trans (preShiftUnitary_preserves_phase1 _ _ hlayout.preShift hpReady)
  have hp2 : e r.phase2 = state r.phase2 :=
    (hmeta _ (by simp)).trans (preShiftUnitary_preserves_phase2 _ _ hlayout.preShift hpReady)
  have hS : wireValues r.lengthS e = wireValues r.lengthS (run (preShiftUnitary r.preShift) state) := by
    apply wireValues_congr_indexedStep
    intro wire hw
    exact hmeta wire (by simp [hw])
  have hshape : run (indexedStepShiftPrefix r n T) state = run (postShiftUnitary r.postShift) e := by
    simp only [indexedStepShiftPrefix, indexedStepRemainderPrefix, blockFForward, e, d, c, b, a,
      Classical.run_append]
  rw [hshape]
  change boolWordToNat (wireValues r.postShift.lengthS (run (postShiftUnitary r.postShift) e)) = _
  rw [postShiftUnitary_counter r.postShift e hlayout.postShift hfReady]
  change (if e r.phase1 then
    (if e r.phase2 then (boolWordToNat (wireValues r.lengthS e) + 2^r.lengthS.length - 1) % 2^r.lengthS.length
      else (1 + boolWordToNat (wireValues r.lengthS e)) % 2^r.lengthS.length)
    else boolWordToNat (wireValues r.lengthS e)) = _
  rw [hp1, hp2, hS]
  have hpre : boolWordToNat (wireValues r.lengthS (run (preShiftUnitary r.preShift) state)) =
      if !state r.phase1 then
        (if state r.phase2 then
          (boolWordToNat (wireValues r.lengthS state) + 2^r.lengthS.length - 1) % 2^r.lengthS.length
          else (1 + boolWordToNat (wireValues r.lengthS state)) % 2^r.lengthS.length)
        else boolWordToNat (wireValues r.lengthS state) :=
    preShiftUnitary_counter r.preShift state hlayout.preShift hpReady
  rw [hpre]
  cases state r.phase1 <;> cases state r.phase2 <;> simp

end

/-- The actual A--F prefix preserves every remainder-length bit from a clean,
nonterminal input, including the temporary coefficient boundary conversion. -/
theorem indexedStepShiftPrefix_remainder (r : IndexedStepRegisters) (n T : Nat)
    (state : BasisState) (hlayout : IndexedStepLayout r n T) (hclean : Clean r.aux state)
    (hrp : wireAnd r.lengthRPrime state = false) :
    ∀ wire ∈ r.lengthRPrime,
      run (indexedStepShiftPrefix r n T) state wire = state wire := by
  have hready : IndexedStepReady r state := by
    intro wire hw
    apply hclean wire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons, List.mem_append] at hw
    rcases hw with he | he | he
    · subst wire; exact hlayout.control_mem_aux
    · exact hlayout.sourceScratch_mem_aux he
    · exact hlayout.remainderRepairScratch_mem_aux he
  have hcondition : registerMatches (terminalConditionWires r) (terminalConditionValue r) state = false := by
    rw [terminalConditionWires, terminalConditionValue, terminal_detection, hrp]
    simp
  have hencoded : IndexedStepEpochEncoded r state := by
    simp only [IndexedStepEpochEncoded, hcondition, Bool.false_eq_true, if_false]
    exact hclean _ hlayout.shiftEpoch_mem_aux
  let a := run (blockAForward r) state
  have ha := blockAForward_correct r n T state hlayout hready
  have har := blockAForward_borrowedReady r n T state hlayout hready hencoded
  have hap : a = run (preShiftUnitary r.preShift) state :=
    ha.1.trans (active_A_shift r n T state hlayout hclean hcondition)
  let b := run (blockBForward r n (certifiedActiveWindows n T).remainder) a
  have hb := blockBForward_correct r n T _ a hlayout rfl har
  let c := run (blockCForward r) b
  have hc := blockCForward_correct r n T b hlayout hb.2
  let d := run (blockDForward r (certifiedActiveWindows n T).quotientSwap) c
  have hd := blockDForward_correct r n T _ c hlayout rfl hc.2
  let e := run (blockEForward r n (certifiedActiveWindows n T).coefficient) d
  have he := blockEForward_correct r n T _ d hlayout rfl hd.2

  intro wire hw
  have hbefore : wire ∉ indexedStepBeforeLengthRPrime r := fun h =>
    (hlayout.lengthRPrime_ne_outside hw (Or.inl h)) rfl
  have hdata : wire ∉ r.sign :: r.work1 ++ r.work2 := by
    intro hm
    apply hbefore
    simp only [List.mem_cons, List.mem_append] at hm
    rcases hm with (h | h) | h <;> simp [indexedStepBeforeLengthRPrime, h]
  have hQ : wire ∉ r.lengthQ := fun h => hbefore (by simp [indexedStepBeforeLengthRPrime, h])
  have hcontrol := hlayout.lengthRPrime_ne_outside hw (Or.inr hlayout.control_mem_aux)
  have hterminal : wire ≠ r.terminal := hlayout.lengthRPrime_ne_outside hw (Or.inr
    (hlayout.sourceScratch_mem_aux (by rw [← hlayout.scratch_view]; simp)))
  have hepoch := hlayout.lengthRPrime_ne_shiftEpoch hw
  have hqlow : wire ≠ r.quotientLow := by
    intro h; subst wire; exact hQ hlayout.quotientLow_mem_lengthQ
  have hsign : wire ≠ r.sign := by intro h; exact hdata (by simp [h])
  have hwork : wire ∉ r.work1 := fun h => hdata (by simp [h])
  have hpost : wire ∉ r.postShift.postUsedWires := by
    intro hu
    have hc : wire ∉ r.postShift.scratch := fun h =>
      (hlayout.lengthRPrime_ne_outside hw (Or.inr (hlayout.sourceScratch_mem_aux
        (hlayout.postShift_scratch_sub_source wire h)))) rfl
    have hp1 : wire ≠ r.phase1 := hlayout.lengthRPrime_ne_outside hw
      (Or.inl (by simp [indexedStepBeforeLengthRPrime]))
    have hp2 : wire ≠ r.phase2 := hlayout.lengthRPrime_ne_outside hw
      (Or.inl (by simp [indexedStepBeforeLengthRPrime]))
    have hw2 := hlayout.lengthRPrime_not_work2 hw
    have hs := hlayout.lengthRPrime_not_lengthS hw
    simp only [ShiftRegisters.postUsedWires, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at hu
    change wire ∉ [r.postShift.phase1IsZero, r.postShift.both] ++
      r.postShift.carries ++ r.postShift.reserved at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
    change wire ≠ r.postShift.phase1 at hp1
    change wire ≠ r.postShift.phase2 at hp2
    change wire ∉ r.postShift.work at hw2
    change wire ∉ r.postShift.lengthS at hs
    rcases hu with (((h | h | h) | h) | h) | h
    · exact hp1 h
    · exact hp2 h
    · exact hc.1.1.2 h
    · exact hw2 h
    · exact hs h
    · exact hc.1.2 h
  have hshape : run (indexedStepShiftPrefix r n T) state = run (postShiftUnitary r.postShift) e := by
    simp only [indexedStepShiftPrefix, indexedStepRemainderPrefix, blockFForward, e, d, c, b, a,
      Classical.run_append]
  rw [hshape]
  rw [postShiftUnitary_preservesOutside _ _ hpost]
  dsimp only [e]
  rw [he.1, active_E_frame r n T _ d hlayout rfl
    (fun w h => hd.2 w (hlayout.blockScratch_mem_sharedScratch h)) hdata hcontrol hterminal]
  dsimp only [d]
  rw [hd.1, active_D_frame r n T _ c hlayout rfl hsign hwork hQ hcontrol]
  dsimp only [c]
  rw [hc.1]
  simp only [blockCForwardState, matchXorState_preserves _ _ _ _ hterminal,
    terminalEpochRestoreState_preserves _ _ _ _ hepoch hqlow]
  dsimp only [b]
  rw [hb.1, active_B_frame r n T _ a hlayout rfl har hdata hcontrol hterminal, hap]
  exact preShiftUnitary_preservesOutside _ _ (hlayout.lengthRPrime_not_preShift hw)

private theorem active_C_idle (r : IndexedStepRegisters) (s : BasisState)
    (ht : s r.terminal = false) (hr : wireAnd r.lengthRPrime s = false) :
    blockCForwardState r s = s := by
  have hm : registerMatches (terminalConditionWires r) (terminalConditionValue r) s = false := by
    rw [terminalConditionWires, terminalConditionValue, terminal_detection, hr]
    simp
  have hmark : matchXorState (terminalConditionWires r) (terminalConditionValue r) r.terminal s = s := by
    simp only [matchXorState, hm, Bool.xor_false, endIdle_update_read]
  have hrestore : terminalEpochRestoreState r.terminal r.shiftEpoch r.quotientLow s = s := by
    simp only [terminalEpochRestoreState, controlledSwapState, ht, Bool.false_eq_true,
      ↓reduceIte, xorWireState, Bool.xor_false, endIdle_update_read]
  rw [blockCForwardState, hmark, hrestore, hmark]

/-- Terminal restoration is the identity on every wire of a clean nonterminal state. -/
theorem blockCForward_nonterminal (r : IndexedStepRegisters) (n index : Nat)
    (state : BasisState) (h : IndexedStepLayout r n index)
    (hc : Clean r.aux state) (hrp : wireAnd r.lengthRPrime state = false) :
    run (blockCForward r) state = state := by
  rw [(blockCForward_correct r n index state h hc).1]
  apply active_C_idle r state _ hrp
  apply hc r.terminal
  exact h.sourceScratch_mem_aux (by rw [← h.scratch_view]; simp)

/-- A clean, nonterminal input returns every auxiliary wire clear after A--F.
In particular the borrowed epoch remains zero rather than gaining a padding bit. -/
theorem indexedStepShiftPrefix_clean (r : IndexedStepRegisters) (n T : Nat)
    (state : BasisState) (hlayout : IndexedStepLayout r n T) (hclean : Clean r.aux state)
    (hrp : wireAnd r.lengthRPrime state = false) :
    Clean r.aux (run (indexedStepShiftPrefix r n T) state) := by
  have hready : IndexedStepReady r state := by
    intro wire hw
    apply hclean wire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons, List.mem_append] at hw
    rcases hw with he | he | he
    · subst wire; exact hlayout.control_mem_aux
    · exact hlayout.sourceScratch_mem_aux he
    · exact hlayout.remainderRepairScratch_mem_aux he
  have hcondition : registerMatches (terminalConditionWires r) (terminalConditionValue r) state = false := by
    rw [terminalConditionWires, terminalConditionValue, terminal_detection, hrp]
    simp
  have hencoded : IndexedStepEpochEncoded r state := by
    simp only [IndexedStepEpochEncoded, hcondition, Bool.false_eq_true, if_false]
    exact hclean _ hlayout.shiftEpoch_mem_aux
  let a := run (blockAForward r) state
  have ha := blockAForward_correct r n T state hlayout hready
  have har := blockAForward_borrowedReady r n T state hlayout hready hencoded
  have hap : a = run (preShiftUnitary r.preShift) state :=
    ha.1.trans (active_A_shift r n T state hlayout hclean hcondition)
  let b := run (blockBForward r n (certifiedActiveWindows n T).remainder) a
  have hb := blockBForward_correct r n T _ a hlayout rfl har
  let c := run (blockCForward r) b
  have hc := blockCForward_correct r n T b hlayout hb.2
  let d := run (blockDForward r (certifiedActiveWindows n T).quotientSwap) c
  have hd := blockDForward_correct r n T _ c hlayout rfl hc.2
  let e := run (blockEForward r n (certifiedActiveWindows n T).coefficient) d
  have he := blockEForward_correct r n T _ d hlayout rfl hd.2

  have hbits : ∀ wire ∈ r.lengthRPrime, b wire = state wire := by
    intro wire hw
    have hg := active_boundary_geometry r n T hlayout (w := wire) (by simp [hw])
    dsimp only [b]
    rw [hb.1, active_B_frame r n T _ a hlayout rfl har hg.1 hg.2.1 hg.2.2, hap]
    exact preShiftUnitary_preservesOutside _ _ (hlayout.lengthRPrime_not_preShift hw)
  have hbrp : wireAnd r.lengthRPrime b = false := (wireAnd_congr _ b state hbits).trans hrp
  have hterminal : r.terminal ∈ r.sourceScratch := by rw [← hlayout.scratch_view]; simp
  have hcidle : c = b := hc.1.trans (active_C_idle r b
    (hb.2 _ (hlayout.sourceScratch_mem_aux hterminal)) hbrp)
  have hedata : r.shiftEpoch ∉ r.sign :: r.work1 ++ r.work2 := by
    intro hm
    apply hlayout.aux_not_payload hlayout.shiftEpoch_mem_aux (payloadWire := r.shiftEpoch) ?_ rfl
    simp only [List.mem_append, List.mem_cons] at hm
    rcases hm with (h | h) | h <;> simp [indexedStepPayload, h]
  have hesign : r.shiftEpoch ≠ r.sign := by intro h; exact hedata (by simp [h])
  have hework : r.shiftEpoch ∉ r.work1 := fun h => hedata (by simp [h])
  have heQ : r.shiftEpoch ∉ r.lengthQ := by
    intro h
    exact hlayout.aux_not_payload hlayout.shiftEpoch_mem_aux (by simp [indexedStepPayload, h]) rfl
  have hect := hlayout.control_ne_shiftEpoch.symm
  have heterm : r.shiftEpoch ≠ r.terminal := fun h =>
    hlayout.shiftEpoch_not_sourceScratch (h.symm ▸ hterminal)
  have hezero : e r.shiftEpoch = false := by
    dsimp only [e]
    rw [he.1, active_E_frame r n T _ d hlayout rfl
      (fun w h => hd.2 w (hlayout.blockScratch_mem_sharedScratch h)) hedata hect heterm]
    dsimp only [d]
    rw [hd.1, active_D_frame r n T _ c hlayout rfl hesign hework heQ hect, hcidle]
    exact hb.2 _ hlayout.shiftEpoch_mem_aux
  have hpost : r.shiftEpoch ∉ r.postShift.postUsedWires := by
    intro hu
    have hs : r.shiftEpoch ∉ r.postShift.scratch := fun h =>
      hlayout.shiftEpoch_not_sourceScratch (hlayout.postShift_scratch_sub_source _ h)
    have hp1 := hlayout.phase1_ne_shiftEpoch.symm
    have hp2 : r.shiftEpoch ≠ r.phase2 := hlayout.aux_not_payload hlayout.shiftEpoch_mem_aux
      (by simp [indexedStepPayload])
    have hw2 := hlayout.shiftEpoch_not_work2
    have hS := hlayout.shiftEpoch_not_lengthS
    simp only [ShiftRegisters.postUsedWires, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at hu
    change r.shiftEpoch ∉ [r.postShift.phase1IsZero, r.postShift.both] ++
      r.postShift.carries ++ r.postShift.reserved at hs
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
    rcases hu with (((h | h | h) | h) | h) | h
    · exact hp1 h
    · exact hp2 h
    · exact hs.1.1.2 h
    · exact hw2 h
    · exact hS h
    · exact hs.1.2 h
  have hf := blockFForward_correct r n T e hlayout he.2
  have hshape : run (indexedStepShiftPrefix r n T) state = run (blockFForward r) e := by
    simp only [indexedStepShiftPrefix, indexedStepRemainderPrefix, e, d, c, b, a,
      Classical.run_append]
  rw [hshape]
  intro wire hw
  rw [← hlayout.aux_view] at hw
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with (h | h) | h | h
  · subst wire
    exact hf.2 _ (by simp [IndexedStepRegisters.sharedScratch])
  · subst wire
    exact (postShiftUnitary_preservesOutside r.postShift e hpost).trans hezero
  · exact hf.2 _ (hlayout.sourceScratch_mem_sharedScratch h)
  · exact hf.2 _ (hlayout.remainderRepairScratch_mem_sharedScratch h)

private theorem active_all_ones (ws : List Wire) (s : BasisState)
    (h : wireAnd ws s = true) : boolWordToNat (wireValues ws s) = 2^ws.length - 1 := by
  induction ws with
  | nil => simp [wireValues]
  | cons w ws ih =>
    simp only [wireAnd, Bool.and_eq_true] at h
    have ht := ih h.2
    change boolWordToNat (List.map s ws) = 2^ws.length - 1 at ht
    simp only [wireValues, List.map_cons, boolWordToNat, h.1, Bool.toNat_true,
      List.length_cons, Nat.pow_succ]
    have hp := Nat.two_pow_pos ws.length
    omega

/-- The active full step reduces to its phase update from original-input conditions.
Only every fourth step needs to avoid the shift-counter sentinel, since other
indices contain no end-iteration block. -/
theorem indexedStepUnitary_active_correct
    (r : IndexedStepRegisters) (n T boundary4 boundary5 : Nat)
    (hboundary4 : (endIterationWindowsAt n T).k4 ≤ boundary4 ∧
      boundary4 ≤ (endIterationWindowsAt n T).K4)
    (hboundary5 : (endIterationWindowsAt n T).k5 ≤ boundary5 ∧
      boundary5 ≤ (endIterationWindowsAt n T).K5Decode n)
    (state : BasisState) (hlayout : IndexedStepLayout r n T)
    (hclean : Clean r.aux state) (hrp : wireAnd r.lengthRPrime state = false)
    (hroutes : T % 4 = 0 → indexedStepEndRoutes r n T state = (boundary4, boundary5))
    (hshift : T % 4 = 0 → (if state r.phase2 then
        (boolWordToNat (wireValues r.lengthS state) + 2^r.lengthS.length - 1) % 2^r.lengthS.length
      else (1 + boolWordToNat (wireValues r.lengthS state)) % 2^r.lengthS.length) ≠
        2^r.lengthS.length - 1) :
    run (indexedStepUnitary r n T) state =
      phaseUpdateEpochState r.phaseUpdate r.shiftEpoch
        (run (indexedStepShiftPrefix r n T) state) ∧
    IndexedStepReady r (run (indexedStepUnitary r n T) state) ∧
    IndexedStepEpochEncoded r (run (indexedStepUnitary r n T) state) := by
  have hready : IndexedStepReady r state := by
    intro wire hw
    apply hclean wire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons, List.mem_append] at hw
    rcases hw with he | he | he
    · subst wire; exact hlayout.control_mem_aux
    · exact hlayout.sourceScratch_mem_aux he
    · exact hlayout.remainderRepairScratch_mem_aux he
  have hcondition : registerMatches (terminalConditionWires r) (terminalConditionValue r) state = false := by
    rw [terminalConditionWires, terminalConditionValue, terminal_detection, hrp]
    simp
  have hencoded : IndexedStepEpochEncoded r state := by
    simp only [IndexedStepEpochEncoded, hcondition, Bool.false_eq_true, if_false]
    exact hclean _ hlayout.shiftEpoch_mem_aux
  have hr : wireAnd r.lengthRPrime (run (indexedStepShiftPrefix r n T) state) = false :=
    (wireAnd_congr _ _ state (indexedStepShiftPrefix_remainder r n T state hlayout hclean hrp)).trans hrp
  have he := indexedStepShiftPrefix_clean r n T state hlayout hclean hrp
  have hs : T % 4 = 0 → wireAnd r.lengthS (run (indexedStepShiftPrefix r n T) state) = false := by
    intro hT
    cases hh : wireAnd r.lengthS (run (indexedStepShiftPrefix r n T) state) with
    | false => rfl
    | true =>
      have hv := active_all_ones r.lengthS (run (indexedStepShiftPrefix r n T) state) hh
      rw [indexedStepShiftPrefix_counter r n T state hlayout hclean hrp] at hv
      exact (hshift hT hv).elim
  exact indexedStepUnitary_active_tail_correct r n T boundary4 boundary5
    hboundary4 hboundary5 state hlayout hready hencoded hroutes hr
    (he _ hlayout.shiftEpoch_mem_aux) hs

private theorem active_H_epoch (r : IndexedStepRegisters) (n T b4 b5 : Nat)
    (state : BasisState) (hl : IndexedStepLayout r n T) :
    blockHForwardState r n T b4 b5 state r.shiftEpoch = state r.shiftEpoch := by
  have hq : r.shiftEpoch ≠ r.sourceScratch.getD 0 0 := by
    intro h
    apply hl.shiftEpoch_not_sourceScratch
    rw [h, ← hl.sourceScratch_view2]
    simp
  have hs : r.shiftEpoch ≠ r.sourceScratch.getD 1 0 := by
    intro h
    apply hl.shiftEpoch_not_sourceScratch
    rw [h, ← hl.sourceScratch_view2]
    simp
  have hc := hl.control_ne_shiftEpoch.symm
  have hi : r.shiftEpoch ≠ r.iter := hl.aux_not_payload hl.shiftEpoch_mem_aux
    (by simp [indexedStepPayload])
  have hm := hl.aux_not_endIterationMutable hl.shiftEpoch_mem_aux
  have fq (s : BasisState) := andListXorState_preserves r.lengthQ
    (r.sourceScratch.getD 0 0) s hq
  have fs (s : BasisState) := andListXorState_preserves (r.lengthS ++ [r.shiftEpoch])
    (r.sourceScratch.getD 1 0) s hs
  have fc (s : BasisState) := andXorWireState_preserves
    (r.sourceScratch.getD 0 0) (r.sourceScratch.getD 1 0) r.control s hc
  have fi (s : BasisState) := xorWireState_preserves r.control r.iter s hi
  have fm (s : BasisState) := endIterationForwardState_preservesOutside r n T b4 b5 s hm
  by_cases hT : T % 4 = 0
  · simp only [blockHForwardState, hT, ↓reduceIte, blockHEndInputState,
      blockHZeroSState, blockHBeforeSState, blockHZeroQState, fq, fs, fc, fi, fm,
      upd_same, Bool.not_not]
  · simp only [blockHForwardState, hT, ↓reduceIte]

/-- A clean nonterminal input returns the entire auxiliary bank clear even when
the end-iteration block runs. This does not assert the next terminal encoding. -/
theorem indexedStepUnitary_active_clean
    (r : IndexedStepRegisters) (n T boundary4 boundary5 : Nat)
    (hboundary4 : (endIterationWindowsAt n T).k4 ≤ boundary4 ∧
      boundary4 ≤ (endIterationWindowsAt n T).K4)
    (hboundary5 : (endIterationWindowsAt n T).k5 ≤ boundary5 ∧
      boundary5 ≤ (endIterationWindowsAt n T).K5Decode n)
    (state : BasisState) (hlayout : IndexedStepLayout r n T)
    (hclean : Clean r.aux state) (hrp : wireAnd r.lengthRPrime state = false)
    (hroutes : T % 4 = 0 → indexedStepEndRoutes r n T state = (boundary4, boundary5)) :
    Clean r.aux (run (indexedStepUnitary r n T) state) := by
  have hready : IndexedStepReady r state := by
    intro wire hw
    apply hclean wire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons, List.mem_append] at hw
    rcases hw with he | he | he
    · subst wire; exact hlayout.control_mem_aux
    · exact hlayout.sourceScratch_mem_aux he
    · exact hlayout.remainderRepairScratch_mem_aux he
  have hcondition : registerMatches (terminalConditionWires r) (terminalConditionValue r) state = false := by
    rw [terminalConditionWires, terminalConditionValue, terminal_detection, hrp]
    simp
  have hencoded : IndexedStepEpochEncoded r state := by
    simp only [IndexedStepEpochEncoded, hcondition, Bool.false_eq_true, if_false]
    exact hclean _ hlayout.shiftEpoch_mem_aux
  have hf := indexedStepUnitary_correct r n T boundary4 boundary5 hboundary4 hboundary5
    state hlayout hready hencoded hroutes
  have hp := active_shift_prefix r n T state hlayout hready hencoded
  have hc := indexedStepShiftPrefix_clean r n T state hlayout hclean hrp
  have hout : run (indexedStepUnitary r n T) state =
      blockHForwardState r n T boundary4 boundary5
        (blockGForwardState r (run (indexedStepShiftPrefix r n T) state)) := by
    rw [hf.1, indexedStepForwardState, ← hp.1]
  have hz : run (indexedStepUnitary r n T) state r.shiftEpoch = false := by
    rw [hout, active_H_epoch r n T boundary4 boundary5 _ hlayout]
    exact (active_phase_frame r n T _ hlayout (by
      simp [indexedStepAfterSign, hlayout.shiftEpoch_mem_aux])).trans
      (hc _ hlayout.shiftEpoch_mem_aux)
  intro wire hw
  rw [← hlayout.aux_view] at hw
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with (h | h) | h | h
  · subst wire
    exact hf.2 _ (by simp [IndexedStepRegisters.sharedScratch])
  · subst wire; exact hz
  · exact hf.2 _ (hlayout.sourceScratch_mem_sharedScratch h)
  · exact hf.2 _ (hlayout.remainderRepairScratch_mem_sharedScratch h)

private theorem active_counter_wrapper_bits (controls : List Wire) (value : Nat)
    (target : Wire) (register : List Wire) (state : BasisState)
    (f : Bool → List Bool → List Bool) (hnd : register.Nodup)
    (ht : target ∉ register) (hz : state target = false)
    (hlen : ∀ b xs, (f b xs).length = xs.length) :
    let enabled := matchXorState controls value target state
    wireValues register (matchXorState controls value target
      (indexedWriteWireValues register (f (enabled target) (wireValues register enabled)) enabled)) =
      f (registerMatches controls value state) (wireValues register state) := by
  dsimp only
  have hf (s : BasisState) : wireValues register (matchXorState controls value target s) =
      wireValues register s := by
    apply wireValues_congr_indexedStep
    intro w hw
    exact matchXorState_preserves _ _ _ _ (by intro h; subst w; exact ht hw)
  rw [hf, indexedWireValues_writeWireValues _ _ _ hnd (by rw [hlen]; simp [wireValues]), hf]
  congr 1
  simp only [matchXorState, upd_same, hz, Bool.false_xor]

private theorem active_Q_nodup (r : IndexedStepRegisters) (n T : Nat)
    (hl : IndexedStepLayout r n T) : r.lengthQ.Nodup := by
  have hp : ((indexedStepBeforeLengthQ r ++ r.lengthQ) ++ indexedStepAfterLengthQ r).Nodup := by
    simpa only [indexedStepBeforeLengthQ, indexedStepAfterLengthQ,
      IndexedStepRegisters.allWires, List.append_assoc] using hl.physical
  exact (List.nodup_append.mp (List.nodup_append.mp hp).1).2.1

private theorem active_D1_bits (r : IndexedStepRegisters) (n T : Nat)
    (s : BasisState) (hl : IndexedStepLayout r n T) (hc : s r.control = false) :
    wireValues r.lengthQ (blockD1ForwardState r s) =
      incrementBits (registerMatches [r.phase1, r.phase2] 2 s) (wireValues r.lengthQ s) := by
  exact active_counter_wrapper_bits _ _ _ _ s incrementBits (active_Q_nodup r n T hl)
    (by intro hw; exact hl.aux_not_payload hl.control_mem_aux (by simp [indexedStepPayload, hw]) rfl)
    hc indexedIncrementBits_length

private theorem active_D3_bits (r : IndexedStepRegisters) (n T : Nat)
    (s : BasisState) (hl : IndexedStepLayout r n T) (hc : s r.control = false) :
    wireValues r.lengthQ (blockD3ForwardState r s) =
      decrementBits (registerMatches [r.phase1, r.phase2] 1 s) (wireValues r.lengthQ s) := by
  exact active_counter_wrapper_bits _ _ _ _ s decrementBits (active_Q_nodup r n T hl)
    (by intro hw; exact hl.aux_not_payload hl.control_mem_aux (by simp [indexedStepPayload, hw]) rfl)
    hc indexedDecrementBits_length

private theorem active_D1_frame (r : IndexedStepRegisters) (s : BasisState)
    {wire : Wire} (hq : wire ∉ r.lengthQ) (hc : wire ≠ r.control) :
    blockD1ForwardState r s wire = s wire := by
  unfold blockD1ForwardState
  rw [matchXorState_preserves _ _ _ _ hc,
    indexedIncrementWordState_preservesOutside _ _ _ hq,
    matchXorState_preserves _ _ _ _ hc]

/-- The phase-2 quotient counter update, with every other wire restored. -/
theorem blockD1Forward_contract (r : IndexedStepRegisters) (n index : Nat)
    (s : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux s) :
    let final := run (blockD1Forward r) s
    wireValues r.lengthQ final = incrementBits (!s r.phase1 && s r.phase2) (wireValues r.lengthQ s) ∧
      AgreesOutside r.lengthQ final s ∧ Clean r.aux final := by
  dsimp only
  have hready : IndexedStepReady r s := by
    intro wire hw
    apply hc wire
    simp only [IndexedStepRegisters.sharedScratch,List.mem_cons,List.mem_append] at hw
    rcases hw with he | hs | hr
    · subst wire; exact h.control_mem_aux
    · exact h.sourceScratch_mem_aux hs
    · exact List.mem_of_mem_drop hr
  have hrun := blockD1Forward_correct r n index s h hready
  change run (blockD1Forward r) s = blockD1ForwardState r s ∧
    IndexedStepReady r (run (blockD1Forward r) s) at hrun
  have hcontrol := hc r.control h.control_mem_aux
  have hf : AgreesOutside r.lengthQ (run (blockD1Forward r) s) s := by
    intro wire hw
    by_cases he : wire = r.control
    · subst wire
      exact (hrun.2 r.control (by simp [IndexedStepRegisters.sharedScratch])).trans hcontrol.symm
    · rw [hrun.1]
      exact active_D1_frame r s hw he
  refine ⟨?_,hf,?_⟩
  · rw [hrun.1,active_D1_bits r n index s h hcontrol]
    have hb : Nat.testBit 2 1 = true := by decide
    simp [registerMatches,registerMatchesFrom,hb]
  · intro wire hw
    rw [hf wire (by intro hq; exact (h.aux_not_payload hw (by simp [indexedStepPayload,hq])) rfl)]
    exact hc wire hw

/-- The phase-3 quotient counter update, with every other wire restored. -/
theorem blockD3Forward_contract (r : IndexedStepRegisters) (n index : Nat)
    (s : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux s) :
    let final := run (blockD3Forward r) s
    wireValues r.lengthQ final = decrementBits (s r.phase1 && !s r.phase2) (wireValues r.lengthQ s) ∧
      AgreesOutside r.lengthQ final s ∧ Clean r.aux final := by
  dsimp only
  have hready : IndexedStepReady r s := by
    intro wire hw
    apply hc wire
    simp only [IndexedStepRegisters.sharedScratch,List.mem_cons,List.mem_append] at hw
    rcases hw with he | hs | hr
    · subst wire; exact h.control_mem_aux
    · exact h.sourceScratch_mem_aux hs
    · exact List.mem_of_mem_drop hr
  have hrun := blockD3Forward_correct r n index s h hready
  change run (blockD3Forward r) s = blockD3ForwardState r s ∧
    IndexedStepReady r (run (blockD3Forward r) s) at hrun
  have hcontrol := hc r.control h.control_mem_aux
  have hf : AgreesOutside r.lengthQ (run (blockD3Forward r) s) s := by
    intro wire hw
    by_cases he : wire = r.control
    · subst wire
      exact (hrun.2 r.control (by simp [IndexedStepRegisters.sharedScratch])).trans hcontrol.symm
    · rw [hrun.1]
      unfold blockD3ForwardState
      rw [matchXorState_preserves _ _ _ _ he,
        indexedDecrementWordState_preservesOutside _ _ _ hw,
        matchXorState_preserves _ _ _ _ he]
  refine ⟨?_,hf,?_⟩
  · rw [hrun.1,active_D3_bits r n index s h hcontrol]
    have hb : Nat.testBit 1 1 = false := by decide
    simp [registerMatches,registerMatchesFrom,hb]
  · intro wire hw
    rw [hf wire (by intro hq; exact (h.aux_not_payload hw (by simp [indexedStepPayload,hq])) rfl)]
    exact hc wire hw

private theorem active_D2_frame (r : IndexedStepRegisters) (n T : Nat)
    (window : ActiveWindow) (s : BasisState) (hl : IndexedStepLayout r n T)
    (hwnd : window = (certifiedActiveWindows n T).quotientSwap)
    {wire : Wire} (hs : wire ≠ r.sign) (hw : wire ∉ r.work1) (hc : wire ≠ r.control) :
    blockD2ForwardState r window s wire = s wire := by
  unfold blockD2ForwardState
  rw [xorWireState_preserves _ _ _ hc, xorWireState_preserves _ _ _ hc,
    active_quotient_frame r n T window _ hl hwnd hs hw,
    xorWireState_preserves _ _ _ hc, xorWireState_preserves _ _ _ hc]

private theorem active_D_bits (r : IndexedStepRegisters) (n T : Nat)
    (window : ActiveWindow) (s : BasisState) (hl : IndexedStepLayout r n T)
    (hwnd : window = (certifiedActiveWindows n T).quotientSwap)
    (hready : IndexedStepReady r s) :
    wireValues r.lengthQ (blockDForwardState r window s) =
      decrementBits (registerMatches [r.phase1, r.phase2] 1 s)
        (incrementBits (registerMatches [r.phase1, r.phase2] 2 s) (wireValues r.lengthQ s)) := by
  let a := blockD1ForwardState r s
  let b := blockD2ForwardState r window a
  have h1 := blockD1Forward_correct r n T s hl hready
  have ha := h1.2
  rw [h1.1] at ha
  have h2 := blockD2Forward_correct r n T window a hl hwnd ha
  have hb := h2.2
  rw [h2.1] at hb
  have hphase : ∀ wire ∈ [r.phase1, r.phase2], b wire = s wire := by
    intro wire hw
    have hn := List.disjoint_left.mp (active_metadata_geometry r n T hl)
      (List.mem_append_left r.lengthS hw)
    have hsign : wire ≠ r.sign := by intro h; apply hn; simp [h]
    have hwork : wire ∉ r.work1 := fun h => hn (by simp [h])
    have hQ : wire ∉ r.lengthQ := fun h => hn (by simp [h])
    have hcontrol : wire ≠ r.control := by intro h; apply hn; simp [h, hl.control_mem_aux]
    dsimp only [b]
    rw [active_D2_frame r n T window a hl hwnd hsign hwork hcontrol]
    exact active_D1_frame r s hQ hcontrol
  have hword : wireValues r.lengthQ b = wireValues r.lengthQ a := by
    apply wireValues_congr_indexedStep
    intro wire hw
    have hsign : wire ≠ r.sign := hl.lengthQ_ne_outside hw
      (Or.inl (by simp [indexedStepBeforeLengthQ]))
    have hwork : wire ∉ r.work1 := by
      intro hm
      exact (hl.lengthQ_ne_outside hw (Or.inl (by simp [indexedStepBeforeLengthQ, hm]))) rfl
    have hcontrol : wire ≠ r.control := hl.lengthQ_ne_outside hw
      (Or.inr (by simp [indexedStepAfterLengthQ, hl.control_mem_aux]))
    exact active_D2_frame r n T window a hl hwnd hsign hwork hcontrol
  change wireValues r.lengthQ (blockD3ForwardState r b) = _
  rw [active_D3_bits r n T b hl (hb _ (by simp [IndexedStepRegisters.sharedScratch])),
    registerMatches_congr _ _ b s hphase, hword]
  exact congrArg _ (active_D1_bits r n T s hl (hready _ (by simp [IndexedStepRegisters.sharedScratch])))

private theorem active_Q_shift_support (r : IndexedStepRegisters) (n T : Nat)
    (hl : IndexedStepLayout r n T) {wire : Wire} (hw : wire ∈ r.lengthQ) :
    wire ∉ r.preShift.preUsedWires ∧ wire ∉ r.postShift.postUsedWires := by
  have hp : wire ∉ indexedStepShiftPayload r := by
    intro hm
    apply (hl.lengthQ_ne_outside hw ?_) rfl
    simp only [indexedStepShiftPayload, indexedStepBeforeLengthQ, indexedStepAfterLengthQ,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    aesop
  have ha : wire ∉ r.aux := by
    intro hm
    exact (hl.lengthQ_ne_outside hw (Or.inr (by simp [indexedStepAfterLengthQ, hm]))) rfl
  constructor
  · intro hm
    rcases hl.preShift_used_payload_or_scratch hm with hm | hm
    · exact hp hm
    · exact ha (hl.blockScratch_mem_aux (hl.preShift_scratch_sub_block wire hm))
  · intro hm
    have hs : wire ∉ r.postShift.scratch := fun h =>
      ha (hl.sourceScratch_mem_aux (hl.postShift_scratch_sub_source wire h))
    change wire ∉ [r.phase1, r.phase2] ++ r.work2 ++ r.lengthS at hp
    change wire ∈ [r.phase1, r.phase2, r.postShift.both] ++
      r.work2 ++ r.lengthS ++ r.postShift.carries at hm
    change wire ∉ [r.postShift.phase1IsZero, r.postShift.both] ++
      r.postShift.carries ++ r.postShift.reserved at hs
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hp hm hs
    aesop

private theorem active_Q_frame_geometry (r : IndexedStepRegisters) (n T : Nat)
    (hl : IndexedStepLayout r n T) {wire : Wire} (hw : wire ∈ r.lengthQ) :
    wire ∉ r.sign :: r.work1 ++ r.work2 ∧ wire ≠ r.control ∧ wire ≠ r.terminal := by
  have ht : r.terminal ∈ r.aux := hl.sourceScratch_mem_aux (by rw [← hl.scratch_view]; simp)
  refine ⟨?_, hl.lengthQ_ne_outside hw (Or.inr (by simp [indexedStepAfterLengthQ, hl.control_mem_aux])),
    hl.lengthQ_ne_outside hw (Or.inr (by simp [indexedStepAfterLengthQ, ht]))⟩
  intro hm
  apply (hl.lengthQ_ne_outside hw (Or.inl ?_)) rfl
  simp only [List.mem_append, List.mem_cons] at hm
  rcases hm with (h | h) | h <;> simp [indexedStepBeforeLengthQ, h]

private theorem active_dec_false (xs : List Bool) : decrementBits false xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [decrementBits, ih]

attribute [local simp] active_inc_false active_dec_false
  boolWordToNat_incrementBits boolWordToNat_decrementBits

/-- The quotient-length counter increments in phase (false,true), decrements in
phase (true,false), and is unchanged when the phase bits agree. -/
theorem indexedStepShiftPrefix_quotient_counter (r : IndexedStepRegisters) (n T : Nat)
    (state : BasisState) (hlayout : IndexedStepLayout r n T) (hclean : Clean r.aux state)
    (hrp : wireAnd r.lengthRPrime state = false) :
    boolWordToNat (wireValues r.lengthQ (run (indexedStepShiftPrefix r n T) state)) =
      if state r.phase1 then
        if state r.phase2 then boolWordToNat (wireValues r.lengthQ state)
        else (boolWordToNat (wireValues r.lengthQ state) + 2^r.lengthQ.length - 1) % 2^r.lengthQ.length
      else if state r.phase2 then (1 + boolWordToNat (wireValues r.lengthQ state)) % 2^r.lengthQ.length
      else boolWordToNat (wireValues r.lengthQ state) := by
  have hready : IndexedStepReady r state := by
    intro wire hw
    apply hclean wire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons, List.mem_append] at hw
    rcases hw with he | he | he
    · subst wire; exact hlayout.control_mem_aux
    · exact hlayout.sourceScratch_mem_aux he
    · exact hlayout.remainderRepairScratch_mem_aux he
  have hcondition : registerMatches (terminalConditionWires r) (terminalConditionValue r) state = false := by
    rw [terminalConditionWires, terminalConditionValue, terminal_detection, hrp]
    simp
  have hencoded : IndexedStepEpochEncoded r state := by
    simp only [IndexedStepEpochEncoded, hcondition, Bool.false_eq_true, if_false]
    exact hclean _ hlayout.shiftEpoch_mem_aux
  let a := run (blockAForward r) state
  have ha := blockAForward_correct r n T state hlayout hready
  have har := blockAForward_borrowedReady r n T state hlayout hready hencoded
  have hap : a = run (preShiftUnitary r.preShift) state :=
    ha.1.trans (active_A_shift r n T state hlayout hclean hcondition)
  let b := run (blockBForward r n (certifiedActiveWindows n T).remainder) a
  have hb := blockBForward_correct r n T _ a hlayout rfl har
  let c := run (blockCForward r) b
  have hc := blockCForward_correct r n T b hlayout hb.2
  let d := run (blockDForward r (certifiedActiveWindows n T).quotientSwap) c
  have hd := blockDForward_correct r n T _ c hlayout rfl hc.2
  let e := run (blockEForward r n (certifiedActiveWindows n T).coefficient) d
  have he := blockEForward_correct r n T _ d hlayout rfl hd.2

  have hbits : ∀ wire ∈ r.lengthRPrime, b wire = state wire := by
    intro wire hw
    have hg := active_boundary_geometry r n T hlayout (w := wire) (by simp [hw])
    dsimp only [b]
    rw [hb.1, active_B_frame r n T _ a hlayout rfl har hg.1 hg.2.1 hg.2.2, hap]
    exact preShiftUnitary_preservesOutside _ _ (hlayout.lengthRPrime_not_preShift hw)
  have hbrp : wireAnd r.lengthRPrime b = false := (wireAnd_congr _ b state hbits).trans hrp
  have hterminal : r.terminal ∈ r.sourceScratch := by rw [← hlayout.scratch_view]; simp
  have hcidle : c = b := hc.1.trans (active_C_idle r b
    (hb.2 _ (hlayout.sourceScratch_mem_aux hterminal)) hbrp)
  have hpReady : ShiftReady r.preShift state := by
    intro wire hw
    exact hclean wire (hlayout.blockScratch_mem_aux (hlayout.preShift_scratch_sub_block wire hw))
  have hphase : ∀ wire ∈ [r.phase1, r.phase2], c wire = state wire := by
    intro wire hw
    have hn := List.disjoint_left.mp (active_metadata_geometry r n T hlayout)
      (List.mem_append_left r.lengthS hw)
    have hdata : wire ∉ r.sign :: r.work1 ++ r.work2 := by
      intro hm
      exact hn (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ hm))))
    have hctl : wire ≠ r.control := by intro h; apply hn; simp [h, hlayout.control_mem_aux]
    have hterm : wire ≠ r.terminal := by
      intro h; apply hn; simp [h, hlayout.sourceScratch_mem_aux hterminal]
    rw [hcidle]
    dsimp only [b]
    rw [hb.1, active_B_frame r n T _ a hlayout rfl har hdata hctl hterm, hap]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h
    · subst wire; exact preShiftUnitary_preserves_phase1 _ _ hlayout.preShift hpReady
    · subst wire; exact preShiftUnitary_preserves_phase2 _ _ hlayout.preShift hpReady
  have hQ : wireValues r.lengthQ c = wireValues r.lengthQ state := by
    apply wireValues_congr_indexedStep
    intro wire hw
    have hg := active_Q_frame_geometry r n T hlayout hw
    rw [hcidle]
    dsimp only [b]
    rw [hb.1, active_B_frame r n T _ a hlayout rfl har hg.1 hg.2.1 hg.2.2, hap]
    exact preShiftUnitary_preservesOutside _ _ (active_Q_shift_support r n T hlayout hw).1
  have hshape : run (indexedStepShiftPrefix r n T) state = run (postShiftUnitary r.postShift) e := by
    simp only [indexedStepShiftPrefix, indexedStepRemainderPrefix, blockFForward, e, d, c, b, a,
      Classical.run_append]
  have hlast : wireValues r.lengthQ (run (indexedStepShiftPrefix r n T) state) =
      wireValues r.lengthQ d := by
    apply wireValues_congr_indexedStep
    intro wire hw
    rw [hshape, postShiftUnitary_preservesOutside _ _ (active_Q_shift_support r n T hlayout hw).2]
    have hg := active_Q_frame_geometry r n T hlayout hw
    dsimp only [e]
    rw [he.1, active_E_frame r n T _ d hlayout rfl
      (fun w h => hd.2 w (hlayout.blockScratch_mem_sharedScratch h)) hg.1 hg.2.1 hg.2.2]
  have hD : wireValues r.lengthQ d =
      decrementBits (registerMatches [r.phase1, r.phase2] 1 c)
        (incrementBits (registerMatches [r.phase1, r.phase2] 2 c) (wireValues r.lengthQ c)) := by
    dsimp only [d]
    rw [hd.1]
    exact active_D_bits r n T _ c hlayout rfl hc.2
  rw [hlast, hD, registerMatches_congr _ 1 c state hphase,
    registerMatches_congr _ 2 c state hphase, hQ]
  cases hp1 : state r.phase1 <;> cases hp2 : state r.phase2 <;>
    simp [registerMatches, registerMatchesFrom, hp1, hp2, wireValues, Nat.testBit]

private theorem active_H_quotient_idle (registers : IndexedStepRegisters) (n T b4 b5 : Nat)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state)
    (hz : wireAnd registers.lengthQ state = false) :
    blockHForwardState registers n T b4 b5 state = state := by
  have hqmem : registers.sourceScratch.getD 0 0 ∈ registers.sourceScratch :=
    indexedStep_getD_mem _ _ _ (by rw [hlayout.sourceScratch_length]; decide)
  have hsmem : registers.sourceScratch.getD 1 0 ∈ registers.sourceScratch :=
    indexedStep_getD_mem _ _ _ (by rw [hlayout.sourceScratch_length]; decide)
  have hqaux := hlayout.sourceScratch_mem_aux hqmem
  have hsaux := hlayout.sourceScratch_mem_aux hsmem
  have hcq : registers.control ≠ registers.sourceScratch.getD 0 0 := by
    intro he
    exact hlayout.control_not_sourceScratch (he ▸ hqmem)
  have hcs : registers.control ≠ registers.sourceScratch.getD 1 0 := by
    intro he
    exact hlayout.control_not_sourceScratch (he ▸ hsmem)
  have heq : registers.shiftEpoch ≠ registers.sourceScratch.getD 0 0 := by
    intro he
    exact hlayout.shiftEpoch_not_sourceScratch (he ▸ hqmem)
  have hes : registers.shiftEpoch ≠ registers.sourceScratch.getD 1 0 := by
    intro he
    exact hlayout.shiftEpoch_not_sourceScratch (he ▸ hsmem)
  have hnodup : (registers.sourceScratch.getD 0 0 :: registers.sourceScratch.getD 1 0 ::
      registers.sourceScratch.drop 2).Nodup := by
    rw [hlayout.sourceScratch_view2]
    exact hlayout.sourceScratch_nodup
  have hsq : registers.sourceScratch.getD 1 0 ≠ registers.sourceScratch.getD 0 0 := by
    intro he
    exact (List.nodup_cons.mp hnodup).1 (by simp only [List.mem_cons]; exact Or.inl he.symm)
  have hqQ : registers.sourceScratch.getD 0 0 ∉ registers.lengthQ := by
    intro hm
    exact (hlayout.aux_not_payload hqaux (by simp only [indexedStepPayload, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto)) rfl
  have hsS : registers.sourceScratch.getD 1 0 ∉ registers.lengthS ++ [registers.shiftEpoch] := by
    simp only [List.mem_append, List.mem_singleton, not_or]
    refine ⟨?_, Ne.symm hes⟩
    intro hm
    exact (hlayout.aux_not_payload hsaux (by simp only [indexedStepPayload, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto)) rfl
  have hqzero := hready _ (hlayout.sourceScratch_mem_sharedScratch hqmem)
  have hczero := hready registers.control (by simp [IndexedStepRegisters.sharedScratch])
  have hc : blockHEndInputState registers state registers.control = false := by
    simp only [blockHEndInputState, blockHZeroSState, blockHBeforeSState,
      blockHZeroQState, andXorWireState, andListXorState, upd,
      hcq, hcs, hlayout.control_ne_shiftEpoch, heq.symm, hsq.symm,
      hz, hqzero, hczero, ↓reduceIte, Bool.xor_false, Bool.false_and]
  exact endIdle_block registers n T b4 b5 state hqQ hsS (Ne.symm hcq) (Ne.symm hcs) hc

private theorem active_H_Q_frame (r : IndexedStepRegisters) (n T b4 b5 : Nat)
    (state : BasisState) (hl : IndexedStepLayout r n T)
    {wire : Wire} (hw : wire ∈ r.lengthQ) :
    blockHForwardState r n T b4 b5 state wire = state wire := by
  have hp : wire ∈ indexedStepPayload r := by simp [indexedStepPayload, hw]
  have hqmem : r.sourceScratch.getD 0 0 ∈ r.sourceScratch :=
    indexedStep_getD_mem _ _ _ (by rw [hl.sourceScratch_length]; decide)
  have hsmem : r.sourceScratch.getD 1 0 ∈ r.sourceScratch :=
    indexedStep_getD_mem _ _ _ (by rw [hl.sourceScratch_length]; decide)
  have hq := (hl.aux_not_payload (hl.sourceScratch_mem_aux hqmem) hp).symm
  have hs := (hl.aux_not_payload (hl.sourceScratch_mem_aux hsmem) hp).symm
  have hc := (hl.aux_not_payload hl.control_mem_aux hp).symm
  have he := (hl.aux_not_payload hl.shiftEpoch_mem_aux hp).symm
  have hi : wire ≠ r.iter := hl.lengthQ_ne_outside hw (Or.inl (by
    simp [indexedStepBeforeLengthQ]))
  have fq (s : BasisState) := andListXorState_preserves r.lengthQ
    (r.sourceScratch.getD 0 0) s hq
  have fs (s : BasisState) := andListXorState_preserves (r.lengthS ++ [r.shiftEpoch])
    (r.sourceScratch.getD 1 0) s hs
  have fc (s : BasisState) := andXorWireState_preserves
    (r.sourceScratch.getD 0 0) (r.sourceScratch.getD 1 0) r.control s hc
  have fi (s : BasisState) := xorWireState_preserves r.control r.iter s hi
  have fm (s : BasisState) := endIterationForwardState_preservesOutside r n T b4 b5 s
    (hl.lengthQ_not_endIterationMutable hw)
  by_cases hT : T % 4 = 0
  · simp only [blockHForwardState, hT, ↓reduceIte, blockHEndInputState,
      blockHZeroSState, blockHBeforeSState, blockHZeroQState, fq, fs, fc, fi, fm,
      upd, he, ↓reduceIte]
  · simp only [blockHForwardState, hT, ↓reduceIte]


private theorem active_wireAnd_member (ws : List Wire) (state : BasisState)
    (h : wireAnd ws state = true) {wire : Wire} (hw : wire ∈ ws) : state wire = true := by
  induction ws with
  | nil => simp at hw
  | cons w ws ih =>
    simp only [wireAnd, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hw with he | hm
    · subst wire; exact h.1
    · exact ih h.2 hm

set_option maxHeartbeats 1000000 in
/-- A routed step from a clean nonterminal input preserves the terminal epoch encoding,
including enabled end-iteration boundaries. -/
theorem indexedStepUnitary_active_encoded
    (r : IndexedStepRegisters) (n T boundary4 boundary5 : Nat)
    (hboundary4 : (endIterationWindowsAt n T).k4 ≤ boundary4 ∧
      boundary4 ≤ (endIterationWindowsAt n T).K4)
    (hboundary5 : (endIterationWindowsAt n T).k5 ≤ boundary5 ∧
      boundary5 ≤ (endIterationWindowsAt n T).K5Decode n)
    (state : BasisState) (hlayout : IndexedStepLayout r n T)
    (hclean : Clean r.aux state) (hrp : wireAnd r.lengthRPrime state = false)
    (hroutes : T % 4 = 0 → indexedStepEndRoutes r n T state = (boundary4, boundary5)) :
    IndexedStepEpochEncoded r (run (indexedStepUnitary r n T) state) := by
  have hready : IndexedStepReady r state := by
    intro wire hw
    apply hclean wire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons, List.mem_append] at hw
    rcases hw with he | he | he
    · subst wire; exact hlayout.control_mem_aux
    · exact hlayout.sourceScratch_mem_aux he
    · exact hlayout.remainderRepairScratch_mem_aux he
  have hcondition : registerMatches (terminalConditionWires r) (terminalConditionValue r) state = false := by
    rw [terminalConditionWires, terminalConditionValue, terminal_detection, hrp]
    simp
  have hencoded : IndexedStepEpochEncoded r state := by
    simp only [IndexedStepEpochEncoded, hcondition, Bool.false_eq_true, if_false]
    exact hclean _ hlayout.shiftEpoch_mem_aux
  have hf := indexedStepUnitary_correct r n T boundary4 boundary5 hboundary4 hboundary5
    state hlayout hready hencoded hroutes
  have hp := active_shift_prefix r n T state hlayout hready hencoded
  have hout : run (indexedStepUnitary r n T) state =
      blockHForwardState r n T boundary4 boundary5
        (blockGForwardState r (run (indexedStepShiftPrefix r n T) state)) := by
    rw [hf.1, indexedStepForwardState, ← hp.1]
  have hcleanOut := indexedStepUnitary_active_clean r n T boundary4 boundary5
    hboundary4 hboundary5 state hlayout hclean hrp hroutes
  have hg := blockGForward_correct r n T _ hlayout hp.2
  have hgReady := hg.2
  rw [hg.1] at hgReady
  have hR : wireAnd r.lengthRPrime
      (blockGForwardState r (run (indexedStepShiftPrefix r n T) state)) = false := by
    calc
      _ = wireAnd r.lengthRPrime (run (indexedStepShiftPrefix r n T) state) :=
        wireAnd_congr _ _ _ (fun wire hw => active_phase_frame r n T _ hlayout (by
          simp [indexedStepAfterSign, hw]))
      _ = wireAnd r.lengthRPrime state := wireAnd_congr _ _ _
        (fun wire hw => indexedStepShiftPrefix_remainder r n T state hlayout hclean hrp wire hw)
      _ = false := hrp
  by_cases hQ : wireAnd r.lengthQ
      (blockGForwardState r (run (indexedStepShiftPrefix r n T) state)) = true
  · have hbit := active_wireAnd_member _ _ hQ hlayout.quotientLow_mem_lengthQ
    have hbitOut : run (indexedStepUnitary r n T) state r.quotientLow = true := by
      rw [hout, active_H_Q_frame r n T boundary4 boundary5 _ hlayout
        hlayout.quotientLow_mem_lengthQ]
      exact hbit
    unfold IndexedStepEpochEncoded
    split
    · exact hbitOut
    · exact hcleanOut _ hlayout.shiftEpoch_mem_aux
  · have hQfalse : wireAnd r.lengthQ
        (blockGForwardState r (run (indexedStepShiftPrefix r n T) state)) = false :=
      Bool.eq_false_iff.mpr hQ
    have hidle := active_H_quotient_idle r n T boundary4 boundary5 _ hlayout hgReady hQfalse
    have hRout : wireAnd r.lengthRPrime (run (indexedStepUnitary r n T) state) = false := by
      rw [hout, hidle]
      exact hR
    have hconditionOut : registerMatches (terminalConditionWires r)
        (terminalConditionValue r) (run (indexedStepUnitary r n T) state) = false := by
      rw [terminalConditionWires, terminalConditionValue, terminal_detection, hRout]
      simp
    simp only [IndexedStepEpochEncoded, hconditionOut, Bool.false_eq_true, if_false]
    exact hcleanOut _ hlayout.shiftEpoch_mem_aux



/-- Block B1 prepares its nonterminal phase control, executes the actual interval,
and clears the control again. The existing complete-state proof supplies both
the prepared interval readiness and final clean auxiliary bank. -/
theorem run_blockB1Forward_interval (r : IndexedStepRegisters) (n index : Nat)
    (state : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux state) :
    let w := (certifiedActiveWindows n index).remainder
    let enabled := state[r.control ↦ rControlNonterminalPredicate [r.phase1] 0 r.lengthRPrime r.terminal state]
    let changed := run (intervalAddSubUnitary (r.remainder w) n w.start w.stop .sub true .work1) enabled
    run (blockB1Forward r n w) state = changed[r.control ↦ false] ∧
      IntervalReady (r.remainder w) enabled ∧ Clean r.aux (run (blockB1Forward r n w) state) := by
  let w := (certifiedActiveWindows n index).remainder
  let enabled := state[r.control ↦ rControlNonterminalPredicate [r.phase1] 0 r.lengthRPrime r.terminal state]
  have hzero := hc _ h.control_mem_aux
  have he : rControlState [r.phase1] 0 r.control r.lengthRPrime r.terminal state = enabled := by
    simp only [rControlState,hzero,Bool.false_xor,enabled]
  have hr : IntervalReady (r.remainder w) enabled := by
    intro wire hw
    have hne : wire ≠ r.control := by
      intro heq
      subst wire
      exact h.control_not_remainder_scratch w rfl hw
    simp only [enabled,upd,hne,if_false]
    exact hc wire (h.remainder_scratch_sub_aux w wire hw)
  have hf := blockB1Forward_correct r n index w state h rfl hc
  have hi := run_intervalAddSubUnitary_state (r.remainder w) n w.start w.stop .sub true .work1 enabled h.remainder hr
  have hcontrol := hf.2 r.control h.control_mem_aux
  dsimp only
  refine ⟨?_,hr,hf.2⟩
  apply funext
  intro wire
  by_cases hn : wire = r.control
  · subst wire
    simpa [upd] using hcontrol
  · rw [hf.1]
    simp only [blockB1ForwardState,he]
    rw [rControlState_preserves _ _ _ _ _ _ hn,← hi]
    simp only [upd,hn,if_false]
    rfl

/-- The restore control is active before phase one, outside the terminal state,
unless both phase two and the sign flag are set. -/
private theorem remainderRestoreControlState_eq (r : IndexedStepRegisters) (n index : Nat)
    (state : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux state) :
    remainderRestoreControlState r state =
      state[r.control ↦ (!state r.phase1 && !(state r.phase2 && state r.sign) &&
        !wireAnd r.lengthRPrime state)] := by
  have htS : r.terminal ∈ r.sourceScratch := by rw [← h.scratch_view]; simp
  have htA := h.sourceScratch_mem_aux htS
  have htc : r.terminal ≠ r.control := fun he => h.control_not_sourceScratch (he ▸ htS)
  have ht1 : r.terminal ≠ r.phase1 := h.aux_not_payload htA (by simp [indexedStepPayload])
  have hc0 := hc _ h.control_mem_aux
  have ht0 := hc _ htA
  have hz : r.blockScratch.getD 0 0 ∈ r.blockScratch :=
    indexedStep_getD_mem _ _ _ (by have := h.terminalPaddingCapacity; omega)
  have hzcond : r.blockScratch.getD 0 0 ∉ [r.phase1,r.terminal] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨h.aux_not_payload (h.blockScratch_mem_aux hz) (by simp [indexedStepPayload]),
      fun he => h.terminal_not_blockScratch (he ▸ hz)⟩
  have hlength : wireAnd r.lengthRPrime (andXorWireState r.phase2 r.sign r.terminal state) =
      wireAnd r.lengthRPrime state := by
    apply wireAnd_congr
    intro wire hw
    have hn : wire ≠ r.terminal := (h.aux_not_payload htA (by simp [indexedStepPayload,hw])).symm
    simp [andXorWireState,upd,hn]
  have hf := remainderRestoreControl_correct r n index state h (by intro wire hw _; exact hc wire hw)
  apply funext
  intro wire
  by_cases hcontrol : wire = r.control
  · subst wire
    simp only [remainderRestoreControlState,andXorWireState,upd,htc.symm,if_false,
      rControlState,if_true,hc0,Bool.false_xor]
    rw [rControlNonterminalPredicate_eq _ _ _ _ _ hzcond]
    simp [registerMatches,registerMatchesFrom,andXorWireState,upd,ht1.symm,ht0] at hlength ⊢
    rw [hlength]
  · by_cases hterminal : wire = r.terminal
    · subst wire
      have hh := hf.2 r.terminal htA htc
      simpa only [upd,htc,if_false,ht0] using hh
    · rw [remainderRestoreControlState_preserves r state hterminal hcontrol]
      simp [upd,hcontrol]

/-- Actual Block B3 is the conditional interval addback followed by control
cleanup. Its sign flag is not changed by the interval. -/
theorem run_blockB3Forward_interval (r : IndexedStepRegisters) (n index : Nat)
    (state : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux state) :
    let w := (certifiedActiveWindows n index).remainder
    let enabled := state[r.control ↦ (!state r.phase1 && !(state r.phase2 && state r.sign) &&
      !wireAnd r.lengthRPrime state)]
    let changed := run (intervalAddSubUnitary (r.remainder w) n w.start w.stop .add false .work1) enabled
    run (blockB3Forward r n w) state = changed[r.control ↦ false] ∧
      IntervalReady (r.remainder w) enabled ∧ Clean r.aux (run (blockB3Forward r n w) state) := by
  let w := (certifiedActiveWindows n index).remainder
  let enabled := state[r.control ↦ (!state r.phase1 && !(state r.phase2 && state r.sign) &&
    !wireAnd r.lengthRPrime state)]
  have he := remainderRestoreControlState_eq r n index state h hc
  have hr : IntervalReady (r.remainder w) enabled := by
    intro wire hw
    have hn : wire ≠ r.control := by
      intro heq
      subst wire
      exact h.control_not_remainder_scratch w rfl hw
    simp only [enabled,upd,hn,if_false]
    exact hc wire (h.remainder_scratch_sub_aux w wire hw)
  have hf := blockB3Forward_correct r n index w state h rfl hc
  have hi := run_intervalAddSubUnitary_state (r.remainder w) n w.start w.stop .add false .work1 enabled h.remainder hr
  have htS : r.terminal ∈ r.sourceScratch := by rw [← h.scratch_view]; simp
  have htA := h.sourceScratch_mem_aux htS
  have htc : r.terminal ≠ r.control := fun heq => h.control_not_sourceScratch (heq ▸ htS)
  have hterm : run (intervalAddSubUnitary (r.remainder w) n w.start w.stop .add false .work1) enabled r.terminal = false := by
    exact remainderInterval_clean_auxAwayControl r n index w .add false enabled h rfl
      (by intro wire hw hn; simpa only [enabled,upd,hn,if_false] using hc wire hw) r.terminal htA htc
  dsimp only
  refine ⟨?_,hr,hf.2⟩
  apply funext
  intro wire
  by_cases hn : wire = r.control
  · subst wire
    simpa [upd] using hf.2 r.control h.control_mem_aux
  · by_cases ht : wire = r.terminal
    · subst wire
      simpa only [w,enabled,upd,htc,if_false] using (hf.2 r.terminal htA).trans hterm.symm
    · rw [hf.1]
      simp only [blockB3ForwardState,he]
      rw [remainderRestoreControlState_preserves r _ ht hn,← hi]
      simp only [upd,hn,if_false]
      rfl

/-- Actual Block B2 flips only the sign, exactly in nonterminal phase two. -/
theorem run_blockB2_sign (r : IndexedStepRegisters) (n index : Nat)
    (state : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux state) :
    run (blockB2 r) state = state[r.sign ↦ (state r.sign ^^
      (!state r.phase1 && state r.phase2 && !wireAnd r.lengthRPrime state))] ∧
    Clean r.aux (run (blockB2 r) state) := by
  have hf := blockB2_correct r n index state h hc
  have hc0 := hc _ h.control_mem_aux
  have hcs : r.control ≠ r.sign := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using (List.nodup_cons.mp h.controlSign).1
  have htA : r.terminal ∈ r.aux := h.sourceScratch_mem_aux (by rw [← h.scratch_view]; simp)
  have htn : r.terminal ∉ [r.phase1,r.phase2] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨h.aux_not_payload htA (by simp [indexedStepPayload]),
      h.aux_not_payload htA (by simp [indexedStepPayload])⟩
  have hp : rControlNonterminalPredicate [r.phase1,r.phase2] 2 r.lengthRPrime r.terminal state =
      (!state r.phase1 && state r.phase2 && !wireAnd r.lengthRPrime state) := by
    rw [rControlNonterminalPredicate_eq _ _ _ _ _ htn]
    have hb : Nat.testBit 2 1 = true := by decide
    simp [registerMatches,registerMatchesFrom,hb]
  refine ⟨?_,hf.2⟩
  apply funext
  intro wire
  by_cases hn : wire = r.control
  · subst wire
    simpa [upd,hcs,hc0] using hf.2 r.control h.control_mem_aux
  · rw [hf.1]
    simp only [blockB2State,rControlState_preserves _ _ _ _ _ _ hn]
    simp [xorWireState,rControlState,upd,hn,hcs.symm,hc0,hp]

/-- The subtraction control toggles by the source phase/sign predicate, returning
its temporary flag and block scratch unchanged. The initial control may be arbitrary. -/
theorem run_coefficientSubtractControl (r : IndexedStepRegisters) (n index : Nat)
    (s : BasisState) (h : IndexedStepLayout r n index)
    (hc : Clean r.blockScratch s) (ht : s r.terminal = false) :
    run (coefficientSubtractControl r) s =
      s[r.control ↦ (s r.control ^^ (s r.phase1 && !(!s r.phase2 && s r.sign)))] ∧
      Clean r.blockScratch (run (coefficientSubtractControl r) s) := by
  let a := matchXorState [r.phase2,r.sign] 2 r.terminal s
  have ha := run_computeControl_state [r.phase2,r.sign] 2 r.terminal r.blockScratch s h.coefficientTemporary hc
  let b := matchXorState [r.phase1,r.terminal] 1 r.control a
  have hb := run_computeControl_state [r.phase1,r.terminal] 1 r.control r.blockScratch a h.coefficientSub (by
    simpa only [ha.1] using ha.2)
  let c := matchXorState [r.phase2,r.sign] 2 r.terminal b
  have hc' := run_computeControl_state [r.phase2,r.sign] 2 r.terminal r.blockScratch b h.coefficientTemporary (by
    simpa only [hb.1] using hb.2)
  have hr : run (coefficientSubtractControl r) s = c := by
    simp only [coefficientSubtractControl,coefficientTemporaryControl,coefficientSubControl,Classical.run_append]
    rw [ha.1,hb.1,hc'.1]
  refine ⟨?_,by simpa only [hr,hc'.1] using hc'.2⟩
  have hta : r.terminal ∈ r.aux := h.sourceScratch_mem_aux (by rw [← h.scratch_view]; simp)
  have hn (w : Wire) (hw : w ∈ [r.phase1,r.phase2,r.sign]) :
      w ≠ r.control ∧ w ≠ r.terminal := by
    have hp : w ∈ indexedStepPayload r := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl | rfl <;> simp [indexedStepPayload]
    exact ⟨Ne.symm (h.aux_not_payload h.control_mem_aux hp),Ne.symm (h.aux_not_payload hta hp)⟩
  have h1 := hn r.phase1 (by simp)
  have h2 := hn r.phase2 (by simp)
  have hs := hn r.sign (by simp)
  have hb2 : Nat.testBit 2 1 = true := by decide
  have hb1 : Nat.testBit 1 1 = false := by decide
  rw [hr]
  funext w
  by_cases hw : w = r.terminal
  · subst w
    simp [c,b,a,matchXorState,upd,h.control_ne_terminal,Ne.symm h.control_ne_terminal,
      h1.2,h2.1,h2.2,hs.1,hs.2,ht,registerMatches,registerMatchesFrom,hb2,hb1]
  · by_cases hwc : w = r.control
    · subst w
      simp [c,b,a,matchXorState,upd,h.control_ne_terminal,Ne.symm h.control_ne_terminal,
        h1.2,h2.1,h2.2,hs.1,hs.2,ht,registerMatches,registerMatchesFrom,hb2,hb1]
    · simp [c,b,a,matchXorState,upd,hw,hwc]

/-- Block E's actual preparation computes the subtraction enable and the prepared
boundary words, preserving everything outside the control and two length words. -/
theorem blockEPrepareForward_contract (r : IndexedStepRegisters) (n index : Nat)
    (s : BasisState) (h : IndexedStepLayout r n index)
    (hc : Clean r.blockScratch s) (ht : s r.terminal = false) :
    let final := run (blockEPrepareForward r n) s
    (wireValues r.lengthT final,wireValues r.lengthRPrime final) =
      prepareLatestPaperTBoundaryWords (s r.phase2) (wireValues r.lengthT s)
        (wireValues r.lengthRPrime s) (wireValues r.tBoundary.lengthSLow s) n ∧
      final r.control = (s r.control ^^ (s r.phase1 && !(!s r.phase2 && s r.sign))) ∧
      AgreesOutside (r.control :: r.lengthT ++ r.lengthRPrime) final s ∧
      Clean r.blockScratch final := by
  let enabled := s[r.control ↦ (s r.control ^^ (s r.phase1 && !(!s r.phase2 && s r.sign)))]
  have he := run_coefficientSubtractControl r n index s h hc ht
  have hclean : Clean r.blockScratch enabled := by simpa only [he.1] using he.2
  have hb := prepareLatestPaperTBoundary_correct r.tBoundary n enabled h.tBoundary
    (fun w hw => hclean w (h.tBoundary_usedScratch_sub_block w hw))
  have hr : run (blockEPrepareForward r n) s = run (prepareLatestPaperTBoundary r.tBoundary n) enabled := by
    simp only [blockEPrepareForward,Classical.run_append,he.1,enabled]
  have hwords (ws : List Wire) (hw : ∀ w ∈ ws, w ∈ indexedStepPayload r) :
      wireValues ws enabled = wireValues ws s := by
    apply List.map_congr_left
    intro w hmem
    simp [enabled,upd,Ne.symm (h.aux_not_payload h.control_mem_aux (hw w hmem))]
  have htword := hwords r.lengthT (by intro w hw; simp [indexedStepPayload,hw])
  have hrword := hwords r.lengthRPrime (by intro w hw; simp [indexedStepPayload,hw])
  have hsword := hwords r.tBoundary.lengthSLow (by
    intro w hw
    have hs : w ∈ r.lengthS := List.mem_of_mem_take hw
    simp [indexedStepPayload,hs])
  have hp2 : enabled r.phase2 = s r.phase2 := by
    have hn : r.phase2 ≠ r.control := Ne.symm (h.aux_not_payload h.control_mem_aux (show r.phase2 ∈ indexedStepPayload r by simp [indexedStepPayload]))
    simp [enabled,upd,hn]
  have hct : r.control ∉ r.lengthT := by
    intro hw; exact (h.aux_not_payload h.control_mem_aux (by simp [indexedStepPayload,hw])) rfl
  have hcr : r.control ∉ r.lengthRPrime := by
    intro hw; exact (h.aux_not_payload h.control_mem_aux (by simp [indexedStepPayload,hw])) rfl
  dsimp only
  rw [hr]
  refine ⟨?_,?_,?_,(run_tBoundaryPrepareState r n index enabled h hclean).2⟩
  · have hbwords := hb.1
    change (wireValues r.lengthT _,wireValues r.lengthRPrime _) =
      prepareLatestPaperTBoundaryWords (enabled r.phase2) (wireValues r.lengthT enabled)
        (wireValues r.lengthRPrime enabled) (wireValues r.tBoundary.lengthSLow enabled) n at hbwords
    simpa only [htword,hrword,hsword,hp2] using hbwords
  · exact (hb.2.2 r.control hct hcr).trans (by simp [enabled])
  · intro w hw
    have hn : w ≠ r.control ∧ w ∉ r.lengthT ∧ w ∉ r.lengthRPrime := by
      simpa only [List.mem_cons,List.mem_append,not_or,and_assoc] using hw
    exact (hb.2.2 w hn.2.1 hn.2.2).trans (by simp [enabled,upd,hn.1])

private theorem coefficient_bank_separation (r : IndexedStepRegisters) (n index : Nat)
    (h : IndexedStepLayout r n index) {w : Wire} (hw : w ∈ r.work1 ++ r.work2) :
    w ≠ r.control ∧ w ∉ r.lengthT ∧ w ∉ r.lengthRPrime := by
  have hn : ([r.phase1,r.phase2,r.iter,r.sign] ++ ((r.work1++r.work2) ++
      (r.lengthT++r.lengthQ++r.lengthS++r.lengthRPrime++r.aux))).Nodup := by
    simpa only [IndexedStepRegisters.allWires,List.append_assoc] using h.physical
  have hd := (List.nodup_append.mp (List.nodup_append.mp hn).2.1).2.2
  have hnot : ∀ w' ∈ r.lengthT++r.lengthQ++r.lengthS++r.lengthRPrime++r.aux, w ≠ w' := by
    intro w' hw' he
    exact hd w hw w' hw' he
  refine ⟨hnot r.control (by simp [h.control_mem_aux]),?_,?_⟩
  · intro ht; exact hnot w (by simp [ht]) rfl
  · intro hr; exact hnot w (by simp [hr]) rfl

private theorem coefficient_prepare_bank (r : IndexedStepRegisters) (n index : Nat)
    (s : BasisState) (h : IndexedStepLayout r n index)
    (hc : Clean r.blockScratch s) (ht : s r.terminal = false)
    (ws : List Wire) (hw : ∀ w ∈ ws, w ∈ r.work1 ++ r.work2) :
    wireValues ws (run (blockEPrepareForward r n) s) = wireValues ws s := by
  apply wireValues_congr_indexedStep
  intro w hm
  have hn := coefficient_bank_separation r n index h (hw w hm)
  apply (blockEPrepareForward_contract r n index s h hc ht).2.2.1 w
  simpa only [List.mem_cons,List.mem_append,not_or,and_assoc] using hn

private theorem coefficient_subtract_cleanup (r : IndexedStepRegisters) (n index : Nat)
    (window : ActiveWindow) (p : BasisState) (h : IndexedStepLayout r n index)
    (hw : window = (certifiedActiveWindows n index).coefficient)
    (hc : Clean r.blockScratch p) (ht : p r.terminal = false)
    (hen : p r.control = (p r.phase1 && !(!p r.phase2 && p r.sign))) :
    let q := run (coefficientPrefixUnitary (r.coefficient window) window.start window.stop .sub false .work2) p
    run (coefficientSubtractControl r) q = q[r.control ↦ false] ∧
      Clean r.blockScratch (run (coefficientSubtractControl r) q) := by
  let q := run (coefficientPrefixUnitary (r.coefficient window) window.start window.stop .sub false .work2) p
  have hl : CoefficientPrefixLayout (r.coefficient window) window.start window.stop := by
    subst window; exact h.coefficient
  have hq := run_coefficientPrefixState_from_blockScratch r n index window .sub false p h hw hc
  have h1 : q r.phase1 = p r.phase1 := coefficientPrefixUnitary_preservesOutside _ _ _ _ _ hl (h.phase1_not_coefficient window)
  have h2 : q r.phase2 = p r.phase2 := coefficientPrefixUnitary_preservesOutside _ _ _ _ _ hl (h.phase2_not_coefficient window)
  have hterm : q r.terminal = false :=
    (coefficientPrefixUnitary_preservesOutside _ _ _ _ _ hl (h.terminal_not_coefficient window)).trans ht
  have hs : q r.sign = p r.sign := hq.2.2.2 rfl
  have hctrl : q r.control = p r.control := hq.2.2.1
  have hh := run_coefficientSubtractControl r n index q h hq.2.1 hterm
  refine ⟨?_,hh.2⟩
  rw [hh.1,h1,h2,hs,hctrl,hen,Bool.xor_self]

/-- Preparation, coefficient subtraction and control cleanup compose on the actual
source prefix. The boundary-range obligation is stated on the prepared input words. -/
theorem blockESubtractForward_words (r : IndexedStepRegisters) (n index : Nat)
    (window : ActiveWindow) (s : BasisState) (h : IndexedStepLayout r n index)
    (hw : window = (certifiedActiveWindows n index).coefficient)
    (hc : Clean r.blockScratch s) (ht : s r.terminal = false) (hctrl : s r.control = false)
    (hv : boolWordToNat (prepareLatestPaperTBoundaryWords (s r.phase2)
      (wireValues r.lengthT s) (wireValues r.lengthRPrime s)
      (wireValues r.tBoundary.lengthSLow s) n).1 ∈ quotientSwapLabels window.start window.stop) :
    let cr := r.coefficient window
    let B := boolWordToNat (prepareLatestPaperTBoundaryWords (s r.phase2)
      (wireValues r.lengthT s) (wireValues r.lengthRPrime s)
      (wireValues r.tBoundary.lengthSLow s) n).1
    let m := B-window.start+1
    let expected := uniformRippleExpectedWords .sub (s r.phase1 && !(!s r.phase2 && s r.sign))
      ((wireValues cr.work2 s).take m).reverse ((wireValues cr.work1 s).take m).reverse false
    let final := run (blockESubtractForward r n window) s
    wireValues cr.work2 final = expected.1.reverse ++ (wireValues cr.work2 s).drop m ∧
      wireValues cr.work1 final = wireValues cr.work1 s ∧
      final r.sign = s r.sign ∧ final r.control = false ∧ final r.terminal = false ∧
      Clean r.blockScratch final ∧
      AgreesOutside (r.control :: r.sign :: cr.work1 ++ cr.work2) final
        (run (blockEPrepareForward r n) s) := by
  let p := run (blockEPrepareForward r n) s
  let cr := r.coefficient window
  let q := run (coefficientPrefixUnitary cr window.start window.stop .sub false .work2) p
  have hp := blockEPrepareForward_contract r n index s h hc ht
  have hpc : Clean r.blockScratch p := hp.2.2.2
  have hfixed (w : Wire) (hm : w ∈ [r.phase1,r.phase2,r.sign,r.control,r.terminal]) (hn : w ≠ r.control) : p w = s w := by
    apply hp.2.2.1 w
    have hh := h.coefficientFixed_not_words w hm
    simpa only [List.mem_cons,List.mem_append,not_or,and_assoc] using And.intro hn hh
  have h1 : p r.phase1 = s r.phase1 := hfixed _ (by simp) (Ne.symm h.control_ne_phase1)
  have h2 : p r.phase2 = s r.phase2 := hfixed _ (by simp)
    (Ne.symm (h.aux_not_payload h.control_mem_aux (show r.phase2 ∈ indexedStepPayload r by simp [indexedStepPayload])))
  have hsign : p r.sign = s r.sign := hfixed _ (by simp)
    (Ne.symm (h.aux_not_payload h.control_mem_aux (show r.sign ∈ indexedStepPayload r by simp [indexedStepPayload])))
  have hterminal : p r.terminal = false := (hfixed _ (by simp) (Ne.symm h.control_ne_terminal)).trans ht
  have hen : p r.control = (p r.phase1 && !(!p r.phase2 && p r.sign)) := by
    rw [h1,h2,hsign]
    simpa only [hctrl,Bool.false_xor] using hp.2.1
  have hl : CoefficientPrefixLayout cr window.start window.stop := by subst window; exact h.coefficient
  have hrdy : CoefficientPrefixReady cr p := fun w hm => hpc w (h.coefficient_scratch_sub_block window w hm)
  have hb := congrArg boolWordToNat (congrArg Prod.fst hp.1)
  change boolWordToNat (wireValues cr.boundary p) = boolWordToNat
    (prepareLatestPaperTBoundaryWords (s r.phase2) (wireValues r.lengthT s)
      (wireValues r.lengthRPrime s) (wireValues r.tBoundary.lengthSLow s) n).1 at hb
  have hval : boolWordToNat (wireValues cr.boundary p) ∈ quotientSwapLabels window.start window.stop := by
    rw [hb]; exact hv
  have hwords := run_coefficientPrefixUnitary_prefix cr window.start window.stop .sub false .work2 p hl hrdy hval
  have hclean := coefficient_subtract_cleanup r n index window p h hw hpc hterminal hen
  have hrun : run (blockESubtractForward r n window) s = q[r.control ↦ false] := by
    calc
      run (blockESubtractForward r n window) s = run (coefficientSubtractControl r) q := by
        simp only [blockESubtractForward,coefficientSubtractControl,Classical.run_append,q,p,cr]
      _ = q[r.control ↦ false] := hclean.1
  have hbank1 (w : Wire) (hm : w ∈ cr.work1) : w ∈ r.work1 ++ r.work2 := by
    exact List.mem_append_left _ (windowSlice_mem r.work1 window hm)
  have hbank2 (w : Wire) (hm : w ∈ cr.work2) : w ∈ r.work1 ++ r.work2 := by
    exact List.mem_append_right _ (windowSlice_mem r.work2 window hm)
  have hpw1 := coefficient_prepare_bank r n index s h hc ht cr.work1 hbank1
  have hpw2 := coefficient_prepare_bank r n index s h hc ht cr.work2 hbank2
  change wireValues cr.work1 p = wireValues cr.work1 s at hpw1
  change wireValues cr.work2 p = wireValues cr.work2 s at hpw2
  have hen' : p cr.control = (s r.phase1 && !(!s r.phase2 && s r.sign)) := by
    change p r.control = _
    rw [hen,h1,h2,hsign]
  have hu (ws : List Wire) (hm : ∀ w ∈ ws, w ∈ r.work1 ++ r.work2) :
      wireValues ws (q[r.control ↦ false]) = wireValues ws q := by
    apply wireValues_congr_indexedStep
    intro w hw'
    simp [upd,(coefficient_bank_separation r n index h (hm w hw')).1]
  have hqsign : q r.sign = s r.sign :=
    (coefficientPrefixUnitary_preserves_sign_of_false cr .sub .work2 p hl).trans hsign
  have hqterminal : q r.terminal = false :=
    (coefficientPrefixUnitary_preservesOutside cr .sub false .work2 p hl (h.terminal_not_coefficient window)).trans hterminal
  have hsignne : r.sign ≠ r.control := Ne.symm (h.aux_not_payload h.control_mem_aux (by simp [indexedStepPayload]))
  dsimp only
  rw [hrun,hu cr.work2 hbank2,hu cr.work1 hbank1]
  refine ⟨?_,?_,?_,by simp [upd],?_,?_,?_⟩
  · simpa only [hen',hpw1,hpw2,hb] using hwords.1
  · exact hwords.2.1.trans hpw1
  · simpa only [upd,if_neg hsignne] using hqsign
  · simpa only [upd,if_neg (Ne.symm h.control_ne_terminal)] using hqterminal
  · simpa only [hclean.1] using hclean.2
  · intro w hw'
    have hn : w ≠ r.control ∧ w ≠ r.sign ∧ w ∉ cr.work1 ∧ w ∉ cr.work2 := by
      simpa only [List.mem_cons,List.mem_append,not_or,and_assoc] using hw'
    change (q[r.control ↦ false]) w = p w
    rw [show (q[r.control ↦ false]) w = q w by simp [upd,hn.1]]
    apply hwords.2.2.2.2 w
    simpa only [List.mem_cons,List.mem_append,not_or,and_assoc] using hn.2

private theorem coefficient_add_control (r : IndexedStepRegisters) (n index : Nat)
    (s : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.blockScratch s) :
    run (coefficientAddControl r) s = s[r.control ↦ (s r.control ^^ s r.phase1)] ∧
      Clean r.blockScratch (run (coefficientAddControl r) s) := by
  have hh := run_computeControl_state [r.phase1] 1 r.control r.blockScratch s h.coefficientAdd hc
  constructor
  · simpa [coefficientAddControl,matchXorState,registerMatches,registerMatchesFrom] using hh.1
  · simpa only [coefficientAddControl,hh.1] using hh.2

private theorem coefficient_sign_not_block (r : IndexedStepRegisters) (n index : Nat)
    (h : IndexedStepLayout r n index) : r.sign ∉ r.blockScratch := by
  intro hm
  exact (h.aux_not_payload (h.blockScratch_mem_aux hm) (by simp [indexedStepPayload])) rfl

/-- The actual sign/add/restore suffix computes the selected prefix sum and its
sign carry, clears its control, and restores block scratch. -/
theorem blockEFinishForward_words (r : IndexedStepRegisters) (n index : Nat)
    (window : ActiveWindow) (s : BasisState) (h : IndexedStepLayout r n index)
    (hw : window = (certifiedActiveWindows n index).coefficient)
    (hc : Clean r.blockScratch s) (hctrl : s r.control = false)
    (hv : boolWordToNat (wireValues r.lengthT s) ∈ quotientSwapLabels window.start window.stop) :
    let cr := r.coefficient window
    let m := boolWordToNat (wireValues r.lengthT s)-window.start+1
    let expected := uniformRippleExpectedWords .add (s r.phase1)
      ((wireValues cr.work2 s).take m).reverse ((wireValues cr.work1 s).take m).reverse false
    let final := run (blockEFinishForward r n window) s
    wireValues cr.work2 final = expected.1.reverse ++ (wireValues cr.work2 s).drop m ∧
      wireValues cr.work1 final = wireValues cr.work1 s ∧
      final r.sign = ((s r.sign ^^ s r.phase1) ^^ expected.2) ∧
      final r.control = false ∧ Clean r.blockScratch final ∧
      AgreesOutside (r.control :: r.sign :: cr.work1 ++ cr.work2 ++ r.lengthT ++ r.lengthRPrime) final s := by
  let cr := r.coefficient window
  let a := s[r.sign ↦ (s r.sign ^^ s r.phase1)]
  let p := a[r.control ↦ s r.phase1]
  let q := run (coefficientPrefixUnitary cr window.start window.stop .add true .work2) p
  let b := q[r.control ↦ false]
  have hl : CoefficientPrefixLayout cr window.start window.stop := by subst window; exact h.coefficient
  have hsc : r.sign ≠ r.control := Ne.symm (h.aux_not_payload h.control_mem_aux (by simp [indexedStepPayload]))
  have h1s : r.phase1 ≠ r.sign := by
    intro he
    exact (List.nodup_cons.mp h.coefficientSign).1 (by simp [he])
  have hac : a r.control = false := by simp [a,upd,Ne.symm hsc,hctrl]
  have ha1 : a r.phase1 = s r.phase1 := by simp [a,upd,h1s]
  have hca : Clean r.blockScratch a := clean_upd_not_mem hc (coefficient_sign_not_block r n index h)
  have ha := coefficient_add_control r n index a h hca
  have har : run (coefficientAddControl r) a = p := by
    rw [ha.1,hac,ha1,Bool.false_xor]
  have hcp : Clean r.blockScratch p := by simpa only [har] using ha.2
  have hp1 : p r.phase1 = s r.phase1 := by simp [p,upd,Ne.symm h.control_ne_phase1,ha1]
  have hpsign : p r.sign = (s r.sign ^^ s r.phase1) := by simp [p,a,upd,hsc]
  have hpc : p r.control = s r.phase1 := by simp [p]
  have hbefore (ws : List Wire) (hn : ∀ w ∈ ws, w ≠ r.sign ∧ w ≠ r.control) :
      wireValues ws p = wireValues ws s := by
    apply wireValues_congr_indexedStep
    intro w hm
    simp [p,a,upd,(hn w hm).1,(hn w hm).2]
  have hbank1 (w : Wire) (hm : w ∈ cr.work1) : w ∈ r.work1 ++ r.work2 :=
    List.mem_append_left _ (windowSlice_mem r.work1 window hm)
  have hbank2 (w : Wire) (hm : w ∈ cr.work2) : w ∈ r.work1 ++ r.work2 :=
    List.mem_append_right _ (windowSlice_mem r.work2 window hm)
  have hbank (w : Wire) (hm : w ∈ r.work1 ++ r.work2) : w ≠ r.sign ∧ w ≠ r.control := by
    refine ⟨?_,(coefficient_bank_separation r n index h hm).1⟩
    have hh : w ∈ indexedStepAfterSign r := by
      simp only [List.mem_append] at hm
      rcases hm with hm | hm <;> simp [indexedStepAfterSign,hm]
    exact Ne.symm (h.sign_ne_after hh)
  have hpw1 := hbefore cr.work1 (fun w hm => hbank w (hbank1 w hm))
  have hpw2 := hbefore cr.work2 (fun w hm => hbank w (hbank2 w hm))
  have hboundary := hbefore r.lengthT (by
    intro w hm
    constructor
    · exact Ne.symm (h.sign_ne_after (by simp [indexedStepAfterSign,hm]))
    · exact Ne.symm (h.aux_not_payload h.control_mem_aux (by simp [indexedStepPayload,hm])))
  have hrdy : CoefficientPrefixReady cr p := fun w hm => hcp w (h.coefficient_scratch_sub_block window w hm)
  have hval : boolWordToNat (wireValues cr.boundary p) ∈ quotientSwapLabels window.start window.stop := by
    change boolWordToNat (wireValues r.lengthT p) ∈ _
    rw [hboundary]; exact hv
  have hwords := run_coefficientPrefixUnitary_prefix cr window.start window.stop .add true .work2 p hl hrdy hval
  have hq := run_coefficientPrefixState_from_blockScratch r n index window .add true p h hw hcp
  have hq1 : q r.phase1 = s r.phase1 :=
    (coefficientPrefixUnitary_preservesOutside cr .add true .work2 p hl (h.phase1_not_coefficient window)).trans hp1
  have hqc : q r.control = s r.phase1 := hq.2.2.1.trans hpc
  have hb := coefficient_add_control r n index q h hq.2.1
  have hbr : run (coefficientAddControl r) q = b := by rw [hb.1,hqc,hq1,Bool.xor_self]
  have hcb : Clean r.blockScratch b := by simpa only [hbr] using hb.2
  have hrestore := restoreLatestPaperTBoundary_correct r.tBoundary n b h.tBoundary
    (fun w hm => hcb w (h.tBoundary_usedScratch_sub_block w hm))
  have hrun : run (blockEFinishForward r n window) s = run (restoreLatestPaperTBoundary r.tBoundary n) b := by
    simp only [blockEFinishForward,Classical.run_append]
    change run (restoreLatestPaperTBoundary r.tBoundary n)
      (run (coefficientAddControl r) (run (coefficientPrefixUnitary cr window.start window.stop .add true .work2)
        (run (coefficientAddControl r) a))) = _
    rw [har,hbr]
  have hfinalbank (ws : List Wire) (hm : ∀ w ∈ ws, w ∈ r.work1 ++ r.work2) :
      wireValues ws (run (restoreLatestPaperTBoundary r.tBoundary n) b) = wireValues ws q := by
    apply wireValues_congr_indexedStep
    intro w hw'
    have hn := coefficient_bank_separation r n index h (hm w hw')
    exact (hrestore.2.2 w hn.2.1 hn.2.2).trans (by simp [b,upd,hn.1])
  have hsignwords := h.coefficientFixed_not_words r.sign (by simp)
  have hcontrolwords := h.coefficientFixed_not_words r.control (by simp)
  dsimp only
  rw [hrun,hfinalbank cr.work2 hbank2,hfinalbank cr.work1 hbank1]
  refine ⟨?_,hwords.2.1.trans hpw1,?_,?_,(run_tBoundaryRestoreState r n index b h hcb).2,?_⟩
  · change p cr.control = s r.phase1 at hpc
    change wireValues cr.boundary p = wireValues r.lengthT s at hboundary
    simpa only [hpc,hpw1,hpw2,hboundary] using hwords.1
  · rw [hrestore.2.2 r.sign hsignwords.1 hsignwords.2]
    have hbs : b r.sign = q r.sign := by simp [b,upd,hsc]
    rw [hbs]
    change p cr.control = s r.phase1 at hpc
    change wireValues cr.boundary p = wireValues r.lengthT s at hboundary
    change p cr.sign = (s r.sign ^^ s r.phase1) at hpsign
    simpa only [hpsign,hpc,hpw1,hpw2,hboundary,Bool.true_and] using hwords.2.2.1
  · rw [hrestore.2.2 r.control hcontrolwords.1 hcontrolwords.2]
    simp [b]
  · intro w hw'
    have hn : w ≠ r.control ∧ w ≠ r.sign ∧ w ∉ cr.work1 ∧ w ∉ cr.work2 ∧
        w ∉ r.lengthT ∧ w ∉ r.lengthRPrime := by
      simpa only [List.mem_cons,List.mem_append,not_or,and_assoc] using hw'
    rw [hrestore.2.2 w hn.2.2.2.2.1 hn.2.2.2.2.2]
    have hqw : q w = p w := hwords.2.2.2.2 w (by
      simpa only [List.mem_cons,List.mem_append,not_or,and_assoc] using
        And.intro hn.2.1 (And.intro hn.2.2.1 hn.2.2.2.1))
    change (q[r.control ↦ false]) w = s w
    rw [show (q[r.control ↦ false]) w = q w by simp [upd,hn.1],hqw]
    simp [p,a,upd,hn.1,hn.2.1]

end ShorECDLP.Paper2607_13816
