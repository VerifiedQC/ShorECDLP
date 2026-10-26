import ShorECDLP.Submission.«2607_13816».Challenge.LengthRefresh
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredBlockH
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def upperEndProgram (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    (count : Nat) × Straight n start (start+count) :=
  ltUpdateProgram n width w.k4 w.K4 (r.upperTree w) r.control (r.rangeAccumulator w.k4 w.K4) (r.temporary w.k4 w.K4) r.carry (r.path w.k4 w.K4) r.work1At r.work2At r.lengthT r.lengthRP r.constants start

theorem upperEndProgram_run (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (upperEndProgram n start r width w) read history = (measuredEndUpper r width w).run := by
  exact ltUpdateProgram_run n width w.k4 w.K4 (r.upperTree w) r.control (r.rangeAccumulator w.k4 w.K4) (r.temporary w.k4 w.K4) r.carry (r.path w.k4 w.K4) r.work1At r.work2At r.lengthT r.lengthRP r.constants start read history

theorem upperEndProgram_tCount (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (upperEndProgram n start r width w) read history = (measuredEndUpper r width w).tCount := by
  exact ltUpdateProgram_tCount n width w.k4 w.K4 (r.upperTree w) r.control (r.rangeAccumulator w.k4 w.K4) (r.temporary w.k4 w.K4) r.carry (r.path w.k4 w.K4) r.work1At r.work2At r.lengthT r.lengthRP r.constants start read history

def lowerEndProgram (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    (count : Nat) × Straight n start (start+count) :=
  lrpUpdateProgram n width w.k5 (w.K5Decode width) (r.lowerTree width w) r.control (r.rangeAccumulator w.k5 (w.K5Decode width)) (r.temporary w.k5 (w.K5Decode width)) r.carry (r.path w.k5 (w.K5Decode width)) r.work1At r.work2At r.lengthT r.lengthRP r.constants start

theorem lowerEndProgram_run (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (lowerEndProgram n start r width w) read history = (measuredEndLower r width w).run := by
  exact lrpUpdateProgram_run n width w.k5 (w.K5Decode width) (r.lowerTree width w) r.control (r.rangeAccumulator w.k5 (w.K5Decode width)) (r.temporary w.k5 (w.K5Decode width)) r.carry (r.path w.k5 (w.K5Decode width)) r.work1At r.work2At r.lengthT r.lengthRP r.constants start read history

theorem lowerEndProgram_tCount (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (lowerEndProgram n start r width w) read history = (measuredEndLower r width w).tCount := by
  exact lrpUpdateProgram_tCount n width w.k5 (w.K5Decode width) (r.lowerTree width w) r.control (r.rangeAccumulator w.k5 (w.K5Decode width)) (r.temporary w.k5 (w.K5Decode width)) r.carry (r.path w.k5 (w.K5Decode width)) r.work1At r.work2At r.lengthT r.lengthRP r.constants start read history

def endProgram (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    (count : Nat) × Straight n start (start+count) :=
  let first := upperEndProgram n start r width w
  prependCompiled (controlledWorkSwap r.control r.work1 r.work2)
    (appendCompiled first (lowerEndProgram n (start+first.1) r width w))

theorem endProgram_run (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (endProgram n start r width w) read history = (measuredEndIteration r width w).run := by
  unfold endProgram measuredEndIteration
  apply prependCompiled_run_eq
  apply appendCompiled_run_eq
  · exact upperEndProgram_run n start r width w read history
  · intro h; exact lowerEndProgram_run n _ r width w read h

theorem endProgram_tCount (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (endProgram n start r width w) read history = (measuredEndIteration r width w).tCount := by
  unfold endProgram measuredEndIteration
  apply prependCompiled_tCount_eq
  apply appendCompiled_tCount_eq
  · exact upperEndProgram_tCount n start r width w read history
  · intro h; exact lowerEndProgram_tCount n _ r width w read h

def endInverseProgram (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    (count : Nat) × Straight n start (start+count) :=
  let first := lowerEndProgram n start r width w
  appendCompiled first (appendCompiled (upperEndProgram n (start+first.1) r width w)
    ⟨0, literalProgram (controlledWorkSwapInverse r.control r.work1 r.work2)⟩)

theorem endInverseProgram_run (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (endInverseProgram n start r width w) read history = (measuredEndIterationInverse r width w).run := by
  unfold endInverseProgram measuredEndIterationInverse
  apply appendCompiled_run_eq
  · exact lowerEndProgram_run n start r width w read history
  · intro h
    apply appendCompiled_run_eq
    · exact upperEndProgram_run n _ r width w read h
    · intro h; exact literalCompiled_run _ read h

theorem endInverseProgram_tCount (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (endInverseProgram n start r width w) read history = (measuredEndIterationInverse r width w).tCount := by
  unfold endInverseProgram measuredEndIterationInverse
  apply appendCompiled_tCount_eq
  · exact lowerEndProgram_tCount n start r width w read history
  · intro h
    apply appendCompiled_tCount_eq
    · exact upperEndProgram_tCount n _ r width w read h
    · intro h; exact literalCompiled_tCount _ read h

def hProgram (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  if T%4=0 then surroundCompiled (blockHPrefix r) ([.CX r.control r.iter] ++ blockHSuffix r)
    (endProgram n start (r.endIteration width T) width (endIterationWindowsAt width T))
  else ⟨0, .done⟩

theorem hProgram_run (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (hProgram n start r width T) read history = (measuredBlockHForward r width T).run := by
  unfold hProgram measuredBlockHForward
  split
  · apply surroundCompiled_run
    exact endProgram_run n start _ width _ read history
  · rfl

theorem hProgram_tCount (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (hProgram n start r width T) read history = (measuredBlockHForward r width T).tCount := by
  unfold hProgram measuredBlockHForward
  split
  · apply surroundCompiled_tCount
    exact endProgram_tCount n start _ width _ read history
  · rfl

def hInverseProgram (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  if T%4=0 then surroundCompiled (blockHPrefix r ++ [.CX r.control r.iter]) (blockHSuffix r)
    (endInverseProgram n start (r.endIteration width T) width (endIterationWindowsAt width T))
  else ⟨0, .done⟩

theorem hInverseProgram_run (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (hInverseProgram n start r width T) read history = (measuredBlockHInverse r width T).run := by
  unfold hInverseProgram measuredBlockHInverse
  split
  · apply surroundCompiled_run
    exact endInverseProgram_run n start _ width _ read history
  · rfl

theorem hInverseProgram_tCount (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (hInverseProgram n start r width T) read history = (measuredBlockHInverse r width T).tCount := by
  unfold hInverseProgram measuredBlockHInverse
  split
  · apply surroundCompiled_tCount
    exact endInverseProgram_tCount n start _ width _ read history
  · rfl

end ShorECDLP.Paper2607_13816.ChallengeMigration
