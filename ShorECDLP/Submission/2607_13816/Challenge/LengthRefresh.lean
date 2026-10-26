import ShorECDLP.Submission.«2607_13816».Challenge.ZeroMap
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredEndIteration
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def upperWriterProgram (n : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  let first := upperMapProgram n k K tree control r t path bitAt dirtyAt start
  prependCompiled (controlledXorConstant control targets (truthMinusOneValue targets.length K) ++ highestPositionDirtyWrites k K targets dirtyAt)
    (appendCompiled first (prependCompiled (highestPositionDirtyWrites k K targets dirtyAt) (upperMapProgram n k K tree control r t path bitAt dirtyAt (start+first.1))))

theorem upperWriterProgram_run (n : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (upperWriterProgram n k K tree control r t path bitAt dirtyAt targets start) read history = (measuredHighestPositionWrite k K tree control r t path bitAt dirtyAt targets).run := by
  unfold upperWriterProgram measuredHighestPositionWrite
  apply prependCompiled_run_eq
  apply appendCompiled_run_eq
  · exact upperMapProgram_run n k K tree control r t path bitAt dirtyAt start read history
  · intro h
    apply prependCompiled_run_eq
    exact upperMapProgram_run n k K tree control r t path bitAt dirtyAt _ read h

theorem upperWriterProgram_tCount (n : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (upperWriterProgram n k K tree control r t path bitAt dirtyAt targets start) read history = (measuredHighestPositionWrite k K tree control r t path bitAt dirtyAt targets).tCount := by
  unfold upperWriterProgram measuredHighestPositionWrite
  apply prependCompiled_tCount_eq
  apply appendCompiled_tCount_eq
  · exact upperMapProgram_tCount n k K tree control r t path bitAt dirtyAt start read history
  · intro h
    apply prependCompiled_tCount_eq
    exact upperMapProgram_tCount n k K tree control r t path bitAt dirtyAt _ read h

def lowerWriterProgram (n : Nat) (width : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  let first := lowerMapProgram n k K tree control r t path bitAt dirtyAt start
  prependCompiled (controlledXorConstant control targets (rightLengthValue width targets.length k) ++ rightLengthDirtyWrites width k K targets dirtyAt)
    (appendCompiled first (prependCompiled (rightLengthDirtyWrites width k K targets dirtyAt) (lowerMapProgram n k K tree control r t path bitAt dirtyAt (start+first.1))))

theorem lowerWriterProgram_run (n : Nat) (width : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (lowerWriterProgram n width k K tree control r t path bitAt dirtyAt targets start) read history = (measuredRightLengthWrite width k K tree control r t path bitAt dirtyAt targets).run := by
  unfold lowerWriterProgram measuredRightLengthWrite
  apply prependCompiled_run_eq
  apply appendCompiled_run_eq
  · exact lowerMapProgram_run n k K tree control r t path bitAt dirtyAt start read history
  · intro h
    apply prependCompiled_run_eq
    exact lowerMapProgram_run n k K tree control r t path bitAt dirtyAt _ read h

theorem lowerWriterProgram_tCount (n : Nat) (width : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (lowerWriterProgram n width k K tree control r t path bitAt dirtyAt targets start) read history = (measuredRightLengthWrite width k K tree control r t path bitAt dirtyAt targets).tCount := by
  unfold lowerWriterProgram measuredRightLengthWrite
  apply prependCompiled_tCount_eq
  apply appendCompiled_tCount_eq
  · exact lowerMapProgram_tCount n k K tree control r t path bitAt dirtyAt start read history
  · intro h
    apply prependCompiled_tCount_eq
    exact lowerMapProgram_tCount n k K tree control r t path bitAt dirtyAt _ read h

def ltUpdateProgram (n : Nat) (width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  let first := upperWriterProgram n k K tree control r t path work2At work1At lengthT start
  surroundCompiled (constMinus lengthRP constants carry (width+2)) (constMinus lengthRP constants carry (width+2))
    (appendCompiled first (upperWriterProgram n k K tree control r t path work1At work2At lengthT (start+first.1)))

theorem ltUpdateProgram_run (n : Nat) (width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (ltUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start) read history = (measuredLenUpdateLtUnary width k K tree control r t carry path work1At work2At lengthT lengthRP constants).run := by
  unfold ltUpdateProgram measuredLenUpdateLtUnary
  rw [← adaptive_seq_assoc]
  apply surroundCompiled_run
  apply appendCompiled_run_eq
  · exact upperWriterProgram_run n k K tree control r t path work2At work1At lengthT start read history
  · intro h
    exact upperWriterProgram_run n k K tree control r t path work1At work2At lengthT _ read h

theorem ltUpdateProgram_tCount (n : Nat) (width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (ltUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start) read history = (measuredLenUpdateLtUnary width k K tree control r t carry path work1At work2At lengthT lengthRP constants).tCount := by
  unfold ltUpdateProgram measuredLenUpdateLtUnary
  rw [← adaptive_seq_assoc]
  apply surroundCompiled_tCount
  apply appendCompiled_tCount_eq
  · exact upperWriterProgram_tCount n k K tree control r t path work2At work1At lengthT start read history
  · intro h
    exact upperWriterProgram_tCount n k K tree control r t path work1At work2At lengthT _ read h

def lrpUpdateProgram (n : Nat) (width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  let first := lowerWriterProgram n width k K tree control r t path work1At work2At lengthRP start
  surroundCompiled (addConstant lengthT constants carry 3) (subConstant lengthT constants carry 3)
    (appendCompiled first (lowerWriterProgram n width k K tree control r t path work2At work1At lengthRP (start+first.1)))

theorem lrpUpdateProgram_run (n : Nat) (width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (lrpUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start) read history = (measuredLenUpdateLrpUnary width k K tree control r t carry path work1At work2At lengthT lengthRP constants).run := by
  unfold lrpUpdateProgram measuredLenUpdateLrpUnary
  rw [← adaptive_seq_assoc]
  apply surroundCompiled_run
  apply appendCompiled_run_eq
  · exact lowerWriterProgram_run n width k K tree control r t path work1At work2At lengthRP start read history
  · intro h
    exact lowerWriterProgram_run n width k K tree control r t path work2At work1At lengthRP _ read h

theorem lrpUpdateProgram_tCount (n : Nat) (width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (lrpUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start) read history = (measuredLenUpdateLrpUnary width k K tree control r t carry path work1At work2At lengthT lengthRP constants).tCount := by
  unfold lrpUpdateProgram measuredLenUpdateLrpUnary
  rw [← adaptive_seq_assoc]
  apply surroundCompiled_tCount
  apply appendCompiled_tCount_eq
  · exact lowerWriterProgram_tCount n width k K tree control r t path work1At work2At lengthRP start read history
  · intro h
    exact lowerWriterProgram_tCount n width k K tree control r t path work2At work1At lengthRP _ read h

end ShorECDLP.Paper2607_13816.ChallengeMigration
