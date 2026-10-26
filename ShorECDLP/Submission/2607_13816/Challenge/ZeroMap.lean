import ShorECDLP.Submission.«2607_13816».Challenge.ZeroLeaf
import ShorECDLP.Submission.«2607_13816».Challenge.RangeScan
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def upperMapProgram (n : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (start : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  let first := rangeScanProgram n true .inc tree control r path
    (fun label dynamic cursor => upperForwardLeafProgram n cursor k K control t bitAt dirtyAt label dynamic) start
  appendCompiled first (rangeScanProgram n false .dec tree control r path
    (fun label dynamic cursor => upperReverseLeafProgram n cursor k K t bitAt dirtyAt label dynamic) (start+first.1))

theorem upperMapProgram_run (n : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (upperMapProgram n k K tree control r t path bitAt dirtyAt start) read history = (measuredUpperZeroMap k K tree control r t path bitAt dirtyAt).run := by
  unfold upperMapProgram measuredUpperZeroMap
  apply appendCompiled_run_eq
  · apply rangeScanProgram_run
    intro label dynamic cursor h
    exact upperForwardLeafProgram_run n cursor k K control t bitAt dirtyAt label dynamic read h
  · intro h
    apply rangeScanProgram_run
    intro label dynamic cursor h
    exact upperReverseLeafProgram_run n cursor k K t bitAt dirtyAt label dynamic read h

theorem upperMapProgram_tCount (n : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (upperMapProgram n k K tree control r t path bitAt dirtyAt start) read history = (measuredUpperZeroMap k K tree control r t path bitAt dirtyAt).tCount := by
  unfold upperMapProgram measuredUpperZeroMap
  apply appendCompiled_tCount_eq
  · apply rangeScanProgram_tCount
    intro label dynamic cursor h
    exact upperForwardLeafProgram_tCount n cursor k K control t bitAt dirtyAt label dynamic read h
  · intro h
    apply rangeScanProgram_tCount
    intro label dynamic cursor h
    exact upperReverseLeafProgram_tCount n cursor k K t bitAt dirtyAt label dynamic read h

def lowerMapProgram (n : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (start : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  let first := rangeScanProgram n true .dec tree control r path
    (fun label dynamic cursor => lowerForwardLeafProgram n cursor k K control t bitAt dirtyAt label dynamic) start
  appendCompiled first (rangeScanProgram n false .inc tree control r path
    (fun label dynamic cursor => lowerReverseLeafProgram n cursor k K t bitAt dirtyAt label dynamic) (start+first.1))

theorem lowerMapProgram_run (n : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (lowerMapProgram n k K tree control r t path bitAt dirtyAt start) read history = (measuredLowerZeroMap k K tree control r t path bitAt dirtyAt).run := by
  unfold lowerMapProgram measuredLowerZeroMap
  apply appendCompiled_run_eq
  · apply rangeScanProgram_run
    intro label dynamic cursor h
    exact lowerForwardLeafProgram_run n cursor k K control t bitAt dirtyAt label dynamic read h
  · intro h
    apply rangeScanProgram_run
    intro label dynamic cursor h
    exact lowerReverseLeafProgram_run n cursor k K t bitAt dirtyAt label dynamic read h

theorem lowerMapProgram_tCount (n : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (lowerMapProgram n k K tree control r t path bitAt dirtyAt start) read history = (measuredLowerZeroMap k K tree control r t path bitAt dirtyAt).tCount := by
  unfold lowerMapProgram measuredLowerZeroMap
  apply appendCompiled_tCount_eq
  · apply rangeScanProgram_tCount
    intro label dynamic cursor h
    exact lowerForwardLeafProgram_tCount n cursor k K control t bitAt dirtyAt label dynamic read h
  · intro h
    apply rangeScanProgram_tCount
    intro label dynamic cursor h
    exact lowerReverseLeafProgram_tCount n cursor k K t bitAt dirtyAt label dynamic read h

end ShorECDLP.Paper2607_13816.ChallengeMigration
