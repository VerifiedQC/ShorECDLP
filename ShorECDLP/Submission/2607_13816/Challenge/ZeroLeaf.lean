import ShorECDLP.Submission.«2607_13816».Challenge.Wrapper
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredZeroMap
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def zeroCellProgram (n start : Nat) (base : Bool) (r bit guard target temporary : Wire) :
    (count : Nat) × Straight n start (start+count) :=
  prependCompiled (measuredZeroPrefix base r bit guard target temporary)
    ⟨1, andEraseProgram n start r bit temporary⟩

theorem zeroCellProgram_run (n start : Nat) (base : Bool) (r bit guard target temporary : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (zeroCellProgram n start base r bit guard target temporary) read history =
      (measuredZeroCell base r bit guard target temporary).run := by
  unfold zeroCellProgram measuredZeroCell
  apply prependCompiled_run_eq
  exact andEraseProgram_run n start r bit temporary read history

theorem zeroCellProgram_tCount (n start : Nat) (base : Bool) (r bit guard target temporary : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (zeroCellProgram n start base r bit guard target temporary) read history =
      (measuredZeroCell base r bit guard target temporary).tCount := by
  unfold zeroCellProgram measuredZeroCell
  apply prependCompiled_tCount_eq
  exact andEraseProgram_tCount n start r bit temporary read history

def upperForwardLeafProgram (n start : Nat) (k K : Nat) (control temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    (count : Nat) × Straight n start (start+count) :=
  if k ≤ label ∧ label ≤ K then
    if label = K then
      zeroCellProgram n start true r (bitAt label) control (dirtyAt label) temporary
    else zeroCellProgram n start false r (bitAt label) (dirtyAt (label + 1)) (dirtyAt label) temporary
  else ⟨0, .done⟩

theorem upperForwardLeafProgram_run (n start : Nat) (k K : Nat) (control temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (upperForwardLeafProgram n start k K control temporary bitAt dirtyAt label r) read history =
      (measuredUpperForwardLeaf k K control temporary bitAt dirtyAt label r).run := by
  unfold upperForwardLeafProgram measuredUpperForwardLeaf
  split
  · split <;> exact zeroCellProgram_run _ _ _ _ _ _ _ _ read history
  · rfl

theorem upperForwardLeafProgram_tCount (n start : Nat) (k K : Nat) (control temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (upperForwardLeafProgram n start k K control temporary bitAt dirtyAt label r) read history =
      (measuredUpperForwardLeaf k K control temporary bitAt dirtyAt label r).tCount := by
  unfold upperForwardLeafProgram measuredUpperForwardLeaf
  split
  · split <;> exact zeroCellProgram_tCount _ _ _ _ _ _ _ _ read history
  · rfl

def upperReverseLeafProgram (n start : Nat) (k K : Nat) (temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    (count : Nat) × Straight n start (start+count) :=
  if k ≤ label ∧ label < K then
    zeroCellProgram n start false r (bitAt label) (dirtyAt (label + 1)) (dirtyAt label) temporary
  else ⟨0, .done⟩

theorem upperReverseLeafProgram_run (n start : Nat) (k K : Nat) (temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (upperReverseLeafProgram n start k K temporary bitAt dirtyAt label r) read history =
      (measuredUpperReverseLeaf k K temporary bitAt dirtyAt label r).run := by
  unfold upperReverseLeafProgram measuredUpperReverseLeaf
  split
  · exact zeroCellProgram_run _ _ _ _ _ _ _ _ read history
  · rfl

theorem upperReverseLeafProgram_tCount (n start : Nat) (k K : Nat) (temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (upperReverseLeafProgram n start k K temporary bitAt dirtyAt label r) read history =
      (measuredUpperReverseLeaf k K temporary bitAt dirtyAt label r).tCount := by
  unfold upperReverseLeafProgram measuredUpperReverseLeaf
  split
  · exact zeroCellProgram_tCount _ _ _ _ _ _ _ _ read history
  · rfl

def lowerForwardLeafProgram (n start : Nat) (k K : Nat) (control temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    (count : Nat) × Straight n start (start+count) :=
  if k ≤ label ∧ label ≤ K then
    if label = k then
      zeroCellProgram n start true r (bitAt label) control (dirtyAt label) temporary
    else zeroCellProgram n start false r (bitAt label) (dirtyAt (label - 1)) (dirtyAt label) temporary
  else ⟨0, .done⟩

theorem lowerForwardLeafProgram_run (n start : Nat) (k K : Nat) (control temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (lowerForwardLeafProgram n start k K control temporary bitAt dirtyAt label r) read history =
      (measuredLowerForwardLeaf k K control temporary bitAt dirtyAt label r).run := by
  unfold lowerForwardLeafProgram measuredLowerForwardLeaf
  split
  · split <;> exact zeroCellProgram_run _ _ _ _ _ _ _ _ read history
  · rfl

theorem lowerForwardLeafProgram_tCount (n start : Nat) (k K : Nat) (control temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (lowerForwardLeafProgram n start k K control temporary bitAt dirtyAt label r) read history =
      (measuredLowerForwardLeaf k K control temporary bitAt dirtyAt label r).tCount := by
  unfold lowerForwardLeafProgram measuredLowerForwardLeaf
  split
  · split <;> exact zeroCellProgram_tCount _ _ _ _ _ _ _ _ read history
  · rfl

def lowerReverseLeafProgram (n start : Nat) (k K : Nat) (temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    (count : Nat) × Straight n start (start+count) :=
  if k < label ∧ label ≤ K then
    zeroCellProgram n start false r (bitAt label) (dirtyAt (label - 1)) (dirtyAt label) temporary
  else ⟨0, .done⟩

theorem lowerReverseLeafProgram_run (n start : Nat) (k K : Nat) (temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (lowerReverseLeafProgram n start k K temporary bitAt dirtyAt label r) read history =
      (measuredLowerReverseLeaf k K temporary bitAt dirtyAt label r).run := by
  unfold lowerReverseLeafProgram measuredLowerReverseLeaf
  split
  · exact zeroCellProgram_run _ _ _ _ _ _ _ _ read history
  · rfl

theorem lowerReverseLeafProgram_tCount (n start : Nat) (k K : Nat) (temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (lowerReverseLeafProgram n start k K temporary bitAt dirtyAt label r) read history =
      (measuredLowerReverseLeaf k K temporary bitAt dirtyAt label r).tCount := by
  unfold lowerReverseLeafProgram measuredLowerReverseLeaf
  split
  · exact zeroCellProgram_tCount _ _ _ _ _ _ _ _ read history
  · rfl

end ShorECDLP.Paper2607_13816.ChallengeMigration
