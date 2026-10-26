import ShorECDLP.Submission.«2607_13816».Challenge.Wrapper
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredZeroMap
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def rangeLeafProgram (n : Nat) (after : Bool) (r : Wire)
    (leaf : Nat → Wire → FixedSegment n) (label : Nat) (dynamic : Wire) (start : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  if after then appendCompiled (leaf label r start) ⟨0, literalProgram [.CX dynamic r]⟩
  else prependCompiled [.CX dynamic r] (leaf label r start)

theorem rangeLeafProgram_run (n : Nat) (after : Bool) (r : Wire)
    (leaf : Nat → Wire → FixedSegment n) (source : Nat → Wire → AdaptiveCircuit)
    (read : ConstantBit n → Bool)
    (hl : ∀ label control start h, compiledRun (leaf label control start) read h = (source label control).run)
    (label : Nat) (dynamic : Wire) (start : Nat) (history : Fin start → Bool) :
    compiledRun (rangeLeafProgram n after r leaf label dynamic start) read history =
      (measuredRangeLeaf after r source label dynamic).run := by
  unfold rangeLeafProgram measuredRangeLeaf
  split
  · apply appendCompiled_run_eq
    · exact hl _ _ _ _
    · intro h; exact literalCompiled_run _ read h
  · apply prependCompiled_run_eq
    exact hl _ _ _ _

theorem rangeLeafProgram_tCount (n : Nat) (after : Bool) (r : Wire)
    (leaf : Nat → Wire → FixedSegment n) (source : Nat → Wire → AdaptiveCircuit)
    (read : ConstantBit n → Bool)
    (hl : ∀ label control start h, compiledTCount (leaf label control start) read h = (source label control).tCount)
    (label : Nat) (dynamic : Wire) (start : Nat) (history : Fin start → Bool) :
    compiledTCount (rangeLeafProgram n after r leaf label dynamic start) read history =
      (measuredRangeLeaf after r source label dynamic).tCount := by
  unfold rangeLeafProgram measuredRangeLeaf
  split
  · apply appendCompiled_tCount_eq
    · exact hl _ _ _ _
    · intro h; exact literalCompiled_tCount _ read h
  · apply prependCompiled_tCount_eq
    exact hl _ _ _ _

def rangeScanProgram (n : Nat) (after : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control r : Wire) (path : List Wire)
    (leaf : Nat → Wire → FixedSegment n) (start : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  if after then prependCompiled [.CX control r]
    (unaryProgram n order (rangeLeafProgram n true r leaf) tree control path start)
  else appendCompiled (unaryProgram n order (rangeLeafProgram n false r leaf) tree control path start)
    ⟨0, literalProgram [.CX control r]⟩

theorem rangeScanProgram_run (n : Nat) (after : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control r : Wire) (path : List Wire)
    (leaf : Nat → Wire → FixedSegment n) (source : Nat → Wire → AdaptiveCircuit)
    (read : ConstantBit n → Bool)
    (hl : ∀ label control start h, compiledRun (leaf label control start) read h = (source label control).run)
    (start : Nat) (history : Fin start → Bool) :
    compiledRun (rangeScanProgram n after order tree control r path leaf start) read history =
      (measuredRangeScan after order tree control r path source).run := by
  unfold rangeScanProgram measuredRangeScan
  split
  · apply prependCompiled_run_eq
    exact unaryProgram_run n order _ _ read (rangeLeafProgram_run n true r leaf source read hl) tree control path start history
  · apply appendCompiled_run_eq
    · exact unaryProgram_run n order _ _ read (rangeLeafProgram_run n false r leaf source read hl) tree control path start history
    · intro h; exact literalCompiled_run _ read h

theorem rangeScanProgram_tCount (n : Nat) (after : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control r : Wire) (path : List Wire)
    (leaf : Nat → Wire → FixedSegment n) (source : Nat → Wire → AdaptiveCircuit)
    (read : ConstantBit n → Bool)
    (hl : ∀ label control start h, compiledTCount (leaf label control start) read h = (source label control).tCount)
    (start : Nat) (history : Fin start → Bool) :
    compiledTCount (rangeScanProgram n after order tree control r path leaf start) read history =
      (measuredRangeScan after order tree control r path source).tCount := by
  unfold rangeScanProgram measuredRangeScan
  split
  · apply prependCompiled_tCount_eq
    exact unaryProgram_tCount n order _ _ read (rangeLeafProgram_tCount n true r leaf source read hl) tree control path start history
  · apply appendCompiled_tCount_eq
    · exact unaryProgram_tCount n order _ _ read (rangeLeafProgram_tCount n false r leaf source read hl) tree control path start history
    · intro h; exact literalCompiled_tCount _ read h

end ShorECDLP.Paper2607_13816.ChallengeMigration
