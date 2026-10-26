import ShorECDLP.Submission.«2607_13816».Challenge.Interval
import ShorECDLP.Submission.«2607_13816».EEA.Interval
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
def intervalTopFirstProgram (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) : (count : Nat) × Straight n start (start+count) :=
  if intervalHasTopSpecial k K then topFirstProgram n start mode (intervalTopRelative k K) r.lengthS r.lengthQ (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K)) (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control
  else ⟨0, literalProgram []⟩
theorem intervalTopFirstProgram_run (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (intervalTopFirstProgram n start r k K mode target) read history =
      (if intervalHasTopSpecial k K then topSpecialFirstLeafAdaptive mode (intervalTopRelative k K) r.lengthS r.lengthQ (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K)) (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control else .unitary [] .done).run := by
  unfold intervalTopFirstProgram
  split
  · exact topFirstProgram_run n start mode (intervalTopRelative k K) r.lengthS r.lengthQ (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K)) (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control read history
  · rfl

theorem intervalTopFirstProgram_tCount (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (intervalTopFirstProgram n start r k K mode target) read history =
      (if intervalHasTopSpecial k K then topSpecialFirstLeafAdaptive mode (intervalTopRelative k K) r.lengthS r.lengthQ (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K)) (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control else .unitary [] .done).tCount := by
  unfold intervalTopFirstProgram
  split
  · exact topFirstProgram_tCount n start mode (intervalTopRelative k K) r.lengthS r.lengthQ (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K)) (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control read history
  · rfl

def intervalTopSecondProgram (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) : (count : Nat) × Straight n start (start+count) :=
  if intervalHasTopSpecial k K then topSecondProgram n start mode (intervalTopRelative k K) r.lengthS r.lengthQ (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K)) (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control
  else ⟨0, literalProgram []⟩
theorem intervalTopSecondProgram_run (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (intervalTopSecondProgram n start r k K mode target) read history =
      (if intervalHasTopSpecial k K then topSpecialSecondLeafAdaptive mode (intervalTopRelative k K) r.lengthS r.lengthQ (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K)) (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control else .unitary [] .done).run := by
  unfold intervalTopSecondProgram
  split
  · exact topSecondProgram_run n start mode (intervalTopRelative k K) r.lengthS r.lengthQ (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K)) (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control read history
  · rfl

theorem intervalTopSecondProgram_tCount (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (intervalTopSecondProgram n start r k K mode target) read history =
      (if intervalHasTopSpecial k K then topSpecialSecondLeafAdaptive mode (intervalTopRelative k K) r.lengthS r.lengthQ (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K)) (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control else .unitary [] .done).tCount := by
  unfold intervalTopSecondProgram
  split
  · exact topSecondProgram_tCount n start mode (intervalTopRelative k K) r.lengthS r.lengthQ (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K)) (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control read history
  · rfl

def intervalProgram (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget) :
    (count : Nat) × Straight n start (start+count) :=
  let top1 := intervalTopFirstProgram n start r k K mode target
  let pass1 := traversalFirstProgram n (start+top1.1) mode (intervalHasTopSpecial k K) (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K) (r.cellScratch k K) (r.targetAt target) (r.addendAt target) (intervalTree r k K) r.control r.control (r.rightPaths k K) (r.leftPaths k K)
  let pass2 := traversalSecondProgram n (start+top1.1+pass1.1) mode (intervalHasTopSpecial k K) (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K) (r.cellScratch k K) (r.targetAt target) (r.addendAt target) (intervalTree r k K) r.control r.control (r.rightPaths k K) (r.leftPaths k K)
  let top2 := intervalTopSecondProgram n (start+top1.1+pass1.1+pass2.1) r k K mode target
  prependCompiled (prepareIntervalEndpoints r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) width k)
    (appendCompiled top1 (appendCompiled pass1 (prependCompiled (intervalSignUpdate r k K signUpdate)
      (appendCompiled pass2 (appendCompiled top2 ⟨0, literalProgram
        (restoreIntervalEndpoints r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) width k)⟩)))))
theorem intervalProgram_run (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (intervalProgram n start r width k K mode signUpdate target) read history =
      (intervalAddSub r width k K mode signUpdate target).run := by
  unfold intervalProgram intervalAddSub
  dsimp only
  simp only [AdaptiveCircuit.seq]
  apply prependCompiled_run_eq
  apply appendCompiled_run_eq
  · exact intervalTopFirstProgram_run n start r k K mode target read history
  · intro h
    apply appendCompiled_run_eq
    · exact traversalFirstProgram_run n _ mode (intervalHasTopSpecial k K) (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K) (r.cellScratch k K) (r.targetAt target) (r.addendAt target) (intervalTree r k K) r.control r.control (r.rightPaths k K) (r.leftPaths k K) read h
    · intro h
      apply prependCompiled_run_eq
      apply appendCompiled_run_eq
      · exact traversalSecondProgram_run n _ mode (intervalHasTopSpecial k K) (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K) (r.cellScratch k K) (r.targetAt target) (r.addendAt target) (intervalTree r k K) r.control r.control (r.rightPaths k K) (r.leftPaths k K) read h
      · intro h
        apply appendCompiled_run_eq
        · exact intervalTopSecondProgram_run n _ r k K mode target read h
        · intro h
          exact literalProgram_run _ read h

theorem intervalProgram_tCount (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (intervalProgram n start r width k K mode signUpdate target) read history =
      (intervalAddSub r width k K mode signUpdate target).tCount := by
  unfold intervalProgram intervalAddSub
  dsimp only
  simp only [AdaptiveCircuit.seq]
  apply prependCompiled_tCount_eq
  apply appendCompiled_tCount_eq
  · exact intervalTopFirstProgram_tCount n start r k K mode target read history
  · intro h
    apply appendCompiled_tCount_eq
    · exact traversalFirstProgram_tCount n _ mode (intervalHasTopSpecial k K) (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K) (r.cellScratch k K) (r.targetAt target) (r.addendAt target) (intervalTree r k K) r.control r.control (r.rightPaths k K) (r.leftPaths k K) read h
    · intro h
      apply prependCompiled_tCount_eq
      apply appendCompiled_tCount_eq
      · exact traversalSecondProgram_tCount n _ mode (intervalHasTopSpecial k K) (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K) (r.cellScratch k K) (r.targetAt target) (r.addendAt target) (intervalTree r k K) r.control r.control (r.rightPaths k K) (r.leftPaths k K) read h
      · intro h
        apply appendCompiled_tCount_eq
        · exact intervalTopSecondProgram_tCount n _ r k K mode target read h
        · intro h
          simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]

def intervalInverseProgram (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget) :
    (count : Nat) × Straight n start (start+count) :=
  intervalProgram n start r width k K mode.inverse signUpdate target
theorem intervalInverseProgram_run (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (intervalInverseProgram n start r width k K mode signUpdate target) read history =
      (intervalAddSubInverse r width k K mode signUpdate target).run :=
  intervalProgram_run n start r width k K mode.inverse signUpdate target read history

theorem intervalInverseProgram_tCount (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (intervalInverseProgram n start r width k K mode signUpdate target) read history =
      (intervalAddSubInverse r width k K mode signUpdate target).tCount :=
  intervalProgram_tCount n start r width k K mode.inverse signUpdate target read history

end ShorECDLP.Paper2607_13816.ChallengeMigration
