import ShorECDLP.Submission.«2607_13816».Challenge.MeasuredStep
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredScheduleCounts
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def measuredScheduleProgram (n : Nat) (r : IndexedStepRegisters) (width : Nat) :
    (count first start : Nat) → (events : Nat) × Straight n start (start+events)
  | 0, _, _ => ⟨0, literalProgram []⟩
  | count+1, first, start =>
    let step := measuredStepProgram n start r width first
    appendCompiled step (measuredScheduleProgram n r width count (first+1) (start+step.1))

def measuredInverseScheduleProgram (n : Nat) (r : IndexedStepRegisters) :
    (count first start : Nat) → (events : Nat) × Straight n start (start+events)
  | 0, _, _ => ⟨0, literalProgram []⟩
  | count+1, first, start =>
    let before := measuredInverseScheduleProgram n r count (first+1) start
    appendCompiled before (measuredInverseStepProgram n (start+before.1) r first)

attribute [local irreducible] measuredStepProgram measuredInverseStepProgram
theorem measuredScheduleProgram_run (n : Nat) (r : IndexedStepRegisters) (width : Nat) (count first start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (measuredScheduleProgram n r width count first start) read history =
      (measuredIndexedSchedule r width first count).run := by
  induction count generalizing first start with
  | zero =>
    exact literalProgram_run [] read history
  | succ count ih =>
    unfold measuredScheduleProgram measuredIndexedSchedule
    dsimp only
    apply appendCompiled_run_eq
    · exact measuredStepProgram_run n start r width first read history
    · intro h
      exact ih (first+1) _ h

theorem measuredScheduleProgram_tCount (n : Nat) (r : IndexedStepRegisters) (width : Nat) (count first start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (measuredScheduleProgram n r width count first start) read history =
      (measuredIndexedSchedule r width first count).tCount := by
  induction count generalizing first start with
  | zero =>
    rfl
  | succ count ih =>
    unfold measuredScheduleProgram measuredIndexedSchedule
    dsimp only
    apply appendCompiled_tCount_eq
    · exact measuredStepProgram_tCount n start r width first read history
    · intro h
      exact ih (first+1) _ h

theorem measuredInverseScheduleProgram_run (n : Nat) (r : IndexedStepRegisters) (count first start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (measuredInverseScheduleProgram n r count first start) read history =
      (measuredIndexedScheduleInverse r 256 first count).run := by
  induction count generalizing first start with
  | zero =>
    exact literalProgram_run [] read history
  | succ count ih =>
    unfold measuredInverseScheduleProgram measuredIndexedScheduleInverse
    dsimp only
    apply appendCompiled_run_eq
    · exact ih (first+1) start history
    · intro h
      exact measuredInverseStepProgram_run n _ r first read h

theorem measuredInverseScheduleProgram_tCount (n : Nat) (r : IndexedStepRegisters) (count first start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (measuredInverseScheduleProgram n r count first start) read history =
      (measuredIndexedScheduleInverse r 256 first count).tCount := by
  induction count generalizing first start with
  | zero =>
    rfl
  | succ count ih =>
    unfold measuredInverseScheduleProgram measuredIndexedScheduleInverse
    dsimp only
    apply appendCompiled_tCount_eq
    · exact ih (first+1) start history
    · intro h
      exact measuredInverseStepProgram_tCount n _ r first read h

def measuredEEAForwardProgram (n start : Nat) (r : IndexedStepRegisters) :
    (count : Nat) × Straight n start (start+count) := measuredScheduleProgram n r 256 secp256k1ScheduleLength 1 start
theorem measuredEEAForwardProgram_run (n start : Nat) (r : IndexedStepRegisters)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (measuredEEAForwardProgram n start r) read history = (secp256k1MeasuredEEAForward r).run :=
  measuredScheduleProgram_run n r 256 secp256k1ScheduleLength 1 start read history

theorem measuredEEAForwardProgram_tCount (n start : Nat) (r : IndexedStepRegisters)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (measuredEEAForwardProgram n start r) read history = (secp256k1MeasuredEEAForward r).tCount :=
  measuredScheduleProgram_tCount n r 256 secp256k1ScheduleLength 1 start read history

def measuredEEAReverseProgram (n start : Nat) (r : IndexedStepRegisters) :
    (count : Nat) × Straight n start (start+count) := measuredInverseScheduleProgram n r secp256k1ScheduleLength 1 start
theorem measuredEEAReverseProgram_run (n start : Nat) (r : IndexedStepRegisters)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (measuredEEAReverseProgram n start r) read history = (secp256k1MeasuredEEAReverse r).run :=
  measuredInverseScheduleProgram_run n r secp256k1ScheduleLength 1 start read history

theorem measuredEEAReverseProgram_tCount (n start : Nat) (r : IndexedStepRegisters)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (measuredEEAReverseProgram n start r) read history = (secp256k1MeasuredEEAReverse r).tCount :=
  measuredInverseScheduleProgram_tCount n r secp256k1ScheduleLength 1 start read history

end ShorECDLP.Paper2607_13816.ChallengeMigration
