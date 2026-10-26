import ShorECDLP.Submission.«2607_13816».Challenge.IndexedStep
import ShorECDLP.Submission.«2607_13816».EEA.Schedule
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def scheduleProgram (n : Nat) (r : IndexedStepRegisters) (width : Nat) :
    (count first start : Nat) → (events : Nat) × Straight n start (start+events)
  | 0, _, _ => ⟨0, literalProgram []⟩
  | count+1, first, start =>
    let step := indexedStepProgram n start r width first
    appendCompiled step (scheduleProgram n r width count (first+1) (start+step.1))

def inverseScheduleProgram (n : Nat) (r : IndexedStepRegisters) :
    (count first start : Nat) → (events : Nat) × Straight n start (start+events)
  | 0, _, _ => ⟨0, literalProgram []⟩
  | count+1, first, start =>
    let before := inverseScheduleProgram n r count (first+1) start
    appendCompiled before (indexedInverseStepProgram n (start+before.1) r first)

attribute [local irreducible] indexedStepProgram indexedInverseStepProgram
theorem scheduleProgram_run (n : Nat) (r : IndexedStepRegisters) (width : Nat) (count first start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (scheduleProgram n r width count first start) read history =
      (indexedScheduleAdaptive r width first count).run := by
  induction count generalizing first start with
  | zero =>
    exact literalProgram_run [] read history
  | succ count ih =>
    unfold scheduleProgram indexedScheduleAdaptive
    dsimp only
    apply appendCompiled_run_eq
    · exact indexedStepProgram_run n start r width first read history
    · intro h
      exact ih (first+1) _ h

theorem scheduleProgram_tCount (n : Nat) (r : IndexedStepRegisters) (width : Nat) (count first start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (scheduleProgram n r width count first start) read history =
      (indexedScheduleAdaptive r width first count).tCount := by
  induction count generalizing first start with
  | zero =>
    rfl
  | succ count ih =>
    unfold scheduleProgram indexedScheduleAdaptive
    dsimp only
    apply appendCompiled_tCount_eq
    · exact indexedStepProgram_tCount n start r width first read history
    · intro h
      exact ih (first+1) _ h

theorem inverseScheduleProgram_run (n : Nat) (r : IndexedStepRegisters) (count first start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (inverseScheduleProgram n r count first start) read history =
      (indexedScheduleInverseAdaptive r 256 first count).run := by
  induction count generalizing first start with
  | zero =>
    exact literalProgram_run [] read history
  | succ count ih =>
    unfold inverseScheduleProgram indexedScheduleInverseAdaptive
    dsimp only
    apply appendCompiled_run_eq
    · exact ih (first+1) start history
    · intro h
      exact indexedInverseStepProgram_run n _ r first read h

theorem inverseScheduleProgram_tCount (n : Nat) (r : IndexedStepRegisters) (count first start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (inverseScheduleProgram n r count first start) read history =
      (indexedScheduleInverseAdaptive r 256 first count).tCount := by
  induction count generalizing first start with
  | zero =>
    rfl
  | succ count ih =>
    unfold inverseScheduleProgram indexedScheduleInverseAdaptive
    dsimp only
    apply appendCompiled_tCount_eq
    · exact ih (first+1) start history
    · intro h
      exact indexedInverseStepProgram_tCount n _ r first read h

def eeaForwardProgram (n start : Nat) (r : IndexedStepRegisters) :
    (count : Nat) × Straight n start (start+count) := scheduleProgram n r 256 secp256k1ScheduleLength 1 start
theorem eeaForwardProgram_run (n start : Nat) (r : IndexedStepRegisters)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (eeaForwardProgram n start r) read history = (secp256k1EEAForwardAdaptive r).run :=
  scheduleProgram_run n r 256 secp256k1ScheduleLength 1 start read history

theorem eeaForwardProgram_tCount (n start : Nat) (r : IndexedStepRegisters)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (eeaForwardProgram n start r) read history = (secp256k1EEAForwardAdaptive r).tCount :=
  scheduleProgram_tCount n r 256 secp256k1ScheduleLength 1 start read history

def eeaReverseProgram (n start : Nat) (r : IndexedStepRegisters) :
    (count : Nat) × Straight n start (start+count) := inverseScheduleProgram n r secp256k1ScheduleLength 1 start
theorem eeaReverseProgram_run (n start : Nat) (r : IndexedStepRegisters)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (eeaReverseProgram n start r) read history = (secp256k1EEAReverseAdaptive r).run :=
  inverseScheduleProgram_run n r secp256k1ScheduleLength 1 start read history

theorem eeaReverseProgram_tCount (n start : Nat) (r : IndexedStepRegisters)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (eeaReverseProgram n start r) read history = (secp256k1EEAReverseAdaptive r).tCount :=
  inverseScheduleProgram_tCount n r secp256k1ScheduleLength 1 start read history

end ShorECDLP.Paper2607_13816.ChallengeMigration
