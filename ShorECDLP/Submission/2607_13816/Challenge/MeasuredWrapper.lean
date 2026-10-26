import ShorECDLP.Submission.«2607_13816».Challenge.MeasuredSchedule
import ShorECDLP.Submission.«2607_13816».Challenge.Wrapper
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredWrapper
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
attribute [local irreducible] measuredEEAForwardProgram measuredEEAReverseProgram
def measuredForwardWrapperSources  : List AdaptiveCircuit :=
  ([eeaPreprocess,
    secp256k1MeasuredEEAForward indexedStepProductionRegisters,
    .unitary (canonicalWork2Rotation ++ terminalEpochCompression) .done,
    secp256k1EEAParityCorrection,
    .unitary (terminalWork1Clear) .done] : List AdaptiveCircuit)
def measuredForwardWrapperSegments (n : Nat)  : List (FixedSegment n) :=
  ([(fun cursor => preprocessProgram n cursor),
    (fun cursor => measuredEEAForwardProgram n cursor indexedStepProductionRegisters),
    (fun _ => ⟨0, literalProgram (canonicalWork2Rotation ++ terminalEpochCompression)⟩),
    (fun cursor => productionParityProgram n cursor),
    (fun _ => ⟨0, literalProgram (terminalWork1Clear)⟩)] : List (FixedSegment n))
theorem measuredForwardWrapperSources_eq  :
    sequenceCircuit (measuredForwardWrapperSources ) = secp256k1MeasuredEEAForwardWrapper := by
  simp only [measuredForwardWrapperSources, sequenceCircuit, secp256k1MeasuredEEAForwardWrapper, adaptive_seq_assoc, adaptive_seq_done]

def measuredForwardWrapperProgram (n start : Nat)  : (count : Nat) × Straight n start (start+count) :=
  sequenceProgram n (measuredForwardWrapperSegments n ) start
attribute [local irreducible] measuredForwardWrapperProgram
theorem measuredForwardWrapperProgram_run (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (measuredForwardWrapperProgram n start ) read history = (secp256k1MeasuredEEAForwardWrapper).run := by
  unfold measuredForwardWrapperProgram
  rw [← measuredForwardWrapperSources_eq ]
  apply sequenceProgram_run
  unfold measuredForwardWrapperSegments measuredForwardWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor h
    exact preprocessProgram_run n cursor read h
  · intro cursor h
    exact measuredEEAForwardProgram_run n cursor indexedStepProductionRegisters read h
  · intro cursor h
    exact literalCompiled_run _ read h
  · intro cursor h
    exact productionParityProgram_run n cursor read h
  · intro cursor h
    exact literalCompiled_run _ read h

theorem measuredForwardWrapperProgram_tCount (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (measuredForwardWrapperProgram n start ) read history = (secp256k1MeasuredEEAForwardWrapper).tCount := by
  unfold measuredForwardWrapperProgram
  rw [← measuredForwardWrapperSources_eq ]
  apply sequenceProgram_tCount
  unfold measuredForwardWrapperSegments measuredForwardWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor h
    exact preprocessProgram_tCount n cursor read h
  · intro cursor h
    exact measuredEEAForwardProgram_tCount n cursor indexedStepProductionRegisters read h
  · intro cursor h
    exact literalCompiled_tCount _ read h
  · intro cursor h
    exact productionParityProgram_tCount n cursor read h
  · intro cursor h
    exact literalCompiled_tCount _ read h

def measuredReverseWrapperSources  : List AdaptiveCircuit :=
  ([.unitary (terminalWork1Clear) .done,
    secp256k1EEAParityCorrection,
    .unitary (terminalEpochCompression ++ canonicalWork2InverseRotation) .done,
    secp256k1MeasuredEEAReverse indexedStepProductionRegisters,
    eeaUnpreprocess] : List AdaptiveCircuit)
def measuredReverseWrapperSegments (n : Nat)  : List (FixedSegment n) :=
  ([(fun _ => ⟨0, literalProgram (terminalWork1Clear)⟩),
    (fun cursor => productionParityProgram n cursor),
    (fun _ => ⟨0, literalProgram (terminalEpochCompression ++ canonicalWork2InverseRotation)⟩),
    (fun cursor => measuredEEAReverseProgram n cursor indexedStepProductionRegisters),
    (fun cursor => unpreprocessProgram n cursor)] : List (FixedSegment n))
theorem measuredReverseWrapperSources_eq  :
    sequenceCircuit (measuredReverseWrapperSources ) = secp256k1MeasuredEEAReverseWrapper := by
  simp only [measuredReverseWrapperSources, sequenceCircuit, secp256k1MeasuredEEAReverseWrapper, secp256k1EEAReversePostprocessing, adaptive_seq_assoc, adaptive_seq_done]

def measuredReverseWrapperProgram (n start : Nat)  : (count : Nat) × Straight n start (start+count) :=
  sequenceProgram n (measuredReverseWrapperSegments n ) start
attribute [local irreducible] measuredReverseWrapperProgram
theorem measuredReverseWrapperProgram_run (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (measuredReverseWrapperProgram n start ) read history = (secp256k1MeasuredEEAReverseWrapper).run := by
  unfold measuredReverseWrapperProgram
  rw [← measuredReverseWrapperSources_eq ]
  apply sequenceProgram_run
  unfold measuredReverseWrapperSegments measuredReverseWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor h
    exact literalCompiled_run _ read h
  · intro cursor h
    exact productionParityProgram_run n cursor read h
  · intro cursor h
    exact literalCompiled_run _ read h
  · intro cursor h
    exact measuredEEAReverseProgram_run n cursor indexedStepProductionRegisters read h
  · intro cursor h
    exact unpreprocessProgram_run n cursor read h

theorem measuredReverseWrapperProgram_tCount (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (measuredReverseWrapperProgram n start ) read history = (secp256k1MeasuredEEAReverseWrapper).tCount := by
  unfold measuredReverseWrapperProgram
  rw [← measuredReverseWrapperSources_eq ]
  apply sequenceProgram_tCount
  unfold measuredReverseWrapperSegments measuredReverseWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor h
    exact literalCompiled_tCount _ read h
  · intro cursor h
    exact productionParityProgram_tCount n cursor read h
  · intro cursor h
    exact literalCompiled_tCount _ read h
  · intro cursor h
    exact measuredEEAReverseProgram_tCount n cursor indexedStepProductionRegisters read h
  · intro cursor h
    exact unpreprocessProgram_tCount n cursor read h

end ShorECDLP.Paper2607_13816.ChallengeMigration
