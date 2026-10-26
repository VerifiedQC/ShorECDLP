import ShorECDLP.Submission.«2607_13816».Challenge.Schedule
import ShorECDLP.Submission.«2607_13816».Challenge.EEACenter
import ShorECDLP.Submission.«2607_13816».EEA.AdaptiveWrapper
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
attribute [local irreducible] eeaCenterProgram eeaUncenterProgram eeaParityProgram eeaForwardProgram eeaReverseProgram
theorem literalCompiled_run {n start : Nat} (gs : Circuit)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun ⟨0, literalProgram gs⟩ read history =
      (AdaptiveCircuit.unitary gs .done).run := by
  exact literalProgram_run gs read history

def surroundCompiled {n start : Nat} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    (count : Nat) × Straight n start (start+count) :=
  prependCompiled before (appendCompiled p ⟨0, literalProgram after⟩)

theorem surroundCompiled_run {n start : Nat} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) (target : AdaptiveCircuit)
    (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (hp : compiledRun p read history = target.run) :
    compiledRun (surroundCompiled before after p) read history =
      (AdaptiveCircuit.unitary before (target.seq (.unitary after .done))).run := by
  unfold surroundCompiled
  apply prependCompiled_run_eq
  apply appendCompiled_run_eq
  · exact hp
  · intro h
    exact literalCompiled_run _ read h

theorem surroundCompiled_tCount {n start : Nat} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) (target : AdaptiveCircuit)
    (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (hp : compiledTCount p read history = target.tCount) :
    compiledTCount (surroundCompiled before after p) read history =
      (AdaptiveCircuit.unitary before (target.seq (.unitary after .done))).tCount := by
  unfold surroundCompiled
  apply prependCompiled_tCount_eq
  apply appendCompiled_tCount_eq
  · exact hp
  · intro h
    simp only [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount, Nat.add_zero]

def preprocessProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  surroundCompiled workRegistersPrepare eeaLengthSetup (eeaCenterProgram n start (List.range' 266 256).reverse (List.range' 4 256) (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2)
theorem preprocessProgram_run (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (preprocessProgram n start) read history = eeaPreprocess.run := by
  unfold preprocessProgram eeaPreprocess
  apply surroundCompiled_run
  exact eeaCenterProgram_run n start (List.range' 266 256).reverse (List.range' 4 256) (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2 (by simp) (by simp [constantBits_length]) (by simp) read history

theorem preprocessProgram_tCount (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (preprocessProgram n start) read history = eeaPreprocess.tCount := by
  unfold preprocessProgram eeaPreprocess
  apply surroundCompiled_tCount
  exact eeaCenterProgram_tCount n start (List.range' 266 256).reverse (List.range' 4 256) (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2 (by simp) (by simp [constantBits_length]) (by simp) read history

def unpreprocessProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  surroundCompiled eeaLengthUndo workRegistersRestore (eeaUncenterProgram n start (List.range' 266 256).reverse (List.range' 4 256) (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2)
theorem unpreprocessProgram_run (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (unpreprocessProgram n start) read history = eeaUnpreprocess.run := by
  unfold unpreprocessProgram eeaUnpreprocess
  apply surroundCompiled_run
  exact eeaUncenterProgram_run n start (List.range' 266 256).reverse (List.range' 4 256) (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2 (by simp) (by simp [constantBits_length]) (by simp) read history

theorem unpreprocessProgram_tCount (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (unpreprocessProgram n start) read history = eeaUnpreprocess.tCount := by
  unfold unpreprocessProgram eeaUnpreprocess
  apply surroundCompiled_tCount
  exact eeaUncenterProgram_tCount n start (List.range' 266 256).reverse (List.range' 4 256) (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2 (by simp) (by simp [constantBits_length]) (by simp) read history

def productionParityProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  eeaParityProgram n start (List.range' 263 256) (List.range' 4 255) secp256k1ModulusBits 560 561 562 2
theorem productionParityProgram_run (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (productionParityProgram n start) read history = secp256k1EEAParityCorrection.run := by
  exact eeaParityProgram_run n start _ _ _ 560 561 562 2 (by simp)
    (by simp [secp256k1ModulusBits]) read history

theorem productionParityProgram_tCount (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (productionParityProgram n start) read history = secp256k1EEAParityCorrection.tCount := by
  exact eeaParityProgram_tCount n start _ _ _ 560 561 562 2 (by simp)
    (by simp [secp256k1ModulusBits]) read history

attribute [local irreducible] eeaPreprocess eeaUnpreprocess secp256k1EEAForwardAdaptive secp256k1EEAReverseAdaptive secp256k1EEAParityCorrection

theorem literalCompiled_tCount {n start : Nat} (gs : Circuit)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount ⟨0, literalProgram gs⟩ read history =
      (AdaptiveCircuit.unitary gs .done).tCount := by
  simp only [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount, Nat.add_zero]

def forwardWrapperSources  : List AdaptiveCircuit :=
  ([eeaPreprocess,
    secp256k1EEAForwardAdaptive indexedStepProductionRegisters,
    .unitary (canonicalWork2Rotation ++ terminalEpochCompression) .done,
    secp256k1EEAParityCorrection,
    .unitary (terminalWork1Clear) .done] : List AdaptiveCircuit)
def forwardWrapperSegments (n : Nat)  : List (FixedSegment n) :=
  ([(fun cursor => preprocessProgram n cursor),
    (fun cursor => eeaForwardProgram n cursor indexedStepProductionRegisters),
    (fun _ => ⟨0, literalProgram (canonicalWork2Rotation ++ terminalEpochCompression)⟩),
    (fun cursor => productionParityProgram n cursor),
    (fun _ => ⟨0, literalProgram (terminalWork1Clear)⟩)] : List (FixedSegment n))
theorem forwardWrapperSources_eq  :
    sequenceCircuit (forwardWrapperSources ) = secp256k1EEAForwardWrapper := by
  simp only [forwardWrapperSources, sequenceCircuit, secp256k1EEAForwardWrapper, adaptive_seq_assoc, adaptive_seq_done]

def forwardWrapperProgram (n start : Nat)  : (count : Nat) × Straight n start (start+count) :=
  sequenceProgram n (forwardWrapperSegments n ) start
attribute [local irreducible] forwardWrapperProgram
theorem forwardWrapperProgram_run (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (forwardWrapperProgram n start ) read history = (secp256k1EEAForwardWrapper).run := by
  unfold forwardWrapperProgram
  rw [← forwardWrapperSources_eq ]
  apply sequenceProgram_run
  unfold forwardWrapperSegments forwardWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor h
    exact preprocessProgram_run n cursor read h
  · intro cursor h
    exact eeaForwardProgram_run n cursor indexedStepProductionRegisters read h
  · intro cursor h
    exact literalCompiled_run _ read h
  · intro cursor h
    exact productionParityProgram_run n cursor read h
  · intro cursor h
    exact literalCompiled_run _ read h

theorem forwardWrapperProgram_tCount (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (forwardWrapperProgram n start ) read history = (secp256k1EEAForwardWrapper).tCount := by
  unfold forwardWrapperProgram
  rw [← forwardWrapperSources_eq ]
  apply sequenceProgram_tCount
  unfold forwardWrapperSegments forwardWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor h
    exact preprocessProgram_tCount n cursor read h
  · intro cursor h
    exact eeaForwardProgram_tCount n cursor indexedStepProductionRegisters read h
  · intro cursor h
    exact literalCompiled_tCount _ read h
  · intro cursor h
    exact productionParityProgram_tCount n cursor read h
  · intro cursor h
    exact literalCompiled_tCount _ read h

def reverseWrapperSources  : List AdaptiveCircuit :=
  ([.unitary (terminalWork1Clear) .done,
    secp256k1EEAParityCorrection,
    .unitary (terminalEpochCompression ++ canonicalWork2InverseRotation) .done,
    secp256k1EEAReverseAdaptive indexedStepProductionRegisters,
    eeaUnpreprocess] : List AdaptiveCircuit)
def reverseWrapperSegments (n : Nat)  : List (FixedSegment n) :=
  ([(fun _ => ⟨0, literalProgram (terminalWork1Clear)⟩),
    (fun cursor => productionParityProgram n cursor),
    (fun _ => ⟨0, literalProgram (terminalEpochCompression ++ canonicalWork2InverseRotation)⟩),
    (fun cursor => eeaReverseProgram n cursor indexedStepProductionRegisters),
    (fun cursor => unpreprocessProgram n cursor)] : List (FixedSegment n))
theorem reverseWrapperSources_eq  :
    sequenceCircuit (reverseWrapperSources ) = secp256k1EEAReverseWrapper := by
  simp only [reverseWrapperSources, sequenceCircuit, secp256k1EEAReverseWrapper, secp256k1EEAReversePostprocessing, adaptive_seq_assoc, adaptive_seq_done]

def reverseWrapperProgram (n start : Nat)  : (count : Nat) × Straight n start (start+count) :=
  sequenceProgram n (reverseWrapperSegments n ) start
attribute [local irreducible] reverseWrapperProgram
theorem reverseWrapperProgram_run (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (reverseWrapperProgram n start ) read history = (secp256k1EEAReverseWrapper).run := by
  unfold reverseWrapperProgram
  rw [← reverseWrapperSources_eq ]
  apply sequenceProgram_run
  unfold reverseWrapperSegments reverseWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor h
    exact literalCompiled_run _ read h
  · intro cursor h
    exact productionParityProgram_run n cursor read h
  · intro cursor h
    exact literalCompiled_run _ read h
  · intro cursor h
    exact eeaReverseProgram_run n cursor indexedStepProductionRegisters read h
  · intro cursor h
    exact unpreprocessProgram_run n cursor read h

theorem reverseWrapperProgram_tCount (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (reverseWrapperProgram n start ) read history = (secp256k1EEAReverseWrapper).tCount := by
  unfold reverseWrapperProgram
  rw [← reverseWrapperSources_eq ]
  apply sequenceProgram_tCount
  unfold reverseWrapperSegments reverseWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor h
    exact literalCompiled_tCount _ read h
  · intro cursor h
    exact productionParityProgram_tCount n cursor read h
  · intro cursor h
    exact literalCompiled_tCount _ read h
  · intro cursor h
    exact eeaReverseProgram_tCount n cursor indexedStepProductionRegisters read h
  · intro cursor h
    exact unpreprocessProgram_tCount n cursor read h

end ShorECDLP.Paper2607_13816.ChallengeMigration
