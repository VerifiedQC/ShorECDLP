import ShorECDLP.Submission.«2607_13816».Challenge.RetainedRecords
import ShorECDLP.Submission.«2607_13816».Challenge.Horner
import ShorECDLP.Submission.«2607_13816».Arithmetic.InPlace
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
attribute [local irreducible] hornerProgram hornerInverseProgram measuredForwardWrapperProgram
  measuredForwardDataBankProgram measuredReverseDataBankProgram

def multiplyWorkProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  hornerProgram n start (List.range' 263 256) (List.range' 580 256) (List.range' 7 256) secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559

theorem multiplyWorkProgram_run (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (multiplyWorkProgram n start) read history = fig15MultiplyToWork.run := by
  exact hornerProgram_run n start (List.range' 263 256) (List.range' 580 256) (List.range' 7 256) secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559
    (by simp) (by simp [secp256k1ReductionConstantBits]) (by simp) read history

theorem multiplyWorkProgram_tCount (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (multiplyWorkProgram n start) read history = fig15MultiplyToWork.tCount := by
  exact hornerProgram_tCount n start (List.range' 263 256) (List.range' 580 256) (List.range' 7 256) secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559
    (by simp) (by simp [secp256k1ReductionConstantBits]) (by simp) read history

def multiplyDataProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  hornerProgram n start (List.range' 263 256) (List.range' 7 256) (List.range' 580 256) secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559

theorem multiplyDataProgram_run (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (multiplyDataProgram n start) read history = fig15MultiplyToData.run := by
  exact hornerProgram_run n start (List.range' 263 256) (List.range' 7 256) (List.range' 580 256) secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559
    (by simp) (by simp [secp256k1ReductionConstantBits]) (by simp) read history

theorem multiplyDataProgram_tCount (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (multiplyDataProgram n start) read history = fig15MultiplyToData.tCount := by
  exact hornerProgram_tCount n start (List.range' 263 256) (List.range' 7 256) (List.range' 580 256) secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559
    (by simp) (by simp [secp256k1ReductionConstantBits]) (by simp) read history

def unmultiplyDataProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  hornerInverseProgram n start (List.range' 263 256) (List.range' 7 256) (List.range' 580 256) (constantBits 256 ShorECDLP.p) ShorECDLP.p 558 560 561 559

theorem unmultiplyDataProgram_run (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (unmultiplyDataProgram n start) read history = fig15MultiplyToDataInverse.run := by
  exact hornerInverseProgram_run n start (List.range' 263 256) (List.range' 7 256) (List.range' 580 256) (constantBits 256 ShorECDLP.p) ShorECDLP.p 558 560 561 559
    (by simp) (by simp) (by simp) read history

theorem unmultiplyDataProgram_tCount (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (unmultiplyDataProgram n start) read history = fig15MultiplyToDataInverse.tCount := by
  exact hornerInverseProgram_tCount n start (List.range' 263 256) (List.range' 7 256) (List.range' 580 256) (constantBits 256 ShorECDLP.p) ShorECDLP.p 558 560 561 559
    (by simp) (by simp) (by simp) read history

def correctionCompiled (n start : Nat) (ws : List Wire) (prior : List (Fin start)) :
    (count : Nat) × Straight n start (start+count) :=
  ⟨0, registerCorrectionProgram ws prior .done⟩

theorem correctionCompiled_run (n start : Nat) (ws : List Wire) (prior : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (correctionCompiled n start ws prior) read history =
      (AdaptiveCircuit.unitary (registerZCorrection ws (prior.map history)) .done).run :=
  registerCorrectionProgram_run ws prior .done read history

theorem correctionCompiled_tCount (n start : Nat) (ws : List Wire) (prior : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (correctionCompiled n start ws prior) read history =
      (AdaptiveCircuit.unitary (registerZCorrection ws (prior.map history)) .done).tCount := by
  simp only [correctionCompiled, compiledTCount, registerCorrectionProgram_tCount,
    registerZCorrection_tCount, Straight.instantiate, AdaptiveCircuit.tCount]



attribute [local irreducible] multiplyWorkProgram multiplyDataProgram unmultiplyDataProgram

def appendLiteral {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (gs : Circuit) : (count : Nat) × Straight n start (start+count) :=
  appendCompiled p ⟨0, literalProgram gs⟩

theorem appendLiteral_run {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (gs : Circuit) (source : AdaptiveCircuit) (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (hp : compiledRun p read history = source.run) :
    compiledRun (appendLiteral p gs) read history = (source.seq (.unitary gs .done)).run := by
  apply appendCompiled_run_eq p _ read history source (.unitary gs .done) hp
  intro h; exact literalCompiled_run gs read h

theorem appendLiteral_tCount {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (gs : Circuit) (source : AdaptiveCircuit) (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (hp : compiledTCount p read history = source.tCount) :
    compiledTCount (appendLiteral p gs) read history = (source.seq (.unitary gs .done)).tCount := by
  apply appendCompiled_tCount_eq p _ read history source (.unitary gs .done) hp
  intro h; exact literalCompiled_tCount gs read h

def divisionCleanupSource : AdaptiveCircuit := fig15MultiplyToDataInverse.seq (.unitary fig15SwapOutput .done)
def divisionCleanupProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  appendLiteral (unmultiplyDataProgram n start) fig15SwapOutput

theorem divisionCleanupProgram_run (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (divisionCleanupProgram n start) read history = divisionCleanupSource.run := by
  unfold divisionCleanupProgram divisionCleanupSource
  apply appendLiteral_run
  exact unmultiplyDataProgram_run n start read history

theorem divisionCleanupProgram_tCount (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (divisionCleanupProgram n start) read history = divisionCleanupSource.tCount := by
  unfold divisionCleanupProgram divisionCleanupSource
  apply appendLiteral_tCount
  exact unmultiplyDataProgram_tCount n start read history

attribute [local irreducible] divisionCleanupProgram

def divisionCorrectionProgram (n start : Nat) (prior : List (Fin start)) :
    (count : Nat) × Straight n start (start+count) :=
  appendCompiled (correctionCompiled n start (List.range' 580 256) prior) (divisionCleanupProgram n start)

theorem divisionCorrectionProgram_run (n start : Nat) (prior : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (divisionCorrectionProgram n start prior) read history =
      ((AdaptiveCircuit.unitary (registerZCorrection (List.range' 580 256) (prior.map history)) .done).seq divisionCleanupSource).run := by
  unfold divisionCorrectionProgram
  apply appendCompiled_run_eq
  · exact correctionCompiled_run n start _ prior read history
  · intro h; exact divisionCleanupProgram_run n start read h

theorem divisionCorrectionProgram_tCount (n start : Nat) (prior : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (divisionCorrectionProgram n start prior) read history =
      ((AdaptiveCircuit.unitary (registerZCorrection (List.range' 580 256) (prior.map history)) .done).seq divisionCleanupSource).tCount := by
  unfold divisionCorrectionProgram
  apply appendCompiled_tCount_eq
  · exact correctionCompiled_tCount n start _ prior read history
  · intro h; exact divisionCleanupProgram_tCount n start read h

def divisionAfterResetProgram (n start : Nat) (prior : List (Fin start)) :
    (count : Nat) × Straight n start (start+count) :=
  let eea := measuredReverseDataBankProgram n start
  appendRetaining (appendCompiled eea (multiplyDataProgram n (start+eea.1)))
    (divisionCorrectionProgram n) prior

theorem divisionAfterResetProgram_run (n start : Nat) (prior : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (divisionAfterResetProgram n start prior) read history = (fig15DivisionAfterReset (prior.map history)).run := by
  unfold divisionAfterResetProgram
  have h := appendRetaining_run
    (appendCompiled (measuredReverseDataBankProgram n start) (multiplyDataProgram n _))
    (divisionCorrectionProgram n) prior (secp256k1MeasuredEEAReverseInDataBank.seq fig15MultiplyToData)
    (fun outcomes => (AdaptiveCircuit.unitary (registerZCorrection (List.range' 580 256) outcomes) .done).seq divisionCleanupSource)
    read history (by
      apply appendCompiled_run_eq
      · exact measuredReverseDataBankProgram_run n start read history
      · intro h; exact multiplyDataProgram_run n _ read h)
    (fun cursor indices h => divisionCorrectionProgram_run n cursor indices read h)
  simpa only [fig15DivisionAfterReset, divisionCleanupSource, adaptive_seq_assoc] using h

theorem divisionAfterResetProgram_tCount (n start : Nat) (prior : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (divisionAfterResetProgram n start prior) read history = (fig15DivisionAfterReset (prior.map history)).tCount := by
  unfold divisionAfterResetProgram
  have h := appendRetaining_tCount
    (appendCompiled (measuredReverseDataBankProgram n start) (multiplyDataProgram n _))
    (divisionCorrectionProgram n) prior (secp256k1MeasuredEEAReverseInDataBank.seq fig15MultiplyToData)
    (fun outcomes => (AdaptiveCircuit.unitary (registerZCorrection (List.range' 580 256) outcomes) .done).seq divisionCleanupSource)
    read history (by
      apply appendCompiled_tCount_eq
      · exact measuredReverseDataBankProgram_tCount n start read history
      · intro h; exact multiplyDataProgram_tCount n _ read h)
    (fun cursor indices h => divisionCorrectionProgram_tCount n cursor indices read h)
  simpa only [fig15DivisionAfterReset, divisionCleanupSource, adaptive_seq_assoc] using h

attribute [local irreducible] divisionAfterResetProgram

def divisionProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  let eea := measuredForwardWrapperProgram n start
  let first := appendCompiled eea (multiplyWorkProgram n (start+eea.1))
  appendCompiled first (collectProgram n (divisionAfterResetProgram n) (List.range' 580 256) (start+first.1) ([] : List (Fin _)))

theorem divisionProgram_run (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (divisionProgram n start) read history = secp256k1InPlaceDivision.run := by
  unfold divisionProgram secp256k1InPlaceDivision
  apply appendCompiled_run_eq
  · apply appendCompiled_run_eq
    · exact measuredForwardWrapperProgram_run n start read history
    · intro h; exact multiplyWorkProgram_run n _ read h
  · intro h
    exact collectProgram_run n (divisionAfterResetProgram n) fig15DivisionAfterReset read
      (fun cursor prior h => divisionAfterResetProgram_run n cursor prior read h) _ _ ([] : List (Fin _)) h

theorem divisionProgram_tCount (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (divisionProgram n start) read history = secp256k1InPlaceDivision.tCount := by
  unfold divisionProgram secp256k1InPlaceDivision
  apply appendCompiled_tCount_eq
  · apply appendCompiled_tCount_eq
    · exact measuredForwardWrapperProgram_tCount n start read history
    · intro h; exact multiplyWorkProgram_tCount n _ read h
  · intro h
    exact collectProgram_tCount n (divisionAfterResetProgram n) fig15DivisionAfterReset read
      (fun cursor prior h => divisionAfterResetProgram_tCount n cursor prior read h) _ _ ([] : List (Fin _)) h

def multiplicationCleanupSource : AdaptiveCircuit := fig15MultiplyToDataInverse.seq (secp256k1MeasuredEEAReverseInDataBank.seq (.unitary fig15SwapOutput .done))
def multiplicationCleanupProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  let first := unmultiplyDataProgram n start
  appendCompiled first (appendLiteral (measuredReverseDataBankProgram n (start+first.1)) fig15SwapOutput)

theorem multiplicationCleanupProgram_run (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (multiplicationCleanupProgram n start) read history = multiplicationCleanupSource.run := by
  unfold multiplicationCleanupProgram multiplicationCleanupSource
  apply appendCompiled_run_eq
  · exact unmultiplyDataProgram_run n start read history
  · intro h
    apply appendLiteral_run
    exact measuredReverseDataBankProgram_run n _ read h

theorem multiplicationCleanupProgram_tCount (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (multiplicationCleanupProgram n start) read history = multiplicationCleanupSource.tCount := by
  unfold multiplicationCleanupProgram multiplicationCleanupSource
  apply appendCompiled_tCount_eq
  · exact unmultiplyDataProgram_tCount n start read history
  · intro h
    apply appendLiteral_tCount
    exact measuredReverseDataBankProgram_tCount n _ read h

attribute [local irreducible] multiplicationCleanupProgram

def multiplicationCorrectionProgram (n start : Nat) (prior : List (Fin start)) :
    (count : Nat) × Straight n start (start+count) :=
  appendCompiled (correctionCompiled n start (List.range' 580 256) prior) (multiplicationCleanupProgram n start)

theorem multiplicationCorrectionProgram_run (n start : Nat) (prior : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (multiplicationCorrectionProgram n start prior) read history =
      ((AdaptiveCircuit.unitary (registerZCorrection (List.range' 580 256) (prior.map history)) .done).seq multiplicationCleanupSource).run := by
  unfold multiplicationCorrectionProgram
  apply appendCompiled_run_eq
  · exact correctionCompiled_run n start _ prior read history
  · intro h; exact multiplicationCleanupProgram_run n start read h

theorem multiplicationCorrectionProgram_tCount (n start : Nat) (prior : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (multiplicationCorrectionProgram n start prior) read history =
      ((AdaptiveCircuit.unitary (registerZCorrection (List.range' 580 256) (prior.map history)) .done).seq multiplicationCleanupSource).tCount := by
  unfold multiplicationCorrectionProgram
  apply appendCompiled_tCount_eq
  · exact correctionCompiled_tCount n start _ prior read history
  · intro h; exact multiplicationCleanupProgram_tCount n start read h

def multiplicationAfterResetProgram (n start : Nat) (prior : List (Fin start)) :
    (count : Nat) × Straight n start (start+count) :=
  let eea := measuredForwardDataBankProgram n start
  appendRetaining (appendCompiled eea (multiplyDataProgram n (start+eea.1)))
    (multiplicationCorrectionProgram n) prior

theorem multiplicationAfterResetProgram_run (n start : Nat) (prior : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (multiplicationAfterResetProgram n start prior) read history = (fig15MultiplicationAfterReset (prior.map history)).run := by
  unfold multiplicationAfterResetProgram
  have h := appendRetaining_run
    (appendCompiled (measuredForwardDataBankProgram n start) (multiplyDataProgram n _))
    (multiplicationCorrectionProgram n) prior (secp256k1MeasuredEEAForwardInDataBank.seq fig15MultiplyToData)
    (fun outcomes => (AdaptiveCircuit.unitary (registerZCorrection (List.range' 580 256) outcomes) .done).seq multiplicationCleanupSource)
    read history (by
      apply appendCompiled_run_eq
      · exact measuredForwardDataBankProgram_run n start read history
      · intro h; exact multiplyDataProgram_run n _ read h)
    (fun cursor indices h => multiplicationCorrectionProgram_run n cursor indices read h)
  simpa only [fig15MultiplicationAfterReset, multiplicationCleanupSource, adaptive_seq_assoc] using h

theorem multiplicationAfterResetProgram_tCount (n start : Nat) (prior : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (multiplicationAfterResetProgram n start prior) read history = (fig15MultiplicationAfterReset (prior.map history)).tCount := by
  unfold multiplicationAfterResetProgram
  have h := appendRetaining_tCount
    (appendCompiled (measuredForwardDataBankProgram n start) (multiplyDataProgram n _))
    (multiplicationCorrectionProgram n) prior (secp256k1MeasuredEEAForwardInDataBank.seq fig15MultiplyToData)
    (fun outcomes => (AdaptiveCircuit.unitary (registerZCorrection (List.range' 580 256) outcomes) .done).seq multiplicationCleanupSource)
    read history (by
      apply appendCompiled_tCount_eq
      · exact measuredForwardDataBankProgram_tCount n start read history
      · intro h; exact multiplyDataProgram_tCount n _ read h)
    (fun cursor indices h => multiplicationCorrectionProgram_tCount n cursor indices read h)
  simpa only [fig15MultiplicationAfterReset, multiplicationCleanupSource, adaptive_seq_assoc] using h

attribute [local irreducible] multiplicationAfterResetProgram

def multiplicationProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  let first := multiplyWorkProgram n start
  appendCompiled first (collectProgram n (multiplicationAfterResetProgram n) (List.range' 580 256) (start+first.1) ([] : List (Fin _)))

theorem multiplicationProgram_run (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (multiplicationProgram n start) read history = secp256k1InPlaceMultiplication.run := by
  unfold multiplicationProgram secp256k1InPlaceMultiplication
  apply appendCompiled_run_eq
  · exact multiplyWorkProgram_run n start read history
  · intro h
    exact collectProgram_run n (multiplicationAfterResetProgram n) fig15MultiplicationAfterReset read
      (fun cursor prior h => multiplicationAfterResetProgram_run n cursor prior read h) _ _ ([] : List (Fin _)) h

theorem multiplicationProgram_tCount (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (multiplicationProgram n start) read history = secp256k1InPlaceMultiplication.tCount := by
  unfold multiplicationProgram secp256k1InPlaceMultiplication
  apply appendCompiled_tCount_eq
  · exact multiplyWorkProgram_tCount n start read history
  · intro h
    exact collectProgram_tCount n (multiplicationAfterResetProgram n) fig15MultiplicationAfterReset read
      (fun cursor prior h => multiplicationAfterResetProgram_tCount n cursor prior read h) _ _ ([] : List (Fin _)) h

end ShorECDLP.Paper2607_13816.ChallengeMigration
