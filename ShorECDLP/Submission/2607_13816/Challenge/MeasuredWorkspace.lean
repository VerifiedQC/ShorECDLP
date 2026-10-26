import ShorECDLP.Submission.«2607_13816».Challenge.MeasuredWrapper
import ShorECDLP.Submission.«2607_13816».Challenge.Relabel
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredWorkspace

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
noncomputable section

/-- Transport the fixed wrapper to the source's exchanged data bank. -/
def measuredForwardDataBankProgram (n start : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  relabelCompiled eeaWorkspaceExchange (measuredForwardWrapperProgram n start)

theorem measuredForwardDataBankProgram_run (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (measuredForwardDataBankProgram n start) read history =
      secp256k1MeasuredEEAForwardInDataBank.run := by
  exact relabelCompiled_run _ _ _ read history (measuredForwardWrapperProgram_run n start read history)

theorem measuredForwardDataBankProgram_tCount (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (measuredForwardDataBankProgram n start) read history =
      secp256k1MeasuredEEAForwardInDataBank.tCount := by
  exact relabelCompiled_tCount _ _ _ read history (measuredForwardWrapperProgram_tCount n start read history)

/-- Transport the fixed wrapper to the source's exchanged data bank. -/
def measuredReverseDataBankProgram (n start : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  relabelCompiled eeaWorkspaceExchange (measuredReverseWrapperProgram n start)

theorem measuredReverseDataBankProgram_run (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (measuredReverseDataBankProgram n start) read history =
      secp256k1MeasuredEEAReverseInDataBank.run := by
  exact relabelCompiled_run _ _ _ read history (measuredReverseWrapperProgram_run n start read history)

theorem measuredReverseDataBankProgram_tCount (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (measuredReverseDataBankProgram n start) read history =
      secp256k1MeasuredEEAReverseInDataBank.tCount := by
  exact relabelCompiled_tCount _ _ _ read history (measuredReverseWrapperProgram_tCount n start read history)

end
end ShorECDLP.Paper2607_13816.ChallengeMigration
