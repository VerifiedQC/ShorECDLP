import ShorECDLP.Submission.«2607_13816».Challenge.Wrapper
import ShorECDLP.Submission.«2607_13816».Challenge.Relabel
import ShorECDLP.Submission.«2607_13816».EEA.WorkspaceReuse

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
noncomputable section

/-- Transport the fixed wrapper to the source's exchanged data bank. -/
def forwardDataBankProgram (n start : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  relabelCompiled eeaWorkspaceExchange (forwardWrapperProgram n start)

theorem forwardDataBankProgram_run (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (forwardDataBankProgram n start) read history =
      secp256k1EEAForwardInDataBank.run := by
  exact relabelCompiled_run _ _ _ read history (forwardWrapperProgram_run n start read history)

theorem forwardDataBankProgram_tCount (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (forwardDataBankProgram n start) read history =
      secp256k1EEAForwardInDataBank.tCount := by
  exact relabelCompiled_tCount _ _ _ read history (forwardWrapperProgram_tCount n start read history)

/-- Transport the fixed wrapper to the source's exchanged data bank. -/
def reverseDataBankProgram (n start : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  relabelCompiled eeaWorkspaceExchange (reverseWrapperProgram n start)

theorem reverseDataBankProgram_run (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (reverseDataBankProgram n start) read history =
      secp256k1EEAReverseInDataBank.run := by
  exact relabelCompiled_run _ _ _ read history (reverseWrapperProgram_run n start read history)

theorem reverseDataBankProgram_tCount (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (reverseDataBankProgram n start) read history =
      secp256k1EEAReverseInDataBank.tCount := by
  exact relabelCompiled_tCount _ _ _ read history (reverseWrapperProgram_tCount n start read history)

end
end ShorECDLP.Paper2607_13816.ChallengeMigration
