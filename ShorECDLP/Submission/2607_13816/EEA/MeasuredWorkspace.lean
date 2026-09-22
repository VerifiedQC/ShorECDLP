import ShorECDLP.Submission.«2607_13816».EEA.MeasuredPhysicalSupport
import ShorECDLP.Submission.«2607_13816».EEA.WrapperLocality
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- The measured forward wrapper borrowing the cleared data bank. -/
def secp256k1MeasuredEEAForwardInDataBank : AdaptiveCircuit :=
  secp256k1MeasuredEEAForwardWrapper.relabel eeaWorkspaceExchange
/-- The measured reverse wrapper borrowing the cleared data bank. -/
def secp256k1MeasuredEEAReverseInDataBank : AdaptiveCircuit :=
  secp256k1MeasuredEEAReverseWrapper.relabel eeaWorkspaceExchange

theorem secp256k1MeasuredEEAForwardInDataBank_coherent :
    CoherentlyImplementsOn secp256k1MeasuredEEAForwardInDataBank
      ((relabelState eeaWorkspaceExchange).comp
        ((Finsupp.lmapDomain ℂ ℂ secp256k1EEAOutputIdealState).comp
          (relabelState eeaWorkspaceExchange.symm)))
      (fun s => Secp256k1EEAInputValid (relabelBasis eeaWorkspaceExchange.symm s)) :=
  secp256k1MeasuredEEAForwardWrapper_coherent.relabel eeaWorkspaceExchange

theorem secp256k1MeasuredEEAInDataBank_wellFormed :
    secp256k1MeasuredEEAForwardInDataBank.WellFormed ∧ secp256k1MeasuredEEAReverseInDataBank.WellFormed := by
  simp only [secp256k1MeasuredEEAForwardInDataBank,secp256k1MeasuredEEAReverseInDataBank,
    AdaptiveCircuit.relabel_wellFormed]
  exact ⟨secp256k1MeasuredEEAForwardWrapper_wellFormed,secp256k1MeasuredEEAReverseWrapper_wellFormed⟩

/-- Retained external values need not equal those of the original forward input. -/
theorem secp256k1MeasuredEEAReverseWrapper_coherent_localImage :
    CoherentlyImplementsOn secp256k1MeasuredEEAReverseWrapper
      (Finsupp.lmapDomain ℂ ℂ secp256k1EEAReverseWrapperIdealState)
      Secp256k1EEAForwardLocalImage := by
  obtain ⟨cs,ha,hm⟩ := secp256k1MeasuredEEAReverseWrapper_coherent
  refine ⟨cs,ha.imp (fun b c hb s hs => hb s ?_),hm⟩
  obtain ⟨original,ho,hagree⟩ := hs
  refine ⟨fun w => if w < 580 then original w else s w,?_,?_⟩
  · exact (Secp256k1EEAInputValid_congrOn original _ (by intro w hw; simp [hw])).mp ho
  · rw [secp256k1EEAOutputIdealState_patchOutside]
    funext w
    by_cases hw : w < 580
    · simp only [if_pos hw]; exact hagree w hw
    · simp only [if_neg hw]

theorem secp256k1MeasuredEEAReverseInDataBank_coherent_localImage :
    CoherentlyImplementsOn secp256k1MeasuredEEAReverseInDataBank
      ((relabelState eeaWorkspaceExchange).comp
        ((Finsupp.lmapDomain ℂ ℂ secp256k1EEAReverseWrapperIdealState).comp
          (relabelState eeaWorkspaceExchange.symm)))
      (fun s => Secp256k1EEAForwardLocalImage (relabelBasis eeaWorkspaceExchange.symm s)) :=
  secp256k1MeasuredEEAReverseWrapper_coherent_localImage.relabel eeaWorkspaceExchange
end ShorECDLP.Paper2607_13816
