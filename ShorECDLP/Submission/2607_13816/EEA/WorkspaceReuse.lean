import ShorECDLP.Framework.Quantum.Relabel
import ShorECDLP.Submission.«2607_13816».EEA.AdaptiveWrapper

/-!
# Reusing a cleared data bank as the EEA workspace

Figure 15 uses the cleared Y register for a subsequent EEA invocation while
retaining its result in A. The bijection below exchanges the existing A bank
(7–262) with a fresh 256-wire bank (580–835), fixing X and every metadata wire.
It relabels the actual adaptive tree and adds no physical swap gates. This is
an interface for the in-place composition, not its completed arithmetic proof
or the paper's aggregate space certificate.
-/
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section

private def exchangeWorkspaceWire (w : Nat) : Nat :=
  if 7 ≤ w ∧ w < 263 then w + 573
  else if 580 ≤ w ∧ w < 836 then w - 573 else w

private theorem exchangeWorkspaceWire_twice : Function.Involutive exchangeWorkspaceWire := by
  intro w
  unfold exchangeWorkspaceWire
  repeat' split
  all_goals omega

/-- Exchange the two data banks; all EEA input and metadata labels stay fixed. -/
def eeaWorkspaceExchange : Wire ≃ Wire :=
  { toFun := exchangeWorkspaceWire, invFun := exchangeWorkspaceWire,
    left_inv := exchangeWorkspaceWire_twice, right_inv := exchangeWorkspaceWire_twice }

@[simp] theorem eeaWorkspaceExchange_work (i : Nat) (hi : i < 256) :
    eeaWorkspaceExchange (7 + i) = 580 + i := by
  change exchangeWorkspaceWire (7 + i) = 580 + i
  simp only [exchangeWorkspaceWire]
  split <;> omega

@[simp] theorem eeaWorkspaceExchange_data (i : Nat) (hi : i < 256) :
    eeaWorkspaceExchange (580 + i) = 7 + i := by
  change exchangeWorkspaceWire (580 + i) = 7 + i
  simp only [exchangeWorkspaceWire]
  repeat' split
  all_goals omega

/-- Everything outside the two exchanged banks is fixed, including arbitrary external wires. -/
theorem eeaWorkspaceExchange_frame (w : Wire)
    (ha : ¬ (7 ≤ w ∧ w < 263)) (hy : ¬ (580 ≤ w ∧ w < 836)) :
    eeaWorkspaceExchange w = w := by
  change exchangeWorkspaceWire w = w
  simp [exchangeWorkspaceWire,ha,hy]

/-- The same source forward tree, now borrowing the cleared Y bank. -/
def secp256k1EEAForwardInDataBank : AdaptiveCircuit :=
  secp256k1EEAForwardWrapper.relabel eeaWorkspaceExchange

/-- The same source inverse tree on the exchanged bank. -/
def secp256k1EEAReverseInDataBank : AdaptiveCircuit :=
  secp256k1EEAReverseWrapper.relabel eeaWorkspaceExchange

attribute [local irreducible] secp256k1EEAForwardWrapper secp256k1EEAReverseWrapper
  secp256k1EEAForwardInDataBank secp256k1EEAReverseInDataBank

/-- The relabeled forward call transports the full output, including its external frame. -/
theorem secp256k1EEAForwardInDataBank_coherent :
    CoherentlyImplementsOn secp256k1EEAForwardInDataBank
      ((relabelState eeaWorkspaceExchange).comp
        ((Finsupp.lmapDomain ℂ ℂ secp256k1EEAOutputIdealState).comp
          (relabelState eeaWorkspaceExchange.symm)))
      (fun s => Secp256k1EEAInputValid (relabelBasis eeaWorkspaceExchange.symm s)) := by
  unfold secp256k1EEAForwardInDataBank
  exact secp256k1EEAForwardWrapper_coherent.relabel eeaWorkspaceExchange

/-- The relabeled inverse applies to the actual forward image in exchanged coordinates. -/
theorem secp256k1EEAReverseInDataBank_coherent :
    CoherentlyImplementsOn secp256k1EEAReverseInDataBank
      ((relabelState eeaWorkspaceExchange).comp
        ((Finsupp.lmapDomain ℂ ℂ secp256k1EEAReverseWrapperIdealState).comp
          (relabelState eeaWorkspaceExchange.symm)))
      (fun s => ∃ original, Secp256k1EEAInputValid original ∧
        relabelBasis eeaWorkspaceExchange.symm s = secp256k1EEAOutputIdealState original) := by
  unfold secp256k1EEAReverseInDataBank
  exact secp256k1EEAReverseWrapper_coherent.relabel eeaWorkspaceExchange

/-- Both relabeled source trees retain physical gate well-formedness. -/
theorem secp256k1EEAInDataBank_wellFormed :
    secp256k1EEAForwardInDataBank.WellFormed ∧ secp256k1EEAReverseInDataBank.WellFormed := by
  simp only [secp256k1EEAForwardInDataBank,secp256k1EEAReverseInDataBank,
    AdaptiveCircuit.relabel_wellFormed]
  exact ⟨secp256k1EEAForwardWrapper_wellFormed,secp256k1EEAReverseWrapper_wellFormed⟩

/-- Relabeling introduces no T gates, measurements, or distinct physical wires. -/
theorem secp256k1EEAInDataBank_resources :
    secp256k1EEAForwardInDataBank.tCount = secp256k1EEAForwardWrapper.tCount ∧
    secp256k1EEAReverseInDataBank.tCount = secp256k1EEAReverseWrapper.tCount ∧
    secp256k1EEAForwardInDataBank.measurementCount = secp256k1EEAForwardWrapper.measurementCount ∧
    secp256k1EEAReverseInDataBank.measurementCount = secp256k1EEAReverseWrapper.measurementCount ∧
    secp256k1EEAForwardInDataBank.qubitCount = secp256k1EEAForwardWrapper.qubitCount ∧
    secp256k1EEAReverseInDataBank.qubitCount = secp256k1EEAReverseWrapper.qubitCount := by
  simp only [secp256k1EEAForwardInDataBank,secp256k1EEAReverseInDataBank,
    AdaptiveCircuit.relabel_tCount,AdaptiveCircuit.relabel_measurementCount,
    AdaptiveCircuit.relabel_qubitCount,and_self]

/-- Full coherent forward/reverse cancellation survives the physical bank reuse. -/
theorem secp256k1EEAInDataBank_roundTrip :
    CoherentlyImplementsOn (secp256k1EEAForwardInDataBank.seq secp256k1EEAReverseInDataBank)
      (Finsupp.lmapDomain ℂ ℂ (fun s : BasisState => s))
      (fun s => Secp256k1EEAInputValid (relabelBasis eeaWorkspaceExchange.symm s)) := by
  unfold secp256k1EEAForwardInDataBank secp256k1EEAReverseInDataBank
  have h := secp256k1EEAForwardReverse_coherent.relabel eeaWorkspaceExchange
  rw [AdaptiveCircuit.relabel_seq] at h
  apply h.congrIdeal
  intro s hs
  simp only [LinearMap.comp_apply,relabelState_ket]
  have hcancel : relabelBasis eeaWorkspaceExchange (relabelBasis eeaWorkspaceExchange.symm s) = s := by
    simpa only [Equiv.symm_symm] using relabelBasis_symm eeaWorkspaceExchange.symm s
  simp [ket,relabelState,hcancel]

end
end ShorECDLP.Paper2607_13816
