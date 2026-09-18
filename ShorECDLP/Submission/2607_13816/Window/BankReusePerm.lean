import ShorECDLP.Framework.Quantum.CleanRelabel
import ShorECDLP.Submission.«2607_13816».Window.StreamAllocation
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
def streamBankPerm (k : Nat) : Wire ≃ Wire :=
  if k=0 then Equiv.refl _ else
    (windowAddressPerm 855 (by omega)).trans
      ((windowAddressPerm (windowBankStart k) (by unfold windowBankStart; omega)).trans
        (windowAddressPerm 855 (by omega)))
theorem streamBankPerm_moved (k : Nat) (w : Wire) (hw : (streamBankPerm k).symm w≠w) :
    w∈List.range' 855 16++List.range' (windowBankStart k) 16 ∧
    (streamBankPerm k).symm w∈List.range' 855 16++List.range' (windowBankStart k) 16 := by
  by_cases hk : k=0
  · subst k; simp [streamBankPerm] at hw
  · simp only [streamBankPerm,if_neg hk] at hw ⊢
    change windowAddressSwap 855 (windowAddressSwap (windowBankStart k) (windowAddressSwap 855 w))≠w at hw
    change w∈List.range' 855 16++List.range' (windowBankStart k) 16 ∧
      windowAddressSwap 855 (windowAddressSwap (windowBankStart k) (windowAddressSwap 855 w))∈
        List.range' 855 16++List.range' (windowBankStart k) 16
    simp only [List.mem_append,List.mem_range'_1]
    unfold windowAddressSwap windowBankStart at *
    split_ifs at * <;> omega
theorem streamBankPerm_symm (k : Nat) : (streamBankPerm k).symm=streamBankPerm k := by
  unfold streamBankPerm
  split <;> rfl
theorem streamBankPerm_address (k i : Nat) (hi : i<16) :
    streamBankPerm k (855+i)=windowBankStart k+i := by
  by_cases hk : k=0
  · subst k; simp [streamBankPerm,windowBankStart]
  · simp only [streamBankPerm,if_neg hk]
    change windowAddressSwap 855 (windowAddressSwap (windowBankStart k) (windowAddressSwap 855 (855+i)))=windowBankStart k+i
    unfold windowAddressSwap windowBankStart
    split_ifs <;> omega
theorem streamBankPerm_core (k : Nat) (w : Wire) (hw : w<839) : streamBankPerm k w=w := by
  by_cases hk : k=0
  · subst k; simp [streamBankPerm]
  · simp only [streamBankPerm,if_neg hk]
    change windowAddressSwap 855 (windowAddressSwap (windowBankStart k) (windowAddressSwap 855 w))=w
    unfold windowAddressSwap windowBankStart
    dsimp only [Wire] at *
    split_ifs <;> omega
theorem streamBankPerm_clean (k : Nat) (ψ : State)
    (hψ : SupportedOn (Clean (List.range' 855 16++List.range' (windowBankStart k) 16)) ψ) :
    relabelState (streamBankPerm k) ψ=ψ :=
  relabelState_clean _ _ (streamBankPerm_moved k) ψ hψ
theorem streamBankBranch_clean (k : Nat) (b : InstrumentBranch) (ψ : State)
    (hin : SupportedOn (Clean (List.range' 855 16++List.range' (windowBankStart k) 16)) ψ)
    (hout : SupportedOn (Clean (List.range' 855 16++List.range' (windowBankStart k) 16)) (b.kraus ψ)) :
    (b.relabel (streamBankPerm k)).kraus ψ=b.kraus ψ := by
  apply branch_relabel_clean _ _ (streamBankPerm_moved k) _ b ψ hin hout
  simpa only [streamBankPerm_symm] using streamBankPerm_moved k
end
end ShorECDLP.Paper2607_13816
