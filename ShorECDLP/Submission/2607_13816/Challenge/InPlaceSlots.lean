import ShorECDLP.Submission.«2607_13816».Challenge.ProductionEEASlots
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
attribute [local irreducible] measuredForwardWrapperProgram measuredReverseWrapperProgram
  hornerProgram hornerInverseProgram multiplyWorkProgram multiplyDataProgram unmultiplyDataProgram fig15SwapOutput
theorem collectProgram_slots_le (n : Nat)
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (bound : Nat) (h : ∀ cursor prior, (next cursor prior).2.gateSlots≤bound)
    (ws : List Wire) (start : Nat) (prior : List (Fin start)) :
    (collectProgram n next ws start prior).2.gateSlots≤bound := by
  induction ws generalizing start with
  | nil => exact h start prior
  | cons w ws ih =>
    simp only [collectProgram,castFinish_gateSlots,Straight.gateSlots]
    exact ih _ _

theorem relabelCompiled_slots {n start : Nat} (e : Wire ≃ Wire)
    (p : (count : Nat) × Straight n start (start+count)) :
    (relabelCompiled e p).2.gateSlots=p.2.gateSlots := by
  exact relabelStraight_slots e p.2

attribute [local irreducible] relabelCompiled measuredForwardDataBankProgram measuredReverseDataBankProgram
  divisionCleanupProgram divisionCorrectionProgram divisionAfterResetProgram divisionProgram
  multiplicationCleanupProgram multiplicationCorrectionProgram multiplicationAfterResetProgram multiplicationProgram

theorem measuredForwardDataBankProgram_slots (n start : Nat) :
    (measuredForwardDataBankProgram n start).2.gateSlots≤325000000 := by
  simp only [measuredForwardDataBankProgram,relabelCompiled_slots]
  exact measuredForwardWrapperProgram_slots n start

theorem measuredReverseDataBankProgram_slots (n start : Nat) :
    (measuredReverseDataBankProgram n start).2.gateSlots≤325000000 := by
  simp only [measuredReverseDataBankProgram,relabelCompiled_slots]
  exact measuredReverseWrapperProgram_slots n start

theorem correctionCompiled_slots_le (n start : Nat) (ws : List Wire) (prior : List (Fin start)) :
    (correctionCompiled n start ws prior).2.gateSlots≤3*ws.length := by
  simp only [correctionCompiled,registerCorrectionProgram_slots,Straight.gateSlots]
  omega

theorem appendLiteral_slots {n start : Nat} (p : (count : Nat) × Straight n start (start+count)) (gs : Circuit) :
    (appendLiteral p gs).2.gateSlots=p.2.gateSlots+gs.length := by
  simp only [appendLiteral,appendCompiled_slots,literalProgram_slots]

theorem fig15SwapOutput_length : fig15SwapOutput.length=768 := by
  rw [circuit_length_primitive,fig15SwapOutput_primitive]; rfl

theorem multiplyWorkProgram_slots (n start : Nat) : (multiplyWorkProgram n start).2.gateSlots≤8000000 := by
  have h := hornerProgram_slots256 n start (List.range' 263 256) (List.range' 580 256) (List.range' 7 256) secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559 (by simp) (by simp) (by simp [secp256k1ReductionConstantBits])
  simp only [List.length_range'] at h
  unfold multiplyWorkProgram
  omega

theorem multiplyDataProgram_slots (n start : Nat) : (multiplyDataProgram n start).2.gateSlots≤8000000 := by
  have h := hornerProgram_slots256 n start (List.range' 263 256) (List.range' 7 256) (List.range' 580 256) secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559 (by simp) (by simp) (by simp [secp256k1ReductionConstantBits])
  simp only [List.length_range'] at h
  unfold multiplyDataProgram
  omega

theorem unmultiplyDataProgram_slots (n start : Nat) : (unmultiplyDataProgram n start).2.gateSlots≤8000000 := by
  have h := hornerInverseProgram_slots256 n start (List.range' 263 256) (List.range' 7 256) (List.range' 580 256) (constantBits 256 ShorECDLP.p) ShorECDLP.p 558 560 561 559 (by simp) (by simp) (by simp)
  simp only [List.length_range'] at h
  unfold unmultiplyDataProgram
  omega

theorem divisionCorrectionProgram_slots (n start : Nat) (prior : List (Fin start)) :
    (divisionCorrectionProgram n start prior).2.gateSlots≤8001536 := by
  have hc := correctionCompiled_slots_le n start (List.range' 580 256) prior
  have hm := unmultiplyDataProgram_slots n start
  simp only [List.length_range'] at hc
  simp only [divisionCorrectionProgram,divisionCleanupProgram,appendCompiled_slots,appendLiteral_slots,fig15SwapOutput_length]
  omega

theorem divisionAfterResetProgram_slots (n start : Nat) (prior : List (Fin start)) :
    (divisionAfterResetProgram n start prior).2.gateSlots≤341001536 := by
  have he := measuredReverseDataBankProgram_slots n start
  have hm (s : Nat) := multiplyDataProgram_slots n s
  have hc (s : Nat) (p : List (Fin s)) := divisionCorrectionProgram_slots n s p
  simp only [divisionAfterResetProgram,appendRetaining,appendCompiled_slots]
  grind only

theorem divisionProgram_slots (n start : Nat) : (divisionProgram n start).2.gateSlots≤675000000 := by
  have he := measuredForwardWrapperProgram_slots n start
  have hm (s : Nat) := multiplyWorkProgram_slots n s
  have hc (s : Nat) (p : List (Fin s)) := collectProgram_slots_le n (divisionAfterResetProgram n)
    341001536 (divisionAfterResetProgram_slots n) (List.range' 580 256) s p
  simp only [divisionProgram,appendCompiled_slots]
  grind only

theorem multiplicationCorrectionProgram_slots (n start : Nat) (prior : List (Fin start)) :
    (multiplicationCorrectionProgram n start prior).2.gateSlots≤333001536 := by
  have hc := correctionCompiled_slots_le n start (List.range' 580 256) prior
  have hm := unmultiplyDataProgram_slots n start
  have he (s : Nat) := measuredReverseDataBankProgram_slots n s
  simp only [List.length_range'] at hc
  simp only [multiplicationCorrectionProgram,multiplicationCleanupProgram,appendCompiled_slots,appendLiteral_slots,fig15SwapOutput_length]
  grind only

theorem multiplicationAfterResetProgram_slots (n start : Nat) (prior : List (Fin start)) :
    (multiplicationAfterResetProgram n start prior).2.gateSlots≤666001536 := by
  have he := measuredForwardDataBankProgram_slots n start
  have hm (s : Nat) := multiplyDataProgram_slots n s
  have hc (s : Nat) (p : List (Fin s)) := multiplicationCorrectionProgram_slots n s p
  simp only [multiplicationAfterResetProgram,appendRetaining,appendCompiled_slots]
  grind only

theorem multiplicationProgram_slots (n start : Nat) : (multiplicationProgram n start).2.gateSlots≤675000000 := by
  have hm := multiplyWorkProgram_slots n start
  have hc (s : Nat) (p : List (Fin s)) := collectProgram_slots_le n (multiplicationAfterResetProgram n)
    666001536 (multiplicationAfterResetProgram_slots n) (List.range' 580 256) s p
  simp only [multiplicationProgram,appendCompiled_slots]
  grind only


end ShorECDLP.Paper2607_13816.ChallengeMigration
