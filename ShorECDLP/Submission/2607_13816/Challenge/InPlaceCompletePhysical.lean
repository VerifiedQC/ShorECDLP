import ShorECDLP.Submission.«2607_13816».Challenge.MeasuredEEAPhysical
import ShorECDLP.Submission.«2607_13816».Challenge.SquarePhysical
import ShorECDLP.Submission.«2607_13816».Challenge.InPlacePhysical
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

theorem correctionCompiled_wellFormed (n start : Nat) (ws : List Wire) (prior : List (Fin start)) :
    (correctionCompiled n start ws prior).2.WellFormed :=
  registerCorrectionProgram_wellFormed _ _ _ trivial

theorem appendLiteral_wellFormed {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (gs : Circuit) (hp : p.2.WellFormed) (hg : CircuitWellFormed gs) :
    (appendLiteral p gs).2.WellFormed :=
  appendCompiled_wellFormed _ _ hp (literalProgram_wellFormed _ hg)

theorem collectProgram_wellFormed (n : Nat)
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (hn : ∀ cursor prior, (next cursor prior).2.WellFormed)
    (ws : List Wire) (start : Nat) (prior : List (Fin start)) :
    (collectProgram n next ws start prior).2.WellFormed := by
  induction ws generalizing start with
  | nil => exact hn _ _
  | cons w ws ih => simpa only [collectProgram,castFinish_wellFormed,Straight.WellFormed] using ih (start+1) _

theorem appendRetaining_wellFormed {n start : Nat}
    (p : (count : Nat) × Straight n start (start+count))
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (prior : List (Fin start)) (hp : p.2.WellFormed)
    (hn : ∀ cursor prior, (next cursor prior).2.WellFormed) :
    (appendRetaining p next prior).2.WellFormed :=
  appendCompiled_wellFormed _ _ hp (hn _ _)

private theorem swapOutput_wellFormed : CircuitWellFormed fig15SwapOutput := by
  intro g hg
  simp only [fig15SwapOutput,List.mem_flatMap,List.mem_range,List.mem_cons,List.not_mem_nil,or_false] at hg
  obtain ⟨i,hi,hg⟩ := hg
  rcases hg with rfl | rfl | rfl <;> simp [Gate.WellFormed]

attribute [local irreducible] multiplyWorkProgram multiplyDataProgram unmultiplyDataProgram
  measuredForwardWrapperProgram measuredReverseWrapperProgram measuredForwardDataBankProgram measuredReverseDataBankProgram

theorem divisionCleanupProgram_wellFormed (n start : Nat) : (divisionCleanupProgram n start).2.WellFormed :=
  appendLiteral_wellFormed _ _ (unmultiplyDataProgram_wellFormed _ _) swapOutput_wellFormed

theorem multiplicationCleanupProgram_wellFormed (n start : Nat) : (multiplicationCleanupProgram n start).2.WellFormed := by
  unfold multiplicationCleanupProgram
  exact appendCompiled_wellFormed _ _ (unmultiplyDataProgram_wellFormed _ _)
    (appendLiteral_wellFormed _ _ (measuredReverseDataBankProgram_wellFormed _ _) swapOutput_wellFormed)

attribute [local irreducible] divisionCleanupProgram multiplicationCleanupProgram
theorem divisionCorrectionProgram_wellFormed (n start : Nat) (prior : List (Fin start)) :
    (divisionCorrectionProgram n start prior).2.WellFormed :=
  appendCompiled_wellFormed _ _ (correctionCompiled_wellFormed _ _ _ _) (divisionCleanupProgram_wellFormed _ _)

theorem divisionAfterResetProgram_wellFormed (n start : Nat) (prior : List (Fin start)) :
    (divisionAfterResetProgram n start prior).2.WellFormed := by
  unfold divisionAfterResetProgram
  apply appendRetaining_wellFormed
  · exact appendCompiled_wellFormed _ _ (measuredReverseDataBankProgram_wellFormed _ _) (multiplyDataProgram_wellFormed _ _)
  · exact divisionCorrectionProgram_wellFormed n

theorem multiplicationCorrectionProgram_wellFormed (n start : Nat) (prior : List (Fin start)) :
    (multiplicationCorrectionProgram n start prior).2.WellFormed :=
  appendCompiled_wellFormed _ _ (correctionCompiled_wellFormed _ _ _ _) (multiplicationCleanupProgram_wellFormed _ _)

theorem multiplicationAfterResetProgram_wellFormed (n start : Nat) (prior : List (Fin start)) :
    (multiplicationAfterResetProgram n start prior).2.WellFormed := by
  unfold multiplicationAfterResetProgram
  apply appendRetaining_wellFormed
  · exact appendCompiled_wellFormed _ _ (measuredForwardDataBankProgram_wellFormed _ _) (multiplyDataProgram_wellFormed _ _)
  · exact multiplicationCorrectionProgram_wellFormed n

attribute [local irreducible] divisionAfterResetProgram multiplicationAfterResetProgram collectProgram
theorem divisionProgram_wellFormed (n start : Nat) : (divisionProgram n start).2.WellFormed := by
  unfold divisionProgram
  apply appendCompiled_wellFormed
  · exact appendCompiled_wellFormed _ _ (measuredForwardWrapperProgram_wellFormed _ _) (multiplyWorkProgram_wellFormed _ _)
  · exact collectProgram_wellFormed _ _ (divisionAfterResetProgram_wellFormed n) _ _ _

theorem multiplicationProgram_wellFormed (n start : Nat) : (multiplicationProgram n start).2.WellFormed := by
  unfold multiplicationProgram
  exact appendCompiled_wellFormed _ _ (multiplyWorkProgram_wellFormed _ _)
    (collectProgram_wellFormed _ _ (multiplicationAfterResetProgram_wellFormed n) _ _ _)
attribute [local irreducible] divisionProgram multiplicationProgram
theorem zeroDivisionProgram_wellFormed (n start : Nat) : (zeroDivisionProgram n start).2.WellFormed :=
  surroundCompiled_wellFormed _ _ _ fig15ZeroPrepare_wellFormed fig15ZeroRestore_wellFormed (divisionProgram_wellFormed _ _)

theorem zeroMultiplicationProgram_wellFormed (n start : Nat) : (zeroMultiplicationProgram n start).2.WellFormed :=
  surroundCompiled_wellFormed _ _ _ fig15ZeroPrepare_wellFormed fig15ZeroRestore_wellFormed (multiplicationProgram_wellFormed _ _)

attribute [local irreducible] squareSubtractProgram

theorem pointSquareProgram_wellFormed (n start : Nat) : (pointSquareProgram n start).2.WellFormed := by
  unfold pointSquareProgram
  apply squareSubtractProgram_wellFormed
  · simp
  · simp
  · simp [secp256k1ReductionConstantBits]
  · simp
  all_goals
    have hw : 7 :: List.range' 8 255 = List.range' 7 256 := rfl
    rw [hw]
    simp only [List.nodup_append]
    refine ⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩
    all_goals
      intro a ha b hb he
      subst a
      simp at ha hb
      rcases ha with h | h | h | h | h
      all_goals first | omega | (rcases h with rfl | ⟨hl,hu⟩ <;> omega)
end ShorECDLP.Paper2607_13816.ChallengeMigration
