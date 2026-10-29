import ShorECDLP.Submission.«2607_13816».Challenge.WrapperSupport
import ShorECDLP.Submission.«2607_13816».Challenge.Coordinate
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
private theorem swap_support : circuitWires fig15SwapOutput ⊆ List.range 836 := by
  intro w hw
  simp only [circuitWires,fig15SwapOutput,List.mem_flatMap] at hw
  obtain ⟨g,⟨i,hi,hg⟩,hw⟩ := hw
  simp only [List.mem_range] at hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl <;>
    simp only [gateWires,List.mem_cons,List.not_mem_nil,or_false] at hw <;>
    simp only [List.mem_range] <;> dsimp only [Wire] at * <;> omega

private theorem range_in_base (k : Nat) (hk : k ≤ 837) : List.range k ⊆ windowBaseSupport := by
  intro w hw
  have := List.mem_range.mp hw
  simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
  exact Or.inl (Or.inl (by omega))
private theorem data_in_base : List.range' 580 256 ⊆ windowBaseSupport := by
  intro w hw
  apply range_in_base 837 (by omega)
  simp only [List.mem_range'_1] at hw
  exact List.mem_range.mpr (by omega)

theorem correctionCompiled_support (n start : Nat) (ws : List Wire) (prior : List (Fin start)) :
    straightWires (correctionCompiled n start ws prior).2 ⊆ ws := by
  unfold correctionCompiled
  induction ws generalizing prior with
  | nil => simp [registerCorrectionProgram,straightWires]
  | cons w ws ih =>
    cases prior with
    | nil => simp [registerCorrectionProgram,straightWires]
    | cons i rest =>
      simp only [registerCorrectionProgram,recordGates_support]
      intro z hz
      simp only [circuitWires,pauliZ,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        gateWires,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false,or_self] at hz
      rcases hz with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons_of_mem w (ih rest h)

attribute [local irreducible] unmultiplyDataProgram multiplyDataProgram multiplyWorkProgram
  measuredForwardWrapperProgram measuredForwardDataBankProgram measuredReverseDataBankProgram

theorem divisionCleanupProgram_support_static (n start : Nat) :
    straightWires (divisionCleanupProgram n start).2 ⊆ windowBaseSupport := by
  simp only [divisionCleanupProgram,appendLiteral,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨unmultiplyDataProgram_support_static n start,swap_support.trans (range_in_base _ (by omega))⟩

theorem multiplicationCleanupProgram_support_static (n start : Nat) :
    straightWires (multiplicationCleanupProgram n start).2 ⊆ windowBaseSupport := by
  simp only [multiplicationCleanupProgram,appendLiteral,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨unmultiplyDataProgram_support_static n start,measuredReverseDataBankProgram_support_static n _,swap_support.trans (range_in_base _ (by omega))⟩

theorem divisionCorrectionProgram_support_static (n start : Nat) (prior : List (Fin start)) :
    straightWires (divisionCorrectionProgram n start prior).2 ⊆ windowBaseSupport := by
  simp only [divisionCorrectionProgram,appendCompiled_support,List.append_subset]
  exact ⟨(correctionCompiled_support n start _ prior).trans data_in_base,divisionCleanupProgram_support_static n start⟩

theorem divisionAfterResetProgram_support_static (n start : Nat) (prior : List (Fin start)) :
    straightWires (divisionAfterResetProgram n start prior).2 ⊆ windowBaseSupport := by
  simp only [divisionAfterResetProgram,appendRetaining,appendCompiled_support,List.append_subset]
  exact ⟨⟨measuredReverseDataBankProgram_support_static n start,multiplyDataProgram_support_static n _⟩,divisionCorrectionProgram_support_static n _ _⟩

theorem multiplicationCorrectionProgram_support_static (n start : Nat) (prior : List (Fin start)) :
    straightWires (multiplicationCorrectionProgram n start prior).2 ⊆ windowBaseSupport := by
  simp only [multiplicationCorrectionProgram,appendCompiled_support,List.append_subset]
  exact ⟨(correctionCompiled_support n start _ prior).trans data_in_base,multiplicationCleanupProgram_support_static n start⟩

theorem multiplicationAfterResetProgram_support_static (n start : Nat) (prior : List (Fin start)) :
    straightWires (multiplicationAfterResetProgram n start prior).2 ⊆ windowBaseSupport := by
  simp only [multiplicationAfterResetProgram,appendRetaining,appendCompiled_support,List.append_subset]
  exact ⟨⟨measuredForwardDataBankProgram_support_static n start,multiplyDataProgram_support_static n _⟩,multiplicationCorrectionProgram_support_static n _ _⟩

theorem divisionProgram_support_static (n start : Nat) :
    straightWires (divisionProgram n start).2 ⊆ windowBaseSupport := by
  simp only [divisionProgram,appendCompiled_support,List.append_subset]
  refine ⟨⟨(measuredForwardWrapperProgram_support n start).trans (range_in_base _ (by omega)),multiplyWorkProgram_support_static n _⟩,?_⟩
  exact collectProgram_support n (divisionAfterResetProgram n) windowBaseSupport
    (divisionAfterResetProgram_support_static n) _ data_in_base _ _

theorem multiplicationProgram_support_static (n start : Nat) :
    straightWires (multiplicationProgram n start).2 ⊆ windowBaseSupport := by
  simp only [multiplicationProgram,appendCompiled_support,List.append_subset]
  refine ⟨multiplyWorkProgram_support_static n start,?_⟩
  exact collectProgram_support n (multiplicationAfterResetProgram n) windowBaseSupport
    (multiplicationAfterResetProgram_support_static n) _ data_in_base _ _
end ShorECDLP.Paper2607_13816.ChallengeMigration
