import ShorECDLP.Submission.«2607_13816».Challenge.ModularPhysical
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
private theorem figure15_layout :
    ([558,560,561,559] ++ List.range' 263 256 ++ List.range' 580 256 ++ List.range' 7 256).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega

private theorem figure15_data_layout :
    ([558,560,561,559] ++ List.range' 263 256 ++ List.range' 7 256 ++ List.range' 580 256).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega


attribute [local irreducible] hornerProgram hornerInverseProgram

theorem multiplyWorkProgram_wellFormed (n start : Nat) : (multiplyWorkProgram n start).2.WellFormed := by
  have ha : List.range' 7 256 = 7 :: List.range' 8 255 := rfl
  unfold multiplyWorkProgram
  rw [ha]
  apply hornerProgram_wellFormed
  · simp
  · simp [secp256k1ReductionConstantBits]
  · rw [← ha]; exact figure15_layout

theorem multiplyDataProgram_wellFormed (n start : Nat) : (multiplyDataProgram n start).2.WellFormed := by
  have ha : List.range' 580 256 = 580 :: List.range' 581 255 := rfl
  unfold multiplyDataProgram
  rw [ha]
  apply hornerProgram_wellFormed
  · simp
  · simp [secp256k1ReductionConstantBits]
  · rw [← ha]; exact figure15_data_layout

theorem unmultiplyDataProgram_wellFormed (n start : Nat) : (unmultiplyDataProgram n start).2.WellFormed := by
  have ha : List.range' 580 256 = 580 :: List.range' 581 255 := rfl
  unfold unmultiplyDataProgram
  rw [ha]
  apply hornerInverseProgram_wellFormed
  · simp
  · simp only [List.length_cons, List.length_range', constantBits_length]
  · rw [← ha]; exact figure15_data_layout
end ShorECDLP.Paper2607_13816.ChallengeMigration
