import ShorECDLP.Framework.Quantum.AdaptiveMeasurement
import ShorECDLP.Submission.«2607_13816».Arithmetic.HornerCoherent
import ShorECDLP.Submission.«2607_13816».EEA.WorkspaceReuse

/-!
# Figure 15 adaptive in-place schedules

These concrete programs follow the pinned wrapped quadratic source. The initial
256 X-measure/reset outcomes remain available across intervening adaptive EEA
and multiplication calls, and select the final Z corrections. The final bank
exchange uses actual three-CX swaps, as in the source. The arithmetic phase
reconstruction and aggregate resource certificates are separate obligations.
-/
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section

/-- The product is written to A; X controls and Y is the reusable addend. -/
def fig15MultiplyToWork : AdaptiveCircuit :=
  hornerMul (List.range' 263 256) (List.range' 580 256) (List.range' 7 256)
    secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559

/-- Recompute the old Y from X and A into the cleared data bank. -/
def fig15MultiplyToData : AdaptiveCircuit :=
  hornerMul (List.range' 263 256) (List.range' 7 256) (List.range' 580 256)
    secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559

/-- Explicit source inverse of the recomputation call. -/
def fig15MultiplyToDataInverse : AdaptiveCircuit :=
  hornerMulInverse (List.range' 263 256) (List.range' 7 256) (List.range' 580 256)
    (constantBits 256 ShorECDLP.p) ShorECDLP.p 558 560 561 559

/-- The final source SWAP of the output and now-cleared work bank. -/
def fig15SwapOutput : Circuit :=
  (List.range 256).flatMap (fun i =>
    [.CX (580+i) (7+i), .CX (7+i) (580+i), .CX (580+i) (7+i)])

/-- Source division continuation: restore X, recompute Y for phase correction,
uncompute it, and swap the quotient into Y. -/
def fig15DivisionAfterReset (outcomes : List Bool) : AdaptiveCircuit :=
  (((secp256k1EEAReverseInDataBank.seq fig15MultiplyToData).seq
    (.unitary (registerZCorrection (List.range' 580 256) outcomes) .done)).seq
      fig15MultiplyToDataInverse).seq (.unitary fig15SwapOutput .done)

/-- Source multiplication continuation: invert X, recompute and phase-correct Y,
uncompute Y, restore X, and swap the product into Y. -/
def fig15MultiplicationAfterReset (outcomes : List Bool) : AdaptiveCircuit :=
  ((((secp256k1EEAForwardInDataBank.seq fig15MultiplyToData).seq
    (.unitary (registerZCorrection (List.range' 580 256) outcomes) .done)).seq
      fig15MultiplyToDataInverse).seq secp256k1EEAReverseInDataBank).seq
        (.unitary fig15SwapOutput .done)

/-- Literal complete Figure 15 division schedule at secp256k1 width. -/
def secp256k1InPlaceDivision : AdaptiveCircuit :=
  (secp256k1EEAForwardWrapper.seq fig15MultiplyToWork).seq
    (measureResetThen (List.range' 580 256) fig15DivisionAfterReset)

/-- Literal complete Figure 15 multiplication schedule at secp256k1 width. -/
def secp256k1InPlaceMultiplication : AdaptiveCircuit :=
  fig15MultiplyToWork.seq
    (measureResetThen (List.range' 580 256) fig15MultiplicationAfterReset)

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

attribute [local irreducible] hornerMul hornerMulInverse

private theorem figure15_multipliers_wellFormed :
    fig15MultiplyToWork.WellFormed ∧ fig15MultiplyToData.WellFormed ∧
      fig15MultiplyToDataInverse.WellFormed := by
  have ha : List.range' 7 256 = 7 :: List.range' 8 255 := rfl
  have hy : List.range' 580 256 = 580 :: List.range' 581 255 := rfl
  refine ⟨?_,?_,?_⟩
  · unfold fig15MultiplyToWork
    rw [ha]
    apply hornerMul_wellFormed
    · simp only [List.length_range',List.length_cons]
    · simp [secp256k1ReductionConstantBits]
    · rw [← ha]; exact figure15_layout
  · unfold fig15MultiplyToData
    rw [hy]
    apply hornerMul_wellFormed
    · simp only [List.length_range',List.length_cons]
    · simp [secp256k1ReductionConstantBits]
    · rw [← hy]; exact figure15_data_layout
  · unfold fig15MultiplyToDataInverse
    rw [hy]
    apply hornerMulInverse_wellFormed
    · simp only [List.length_range',List.length_cons]
    · simp only [List.length_cons,List.length_range',constantBits_length]
    · rw [← hy]; exact figure15_data_layout

private theorem figure15_swap_wellFormed : CircuitWellFormed fig15SwapOutput := by
  intro g hg
  simp only [fig15SwapOutput,List.mem_flatMap] at hg
  obtain ⟨i,hi,hg⟩ := hg
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl <;> norm_num [Gate.WellFormed,Nat.add_right_cancel_iff]

attribute [local irreducible] fig15MultiplyToWork fig15MultiplyToData fig15MultiplyToDataInverse
  secp256k1EEAForwardWrapper secp256k1EEAForwardInDataBank secp256k1EEAReverseInDataBank

private theorem figure15_unitary_wellFormed (c : Circuit) (h : CircuitWellFormed c) :
    (AdaptiveCircuit.unitary c .done).WellFormed := ⟨h,trivial⟩

private theorem division_continuation_wellFormed (outcomes : List Bool) :
    (fig15DivisionAfterReset outcomes).WellFormed := by
  exact (((secp256k1EEAInDataBank_wellFormed.2.seq figure15_multipliers_wellFormed.2.1).seq
    (figure15_unitary_wellFormed _ (registerZCorrection_wellFormed (List.range' 580 256) outcomes))).seq figure15_multipliers_wellFormed.2.2).seq
      (figure15_unitary_wellFormed _ figure15_swap_wellFormed)

private theorem multiplication_continuation_wellFormed (outcomes : List Bool) :
    (fig15MultiplicationAfterReset outcomes).WellFormed := by
  exact ((((secp256k1EEAInDataBank_wellFormed.1.seq figure15_multipliers_wellFormed.2.1).seq
    (figure15_unitary_wellFormed _ (registerZCorrection_wellFormed (List.range' 580 256) outcomes))).seq figure15_multipliers_wellFormed.2.2).seq
      secp256k1EEAInDataBank_wellFormed.2).seq (figure15_unitary_wellFormed _ figure15_swap_wellFormed)

/-- All gates and measurements in both complete source schedules are physically well formed. -/
theorem secp256k1InPlace_wellFormed :
    secp256k1InPlaceDivision.WellFormed ∧ secp256k1InPlaceMultiplication.WellFormed := by
  constructor
  · exact (secp256k1EEAForwardWrapper_wellFormed.seq figure15_multipliers_wellFormed.1).seq
      (measureResetThen_wellFormed _ _ (fun outcomes _ => division_continuation_wellFormed outcomes))
  · exact figure15_multipliers_wellFormed.1.seq
      (measureResetThen_wellFormed _ _ (fun outcomes _ => multiplication_continuation_wellFormed outcomes))

end
end ShorECDLP.Paper2607_13816
