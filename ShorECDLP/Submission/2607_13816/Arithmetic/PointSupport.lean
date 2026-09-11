import ShorECDLP.Submission.«2607_13816».Arithmetic.PointResourceCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstantSupport

namespace ShorECDLP.Paper2607_13816
open Classical Quantum

private theorem bounded_banks (start : Nat) (hs : start+256≤839) :
    [836,559,560,561,558]++List.range' start 256++List.range' 7 256 ⊆ List.range 839 := by
  intro w hw
  simp at hw ⊢
  omega
private theorem bounded_uncontrolled_banks (start : Nat) (hs : start+256≤839) :
    [559,560,561,558]++List.range' start 256++List.range' 7 256 ⊆ List.range 839 := by
  intro w hw
  simp at hw ⊢
  omega
private theorem point_controlled_constant_support (start k : Nat) (hs : start+256≤839) :
    (controlledConstantModularAdd (List.range' start 256) (List.range' 7 256) (constantBits 256 k)
      secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558).wires ⊆ List.range 839 := by
  apply List.Subset.trans (controlledConstantModularAdd256_wires_subset _ _ _ _ _ _ _ _ _ _
    (by simp) (by simp) (by simp) (by decide +kernel) ?_ ShorECDLP.Secp256k1.p_prime.pos (by decide +kernel)) (bounded_banks start hs)
  rw [boolWordToNat_constantBits]
  exact Nat.mod_lt _ (by decide)
private theorem point_constant_support (k : Nat) :
    (fig14ConstantX k).wires ⊆ List.range 839 := by
  apply List.Subset.trans (uncontrolledConstantModularAdd256_wires_subset _ _ _ _ _ _ _ _ _
    (by simp) (by simp) (by simp) (by decide +kernel) ?_ ShorECDLP.Secp256k1.p_prime.pos (by decide +kernel)) (bounded_uncontrolled_banks 263 (by decide))
  rw [boolWordToNat_constantBits]
  exact Nat.mod_lt _ (by decide)
private theorem point_negate_support : fig14Negate.wires ⊆ List.range 839 := by
  exact List.Subset.trans (controlledModularNegate256_wires_subset _ _ _ _ _ _ _ _
    (by simp) (by simp) (by simp)) (bounded_banks 263 (by decide))
private theorem point_square_support : fig14SquareSubtract.wires ⊆ List.range 839 := by
  have hc : secp256k1ReductionConstantBits=true::secp256k1ReductionConstantBits.tail := by decide +kernel
  have hm : constantBits 256 ShorECDLP.p=true::(constantBits 256 ShorECDLP.p).tail := by decide +kernel
  have hh := squareSubtract256_wires_subset (List.range' 263 256) (List.range' 580 256) (List.range' 7 256)
    secp256k1ReductionConstantBits.tail (constantBits 256 ShorECDLP.p).tail ShorECDLP.p
    836 558 559 561 562 560 (by simp) (by simp) (by simp) (by decide +kernel) (by simp)
    ShorECDLP.Secp256k1.p_prime.pos (by decide +kernel)
  rw [←hc,←hm] at hh
  apply List.Subset.trans hh
  intro w hw
  simp at hw ⊢
  dsimp only [Wire] at *
  omega
private theorem seq_support (a b : AdaptiveCircuit) (ha : a.wires ⊆ List.range 839)
    (hb : b.wires ⊆ List.range 839) : (a.seq b).wires ⊆ List.range 839 := by
  intro w hw
  rw [modularWires_seq] at hw
  exact hw.elim (fun h => ha h) (fun h => hb h)
private theorem field_support (a : AdaptiveCircuit) (ha : a.wires ⊆ zeroAllowedLayout) :
    a.wires ⊆ List.range 839 := by
  intro w hw
  have hh := ha hw
  simp [zeroAllowedLayout] at hh ⊢
  dsimp only [Wire] at *
  omega

theorem fig14CoordinateProgram_wires_subset (x y : Nat) :
    (fig14CoordinateProgram x y).wires ⊆ List.range 839 := by
  unfold fig14CoordinateProgram
  apply seq_support
  · apply seq_support
    · apply seq_support
      · apply seq_support
        · apply seq_support
          · apply seq_support
            · apply seq_support
              · apply seq_support
                · exact point_constant_support _
                · exact point_controlled_constant_support 580 _ (by decide)
              · exact field_support _ secp256k1ZeroAllowedDivision_wires_subset
            · exact point_square_support
          · exact point_controlled_constant_support 263 _ (by decide)
        · exact field_support _ secp256k1ZeroAllowedMultiplication_wires_subset
      · exact point_negate_support
    · exact point_constant_support _
  · exact point_controlled_constant_support 580 _ (by decide)

theorem totalPointProgram_wires_subset {x y : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) :
    (totalPointProgram hC).wires ⊆ List.range 839 := by
  apply seq_support _ _ (fig14CoordinateProgram_wires_subset x.val y.val)
  intro w hw
  simp only [AdaptiveCircuit.wires,List.append_nil] at hw
  obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
  exact pointCorrectionCircuit_usesOnly hC g hg w hw

theorem pointAddProgram_wires_subset (C : ShorECDLP.Secp256k1.Point) :
    (pointAddProgram C).wires ⊆ List.range 839 := by
  cases C with
  | zero => simp [pointAddProgram,AdaptiveCircuit.wires]
  | some hC => exact totalPointProgram_wires_subset hC

theorem pointAddProgram_qubitCount (C : ShorECDLP.Secp256k1.Point) :
    (pointAddProgram C).qubitCount≤839 := by
  have hs : (pointAddProgram C).wires.dedup.toFinset ⊆ (List.range 839).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (pointAddProgram_wires_subset C (by simpa using hw))
  have hh := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _),List.toFinset_card_of_nodup List.nodup_range] at hh
  simpa only [AdaptiveCircuit.qubitCount,List.length_range] using hh
/-- Total group semantics and coherent execution with exact T/measurement counts
and one conservative physical layout. Other resource-vector components remain separate. -/
theorem pointAddProgram_certificate (C : ShorECDLP.Secp256k1.Point) :
    (∀ (P : ShorECDLP.Secp256k1.Point) (s : BasisState), Secp256k1ZeroAllowedInputValid s →
      pointStateCoordinates s=fig14PointEncoding P →
      pointAddState C s=if s 836 then pointWrite (P+C) s else s) ∧
    CoherentlyImplementsOn (pointAddProgram C)
      (Finsupp.lmapDomain ℂ ℂ (pointAddState C)) Secp256k1ZeroAllowedInputValid ∧
    (pointAddProgram C).tCount=pointAddT C ∧
    (pointAddProgram C).measurementCount=pointAddMeasurements C ∧
    (pointAddProgram C).qubitCount≤839 :=
  ⟨pointAddState_correct C,pointAddProgram_coherent C,(pointAddProgram_counts C).1,
    (pointAddProgram_counts C).2,pointAddProgram_qubitCount C⟩
end ShorECDLP.Paper2607_13816
