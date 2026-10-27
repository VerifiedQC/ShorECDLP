import ShorECDLP.Submission.«2607_13816».Challenge.InPlaceCompletePhysical
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

theorem fieldLoadOps_physical (field : PointField) : ∀ op ∈ fieldLoadOps field, op.Physical := by
  apply unaryLookupOps_physical
  · exact tableAddressTree_layout _ _ _ _ _ (by decide) (by decide)
  · intro label control hc g hg
    simp only [fieldLeaf,lookupLeafGates,List.mem_map] at hg
    obtain ⟨⟨ref,target⟩,hm,rfl⟩ := hg
    have ht := (List.of_mem_zip hm).2
    simp only [List.mem_range'] at ht
    simp only [List.mem_cons,pointLookupPath,List.mem_range'] at hc
    change control ≠ target
    rcases hc with rfl | hc
    all_goals intro he; subst target; omega

theorem fieldLoadProgram_wellFormed (field : PointField) (start : Nat) :
    (fieldLoadProgram field start).WellFormed := by
  unfold fieldLoadProgram
  rw [castFinish_wellFormed]
  exact lookupProgram_wellFormed _ (fieldLoadOps_physical field) _

attribute [local irreducible] fieldLoadProgram modularAddProgram appendCompiled

theorem fieldLookupAddProgram_wellFormed (field : PointField) (acc : List Wire) (start : Nat)
    (hl : acc.length = 256) (hn : ([836,559,560,561,558] ++ List.range' 7 256 ++ acc).Nodup) :
    (fieldLookupAddProgram field acc start).2.WellFormed := by
  let add := modularAddProgram 32768 (start+32767) (List.range' 7 256) acc
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558
  have ha : add.2.WellFormed := modularAddProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _
    (by simpa using hl.symm) (by omega) (by simp [hl,secp256k1ReductionConstantBits]) hn
  exact appendCompiled_wellFormed ⟨32767,fieldLoadProgram field start⟩
    (appendCompiled add ⟨32767,fieldLoadProgram field (start+32767+add.1)⟩)
    (fieldLoadProgram_wellFormed _ _)
    (appendCompiled_wellFormed add ⟨32767,fieldLoadProgram field (start+32767+add.1)⟩ ha (fieldLoadProgram_wellFormed _ _))
private theorem fieldAccumulator_layout (base : Nat) (hb : base=263 ∨ base=580) :
    ([836,559,560,561,558] ++ List.range' 7 256 ++ List.range' base 256).Nodup := by
  rcases hb with rfl | rfl
  all_goals
    simp only [List.nodup_append]
    refine ⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩
    all_goals
      intro a ha b hb he
      subst a
      simp at ha hb
      rcases ha with h | h | h | h | h
      all_goals omega

theorem fieldLookupXProgram_wellFormed (field : PointField) (start : Nat) :
    (fieldLookupAddProgram field (List.range' 263 256) start).2.WellFormed :=
  fieldLookupAddProgram_wellFormed _ _ _ (by simp) (fieldAccumulator_layout _ (Or.inl rfl))

theorem fieldLookupYProgram_wellFormed (field : PointField) (start : Nat) :
    (fieldLookupAddProgram field (List.range' 580 256) start).2.WellFormed :=
  fieldLookupAddProgram_wellFormed _ _ _ (by simp) (fieldAccumulator_layout _ (Or.inr rfl))

attribute [local irreducible] fieldLookupAddProgram yNegateProgram

theorem signedFieldProgram_wellFormed (field : PointField) (start : Nat) :
    (signedFieldProgram field start).2.WellFormed := by
  unfold signedFieldProgram
  exact appendCompiled_wellFormed _ _ (yNegateProgram_wellFormed _)
    (appendCompiled_wellFormed _ _ (fieldLookupYProgram_wellFormed _ _) (yNegateProgram_wellFormed _))

attribute [local irreducible] zeroDivisionProgram zeroMultiplicationProgram pointSquareProgram signedFieldProgram xNegateProgram

theorem coordinateProgram_wellFormed (start : Nat) : (coordinateProgram start).2.WellFormed := by
  unfold coordinateProgram
  apply sequenceProgram_wellFormed
  intro p hp cursor
  simp only [coordinateSegments,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fieldLookupXProgram_wellFormed _ _
  · exact signedFieldProgram_wellFormed _ _
  · exact zeroDivisionProgram_wellFormed _ _
  · exact pointSquareProgram_wellFormed _ _
  · exact fieldLookupXProgram_wellFormed _ _
  · exact zeroMultiplicationProgram_wellFormed _ _
  · exact xNegateProgram_wellFormed _ _
  · exact fieldLookupXProgram_wellFormed _ _
  · exact signedFieldProgram_wellFormed _ _
end ShorECDLP.Paper2607_13816.ChallengeMigration
