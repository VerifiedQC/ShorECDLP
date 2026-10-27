import ShorECDLP.Submission.«2607_13816».Challenge.CoordinatePhysical

/-! Physical validity of the actual first and signed windows and their outer composition. -/
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
attribute [local irreducible] coordinateProgram

theorem sharedCoordinateProgram_wellFormed (w : OddWindow) (start : Nat) :
    (sharedCoordinateProgram w start).2.WellFormed :=
  (reindexCompiled_wellFormed _ _).mpr (coordinateProgram_wellFormed start)

attribute [local irreducible] sharedCoordinateProgram sharedYNegateProgram placedBatchProgram

theorem batchedWindowCore_wellFormed (w : OddWindow) (start : Nat) :
    (batchedWindowCore w start).2.WellFormed := by
  apply sequenceProgram_wellFormed
  intro p hp cursor
  simp only [batchedWindowSegments,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact sharedCoordinateProgram_wellFormed _ _
  · exact sharedYNegateProgram_wellFormed _ _
  · exact placedBatchProgram_wellFormed _ _
  · exact sharedYNegateProgram_wellFormed _ _

attribute [local irreducible] batchedWindowCore

theorem batchedWindowPrepared_wellFormed (w : OddWindow) (start : Nat) :
    (batchedWindowPrepared w start).2.WellFormed := by
  exact surroundCompiled_wellFormed _ _ _
    (signedAddressCircuit_wellFormed _ _ _ (by decide) (by decide))
    (signedAddressCircuit_wellFormed _ _ _ (by decide) (by decide))
    (batchedWindowCore_wellFormed w start)

attribute [local irreducible] batchedWindowPrepared

theorem actualBatchedWindow_wellFormed (w : OddWindow) (start : Nat) :
    ((actualBatchedWindow w).program start).WellFormed := by
  apply shiftStraight_wellFormed
  exact (relabelStraight_wellFormed _ _).mpr (batchedWindowPrepared_wellFormed w 0)

theorem firstLookupOps_physical : ∀ op ∈ firstLookupOps, op.Physical := by
  apply unaryLookupOps_physical
  · exact tableAddressTree_layout _ _ _ _ _ (by decide) (by decide)
  · intro label control hc g hg
    simp only [pointLeaf,lookupLeafGates,List.mem_map] at hg
    obtain ⟨⟨ref,target⟩,hm,rfl⟩ := hg
    have ht := (List.of_mem_zip hm).2
    change control ≠ target
    have hn : ∀ c ∈ 836 :: List.range' 519 16, c ∉ pointLogicalWires := by
      intro c hc ht
      simp only [List.mem_cons,List.mem_range'] at hc
      simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
        List.mem_range',List.mem_singleton] at ht
      rcases hc with rfl | hc
      all_goals omega
    exact fun he => hn control hc (he ▸ ht)

theorem firstLookupProgram_wellFormed (start : Nat) : (firstLookupProgram start).WellFormed := by
  unfold firstLookupProgram
  rw [castFinish_wellFormed]
  exact lookupProgram_wellFormed _ firstLookupOps_physical _

attribute [local irreducible] firstLookupProgram

theorem actualFirstWindow_wellFormed (start : Nat) :
    (actualFirstWindow.program start).WellFormed :=
  (reindexStraight_wellFormed _ _).mpr (firstLookupProgram_wellFormed start)

attribute [local irreducible] actualBatchedWindow actualFirstWindow

theorem batchedOuterPlan_windowsWellFormed : batchedOuterPlan.WindowsWellFormed := by
  intro w hw start
  change w ∈ actualLeftWindows ++ actualRightWindows at hw
  simp only [actualLeftWindows,actualRightWindows,List.mem_append,List.mem_cons,List.mem_ofFn] at hw
  rcases hw with (rfl | ⟨k,rfl⟩) | ⟨k,rfl⟩
  · exact actualFirstWindow_wellFormed _
  · exact actualBatchedWindow_wellFormed _ _
  · exact actualBatchedWindow_wellFormed _ _

attribute [local irreducible] batchedOuterPlan

theorem batchedOuterPlan_round_wellFormed (start : Nat) :
    (batchedOuterPlan.round start).WellFormed :=
  batchedOuterPlan.round_wellFormed batchedOuterPlan_windowsWellFormed start

theorem batchedOuterPlan_repeat_wellFormed (count start : Nat) :
    (batchedOuterPlan.repeat count start).WellFormed :=
  batchedOuterPlan.repeat_wellFormed batchedOuterPlan_windowsWellFormed count start

end ShorECDLP.Paper2607_13816.ChallengeMigration
