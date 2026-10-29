import ShorECDLP.Submission.«2607_13816».Challenge.CoordinateSupport
import ShorECDLP.Submission.«2607_13816».Challenge.WindowSupport
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
/-- Static allocation includes the zero-divisor flag even though the reset list omits it. -/
def completeBatchedSupport : List Wire := 837 :: batchedResetWires

theorem completeBatchedSupport_length : completeBatchedSupport.length = 3932 := by
  simp only [completeBatchedSupport,List.length_cons,batchedResetWires_length]

private theorem old_in_complete : batchedResetWires ⊆ completeBatchedSupport :=
  List.subset_cons_of_subset 837 (List.Subset.refl _)

theorem sharedCoordinateProgram_support_static (w : OddWindow) (start : Nat) :
    (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) ⊆ completeBatchedSupport := by
  simp only [sharedCoordinateProgram,reindexCompiled_support]
  intro z hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  have h := coordinateProgram_support_static start hv
  rcases List.mem_cons.mp h with rfl | h
  · have he : windowAddressPerm 855 (by decide) 837 = 837 := by decide +kernel
    rw [he]
    exact List.mem_cons_self
  · exact old_in_complete (List.mem_append_left _ (List.mem_append_left _ (windowBaseSupport_relocated v h)))

theorem actualBatchedWindow_support_static (w : OddWindow) (start : Nat) :
    straightWires ((actualBatchedWindow w).program start) ⊆ completeBatchedSupport := by
  have hcore cursor : (straightWires (batchedWindowCore w cursor).2).map
      (windowAddressPerm 855 (by decide)) ⊆ completeBatchedSupport := by
    apply sequenceProgram_mapped_support
    simp only [batchedWindowSegments,List.forall_mem_cons,List.mem_nil_iff,false_implies,implies_true,and_true]
    exact ⟨sharedCoordinateProgram_support_static w,
      fun cursor => (sharedYNegateProgram_support_static w cursor).trans old_in_complete,
      fun cursor => (placedBatchProgram_support_static w cursor).trans old_in_complete,
      fun cursor => (sharedYNegateProgram_support_static w cursor).trans old_in_complete⟩
  simp only [actualBatchedWindow,closedWindow,straightWires_shift,straightWires_relabel,
    batchedWindowPrepared,surroundCompiled_support,List.map_append,List.append_subset]
  exact ⟨⟨signedAddressCircuit_support_static.trans old_in_complete,hcore 0⟩,
    signedAddressCircuit_support_static.trans old_in_complete⟩

theorem actualWindows_support_static
    (window : OuterWindow 983040) (hw : window ∈ actualLeftWindows ++ actualRightWindows)
    (start : Nat) : straightWires (window.program start) ⊆ completeBatchedSupport := by
  simp only [actualLeftWindows,actualRightWindows,List.mem_append,List.mem_cons,List.mem_ofFn] at hw
  rcases hw with (rfl | ⟨k,rfl⟩) | ⟨k,rfl⟩
  · exact (actualFirstWindow_support_static start).trans
      (fun _ h => old_in_complete (List.mem_append_left _ (List.mem_append_left _ h)))
  · exact actualBatchedWindow_support_static _ start
  · exact actualBatchedWindow_support_static _ start

theorem batchedOuter_support_static
    (count start : Nat) (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    ((batchedOuterPlan.repeat count start).instantiate read history).wires ⊆ completeBatchedSupport := by
  apply OuterPlan.repeat_support
  · intro w hw
    simp only [batchedOuterPlan,standardOuterPlan,Vector.toList_mk,List.mem_reverse] at hw
    exact old_in_complete (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw)))
  · exact old_in_complete
  · simp [completeBatchedSupport,batchedResetWires,resetWires]
  · intro window hw cursor h
    apply (straight_instantiate_support _ read h).trans
    apply actualWindows_support_static window _ cursor
    simpa only [batchedOuterPlan,standardOuterPlan,Vector.toList_mk,List.toList_toArray] using hw

theorem wire837_not_in_old_allocation : 837 ∉ batchedResetWires := by
  simp only [batchedResetWires,resetWires,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
  norm_num

theorem sharedCoordinateProgram_touches837 (w : OddWindow) (start : Nat) :
    837 ∈ (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) := by
  simp only [sharedCoordinateProgram,reindexCompiled_support]
  exact List.mem_map.mpr ⟨837,coordinateProgram_touches837 start,by decide +kernel⟩

theorem old_coordinate_support_false (w : OddWindow) (start : Nat) :
    ¬ (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) ⊆ batchedResetWires := by
  intro h
  exact wire837_not_in_old_allocation (h (sharedCoordinateProgram_touches837 w start))

/-- An upper bound on the actual program's deduplicated wire set, not an exact usage count. -/
theorem batchedOuter_qubits_le_3932
    (count start : Nat) (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    ((batchedOuterPlan.repeat count start).instantiate read history).wires.toFinset.card ≤ 3932 := by
  have hs := batchedOuter_support_static count start read history
  have hfin : ((batchedOuterPlan.repeat count start).instantiate read history).wires.toFinset ⊆
      completeBatchedSupport.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (hs (List.mem_toFinset.mp hw))
  exact (Finset.card_le_card hfin).trans ((List.toFinset_card_le _).trans_eq completeBatchedSupport_length)
end ShorECDLP.Paper2607_13816.ChallengeMigration
