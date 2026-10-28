import ShorECDLP.Submission.«2607_13816».Challenge.ArithmeticSupport
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

/-- Mapping a shared allocation through a fixed wire permutation commutes with
sequential compilation, without expanding any window body. -/
theorem sequenceProgram_mapped_support (n : Nat) (ps : List (FixedSegment n))
    (e : Wire → Wire) (support : List Wire)
    (h : ∀ p ∈ ps, ∀ start, (straightWires (p start).2).map e ⊆ support) (start : Nat) :
    (straightWires (sequenceProgram n ps start).2).map e ⊆ support := by
  induction ps generalizing start with
  | nil => exact List.nil_subset _
  | cons p ps ih =>
    simp only [sequenceProgram,appendCompiled_support,List.map_append,List.append_subset]
    exact ⟨h p (by simp) start,ih (fun q hq => h q (by simp [hq])) _⟩

theorem signedAddressCircuit_support_static :
    (circuitWires (signedAddressCircuit 836 854 pointLookupAddress)).map
      (windowAddressPerm 855 (by decide)) ⊆ batchedResetWires := by
  have hx (q : Wire) (hq : q ∈ windowBaseSupport) :
      circuitWires (tableXorGates q pointLookupAddress) ⊆ windowBaseSupport := by
    intro z hz
    obtain ⟨g,hg,hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hg
    have hw' : w ∈ windowBaseSupport := by simp [windowBaseSupport,pointLookupAddress] at hw ⊢; omega
    rcases (show z = q ∨ z = w by simpa [gateWires] using hz) with rfl | rfl
    · exact hq
    · exact hw'
  have hp : circuitWires (signedAddressCircuit 836 854 pointLookupAddress) ⊆ windowBaseSupport := by
    simpa only [signedAddressCircuit,circuitWires,List.flatMap_append,List.append_subset] using
      And.intro (hx 836 (by simp [windowBaseSupport])) (hx 854 (by simp [windowBaseSupport]))
  intro z hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  exact List.mem_append_left _ (List.mem_append_left _ (windowBaseSupport_relocated v (hp hv)))

/-- The remaining arithmetic obligation is explicit. The correction and both
negation segments have unconditional concrete support proofs. -/
theorem actualBatchedWindow_support_of_coordinate (w : OddWindow)
    (hc : ∀ start, (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) ⊆ batchedResetWires) (start : Nat) :
    straightWires ((actualBatchedWindow w).program start) ⊆ batchedResetWires := by
  have hcore cursor : (straightWires (batchedWindowCore w cursor).2).map
      (windowAddressPerm 855 (by decide)) ⊆ batchedResetWires := by
    apply sequenceProgram_mapped_support
    simp only [batchedWindowSegments,List.forall_mem_cons,List.mem_nil_iff,false_implies,implies_true,and_true]
    exact ⟨hc,sharedYNegateProgram_support_static w,placedBatchProgram_support_static w,
      sharedYNegateProgram_support_static w⟩
  simp only [actualBatchedWindow,closedWindow,straightWires_shift,straightWires_relabel,
    batchedWindowPrepared,surroundCompiled_support,List.map_append,List.append_subset]
  exact ⟨⟨signedAddressCircuit_support_static,hcore 0⟩,signedAddressCircuit_support_static⟩



theorem actualWindows_support_of_coordinate
    (hc : ∀ w start, (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) ⊆ batchedResetWires)
    (window : OuterWindow 983040) (hw : window ∈ actualLeftWindows ++ actualRightWindows)
    (start : Nat) : straightWires (window.program start) ⊆ batchedResetWires := by
  simp only [actualLeftWindows,actualRightWindows,List.mem_append,List.mem_cons,List.mem_ofFn] at hw
  rcases hw with (rfl | ⟨k,rfl⟩) | ⟨k,rfl⟩
  · exact (actualFirstWindow_support_static start).trans
      (fun _ h => List.mem_append_left _ (List.mem_append_left _ h))
  · exact actualBatchedWindow_support_of_coordinate _ (hc _) start
  · exact actualBatchedWindow_support_of_coordinate _ (hc _) start

theorem batchedOuter_support_of_coordinate
    (hc : ∀ w start, (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) ⊆ batchedResetWires)
    (count start : Nat) (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    ((batchedOuterPlan.repeat count start).instantiate read history).wires ⊆ batchedResetWires := by
  apply OuterPlan.repeat_support
  · intro w hw
    simp only [batchedOuterPlan,standardOuterPlan,Vector.toList_mk,List.mem_reverse] at hw
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw))
  · exact List.Subset.refl _
  · simp [batchedResetWires,resetWires]
  · intro window hw cursor h
    apply (straight_instantiate_support _ read h).trans
    apply actualWindows_support_of_coordinate hc window _ cursor
    simpa only [batchedOuterPlan,standardOuterPlan,Vector.toList_mk,List.toList_toArray] using hw

/-- Conditional assembly only: the concrete coordinate compiler support must
still be supplied. This is not an unconditional Streaming resource certificate. -/
theorem batchedOuter_qubits_le_of_coordinate
    (hc : ∀ w start, (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) ⊆ batchedResetWires)
    (count start : Nat) (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    ((batchedOuterPlan.repeat count start).instantiate read history).wires.toFinset.card ≤ 3931 := by
  have hs := batchedOuter_support_of_coordinate hc count start read history
  have hfin : ((batchedOuterPlan.repeat count start).instantiate read history).wires.toFinset ⊆
      batchedResetWires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (hs (List.mem_toFinset.mp hw))
  exact (Finset.card_le_card hfin).trans ((List.toFinset_card_le _).trans_eq batchedResetWires_length)

end ShorECDLP.Paper2607_13816.ChallengeMigration
