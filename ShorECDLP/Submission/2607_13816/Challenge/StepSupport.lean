import ShorECDLP.Submission.«2607_13816».Challenge.IntervalSupport
import ShorECDLP.Submission.«2607_13816».Challenge.CoefficientSupport
import ShorECDLP.Submission.«2607_13816».Challenge.PhaseSupport
import ShorECDLP.Submission.«2607_13816».EEA.PhysicalSupport
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
private theorem support_to_580 (support : List Wire)
    (h : support.all (fun w => decide (w < 580)) = true) :
    ∀ w ∈ support, w ∈ List.range 580 := by
  intro w hw
  exact List.mem_range.mpr (of_decide_eq_true ((List.all_eq_true.mp h) w hw))


private theorem range580_of_closed (ws : List Wire) (h : ws.all (fun w => decide (w < 580)) = true)
    (w : Wire) (hw : w ∈ ws) : w ∈ List.range 580 := support_to_580 ws h w hw


private theorem window_mem {work : List Wire} {window : ActiveWindow} {w : Wire}
    (hw : w ∈ IndexedStepRegisters.windowSlice work window) : w ∈ work :=
  List.mem_of_mem_drop (List.mem_of_mem_take hw)


private theorem production_remainder_support (window : ActiveWindow) :
    ∀ w ∈ (indexedStepProductionRegisters.remainder window).allWires, w ∈ List.range 580 := by
  let r := indexedStepProductionRegisters
  intro w hw
  change w ∈ [r.control,r.sign] ++
    (IndexedStepRegisters.windowSlice r.work1 window ++ (IndexedStepRegisters.windowSlice r.work2 window ++
    (r.lengthT ++ (r.lengthQ ++ (r.lengthS ++
    (r.shiftEpoch :: (r.sourceScratch ++ r.remainderRepairScratch)).take (r.remainderScratchSize window)))))) at hw
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with (hw | hw) | hw | hw | hw | hw | hw | hw
  · subst w; exact List.mem_range.mpr (show (558 : Nat) < 580 by decide)
  · subst w; exact List.mem_range.mpr (show (3 : Nat) < 580 by decide)
  · exact range580_of_closed r.work1 (by decide +kernel) w (window_mem hw)
  · exact range580_of_closed r.work2 (by decide +kernel) w (window_mem hw)
  · exact range580_of_closed r.lengthT (by decide +kernel) w hw
  · exact range580_of_closed r.lengthQ (by decide +kernel) w hw
  · exact range580_of_closed r.lengthS (by decide +kernel) w hw
  · exact range580_of_closed (r.shiftEpoch :: (r.sourceScratch ++ r.remainderRepairScratch))
      (by decide +kernel) w (List.mem_of_mem_take hw)


private theorem gate_support_580 (g : Gate)
    (h : (gateWires g).all (fun w => decide (w < 580)) = true) :
    PaperCircuitUsesOnly (List.range 580) ([g] : Circuit) := by
  intro g' hg
  simp only [List.mem_singleton] at hg
  subst g'
  exact support_to_580 _ h


private theorem production_coefficient_support (window : ActiveWindow) :
    ∀ w ∈ (indexedStepProductionRegisters.coefficient window).allWires, w ∈ List.range 580 := by
  let r := indexedStepProductionRegisters
  intro w hw
  change w ∈ [r.control,r.sign] ++
    (IndexedStepRegisters.windowSlice r.work1 window ++ (IndexedStepRegisters.windowSlice r.work2 window ++
    (r.lengthT ++ r.blockScratch.take (max (quotientSwapUnaryDepth window.start window.stop) r.lengthT.length+3)))) at hw
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with (hw | hw) | hw | hw | hw | hw
  · subst w; exact List.mem_range.mpr (show (558 : Nat) < 580 by decide)
  · subst w; exact List.mem_range.mpr (show (3 : Nat) < 580 by decide)
  · exact range580_of_closed r.work1 (by decide +kernel) w (window_mem hw)
  · exact range580_of_closed r.work2 (by decide +kernel) w (window_mem hw)
  · exact range580_of_closed r.lengthT (by decide +kernel) w hw
  · exact range580_of_closed r.blockScratch (by decide +kernel) w (List.mem_of_mem_take hw)


attribute [local irreducible] intervalProgram rControlNonterminal coefficientProgram

theorem remainderBlockProgram_support_production (n start width : Nat) (w : ActiveWindow)
    (hl : IntervalLayout (indexedStepProductionRegisters.remainder w) w.start w.stop .work1) :
    straightWires (remainderBlockProgram n start indexedStepProductionRegisters width w).2 ⊆ List.range 580 := by
  let r := indexedStepProductionRegisters
  have hs := (rControlNonterminal_usesOnly [r.phase1] 0 r.control r.lengthRPrime
    r.terminal r.blockScratch).mono (support_to_580 _ (by decide +kernel))
  have hp := (rControlNonterminal_usesOnly [r.phase1,r.phase2] 2 r.control r.lengthRPrime
    r.terminal r.blockScratch).mono (support_to_580 _ (by decide +kernel))
  have hr := (rControlNonterminal_usesOnly [r.phase1,r.terminal] 0 r.control r.lengthRPrime
    (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)).mono
    (support_to_580 _ (by decide +kernel))
  have hc := gate_support_580 (.CCX r.phase2 r.sign r.terminal) (by decide +kernel)
  have hx := gate_support_580 (.CX r.control r.sign) (by decide +kernel)
  have hrestore := circuitWires_subset_of_usesOnly ((hc.append hr).append hc)
  have h2 : circuitWires (blockB2 r) ⊆ List.range 580 := by
    exact circuitWires_subset_of_usesOnly ((hp.append hx).append hp)
  have hiSub cursor := (intervalProgram_support_layout n cursor (r.remainder w) width w.start w.stop .sub true .work1 hl).trans
    (fun _ h => production_remainder_support w _ h)
  have hiAdd cursor := (intervalProgram_support_layout n cursor (r.remainder w) width w.start w.stop .add false .work1 hl).trans
    (fun _ h => production_remainder_support w _ h)
  unfold remainderBlockProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [remainderBlockSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact hiSub _ | exact hiAdd _ | simpa only [literalProgram_support] using circuitWires_subset_of_usesOnly hs | simpa only [literalProgram_support] using h2 | simpa only [literalProgram_support] using hrestore

theorem coefficientBlockProgram_support_production (n start width : Nat) (w : ActiveWindow)
    (hl : CoefficientPrefixLayout (indexedStepProductionRegisters.coefficient w) w.start w.stop) :
    straightWires (coefficientBlockProgram n start indexedStepProductionRegisters width w).2 ⊆ List.range 580 := by
  let r := indexedStepProductionRegisters
  have ht := (computeControl_usesOnly [r.phase2,r.sign] 2 r.terminal r.blockScratch).mono
    (support_to_580 _ (by decide +kernel))
  have hs := (computeControl_usesOnly [r.phase1,r.terminal] 1 r.control r.blockScratch).mono
    (support_to_580 _ (by decide +kernel))
  have ha := (computeControl_usesOnly [r.phase1] 1 r.control r.blockScratch).mono
    (support_to_580 _ (by decide +kernel))
  have hp := (prepareLatestPaperTBoundary_usesOnly r.tBoundary width).mono
    (support_to_580 _ (by decide +kernel))
  have hr := (restoreLatestPaperTBoundary_usesOnly r.tBoundary width).mono
    (support_to_580 _ (by decide +kernel))
  have hx := gate_support_580 (.CX r.phase1 r.sign) (by decide +kernel)
  have hfirst := circuitWires_subset_of_usesOnly (((ht.append hs).append ht).append hp)
  have hmiddle := circuitWires_subset_of_usesOnly ((((ht.append hs).append ht).append hx).append ha)
  have hlast := circuitWires_subset_of_usesOnly (ha.append hr)
  have hiSub cursor := (coefficientProgram_support_layout n cursor (r.coefficient w) w.start w.stop .sub false .work2 hl).trans
    (fun _ h => production_coefficient_support w _ h)
  have hiAdd cursor := (coefficientProgram_support_layout n cursor (r.coefficient w) w.start w.stop .add true .work2 hl).trans
    (fun _ h => production_coefficient_support w _ h)
  unfold coefficientBlockProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [coefficientBlockSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl
  all_goals first | exact hiSub _ | exact hiAdd _ | simpa only [literalProgram_support] using hfirst | simpa only [literalProgram_support] using hmiddle | simpa only [literalProgram_support] using hlast

attribute [local irreducible] remainderBlockProgram coefficientBlockProgram phaseProgram
  blockAForward blockBForward blockCForward blockDForward blockEForward blockFForward blockGForward blockHForward

theorem indexedStepProgram_support_production (n start T : Nat)
    (hl : IndexedStepLayout indexedStepProductionRegisters 256 T) :
    straightWires (indexedStepProgram n start indexedStepProductionRegisters 256 T).2 ⊆ List.range 580 := by
  have hs := circuitWires_subset_of_usesOnly (indexedStepUnitary_production_usesOnly T hl)
  simp only [indexedStepUnitary,circuitWires,List.flatMap_append,List.append_subset] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨hA,hB⟩,hC⟩,hD⟩,hE⟩,hF⟩,hG⟩,hH⟩ := hs
  have hCD : circuitWires (blockCForward indexedStepProductionRegisters ++ blockDForward indexedStepProductionRegisters (certifiedActiveWindows 256 T).quotientSwap) ⊆ List.range 580 := by
    simp only [circuitWires,List.flatMap_append,List.append_subset]
    exact ⟨hC,hD⟩
  have hrem cursor := remainderBlockProgram_support_production n cursor 256 _ hl.remainder
  have hcoef cursor := coefficientBlockProgram_support_production n cursor 256 _ hl.coefficient
  have hphase cursor := (phaseProgram_support n cursor indexedStepProductionRegisters.phaseUpdate indexedStepProductionRegisters.shiftEpoch).trans
    (support_to_580 _ (by decide +kernel))
  unfold indexedStepProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [indexedStepSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simpa only [literalProgram_support,circuitWires] using hA
  · exact hrem _
  · simpa only [literalProgram_support] using hCD
  · exact hcoef _
  · simpa only [literalProgram_support,circuitWires] using hF
  · exact hphase _
  · simpa only [literalProgram_support,circuitWires] using hH
end ShorECDLP.Paper2607_13816.ChallengeMigration
