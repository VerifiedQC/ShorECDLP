import ShorECDLP.Submission.«2607_13816».Challenge.LengthSupport
import ShorECDLP.Submission.«2607_13816».Challenge.MeasuredStep
import ShorECDLP.Submission.«2607_13816».Challenge.StepSupport
import ShorECDLP.Submission.«2607_13816».EEA.PhysicalSupport
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
private theorem getD_support (ws : List Wire) (i : Nat)
    (hws : ∀ w ∈ ws, w ∈ List.range 580) : ws.getD i 0 ∈ List.range 580 := by
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hws _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact List.mem_range.mpr (by decide)

private theorem endpoint_width {k K : Nat} (hK : K ≤ 259) :
    DualUnaryActionTree.sourceWidth (quotientSwapLabels k K).toFinset ≤ 9 := by
  apply DualUnaryActionTree.sourceWidth_le _ 9 (by decide)
  intro label hlabel
  have hmem : label ∈ quotientSwapLabels k K := by simpa using hlabel
  simp only [quotientSwapLabels, List.mem_range'_1] at hmem
  norm_num
  omega

private theorem support_to_580 (support : List Wire)
    (h : support.all (fun w => decide (w < 580)) = true) :
    ∀ w ∈ support, w ∈ List.range 580 := by
  intro w hw
  exact List.mem_range.mpr (of_decide_eq_true ((List.all_eq_true.mp h) w hw))
theorem endPrograms_support_production (n start T : Nat)
    (hlayout : EndIterationLayout (indexedStepProductionRegisters.endIteration 256 T) 256
      (endIterationWindowsAt 256 T)) :
    straightWires (endProgram n start (indexedStepProductionRegisters.endIteration 256 T) 256 (endIterationWindowsAt 256 T)).2 ⊆ List.range 580 ∧
    straightWires (endInverseProgram n start (indexedStepProductionRegisters.endIteration 256 T) 256 (endIterationWindowsAt 256 T)).2 ⊆ List.range 580 := by
  let r := indexedStepProductionRegisters.endIteration 256 T
  let windows := endIterationWindowsAt 256 T
  have hc : r.control ∈ List.range 580 := List.mem_range.mpr (show (558 : Nat) < 580 by decide)
  have h1 : ∀ w ∈ r.work1, w ∈ List.range 580 := support_to_580 indexedStepProductionRegisters.work1 (by decide +kernel)
  have h2 : ∀ w ∈ r.work2, w ∈ List.range 580 := support_to_580 indexedStepProductionRegisters.work2 (by decide +kernel)
  have hT : ∀ w ∈ r.lengthT, w ∈ List.range 580 := support_to_580 indexedStepProductionRegisters.lengthT (by decide +kernel)
  have hRP : ∀ w ∈ r.lengthRP, w ∈ List.range 580 := support_to_580 indexedStepProductionRegisters.lengthRPrime (by decide +kernel)
  have hs : ∀ w ∈ r.scratch, w ∈ List.range 580 := by
    intro w hw
    exact support_to_580 (indexedStepProductionRegisters.sourceScratch.drop 2)
      (by decide +kernel) w (List.mem_of_mem_take hw)
  have hpath : ∀ k K w, w ∈ r.path k K → w ∈ List.range 580 := by
    intro k K w hw; exact hs w (List.mem_of_mem_take hw)
  have hconst : ∀ w ∈ r.constants, w ∈ List.range 580 := by
    intro w hw; exact hs w (List.mem_of_mem_take hw)
  have huIndex : ∀ w ∈ (r.upperTree windows).indexWires, w ∈ List.range 580 := by
    let q : QuotientSwapRegisters := ⟨0,0,[],[],r.lengthRP,[]⟩
    intro w hw
    exact hRP w (quotientSwapTree_indexWires_mem_lengthQ q hlayout.k4_le_K4
      (endpoint_width hlayout.K4_le_work) w hw)
  have hlIndex : ∀ w ∈ (r.lowerTree 256 windows).indexWires, w ∈ List.range 580 := by
    let q : QuotientSwapRegisters := ⟨0,0,[],[],r.lengthT,[]⟩
    intro w hw
    exact hT w (quotientSwapTree_indexWires_mem_lengthQ q hlayout.k5_le_decode
      (endpoint_width (Nat.min_le_right _ _)) w hw)
  have hu cursor := ltUpdateProgram_support n 256 windows.k4 windows.K4 (r.upperTree windows) r.control
    (r.rangeAccumulator windows.k4 windows.K4) (r.temporary windows.k4 windows.K4) r.carry
    (r.path windows.k4 windows.K4) r.work1At r.work2At r.lengthT r.lengthRP r.constants cursor (List.range 580)
    (fun _ h => huIndex _ h) hc (getD_support _ _ hs) (getD_support _ _ hs) (getD_support _ _ hs)
    (fun _ h => hpath _ _ _ h) (fun _ => getD_support _ _ h1) (fun _ => getD_support _ _ h2)
    (fun _ h => hT _ h) (fun _ h => hRP _ h) (fun _ h => hconst _ h)
  have hl cursor := lrpUpdateProgram_support n 256 windows.k5 (windows.K5Decode 256) (r.lowerTree 256 windows) r.control
    (r.rangeAccumulator windows.k5 (windows.K5Decode 256)) (r.temporary windows.k5 (windows.K5Decode 256)) r.carry
    (r.path windows.k5 (windows.K5Decode 256)) r.work1At r.work2At r.lengthT r.lengthRP r.constants cursor (List.range 580)
    (fun _ h => hlIndex _ h) hc (getD_support _ _ hs) (getD_support _ _ hs) (getD_support _ _ hs)
    (fun _ h => hpath _ _ _ h) (fun _ => getD_support _ _ h1) (fun _ => getD_support _ _ h2)
    (fun _ h => hT _ h) (fun _ h => hRP _ h) (fun _ h => hconst _ h)
  have hws : r.control :: r.work1 ++ r.work2 ⊆ List.range 580 := by
    simp only [List.append_subset,List.cons_subset]
    exact ⟨⟨hc,fun _ h => h1 _ h⟩,fun _ h => h2 _ h⟩
  have hf := (circuitWires_subset_of_usesOnly (controlledWorkSwap_usesOnly r.control r.work1 r.work2)).trans hws
  have hb := (circuitWires_subset_of_usesOnly (controlledWorkSwapInverse_usesOnly r.control r.work1 r.work2)).trans hws
  constructor
  · simp only [endProgram,prependCompiled_support,appendCompiled_support,List.append_subset]
    exact ⟨hf,hu _,hl _⟩
  · simp only [endInverseProgram,appendCompiled_support,literalProgram_support,List.append_subset]
    exact ⟨hl _,hu _,hb⟩


private theorem production_h_literals :
    circuitWires (blockHPrefix indexedStepProductionRegisters) ⊆ List.range 580 ∧
    circuitWires (blockHSuffix indexedStepProductionRegisters) ⊆ List.range 580 := by
  let r := indexedStepProductionRegisters
  have hq := (mcxVChain_usesOnly r.lengthQ (r.sourceScratch.getD 0 0)
    (r.sourceScratch.drop 2)).mono (support_to_580 _ (by decide +kernel))
  have hs := (mcxVChain_usesOnly (r.lengthS ++ [r.shiftEpoch]) (r.sourceScratch.getD 1 0)
    (r.sourceScratch.drop 2)).mono (support_to_580 _ (by decide +kernel))
  have hx : PaperCircuitUsesOnly (List.range 580) ([.X r.shiftEpoch] : Circuit) := by
    intro g hg w hw
    simp only [List.mem_singleton] at hg
    subst g
    exact support_to_580 _ (by decide +kernel) w hw
  have hc : PaperCircuitUsesOnly (List.range 580)
      ([.CCX (r.sourceScratch.getD 0 0) (r.sourceScratch.getD 1 0) r.control] : Circuit) := by
    intro g hg w hw
    simp only [List.mem_singleton] at hg
    subst g
    exact support_to_580 _ (by decide +kernel) w hw
  constructor
  · exact circuitWires_subset_of_usesOnly ((((hq.append hx).append hs).append hx).append hc)
  · exact circuitWires_subset_of_usesOnly ((((hc.append hx).append hs).append hx).append hq)

theorem hPrograms_support_production (n start T : Nat)
    (hl : T%4=0 → EndIterationLayout (indexedStepProductionRegisters.endIteration 256 T) 256
      (endIterationWindowsAt 256 T)) :
    straightWires (hProgram n start indexedStepProductionRegisters 256 T).2 ⊆ List.range 580 ∧
    straightWires (hInverseProgram n start indexedStepProductionRegisters 256 T).2 ⊆ List.range 580 := by
  have hx : circuitWires ([.CX indexedStepProductionRegisters.control indexedStepProductionRegisters.iter] : Circuit) ⊆ List.range 580 := by
    intro w hw
    exact support_to_580 _ (by decide +kernel) w hw
  unfold hProgram hInverseProgram
  rw [compiledIf_support,compiledIf_support]
  by_cases h : T%4=0
  · simp only [h,ite_true,surroundCompiled_support,circuitWires,List.flatMap_append,List.append_subset]
    obtain ⟨hf,hb⟩ := production_h_literals
    obtain ⟨he,hi⟩ := endPrograms_support_production n start T (hl h)
    exact ⟨⟨⟨hf,he⟩,hx,hb⟩,⟨⟨hf,hx⟩,hi⟩,hb⟩
  · simp [h,straightWires]

attribute [local irreducible] remainderBlockProgram coefficientBlockProgram phaseProgram
  blockAForward blockBForward blockCForward blockDForward blockEForward blockFForward blockGForward blockHForward

theorem measuredStepProgram_support_production (n start T : Nat)
    (hl : IndexedStepLayout indexedStepProductionRegisters 256 T) :
    straightWires (measuredStepProgram n start indexedStepProductionRegisters 256 T).2 ⊆ List.range 580 := by
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
  unfold measuredStepProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [measuredStepSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simpa only [literalProgram_support,circuitWires] using hA
  · exact hrem _
  · simpa only [literalProgram_support] using hCD
  · exact hcoef _
  · simpa only [literalProgram_support,circuitWires] using hF
  · exact hphase _
  · exact (hPrograms_support_production n _ T hl.endIteration).1
end ShorECDLP.Paper2607_13816.ChallengeMigration
