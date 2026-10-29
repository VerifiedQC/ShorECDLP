import ShorECDLP.Submission.«2607_13816».Challenge.EndpointSupport
import ShorECDLP.Submission.«2607_13816».Challenge.MeasuredWorkspace
import ShorECDLP.Submission.«2607_13816».Challenge.EEACenterSupport
import ShorECDLP.Submission.«2607_13816».EEA.WrapperSupport
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



attribute [local irreducible] coefficientInverseProgram intervalInverseProgram phaseInverseProgram hInverseProgram
  blockAInverse blockCInverse blockDInverse blockFForward

theorem measuredInverseStepProgram_support_production (n start T : Nat)
    (hl : IndexedStepLayout indexedStepProductionRegisters 256 T) :
    straightWires (measuredInverseStepProgram n start indexedStepProductionRegisters T).2 ⊆ List.range 580 := by
  let r := indexedStepProductionRegisters
  have hs := circuitWires_subset_of_usesOnly (indexedStepInverseUnitary_production_usesOnly T hl)
  simp only [indexedStepInverseUnitary,circuitWires,List.flatMap_append,List.append_subset] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨hH,hG⟩,hF⟩,hE⟩,hD⟩,hC⟩,hB⟩,hA⟩ := hs
  have hsf := circuitWires_subset_of_usesOnly (indexedStepUnitary_production_usesOnly T hl)
  simp only [indexedStepUnitary,circuitWires,List.flatMap_append,List.append_subset] at hsf
  have hforwardF : PaperCircuitUsesOnly (List.range 580) (blockFForward r) := by
    intro g hg w hw
    exact hsf.1.1.2 (List.mem_flatMap.mpr ⟨g,hg,hw⟩)
  have hFadj := circuitWires_subset_of_usesOnly hforwardF.adjoint
  have hcAdd := circuitWires_subset_of_usesOnly ((computeControl_usesOnly [r.phase1] 1 r.control r.blockScratch).mono (support_to_580 _ (by decide +kernel)))
  have hcSub := circuitWires_subset_of_usesOnly ((computeControl_usesOnly [r.phase1,r.terminal] 1 r.control r.blockScratch).mono (support_to_580 _ (by decide +kernel)))
  have hcTmp := circuitWires_subset_of_usesOnly ((computeControl_usesOnly [r.phase2,r.sign] 2 r.terminal r.blockScratch).mono (support_to_580 _ (by decide +kernel)))
  have hprep := circuitWires_subset_of_usesOnly ((prepareLatestPaperTBoundary_usesOnly r.tBoundary 256).mono (support_to_580 _ (by decide +kernel)))
  have hrest := circuitWires_subset_of_usesOnly ((restoreLatestPaperTBoundary_usesOnly r.tBoundary 256).mono (support_to_580 _ (by decide +kernel)))
  have hx := circuitWires_subset_of_usesOnly (gate_support_580 (.CX r.phase1 r.sign) (by decide +kernel))
  have hterm := circuitWires_subset_of_usesOnly (gate_support_580 (.CCX r.phase2 r.sign r.terminal) (by decide +kernel))
  have hrst := circuitWires_subset_of_usesOnly ((rControlNonterminal_usesOnly [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)).mono (support_to_580 _ (by decide +kernel)))
  have hrsub := circuitWires_subset_of_usesOnly ((rControlNonterminal_usesOnly [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch).mono (support_to_580 _ (by decide +kernel)))
  have hrc := (rControlNonterminal_usesOnly [r.phase1,r.phase2] 2 r.control r.lengthRPrime r.terminal r.blockScratch).mono (support_to_580 _ (by decide +kernel))
  have hrx := gate_support_580 (.CX r.control r.sign) (by decide +kernel)
  have hB2 : circuitWires (blockB2 r) ⊆ List.range 580 := circuitWires_subset_of_usesOnly ((hrc.append hrx).append hrc)
  have hci mode phase cursor := (coefficientInverseProgram_support_layout n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) _ _ mode phase .work2 hl.coefficient).trans (fun _ h => production_coefficient_support _ _ h)
  have hii mode phase cursor := (intervalInverseProgram_support_layout n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 _ _ mode phase .work1 hl.remainder).trans (fun _ h => production_remainder_support _ _ h)
  have hphase cursor := (phaseInverseProgram_support n cursor r.phaseUpdate r.shiftEpoch).trans (support_to_580 _ (by decide +kernel))
  unfold measuredInverseStepProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [measuredInverseStepSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact (hPrograms_support_production n _ T hl.endIteration).2
  · exact hphase _
  · simp only [literalProgram_support,circuitWires,List.flatMap_append,List.append_subset]
    exact ⟨⟨hFadj,hprep⟩,hcAdd⟩
  · exact hci _ _ _
  · simp only [literalProgram_support,circuitWires,List.flatMap_append,List.append_subset]
    exact ⟨⟨⟨⟨hcAdd,hx⟩,hcTmp⟩,hcSub⟩,hcTmp⟩
  · exact hci _ _ _
  · simp only [literalProgram_support,circuitWires,List.flatMap_append,List.append_subset]
    exact ⟨⟨⟨⟨⟨⟨hcTmp,hcSub⟩,hcTmp⟩,hrest⟩,hD⟩,hC⟩,⟨hterm,hrst⟩,hterm⟩
  · exact hii _ _ _
  · simp only [literalProgram_support,circuitWires,List.flatMap_append,List.append_subset]
    exact ⟨⟨⟨⟨hterm,hrst⟩,hterm⟩,hB2⟩,hrsub⟩
  · exact hii _ _ _
  · simp only [literalProgram_support,circuitWires,List.flatMap_append,List.append_subset]
    exact ⟨hrsub,hA⟩


attribute [local irreducible] measuredStepProgram measuredInverseStepProgram

theorem measuredScheduleProgram_support_production (n first count start : Nat)
    (hl : IndexedScheduleLayout indexedStepProductionRegisters 256 first count) :
    straightWires (measuredScheduleProgram n indexedStepProductionRegisters 256 count first start).2 ⊆ List.range 580 := by
  induction hl generalizing start with
  | done first => simp [measuredScheduleProgram,literalProgram_support,circuitWires]
  | step head tail ih =>
    rw [measuredScheduleProgram,appendCompiled_support,List.append_subset]
    exact ⟨measuredStepProgram_support_production n _ _ head,ih _⟩

theorem measuredInverseScheduleProgram_support_production (n first count start : Nat)
    (hl : IndexedScheduleLayout indexedStepProductionRegisters 256 first count) :
    straightWires (measuredInverseScheduleProgram n indexedStepProductionRegisters count first start).2 ⊆ List.range 580 := by
  induction hl generalizing start with
  | done first => simp [measuredInverseScheduleProgram,literalProgram_support,circuitWires]
  | step head tail ih =>
    rw [measuredInverseScheduleProgram,appendCompiled_support,List.append_subset]
    exact ⟨ih _,measuredInverseStepProgram_support_production n _ _ head⟩

theorem measuredEEAForwardProgram_support_production (n start : Nat) :
    straightWires (measuredEEAForwardProgram n start indexedStepProductionRegisters).2 ⊆ List.range 580 :=
  measuredScheduleProgram_support_production n 1 secp256k1ScheduleLength start secp256k1ScheduleLayout_production

theorem measuredEEAReverseProgram_support_production (n start : Nat) :
    straightWires (measuredEEAReverseProgram n start indexedStepProductionRegisters).2 ⊆ List.range 580 :=
  measuredInverseScheduleProgram_support_production n 1 secp256k1ScheduleLength start secp256k1ScheduleLayout_production


theorem preprocessProgram_support (n start : Nat) :
    straightWires (preprocessProgram n start).2 ⊆ List.range 580 := by
  have hc := eeaCenterProgram_support n start (List.range' 266 256).reverse (List.range' 4 256)
    (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2 (List.range 580)
    (by simp) (by simp [constantBits_length]) (by simp)
    (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide))
    (fun _ h => support_to_580 _ (by decide +kernel) _ h)
    (fun _ h => support_to_580 _ (by decide +kernel) _ h)
  have hbefore : circuitWires workRegistersPrepare ⊆ List.range 580 := by
    intro w hw
    apply eeaPreprocess_wires_subset
    simp only [eeaPreprocess,AdaptiveCircuit.wires,modularWires_seq,List.mem_append,List.not_mem_nil,or_false]
    exact Or.inl hw
  have hafter : circuitWires eeaLengthSetup ⊆ List.range 580 := by
    intro w hw
    apply eeaPreprocess_wires_subset
    simp only [eeaPreprocess,AdaptiveCircuit.wires,modularWires_seq,List.mem_append,List.not_mem_nil,or_false]
    exact Or.inr (Or.inr hw)
  unfold preprocessProgram
  simp only [surroundCompiled_support,List.append_subset]
  exact ⟨⟨hbefore,hc⟩,hafter⟩

theorem unpreprocessProgram_support (n start : Nat) :
    straightWires (unpreprocessProgram n start).2 ⊆ List.range 580 := by
  have hc := eeaUncenterProgram_support n start (List.range' 266 256).reverse (List.range' 4 256)
    (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2 (List.range 580)
    (by simp) (by simp [constantBits_length]) (by simp)
    (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide))
    (fun _ h => support_to_580 _ (by decide +kernel) _ h)
    (fun _ h => support_to_580 _ (by decide +kernel) _ h)
  have hbefore : circuitWires eeaLengthUndo ⊆ List.range 580 := by
    intro w hw
    apply eeaUnpreprocess_wires_subset
    simp only [eeaUnpreprocess,AdaptiveCircuit.wires,modularWires_seq,List.mem_append,List.not_mem_nil,or_false]
    exact Or.inl hw
  have hafter : circuitWires workRegistersRestore ⊆ List.range 580 := by
    intro w hw
    apply eeaUnpreprocess_wires_subset
    simp only [eeaUnpreprocess,AdaptiveCircuit.wires,modularWires_seq,List.mem_append,List.not_mem_nil,or_false]
    exact Or.inr (Or.inr hw)
  unfold unpreprocessProgram
  simp only [surroundCompiled_support,List.append_subset]
  exact ⟨⟨hbefore,hc⟩,hafter⟩

theorem productionParityProgram_support (n start : Nat) :
    straightWires (productionParityProgram n start).2 ⊆ List.range 580 := by
  exact eeaParityProgram_support n start (List.range' 263 256) (List.range' 4 255)
    secp256k1ModulusBits 560 561 562 2 (List.range 580)
    (by simp) (by simp [secp256k1ModulusBits])
    (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide))
    (fun _ h => support_to_580 _ (by decide +kernel) _ h)
    (fun _ h => support_to_580 _ (by decide +kernel) _ h)


attribute [local irreducible] preprocessProgram unpreprocessProgram productionParityProgram
  measuredEEAForwardProgram measuredEEAReverseProgram
  eeaPreprocess eeaUnpreprocess secp256k1EEAForwardAdaptive secp256k1EEAReverseAdaptive
  secp256k1EEAParityCorrection canonicalWork2Rotation canonicalWork2InverseRotation
  terminalEpochCompression terminalWork1Clear

theorem measuredForwardWrapperProgram_support (n start : Nat) :
    straightWires (measuredForwardWrapperProgram n start).2 ⊆ List.range 580 := by
  have hmid : circuitWires (canonicalWork2Rotation ++ terminalEpochCompression) ⊆ List.range 580 := by
    intro w hw
    apply secp256k1EEAForwardWrapper_wires_subset
    simp only [secp256k1EEAForwardWrapper,modularWires_seq,AdaptiveCircuit.wires,
      circuitWires,List.flatMap_append,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    aesop
  have hclear : circuitWires terminalWork1Clear ⊆ List.range 580 := by
    intro w hw
    apply secp256k1EEAForwardWrapper_wires_subset
    simp only [secp256k1EEAForwardWrapper,modularWires_seq,AdaptiveCircuit.wires,
      circuitWires,List.flatMap_append,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    aesop
  unfold measuredForwardWrapperProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [measuredForwardWrapperSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl
  · exact preprocessProgram_support n _
  · exact measuredEEAForwardProgram_support_production n _
  · simpa only [literalProgram_support] using hmid
  · exact productionParityProgram_support n _
  · simpa only [literalProgram_support] using hclear

theorem measuredReverseWrapperProgram_support (n start : Nat) :
    straightWires (measuredReverseWrapperProgram n start).2 ⊆ List.range 580 := by
  have hmid : circuitWires (terminalEpochCompression ++ canonicalWork2InverseRotation) ⊆ List.range 580 := by
    intro w hw
    apply secp256k1EEAReverseWrapper_wires_subset
    simp only [secp256k1EEAReverseWrapper,secp256k1EEAReversePostprocessing,modularWires_seq,AdaptiveCircuit.wires,
      circuitWires,List.flatMap_append,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    aesop
  have hclear : circuitWires terminalWork1Clear ⊆ List.range 580 := by
    intro w hw
    apply secp256k1EEAReverseWrapper_wires_subset
    simp only [secp256k1EEAReverseWrapper,secp256k1EEAReversePostprocessing,modularWires_seq,AdaptiveCircuit.wires,
      circuitWires,List.flatMap_append,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    aesop
  unfold measuredReverseWrapperProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [measuredReverseWrapperSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl
  · simpa only [literalProgram_support] using hclear
  · exact productionParityProgram_support n _
  · simpa only [literalProgram_support] using hmid
  · exact measuredEEAReverseProgram_support_production n _
  · exact unpreprocessProgram_support n _


private theorem exchanged_580_in_base (w : Wire) (hw : w ∈ List.range 580) :
    eeaWorkspaceExchange w ∈ windowBaseSupport := by
  have h : (List.range 580).all (fun w => decide (eeaWorkspaceExchange w < 837)) = true := by decide +kernel
  have hlt := of_decide_eq_true ((List.all_eq_true.mp h) w hw)
  simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
  exact Or.inl (Or.inl hlt)

theorem measuredForwardDataBankProgram_support_static (n start : Nat) :
    straightWires (measuredForwardDataBankProgram n start).2 ⊆ windowBaseSupport := by
  rw [measuredForwardDataBankProgram,relabelCompiled_support]
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  exact exchanged_580_in_base v (measuredForwardWrapperProgram_support n start hv)

theorem measuredReverseDataBankProgram_support_static (n start : Nat) :
    straightWires (measuredReverseDataBankProgram n start).2 ⊆ windowBaseSupport := by
  rw [measuredReverseDataBankProgram,relabelCompiled_support]
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  exact exchanged_580_in_base v (measuredReverseWrapperProgram_support n start hv)
end ShorECDLP.Paper2607_13816.ChallengeMigration
