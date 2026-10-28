import ShorECDLP.Submission.«2607_13816».Challenge.EEACoreSupport
import ShorECDLP.Submission.«2607_13816».Challenge.MultiplicationSupport
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
private theorem list_getD_mem
    (list : List α) (index : Nat) (fallback : α)
    (hindex : index < list.length) :
    list.getD index fallback ∈ list := by
  rw [List.getD_eq_getElem list fallback hindex]
  exact List.getElem_mem hindex


private theorem intervalTopRelative_lt_laneCount
    (k K : Nat) (hkK : k ≤ K) :
    intervalTopRelative k K < intervalLaneCount k K := by
  simp only [intervalTopRelative, intervalLaneCount]
  omega


private theorem intervalTargetAt_mem_allWires
    (registers : IntervalRegisters) (k K label : Nat)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target)
    (hlabel : label < intervalLaneCount k K) :
    registers.targetAt target label ∈ registers.allWires := by
  cases target with
  | work1 =>
      have hbound : label < registers.work1.length := by
        rw [hlayout.work1_length]
        exact hlabel
      have hmem := list_getD_mem registers.work1 label 0 hbound
      change registers.work1.getD label 0 ∈ registers.allWires
      rw [IntervalRegisters.allWires]
      exact List.mem_append_right _ (List.mem_append_left _ hmem)
  | work2 =>
      have hbound : label < registers.work2.length := by
        rw [hlayout.work2_length]
        exact hlabel
      have hmem := list_getD_mem registers.work2 label 0 hbound
      change registers.work2.getD label 0 ∈ registers.allWires
      rw [IntervalRegisters.allWires]
      exact List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ hmem))


private theorem intervalAddendAt_mem_allWires
    (registers : IntervalRegisters) (k K label : Nat)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target)
    (hlabel : label < intervalLaneCount k K) :
    registers.addendAt target label ∈ registers.allWires := by
  cases target with
  | work1 =>
      have hbound : label < registers.work2.length := by
        rw [hlayout.work2_length]
        exact hlabel
      have hmem := list_getD_mem registers.work2 label 0 hbound
      change registers.work2.getD label 0 ∈ registers.allWires
      rw [IntervalRegisters.allWires]
      exact List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ hmem))
  | work2 =>
      have hbound : label < registers.work1.length := by
        rw [hlayout.work1_length]
        exact hlabel
      have hmem := list_getD_mem registers.work1 label 0 hbound
      change registers.work1.getD label 0 ∈ registers.allWires
      rw [IntervalRegisters.allWires]
      exact List.mem_append_right _ (List.mem_append_left _ hmem)


private theorem intervalScratch_mem_allWires
    (registers : IntervalRegisters) {wire : Wire}
    (hwire : wire ∈ registers.scratch) :
    wire ∈ registers.allWires := by
  rw [IntervalRegisters.allWires]
  exact List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _ hwire)))))


private theorem intervalRightTop_mem_allWires
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.rightTop k K ∈ registers.allWires := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · have hmem := list_getD_mem registers.lengthS (intervalTopBit k K) 0
      (hlayout.right_top_capacity hspecial)
    rw [IntervalRegisters.rightTop, if_pos hspecial, IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ hmem)))))
  · have hbound : 0 < registers.lengthT.length := by
      have := hlayout.lengthT_two_le
      omega
    have hmem := list_getD_mem registers.lengthT 0 0 hbound
    rw [IntervalRegisters.rightTop, if_neg hspecial, IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ hmem)))


private theorem intervalLeftTop_mem_allWires
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.leftTop k K ∈ registers.allWires := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · have hmem := list_getD_mem registers.lengthQ (intervalTopBit k K) 0
      (hlayout.left_top_capacity hspecial)
    rw [IntervalRegisters.leftTop, if_pos hspecial, IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ hmem))))
  · have hbound : 1 < registers.lengthT.length := by
      have := hlayout.lengthT_two_le
      omega
    have hmem := list_getD_mem registers.lengthT 1 0 hbound
    rw [IntervalRegisters.leftTop, if_neg hspecial, IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ hmem)))


private theorem intervalEndpointSupport_mem_allWires
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    ∀ wire,
      wire ∈ intervalEndpointSupport registers.lengthT registers.lengthQ
          registers.lengthS registers.endpointScratch (registers.carry k K) →
        wire ∈ registers.allWires := by
  intro wire hwire
  simp only [intervalEndpointSupport, List.mem_append, List.mem_singleton] at hwire
  rcases hwire with ((((hscratch | hcarry) | ht) | hq) | hs)
  · exact intervalScratch_mem_allWires registers
      (List.mem_of_mem_take hscratch)
  · subst wire
    exact intervalScratch_mem_allWires registers
      (intervalCarry_mem_scratch registers k K target hlayout)
  · simp [IntervalRegisters.allWires, ht]
  · simp [IntervalRegisters.allWires, hq]
  · simp [IntervalRegisters.allWires, hs]


private theorem intervalDecoder_mem_allWires
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    ∀ wire,
      wire ∈ (intervalTree registers k K).decoderWires registers.control
          registers.control (registers.rightPaths k K) (registers.leftPaths k K) →
        wire ∈ registers.allWires := by
  intro wire hwire
  simp only [DualUnaryActionTree.decoderWires, List.mem_append,
    List.mem_dedup, List.mem_cons, List.not_mem_nil, or_false] at hwire
  rcases hwire with hcontrol | hindexA | hindexB | hrightPath | hleftPath
  · rcases hcontrol with rfl | rfl <;> simp [IntervalRegisters.allWires]
  · obtain ⟨bit, hbit, rfl⟩ := DualUnaryActionTree.build_indexAWires
      registers.rightIndex registers.leftIndex
      (DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset)
      (intervalMainLabels k K).toFinset (intervalTree registers k K) (by
        simpa [DualUnaryActionTree.buildSourceFromList,
          DualUnaryActionTree.buildSource] using intervalTree_built registers k K)
      (by simpa using hindexA)
    have hbound : bit < registers.lengthS.length :=
      lt_of_lt_of_le hbit hlayout.right_index_capacity
    have hmem := list_getD_mem registers.lengthS bit 0 hbound
    change registers.lengthS.getD bit 0 ∈ registers.allWires
    rw [IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ hmem)))))
  · obtain ⟨bit, hbit, rfl⟩ := DualUnaryActionTree.build_indexBWires
      registers.rightIndex registers.leftIndex
      (DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset)
      (intervalMainLabels k K).toFinset (intervalTree registers k K) (by
        simpa [DualUnaryActionTree.buildSourceFromList,
          DualUnaryActionTree.buildSource] using intervalTree_built registers k K)
      (by simpa using hindexB)
    have hbound : bit < registers.lengthQ.length :=
      lt_of_lt_of_le hbit hlayout.left_index_capacity
    have hmem := list_getD_mem registers.lengthQ bit 0 hbound
    change registers.lengthQ.getD bit 0 ∈ registers.allWires
    rw [IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ hmem))))
  · have hscratch : wire ∈ registers.scratch :=
      List.mem_of_mem_take hrightPath
    simp [IntervalRegisters.allWires, hscratch]
  · have hscratch : wire ∈ registers.scratch :=
      List.mem_of_mem_drop (List.mem_of_mem_take hleftPath)
    simp [IntervalRegisters.allWires, hscratch]



theorem intervalTopFirstProgram_support (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) (hl : IntervalLayout r k K target) :
    straightWires (intervalTopFirstProgram n start r k K mode target).2 ⊆ r.allWires := by
  unfold intervalTopFirstProgram
  rw [compiledIf_support]
  split
  · apply topFirstProgram_support
    · intro w hw; simp [IntervalRegisters.allWires,hw]
    · intro w hw; simp [IntervalRegisters.allWires,hw]
    · exact intervalScratch_mem_allWires r (intervalAccumulator_mem_scratch r k K target hl)
    · exact intervalTargetAt_mem_allWires r k K _ target hl (intervalTopRelative_lt_laneCount k K hl.k_le_K)
    · exact intervalAddendAt_mem_allWires r k K _ target hl (intervalTopRelative_lt_laneCount k K hl.k_le_K)
    · exact intervalScratch_mem_allWires r (intervalCarry_mem_scratch r k K target hl)
    · exact intervalScratch_mem_allWires r (intervalCellScratch_mem_scratch r k K target hl)
    · exact intervalScratch_mem_allWires r (intervalCellScratch_mem_scratch r k K target hl)
    · intro w hw; exact intervalScratch_mem_allWires r (List.mem_of_mem_take hw)
    · simp [IntervalRegisters.allWires]
    · simp [IntervalRegisters.allWires]
  · exact List.nil_subset _

theorem intervalTopSecondProgram_support (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) (hl : IntervalLayout r k K target) :
    straightWires (intervalTopSecondProgram n start r k K mode target).2 ⊆ r.allWires := by
  unfold intervalTopSecondProgram
  rw [compiledIf_support]
  split
  · apply topSecondProgram_support
    · intro w hw; simp [IntervalRegisters.allWires,hw]
    · intro w hw; simp [IntervalRegisters.allWires,hw]
    · exact intervalScratch_mem_allWires r (intervalAccumulator_mem_scratch r k K target hl)
    · exact intervalTargetAt_mem_allWires r k K _ target hl (intervalTopRelative_lt_laneCount k K hl.k_le_K)
    · exact intervalAddendAt_mem_allWires r k K _ target hl (intervalTopRelative_lt_laneCount k K hl.k_le_K)
    · exact intervalScratch_mem_allWires r (intervalCarry_mem_scratch r k K target hl)
    · exact intervalScratch_mem_allWires r (intervalCellScratch_mem_scratch r k K target hl)
    · exact intervalScratch_mem_allWires r (intervalCellScratch_mem_scratch r k K target hl)
    · intro w hw; exact intervalScratch_mem_allWires r (List.mem_of_mem_take hw)
    · simp [IntervalRegisters.allWires]
    · simp [IntervalRegisters.allWires]
  · exact List.nil_subset _

theorem intervalTraversalFirstProgram_support (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) (hl : IntervalLayout r k K target) :
    straightWires (traversalFirstProgram n start mode (intervalHasTopSpecial k K)
      (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K)
      (r.cellScratch k K) (r.targetAt target) (r.addendAt target) (intervalTree r k K)
      r.control r.control (r.rightPaths k K) (r.leftPaths k K)).2 ⊆ r.allWires := by
  have hd := intervalDecoder_mem_allWires r k K target hl
  apply traversalFirstProgram_support
  · exact intervalRightTop_mem_allWires r k K target hl
  · exact intervalLeftTop_mem_allWires r k K target hl
  · exact intervalScratch_mem_allWires r (intervalAccumulator_mem_scratch r k K target hl)
  · exact intervalScratch_mem_allWires r (intervalCarry_mem_scratch r k K target hl)
  · exact intervalScratch_mem_allWires r (intervalCellScratch_mem_scratch r k K target hl)
  · intro l hlab; exact intervalTargetAt_mem_allWires r k K l target hl (intervalTree_label_lt_laneCount r k K l hlab)
  · intro l hlab; exact intervalAddendAt_mem_allWires r k K l target hl (intervalTree_label_lt_laneCount r k K l hlab)
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])
  · simp [IntervalRegisters.allWires]
  · simp [IntervalRegisters.allWires]
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])

theorem intervalTraversalSecondProgram_support (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) (hl : IntervalLayout r k K target) :
    straightWires (traversalSecondProgram n start mode (intervalHasTopSpecial k K)
      (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K)
      (r.cellScratch k K) (r.targetAt target) (r.addendAt target) (intervalTree r k K)
      r.control r.control (r.rightPaths k K) (r.leftPaths k K)).2 ⊆ r.allWires := by
  have hd := intervalDecoder_mem_allWires r k K target hl
  apply traversalSecondProgram_support
  · exact intervalRightTop_mem_allWires r k K target hl
  · exact intervalLeftTop_mem_allWires r k K target hl
  · exact intervalScratch_mem_allWires r (intervalAccumulator_mem_scratch r k K target hl)
  · exact intervalScratch_mem_allWires r (intervalCarry_mem_scratch r k K target hl)
  · exact intervalScratch_mem_allWires r (intervalCellScratch_mem_scratch r k K target hl)
  · intro l hlab; exact intervalTargetAt_mem_allWires r k K l target hl (intervalTree_label_lt_laneCount r k K l hlab)
  · intro l hlab; exact intervalAddendAt_mem_allWires r k K l target hl (intervalTree_label_lt_laneCount r k K l hlab)
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])
  · simp [IntervalRegisters.allWires]
  · simp [IntervalRegisters.allWires]
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])


theorem intervalProgram_support_layout (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (hl : IntervalLayout r k K target) :
    straightWires (intervalProgram n start r width k K mode signUpdate target).2 ⊆ r.allWires := by
  have he := intervalEndpointSupport_mem_allWires r k K target hl
  have hprep := (circuitWires_subset_of_usesOnly (prepareIntervalEndpoints_usesOnly r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) width k)).trans (fun _ h => he _ h)
  have hrest := (circuitWires_subset_of_usesOnly (restoreIntervalEndpoints_usesOnly r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) width k)).trans (fun _ h => he _ h)
  have ht1 cursor := intervalTopFirstProgram_support n cursor r k K mode target hl
  have ht2 cursor := intervalTopSecondProgram_support n cursor r k K mode target hl
  have hp1 cursor := intervalTraversalFirstProgram_support n cursor r k K mode target hl
  have hp2 cursor := intervalTraversalSecondProgram_support n cursor r k K mode target hl
  have hcarry := intervalScratch_mem_allWires r (intervalCarry_mem_scratch r k K target hl)
  have hsign : r.sign ∈ r.allWires := by simp [IntervalRegisters.allWires]
  have hsgn : circuitWires (intervalSignUpdate r k K signUpdate) ⊆ r.allWires := by
    cases signUpdate <;> simp [intervalSignUpdate,circuitWires,gateWires,hcarry,hsign]
  simp only [intervalProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hprep,ht1 _,hp1 _,hsgn,hp2 _,ht2 _,hrest⟩

theorem intervalInverseProgram_support_layout (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (hl : IntervalLayout r k K target) :
    straightWires (intervalInverseProgram n start r width k K mode signUpdate target).2 ⊆ r.allWires := by
  exact intervalProgram_support_layout n start r width k K mode.inverse signUpdate target hl
end ShorECDLP.Paper2607_13816.ChallengeMigration
