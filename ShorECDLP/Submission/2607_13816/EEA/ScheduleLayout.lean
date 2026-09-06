import ShorECDLP.Submission.«2607_13816».EEA.Schedule

/-!
# Closed secp256k1 schedule layout

This module checks the one repaired 580-role indexed-step allocation against every physical
window used by the fixed `T = 1, ..., 1620` schedule.  The Boolean checks below are private proof
machinery: their soundness theorems reconstruct the ordinary inductive layout contracts, and the
public result mentions only the concrete register map and `Secp256k1ScheduleLayout`.
-/

namespace ShorECDLP.Paper2607_13816

open Classical Quantum

noncomputable section

/-! ## Decoder-layout transport -/

private theorem listDisjoint_mono
    {left right smallerLeft smallerRight : List α}
    (hdisjoint : List.Disjoint left right)
    (hleft : ∀ wire, wire ∈ smallerLeft → wire ∈ left)
    (hright : ∀ wire, wire ∈ smallerRight → wire ∈ right) :
    List.Disjoint smallerLeft smallerRight := by
  rw [List.disjoint_left] at hdisjoint ⊢
  intro wire hsmallerLeft hsmallerRight
  exact hdisjoint (hleft wire hsmallerLeft) (hright wire hsmallerRight)

private theorem dualTreeLayout_of_nodup
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (pathsA pathsB : List Wire)
    (hdepthA : tree.pathDepth ≤ pathsA.length)
    (hdepthB : tree.pathDepth ≤ pathsB.length)
    (hnodup : (tree.decoderWires controlA controlB pathsA pathsB).Nodup) :
    tree.Layout controlA controlB pathsA pathsB := by
  induction tree generalizing controlA controlB pathsA pathsB with
  | leaf label => exact .leaf label controlA controlB pathsA pathsB hnodup
  | node indexA indexB zero one ihZero ihOne =>
      cases pathsA with
      | nil => simp [DualUnaryActionTree.pathDepth] at hdepthA
      | cons pathA restA =>
          cases pathsB with
          | nil => simp [DualUnaryActionTree.pathDepth] at hdepthB
          | cons pathB restB =>
              simp only [DualUnaryActionTree.decoderWires] at hnodup
              have htop := List.nodup_append.mp hnodup
              have hindexA := List.nodup_append.mp htop.2.1
              have hindexB := List.nodup_append.mp hindexA.2.1
              have hdisjointA := List.disjoint_of_nodup_append htop.2.1
              have hdisjointB := List.disjoint_of_nodup_append hindexA.2.1
              have hpaths :
                  ((pathA :: restA) ++ pathB :: restB).Nodup := hindexB.2.1
              have hpaths' :
                  (pathA :: (restA ++ pathB :: restB)).Nodup := by
                simpa only [List.cons_append] using hpaths
              have hpathA := List.nodup_cons.mp hpaths'
              have hpathB : (pathB :: (restA ++ restB)).Nodup :=
                List.nodup_middle.mp hpathA.2
              have hpathTail : (restA ++ restB).Nodup :=
                (List.nodup_cons.mp hpathB).2
              have hcontrolsPath : List.Disjoint [pathA, pathB].dedup
                  (restA ++ restB) := by
                rw [List.disjoint_left]
                intro wire hcontrol hrest
                simp only [List.mem_dedup, List.mem_cons, List.not_mem_nil,
                  or_false] at hcontrol
                rcases hcontrol with rfl | rfl
                · apply hpathA.1
                  simp only [List.mem_append, List.mem_cons]
                  rcases List.mem_append.mp hrest with hrest | hrest
                  · exact Or.inl hrest
                  · exact Or.inr (Or.inr hrest)
                · exact (List.nodup_cons.mp hpathB).1 hrest
              have childNodup (child : DualUnaryActionTree)
                  (hchildA : ∀ wire, wire ∈ child.indexAWires →
                    wire ∈ (DualUnaryActionTree.node indexA indexB zero one).indexAWires)
                  (hchildB : ∀ wire, wire ∈ child.indexBWires →
                    wire ∈ (DualUnaryActionTree.node indexA indexB zero one).indexBWires) :
                  (child.decoderWires pathA pathB restA restB).Nodup := by
                have hsubsetA : ∀ wire, wire ∈ child.indexAWires.dedup →
                    wire ∈ (DualUnaryActionTree.node indexA indexB zero one).indexAWires.dedup := by
                  intro wire hwire
                  simpa only [List.mem_dedup] using hchildA wire (by simpa using hwire)
                have hsubsetB : ∀ wire, wire ∈ child.indexBWires.dedup →
                    wire ∈ (DualUnaryActionTree.node indexA indexB zero one).indexBWires.dedup := by
                  intro wire hwire
                  simpa only [List.mem_dedup] using hchildB wire (by simpa using hwire)
                have hpathSubset : ∀ wire, wire ∈ restA ++ restB →
                    wire ∈ (pathA :: restA) ++ pathB :: restB := by
                  intro wire hwire
                  rcases List.mem_append.mp hwire with hwire | hwire
                  · simp [hwire]
                  · simp [hwire]
                have hcontrolSubset : ∀ wire, wire ∈ [pathA, pathB].dedup →
                    wire ∈ (pathA :: restA) ++ pathB :: restB := by
                  intro wire hwire
                  simp only [List.mem_dedup, List.mem_cons, List.not_mem_nil,
                    or_false] at hwire
                  rcases hwire with rfl | rfl <;> simp
                have hAB : List.Disjoint child.indexAWires.dedup
                    child.indexBWires.dedup :=
                  listDisjoint_mono hdisjointA hsubsetA (fun wire hwire ↦
                    List.mem_append_left _ (hsubsetB wire hwire))
                have hAP : List.Disjoint child.indexAWires.dedup
                    (restA ++ restB) :=
                  listDisjoint_mono hdisjointA hsubsetA (fun wire hwire ↦
                    List.mem_append_right _ (hpathSubset wire hwire))
                have hBP : List.Disjoint child.indexBWires.dedup
                    (restA ++ restB) :=
                  listDisjoint_mono hdisjointB hsubsetB hpathSubset
                have hCA : List.Disjoint [pathA, pathB].dedup
                    child.indexAWires.dedup :=
                  listDisjoint_mono hdisjointA.symm (fun wire hwire ↦
                    List.mem_append_right _ (hcontrolSubset wire hwire)) hsubsetA
                have hCB : List.Disjoint [pathA, pathB].dedup
                    child.indexBWires.dedup :=
                  listDisjoint_mono hdisjointB.symm hcontrolSubset hsubsetB
                have hBAndPath := (List.nodup_dedup child.indexBWires).append
                  hpathTail hBP
                have hAAndTail := (List.nodup_dedup child.indexAWires).append
                  hBAndPath (by
                    rw [List.disjoint_left]
                    intro wire hwire htail
                    rcases List.mem_append.mp htail with htail | htail
                    · exact (List.disjoint_left.mp hAB) hwire htail
                    · exact (List.disjoint_left.mp hAP) hwire htail)
                have hAll := (List.nodup_dedup [pathA, pathB]).append
                  hAAndTail (by
                    rw [List.disjoint_left]
                    intro wire hwire htail
                    rcases List.mem_append.mp htail with htail | htail
                    · exact (List.disjoint_left.mp hCA) hwire htail
                    · rcases List.mem_append.mp htail with htail | htail
                      · exact (List.disjoint_left.mp hCB) hwire htail
                      · exact (List.disjoint_left.mp hcontrolsPath) hwire htail)
                simpa only [DualUnaryActionTree.decoderWires] using hAll
              exact .node indexA indexB controlA controlB pathA pathB zero one
                restA restB hnodup
                (ihZero pathA pathB restA restB
                  (by simp [DualUnaryActionTree.pathDepth] at hdepthA; omega)
                  (by simp [DualUnaryActionTree.pathDepth] at hdepthB; omega)
                  (childNodup zero (by
                    intro wire hwire
                    simp [DualUnaryActionTree.indexAWires, hwire]) (by
                    intro wire hwire
                    simp [DualUnaryActionTree.indexBWires, hwire])))
                (ihOne pathA pathB restA restB
                  (by simp [DualUnaryActionTree.pathDepth] at hdepthA; omega)
                  (by simp [DualUnaryActionTree.pathDepth] at hdepthB; omega)
                  (childNodup one (by
                    intro wire hwire
                    simp [DualUnaryActionTree.indexAWires, hwire]) (by
                    intro wire hwire
                    simp [DualUnaryActionTree.indexBWires, hwire])))

/-! ## One fixed physical envelope -/

private def indexedStepProductionPhysicalEnvelope : List Wire :=
  let registers := indexedStepProductionRegisters
  ([registers.control, registers.sign] : List Wire) ++
    registers.work1 ++ registers.work2 ++ registers.lengthT ++
      registers.lengthQ ++ registers.lengthS ++ registers.lengthRPrime ++
        (registers.aux).drop 1

private theorem nodup_move_suffix_head
    {front frontTail suffix : List α} {pivot : α}
    (hglobal : (front ++ pivot :: suffix).Nodup)
    (hsub : frontTail.Sublist front) :
    (pivot :: (frontTail ++ suffix)).Nodup := by
  have hparts := List.nodup_append.mp hglobal
  have hsuffix := List.nodup_cons.mp hparts.2.1
  rw [List.nodup_cons]
  constructor
  · intro hmem
    rcases List.mem_append.mp hmem with hfront | hsuffixMem
    · exact (hparts.2.2 pivot (hsub.mem hfront) pivot (by simp)) rfl
    · exact hsuffix.1 hsuffixMem
  · exact (hsub.nodup hparts.1).append hsuffix.2 (by
      rw [List.disjoint_left]
      intro wire hfront hsuffixMem
      exact hparts.2.2 wire (hsub.mem hfront) wire (by simp [hsuffixMem]) rfl)

private theorem indexedStepProductionPhysicalEnvelope_nodup :
    indexedStepProductionPhysicalEnvelope.Nodup := by
  let registers := indexedStepProductionRegisters
  let front := ([registers.phase1, registers.phase2, registers.iter,
    registers.sign] : List Wire) ++
    registers.work1 ++ registers.work2 ++ registers.lengthT ++
      registers.lengthQ ++ registers.lengthS ++ registers.lengthRPrime
  let frontTail := ([registers.sign] : List Wire) ++ registers.work1 ++ registers.work2 ++
    registers.lengthT ++ registers.lengthQ ++ registers.lengthS ++
      registers.lengthRPrime
  have hglobal := indexedStepProduction_layout.physical
  have haux : registers.aux = registers.control :: (registers.aux).drop 1 := by
    decide
  have hsplit : registers.allWires = front ++ registers.aux := by
    simp [registers, front, IndexedStepRegisters.allWires, List.append_assoc]
  have hsub : frontTail.Sublist front := by
    simpa [front, frontTail, List.append_assoc] using
      (List.drop_sublist 3 front)
  rw [hsplit, haux] at hglobal
  have hmoved := nodup_move_suffix_head hglobal hsub
  simpa [indexedStepProductionPhysicalEnvelope, registers, frontTail,
    List.append_assoc] using hmoved

private theorem productionPhysicalNodup
    (fixed work1 work2 lengthT lengthQ lengthS lengthRPrime scratch : List Wire)
    (hfixed : fixed.Sublist
      [indexedStepProductionRegisters.control, indexedStepProductionRegisters.sign])
    (hwork1 : work1.Sublist indexedStepProductionRegisters.work1)
    (hwork2 : work2.Sublist indexedStepProductionRegisters.work2)
    (hlengthT : lengthT.Sublist indexedStepProductionRegisters.lengthT)
    (hlengthQ : lengthQ.Sublist indexedStepProductionRegisters.lengthQ)
    (hlengthS : lengthS.Sublist indexedStepProductionRegisters.lengthS)
    (hlengthRPrime : lengthRPrime.Sublist indexedStepProductionRegisters.lengthRPrime)
    (hscratch : scratch.Sublist
      (List.drop 1 indexedStepProductionRegisters.aux)) :
    (fixed ++ work1 ++ work2 ++ lengthT ++ lengthQ ++ lengthS ++
      lengthRPrime ++ scratch).Nodup := by
  have hsub := hfixed.append (hwork1.append (hwork2.append
    (hlengthT.append (hlengthQ.append (hlengthS.append
      (hlengthRPrime.append hscratch))))))
  have hnodup := hsub.nodup (by
    simpa [indexedStepProductionPhysicalEnvelope, List.append_assoc] using
      indexedStepProductionPhysicalEnvelope_nodup)
  simpa [List.append_assoc] using hnodup

private theorem windowSlice_sublist (work : List Wire) (window : ActiveWindow) :
    (IndexedStepRegisters.windowSlice work window).Sublist work := by
  exact (List.take_sublist _ _).trans (List.drop_sublist _ _)

private theorem indexedStepProductionSourceScratch_sub_auxTail :
    indexedStepProductionRegisters.sourceScratch.Sublist
      (List.drop 1 indexedStepProductionRegisters.aux) := by
  change (List.range' 560 18).Sublist (List.range' 559 21)
  decide

private theorem indexedStepProductionBlockScratch_sub_auxTail :
    indexedStepProductionRegisters.blockScratch.Sublist
      (List.drop 1 indexedStepProductionRegisters.aux) := by
  exact (List.drop_sublist 1 indexedStepProductionRegisters.sourceScratch).trans
    indexedStepProductionSourceScratch_sub_auxTail

private theorem indexedStepProductionRemainderScratchSource :
    indexedStepProductionRegisters.shiftEpoch ::
        (indexedStepProductionRegisters.sourceScratch ++
          indexedStepProductionRegisters.remainderRepairScratch) =
      List.drop 1 indexedStepProductionRegisters.aux := by
  rfl

private theorem indexedStepProduction_remainder_physical (window : ActiveWindow) :
    (indexedStepProductionRegisters.remainder window).allWires.Nodup := by
  rw [IntervalRegisters.allWires]
  have hscratch :
      (indexedStepProductionRegisters.remainder window).scratch.Sublist
        (List.drop 1 indexedStepProductionRegisters.aux) := by
    rw [IndexedStepRegisters.remainder,
      indexedStepProductionRemainderScratchSource]
    exact List.take_sublist _ _
  have h := productionPhysicalNodup
    ([indexedStepProductionRegisters.control,
      indexedStepProductionRegisters.sign] : List Wire)
    (IndexedStepRegisters.windowSlice indexedStepProductionRegisters.work1 window)
    (IndexedStepRegisters.windowSlice indexedStepProductionRegisters.work2 window)
    indexedStepProductionRegisters.lengthT indexedStepProductionRegisters.lengthQ
    indexedStepProductionRegisters.lengthS ([] : List Wire)
    (indexedStepProductionRegisters.remainder window).scratch
    (.refl _) (windowSlice_sublist _ _) (windowSlice_sublist _ _)
    (.refl _) (.refl _) (.refl _) (List.nil_sublist _) hscratch
  simpa [IndexedStepRegisters.remainder, List.append_assoc] using h

private theorem indexedStepProduction_quotient_physical (window : ActiveWindow) :
    (indexedStepProductionRegisters.quotient window).allWires.Nodup := by
  rw [QuotientSwapRegisters.allWires]
  have hscratch :
      (indexedStepProductionRegisters.quotient window).scratch.Sublist
        (List.drop 1 indexedStepProductionRegisters.aux) := by
    rw [IndexedStepRegisters.quotient]
    exact (List.take_sublist _ _).trans
      indexedStepProductionSourceScratch_sub_auxTail
  have h := productionPhysicalNodup
    ([indexedStepProductionRegisters.control,
      indexedStepProductionRegisters.sign] : List Wire)
    (IndexedStepRegisters.windowSlice indexedStepProductionRegisters.work1 window)
    ([] : List Wire) indexedStepProductionRegisters.lengthT
    indexedStepProductionRegisters.lengthQ
    ([] : List Wire) ([] : List Wire)
    (indexedStepProductionRegisters.quotient window).scratch
    (.refl _) (windowSlice_sublist _ _) (List.nil_sublist _) (.refl _) (.refl _)
    (List.nil_sublist _) (List.nil_sublist _) hscratch
  simpa [IndexedStepRegisters.quotient, List.append_assoc] using h

private theorem indexedStepProduction_coefficient_physical (window : ActiveWindow) :
    (indexedStepProductionRegisters.coefficient window).allWires.Nodup := by
  rw [CoefficientPrefixRegisters.allWires]
  have hscratch :
      (indexedStepProductionRegisters.coefficient window).scratch.Sublist
        (List.drop 1 indexedStepProductionRegisters.aux) := by
    rw [IndexedStepRegisters.coefficient]
    exact (List.take_sublist _ _).trans
      indexedStepProductionBlockScratch_sub_auxTail
  have h := productionPhysicalNodup
    ([indexedStepProductionRegisters.control,
      indexedStepProductionRegisters.sign] : List Wire)
    (IndexedStepRegisters.windowSlice indexedStepProductionRegisters.work1 window)
    (IndexedStepRegisters.windowSlice indexedStepProductionRegisters.work2 window)
    indexedStepProductionRegisters.lengthT ([] : List Wire) ([] : List Wire)
    ([] : List Wire)
    (indexedStepProductionRegisters.coefficient window).scratch
    (.refl _) (windowSlice_sublist _ _) (windowSlice_sublist _ _)
    (.refl _) (List.nil_sublist _) (List.nil_sublist _) (List.nil_sublist _) hscratch
  simpa [IndexedStepRegisters.coefficient, List.append_assoc] using h

private theorem indexedStepProduction_endIteration_physical (T : Nat) :
    (indexedStepProductionRegisters.endIteration 256 T).allWires.Nodup := by
  rw [EndIterationRegisters.allWires]
  have hscratch :
      (indexedStepProductionRegisters.endIteration 256 T).scratch.Sublist
        (List.drop 1 indexedStepProductionRegisters.aux) := by
    rw [IndexedStepRegisters.endIteration]
    exact (List.take_sublist _ _).trans <|
      (List.drop_sublist 2 indexedStepProductionRegisters.sourceScratch).trans
        indexedStepProductionSourceScratch_sub_auxTail
  have hfixed : ([indexedStepProductionRegisters.control] : List Wire).Sublist
      [indexedStepProductionRegisters.control, indexedStepProductionRegisters.sign] :=
    .cons₂ _ (List.nil_sublist _)
  have h := productionPhysicalNodup
    ([indexedStepProductionRegisters.control] : List Wire)
    indexedStepProductionRegisters.work1 indexedStepProductionRegisters.work2
    indexedStepProductionRegisters.lengthT ([] : List Wire) ([] : List Wire)
    indexedStepProductionRegisters.lengthRPrime
    (indexedStepProductionRegisters.endIteration 256 T).scratch
    hfixed (.refl _) (.refl _) (.refl _) (List.nil_sublist _)
    (List.nil_sublist _) (.refl _) hscratch
  simpa [IndexedStepRegisters.endIteration, List.append_assoc] using h

private theorem listGetDMem
    (list : List α) (index : Nat) (fallback : α)
    (hindex : index < list.length) :
    list.getD index fallback ∈ list := by
  rw [List.getD_eq_getElem list fallback hindex]
  exact List.getElem_mem hindex

private theorem intervalTree_indexAWires_mem_lengthS
    (registers : IntervalRegisters) {k K : Nat}
    (hindexWidth : DualUnaryActionTree.sourceWidth
      (intervalMainLabels k K).toFinset ≤ registers.lengthS.length) :
    ∀ wire, wire ∈ (intervalTree registers k K).indexAWires →
      wire ∈ registers.lengthS := by
  intro wire hwire
  obtain ⟨bit, hbit, rfl⟩ := DualUnaryActionTree.build_indexAWires
    registers.rightIndex registers.leftIndex
    (DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset)
    (intervalMainLabels k K).toFinset (intervalTree registers k K) (by
      simpa [DualUnaryActionTree.buildSourceFromList,
        DualUnaryActionTree.buildSource] using intervalTree_built registers k K) hwire
  exact listGetDMem registers.lengthS bit 0 (lt_of_lt_of_le hbit hindexWidth)

private theorem intervalTree_indexBWires_mem_lengthQ
    (registers : IntervalRegisters) {k K : Nat}
    (hindexWidth : DualUnaryActionTree.sourceWidth
      (intervalMainLabels k K).toFinset ≤ registers.lengthQ.length) :
    ∀ wire, wire ∈ (intervalTree registers k K).indexBWires →
      wire ∈ registers.lengthQ := by
  intro wire hwire
  obtain ⟨bit, hbit, rfl⟩ := DualUnaryActionTree.build_indexBWires
    registers.rightIndex registers.leftIndex
    (DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset)
    (intervalMainLabels k K).toFinset (intervalTree registers k K) (by
      simpa [DualUnaryActionTree.buildSourceFromList,
        DualUnaryActionTree.buildSource] using intervalTree_built registers k K) hwire
  exact listGetDMem registers.lengthQ bit 0 (lt_of_lt_of_le hbit hindexWidth)

private theorem intervalTree_layout_from_physical
    (registers : IntervalRegisters) {k K : Nat}
    (hrightWidth : DualUnaryActionTree.sourceWidth
      (intervalMainLabels k K).toFinset ≤ registers.lengthS.length)
    (hleftWidth : DualUnaryActionTree.sourceWidth
      (intervalMainLabels k K).toFinset ≤ registers.lengthQ.length)
    (hscratch : registers.scratch.length = intervalScratchBase registers k K + 3)
    (hphysical : registers.allWires.Nodup) :
    (intervalTree registers k K).Layout registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K) := by
  let depth := intervalTreeDepth registers k K
  have hpaths : registers.rightPaths k K ++ registers.leftPaths k K =
      registers.scratch.take (depth + depth) := by
    exact (List.take_add (l := registers.scratch) (i := depth) (j := depth)).symm
  have htwoDepth : depth + depth ≤ registers.scratch.length := by
    rw [hscratch]
    exact le_trans (by
      simp [intervalScratchBase, depth, two_mul]) (Nat.le_add_right _ _)
  have hrightLength : depth ≤ (registers.rightPaths k K).length := by
    change depth ≤ (registers.scratch.take depth).length
    simp only [List.length_take]
    rw [Nat.min_eq_left (le_trans (Nat.le_add_right depth depth) htwoDepth)]
  have hleftLength : depth ≤ (registers.leftPaths k K).length := by
    change depth ≤ ((registers.scratch.drop depth).take depth).length
    simp only [List.length_take, List.length_drop]
    rw [Nat.min_eq_left]
    omega
  have hpathsSub :
      (registers.rightPaths k K ++ registers.leftPaths k K).Sublist
        registers.scratch := by
    rw [hpaths]
    exact List.take_sublist _ _
  have hcontrolSub : ([registers.control] : List Wire).Sublist
      [registers.control, registers.sign] :=
    .cons₂ _ (List.nil_sublist _)
  have htailSub :
      (registers.lengthQ ++ (registers.lengthS ++
        (registers.rightPaths k K ++ registers.leftPaths k K))).Sublist
        (registers.work1 ++ (registers.work2 ++
          (registers.lengthT ++ (registers.lengthQ ++
            (registers.lengthS ++ registers.scratch))))) :=
    (List.nil_sublist _).append <| (List.nil_sublist _).append <|
      (List.nil_sublist _).append <| (List.Sublist.refl _).append <|
        (List.Sublist.refl _).append hpathsSub
  have hordered :
      (registers.control :: registers.lengthQ ++ (registers.lengthS ++
        (registers.rightPaths k K ++ registers.leftPaths k K))).Nodup := by
    have hsub := hcontrolSub.append htailSub
    have hnodup := hsub.nodup (by
      simpa only [IntervalRegisters.allWires] using hphysical)
    simpa only [List.singleton_append] using hnodup
  have hreordered :
      (registers.control :: registers.lengthS ++ (registers.lengthQ ++
        (registers.rightPaths k K ++ registers.leftPaths k K))).Nodup := by
    apply hordered.perm
    apply List.Perm.cons
    simpa only [List.append_assoc] using
      List.Perm.append_right
        (registers.rightPaths k K ++ registers.leftPaths k K)
        (List.perm_append_comm :
          (registers.lengthQ ++ registers.lengthS).Perm
            (registers.lengthS ++ registers.lengthQ))
  have hrest := (List.nodup_cons.mp hreordered).2
  obtain ⟨hS, hQPaths, hSDisjoint⟩ := List.nodup_append.mp hrest
  obtain ⟨hQ, hpathsNodup, hQDisjoint⟩ := List.nodup_append.mp hQPaths
  have hSDisjoint' : List.Disjoint registers.lengthS
      (registers.lengthQ ++
        (registers.rightPaths k K ++ registers.leftPaths k K)) :=
    List.disjoint_of_nodup_append hrest
  have hQDisjoint' : List.Disjoint registers.lengthQ
      (registers.rightPaths k K ++ registers.leftPaths k K) :=
    List.disjoint_of_nodup_append hQPaths
  let indexA := (intervalTree registers k K).indexAWires.dedup
  let indexB := (intervalTree registers k K).indexBWires.dedup
  let paths := registers.rightPaths k K ++ registers.leftPaths k K
  have hindexASub : ∀ wire, wire ∈ indexA → wire ∈ registers.lengthS := by
    intro wire hwire
    exact intervalTree_indexAWires_mem_lengthS registers hrightWidth _ (by
      simpa [indexA] using hwire)
  have hindexBSub : ∀ wire, wire ∈ indexB → wire ∈ registers.lengthQ := by
    intro wire hwire
    exact intervalTree_indexBWires_mem_lengthQ registers hleftWidth _ (by
      simpa [indexB] using hwire)
  have hindexBPaths : List.Disjoint indexB paths :=
    listDisjoint_mono hQDisjoint' hindexBSub (fun _ hwire ↦ hwire)
  have hindexAIndexB : List.Disjoint indexA indexB :=
    listDisjoint_mono hSDisjoint' hindexASub (fun wire hwire ↦
      List.mem_append_left _ (hindexBSub wire hwire))
  have hindexAPaths : List.Disjoint indexA paths :=
    listDisjoint_mono hSDisjoint' hindexASub (fun wire hwire ↦
      List.mem_append_right _ hwire)
  have hindexBTail : (indexB ++ paths).Nodup :=
    (List.nodup_dedup _).append hpathsNodup hindexBPaths
  have htailNodup : (indexA ++ (indexB ++ paths)).Nodup :=
    (List.nodup_dedup _).append hindexBTail (by
      rw [List.disjoint_left]
      intro wire hwire htail
      rcases List.mem_append.mp htail with hindexB | hpath
      · exact (List.disjoint_left.mp hindexAIndexB) hwire hindexB
      · exact (List.disjoint_left.mp hindexAPaths) hwire hpath)
  have hdecoder : ((intervalTree registers k K).decoderWires registers.control
      registers.control (registers.rightPaths k K) (registers.leftPaths k K)).Nodup := by
    have hcontrolTail : registers.control ∉ indexA ++ (indexB ++ paths) := by
      intro hmem
      have hcontrolAll := (List.nodup_cons.mp hreordered).1
      rcases List.mem_append.mp hmem with hindexAMem | htail
      · exact hcontrolAll (by simp [hindexASub _ hindexAMem])
      · rcases List.mem_append.mp htail with hindexBMem | hpathMem
        · exact hcontrolAll (by simp [hindexBSub _ hindexBMem])
        · rcases List.mem_append.mp hpathMem with hright | hleft
          · exact hcontrolAll (by simp [hright])
          · exact hcontrolAll (by simp [hleft])
    rw [DualUnaryActionTree.decoderWires]
    simpa [indexA, indexB, paths] using
      (List.nodup_cons.mpr ⟨hcontrolTail, htailNodup⟩)
  exact dualTreeLayout_of_nodup _ _ _ _ _ hrightLength hleftLength hdecoder

private theorem quotientSwapTree_layout_from_physical
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hkK : k ≤ K)
    (hindexWidth : DualUnaryActionTree.sourceWidth
      (quotientSwapLabels k K).toFinset ≤ registers.lengthQ.length)
    (hscratch : registers.scratch.length = registers.scratchBase k K + 1)
    (hphysical : registers.allWires.Nodup) :
    (quotientSwapTree registers k K).Layout registers.control
      (registers.path k K) := by
  have hpathSub : (registers.path k K).Sublist registers.scratch :=
    List.take_sublist _ _
  have hcontrolSub : ([registers.control] : List Wire).Sublist
      [registers.control, registers.sign] :=
    .cons₂ _ (List.nil_sublist _)
  have htailSub :
      (registers.lengthQ ++ registers.path k K).Sublist
    (registers.work1 ++
          (registers.lengthT ++ (registers.lengthQ ++ registers.scratch))) :=
    (List.nil_sublist _).append <|
      (List.nil_sublist _).append <| (List.Sublist.refl _).append hpathSub
  have hdecoder :
      (registers.control :: registers.lengthQ ++ registers.path k K).Nodup := by
    have hsub := hcontrolSub.append htailSub
    have hnodup := hsub.nodup (by
      simpa only [QuotientSwapRegisters.allWires] using hphysical)
    simpa only [List.singleton_append] using hnodup
  have hcapacity : quotientSwapUnaryDepth k K ≤ registers.scratch.length := by
    rw [hscratch]
    exact le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
  have hpathLength : quotientSwapUnaryDepth k K ≤ (registers.path k K).length := by
    simp only [QuotientSwapRegisters.path, List.length_take]
    rw [Nat.min_eq_left hcapacity]
  have htail := (List.nodup_cons.mp hdecoder).2
  exact quotientSwapTree_layout_of_separated registers hkK hindexWidth
    registers.control (registers.path k K) hpathLength
    (by
      intro hmem
      exact (List.nodup_cons.mp hdecoder).1 (by simp [hmem]))
    (by
      intro hmem
      exact (List.nodup_cons.mp hdecoder).1 (by simp [hmem]))
    (List.nodup_append.mp htail).2.1
    (List.disjoint_of_nodup_append htail)

private theorem coefficientPrefixTree_layout_from_physical
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hkK : k ≤ K)
    (hindexWidth : DualUnaryActionTree.sourceWidth
      (quotientSwapLabels k K).toFinset ≤ registers.boundary.length)
    (hscratch : registers.scratch.length = registers.scratchBase k K + 3)
    (hphysical : registers.allWires.Nodup) :
    (coefficientPrefixTree registers k K).Layout registers.control
      (registers.path k K) := by
  have hpathSub : (registers.path k K).Sublist registers.scratch := by
    rw [CoefficientPrefixRegisters.path, QuotientSwapRegisters.path]
    exact List.take_sublist _ _
  have hcontrolSub : ([registers.control] : List Wire).Sublist
      [registers.control, registers.sign] :=
    .cons₂ _ (List.nil_sublist _)
  have htailSub :
      (registers.boundary ++ registers.path k K).Sublist
        (registers.work1 ++
          (registers.work2 ++ (registers.boundary ++ registers.scratch))) :=
    (List.nil_sublist _).append <|
      (List.nil_sublist _).append <| (List.Sublist.refl _).append hpathSub
  have hdecoder :
      (registers.control :: registers.boundary ++ registers.path k K).Nodup := by
    have hsub := hcontrolSub.append htailSub
    have hnodup := hsub.nodup (by
      simpa only [CoefficientPrefixRegisters.allWires] using hphysical)
    simpa only [List.singleton_append] using hnodup
  have hcapacity : quotientSwapUnaryDepth k K ≤ registers.scratch.length := by
    rw [hscratch]
    exact le_trans (by
      simp [CoefficientPrefixRegisters.scratchBase]) (Nat.le_add_right _ _)
  have hpathLength : quotientSwapUnaryDepth k K ≤ (registers.path k K).length := by
    simp only [CoefficientPrefixRegisters.path, QuotientSwapRegisters.path,
      CoefficientPrefixRegisters.routing, List.length_take]
    rw [Nat.min_eq_left hcapacity]
  have htail := (List.nodup_cons.mp hdecoder).2
  exact quotientSwapTree_layout_of_separated (registers.routing k K) hkK
    (by simpa [CoefficientPrefixRegisters.routing] using hindexWidth)
    registers.control (registers.path k K) hpathLength
    (by
      intro hmem
      have hmem' : registers.control ∈ registers.boundary := by
        simpa [CoefficientPrefixRegisters.routing] using hmem
      exact (List.nodup_cons.mp hdecoder).1
        (List.mem_append_left _ hmem'))
    (by
      intro hmem
      exact (List.nodup_cons.mp hdecoder).1 (by simp [hmem]))
    (List.nodup_append.mp htail).2.1
    (by
      simpa [CoefficientPrefixRegisters.routing] using
        (List.disjoint_of_nodup_append htail))

/-! ## Uniform production remainder geometry -/

private theorem take_range'_eq
    (start total count : Nat) (hcount : count ≤ total) :
    (List.range' start total).take count = List.range' start count := by
  apply List.ext_getElem
  · simp [hcount]
  · intro index hleft hright
    rw [List.getElem_take, List.getElem_range'_1, List.getElem_range'_1]

private theorem intervalMainLabel_lt_laneCount
    {k K label : Nat} (hlabel : label ∈ (intervalMainLabels k K).toFinset) :
    label < intervalLaneCount k K := by
  have hmain : label ∈ intervalMainLabels k K := by simpa using hlabel
  by_cases hspecial : intervalHasTopSpecial k K = true
  · simp [intervalMainLabels, hspecial] at hmain
    omega
  · simpa [intervalMainLabels, hspecial] using hmain

private theorem intervalTreeLabel_lt_laneCount
    (registers : IntervalRegisters) {k K label : Nat}
    (hlabel : label ∈ (intervalTree registers k K).labels) :
    label < intervalLaneCount k K := by
  rw [intervalTree_labels] at hlabel
  exact intervalMainLabel_lt_laneCount (by simpa using hlabel)

private theorem intervalSourceWidth_le_nine
    {k K : Nat} (hcount : intervalLaneCount k K ≤ 259) :
    DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset ≤ 9 := by
  apply DualUnaryActionTree.sourceWidth_le _ 9 (by decide)
  intro label hlabel
  have hlt := intervalMainLabel_lt_laneCount hlabel
  norm_num
  omega

private theorem intervalTreeDepth_le_nine
    (registers : IntervalRegisters) {k K : Nat}
    (hcount : intervalLaneCount k K ≤ 259) :
    intervalTreeDepth registers k K ≤ 9 := by
  exact (DualUnaryActionTree.buildSource_pathDepth_le
    registers.rightIndex registers.leftIndex
    (intervalMainLabels k K).toFinset (intervalTree registers k K) (by
      simpa [DualUnaryActionTree.buildSourceFromList] using
        intervalTree_built registers k K)).trans
          (intervalSourceWidth_le_nine hcount)

private theorem intervalTopSpecial_cases
    (count : Nat) (hcount : count ≤ 259)
    (hspecial : decide (1 < count ∧ ((count - 1) &&& (count - 2)) = 0) = true) :
    count = 2 ∨ count = 3 ∨ count = 5 ∨ count = 9 ∨ count = 17 ∨
      count = 33 ∨ count = 65 ∨ count = 129 ∨ count = 257 := by
  have hmemRange : count ∈ List.range 260 := by simp; omega
  have hmem : count ∈ (List.range 260).filter fun value ↦
      decide (1 < value ∧ ((value - 1) &&& (value - 2)) = 0) :=
    List.mem_filter.mpr ⟨hmemRange, by exact_mod_cast hspecial⟩
  have hfilter : (List.range 260).filter (fun value ↦
      decide (1 < value ∧ ((value - 1) &&& (value - 2)) = 0)) =
      [2, 3, 5, 9, 17, 33, 65, 129, 257] := by decide
  rw [hfilter] at hmem
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hmem

private theorem sourceWidth_range_two_pow_le
    (depth : Nat) (hdepth : 0 < depth) :
    DualUnaryActionTree.sourceWidth (List.range (2 ^ depth)).toFinset ≤ depth := by
  apply DualUnaryActionTree.sourceWidth_le _ _ hdepth
  intro label hlabel
  simpa using hlabel

private theorem intervalTopSpecial_sourceWidth_le_topBit
    {k K : Nat} (hcount : intervalLaneCount k K ≤ 259)
    (hthree : 3 ≤ intervalLaneCount k K)
    (hspecial : intervalHasTopSpecial k K = true) :
    DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset ≤
      intervalTopBit k K := by
  have hcases := intervalTopSpecial_cases (intervalLaneCount k K) hcount (by
    simpa [intervalHasTopSpecial] using hspecial)
  rcases hcases with h | h | h | h | h | h | h | h | h
  · omega
  · simpa [intervalMainLabels, intervalTopBit, intervalTopRelative, hspecial, h] using
      sourceWidth_range_two_pow_le 1 (by decide)
  · simpa [intervalMainLabels, intervalTopBit, intervalTopRelative, hspecial, h] using
      sourceWidth_range_two_pow_le 2 (by decide)
  · simpa [intervalMainLabels, intervalTopBit, intervalTopRelative, hspecial, h] using
      sourceWidth_range_two_pow_le 3 (by decide)
  · simpa [intervalMainLabels, intervalTopBit, intervalTopRelative, hspecial, h] using
      sourceWidth_range_two_pow_le 4 (by decide)
  · simpa [intervalMainLabels, intervalTopBit, intervalTopRelative, hspecial, h] using
      sourceWidth_range_two_pow_le 5 (by decide)
  · simpa [intervalMainLabels, intervalTopBit, intervalTopRelative, hspecial, h] using
      sourceWidth_range_two_pow_le 6 (by decide)
  · simpa [intervalMainLabels, intervalTopBit, intervalTopRelative, hspecial, h] using
      sourceWidth_range_two_pow_le 7 (by decide)
  · simpa [intervalMainLabels, intervalTopBit, intervalTopRelative, hspecial, h] using
      sourceWidth_range_two_pow_le 8 (by decide)

private theorem productionRemainder_scratch_eq
    (window : ActiveWindow)
    (hcount : intervalLaneCount window.start window.stop ≤ 259) :
    (indexedStepProductionRegisters.remainder window).scratch =
      List.range' 559
        (intervalScratchBase (indexedStepProductionRegisters.remainder window)
          window.start window.stop + 3) := by
  let registers := indexedStepProductionRegisters.remainder window
  have hdepth := intervalTreeDepth_le_nine registers hcount
  have hbase : intervalScratchBase registers window.start window.stop ≤ 18 := by
    simp only [intervalScratchBase, intervalEndpointWidth]
    change max (2 * intervalTreeDepth registers window.start window.stop) (max 9 9) ≤ 18
    omega
  have hsource : indexedStepProductionRegisters.shiftEpoch ::
      (indexedStepProductionRegisters.sourceScratch ++
        indexedStepProductionRegisters.remainderRepairScratch) =
      List.range' 559 21 := by rfl
  rw [show registers.scratch =
      (indexedStepProductionRegisters.shiftEpoch ::
        (indexedStepProductionRegisters.sourceScratch ++
          indexedStepProductionRegisters.remainderRepairScratch)).take
            (intervalScratchBase registers window.start window.stop + 3) by rfl,
    hsource]
  exact take_range'_eq 559 21 _ (by omega)

private theorem productionRemainder_scratch_length
    (window : ActiveWindow)
    (hcount : intervalLaneCount window.start window.stop ≤ 259) :
    (indexedStepProductionRegisters.remainder window).scratch.length =
      intervalScratchBase (indexedStepProductionRegisters.remainder window)
        window.start window.stop + 3 := by
  rw [productionRemainder_scratch_eq window hcount, List.length_range']

private theorem productionRemainder_base_bounds
    (window : ActiveWindow)
    (_hcount : intervalLaneCount window.start window.stop ≤ 259) :
    9 ≤ intervalScratchBase (indexedStepProductionRegisters.remainder window)
        window.start window.stop ∧
      2 * intervalTreeDepth (indexedStepProductionRegisters.remainder window)
        window.start window.stop ≤
          intervalScratchBase (indexedStepProductionRegisters.remainder window)
            window.start window.stop := by
  constructor
  · change 9 ≤ max
      (2 * intervalTreeDepth (indexedStepProductionRegisters.remainder window)
        window.start window.stop) (max 9 9)
    omega
  · exact Nat.le_max_left _ _

private theorem productionRemainder_rightPaths_eq
    (window : ActiveWindow)
    (hcount : intervalLaneCount window.start window.stop ≤ 259) :
    (indexedStepProductionRegisters.remainder window).rightPaths
        window.start window.stop =
      List.range' 559 (intervalTreeDepth
        (indexedStepProductionRegisters.remainder window) window.start window.stop) := by
  rw [IntervalRegisters.rightPaths, productionRemainder_scratch_eq window hcount]
  apply take_range'_eq
  have hbounds := productionRemainder_base_bounds window hcount
  omega

private theorem productionRemainder_leftPaths_eq
    (window : ActiveWindow)
    (hcount : intervalLaneCount window.start window.stop ≤ 259) :
    (indexedStepProductionRegisters.remainder window).leftPaths
        window.start window.stop =
      List.range' (559 + intervalTreeDepth
        (indexedStepProductionRegisters.remainder window) window.start window.stop)
        (intervalTreeDepth (indexedStepProductionRegisters.remainder window)
          window.start window.stop) := by
  rw [IntervalRegisters.leftPaths, productionRemainder_scratch_eq window hcount,
    List.drop_range']
  have hbounds := productionRemainder_base_bounds window hcount
  simpa only [Nat.mul_one] using take_range'_eq
    (559 + intervalTreeDepth (indexedStepProductionRegisters.remainder window)
      window.start window.stop)
    (intervalScratchBase (indexedStepProductionRegisters.remainder window)
      window.start window.stop + 3 -
        intervalTreeDepth (indexedStepProductionRegisters.remainder window)
          window.start window.stop)
    (intervalTreeDepth (indexedStepProductionRegisters.remainder window)
      window.start window.stop) (by omega)

private theorem productionRemainder_endpointScratch_eq
    (window : ActiveWindow)
    (hcount : intervalLaneCount window.start window.stop ≤ 259) :
    (indexedStepProductionRegisters.remainder window).endpointScratch =
      List.range' 559 9 := by
  rw [IntervalRegisters.endpointScratch, productionRemainder_scratch_eq window hcount]
  change (List.range' 559
    (intervalScratchBase (indexedStepProductionRegisters.remainder window)
      window.start window.stop + 3)).take 9 = _
  apply take_range'_eq
  have hbounds := productionRemainder_base_bounds window hcount
  omega

private theorem productionRemainder_equalityScratch_eq
    (window : ActiveWindow)
    (hcount : intervalLaneCount window.start window.stop ≤ 259) :
    (indexedStepProductionRegisters.remainder window).equalityScratch
        window.start window.stop =
      List.range' 559
        (intervalScratchBase (indexedStepProductionRegisters.remainder window)
          window.start window.stop) := by
  rw [IntervalRegisters.equalityScratch, productionRemainder_scratch_eq window hcount]
  apply take_range'_eq
  omega

private theorem productionRemainder_carry_eq
    (window : ActiveWindow)
    (hcount : intervalLaneCount window.start window.stop ≤ 259) :
    (indexedStepProductionRegisters.remainder window).carry window.start window.stop =
      559 + intervalScratchBase (indexedStepProductionRegisters.remainder window)
        window.start window.stop := by
  rw [IntervalRegisters.carry, productionRemainder_scratch_eq window hcount,
    List.getD_eq_getElem _ 0 (by simp), List.getElem_range'_1]

private theorem productionRemainder_accumulator_eq
    (window : ActiveWindow)
    (hcount : intervalLaneCount window.start window.stop ≤ 259) :
    (indexedStepProductionRegisters.remainder window).accumulator window.start window.stop =
      560 + intervalScratchBase (indexedStepProductionRegisters.remainder window)
        window.start window.stop := by
  rw [IntervalRegisters.accumulator, productionRemainder_scratch_eq window hcount,
    List.getD_eq_getElem _ 0 (by simp), List.getElem_range'_1]
  ring

private theorem productionRemainder_cellScratch_eq
    (window : ActiveWindow)
    (hcount : intervalLaneCount window.start window.stop ≤ 259) :
    (indexedStepProductionRegisters.remainder window).cellScratch window.start window.stop =
      561 + intervalScratchBase (indexedStepProductionRegisters.remainder window)
        window.start window.stop := by
  rw [IntervalRegisters.cellScratch, productionRemainder_scratch_eq window hcount,
    List.getD_eq_getElem _ 0 (by simp), List.getElem_range'_1]
  ring

private theorem windowSlice_length
    (start size : Nat) (window : ActiveWindow)
    (hstart : 1 ≤ window.start) (hkK : window.start ≤ window.stop)
    (hstop : window.stop ≤ size) :
    (IndexedStepRegisters.windowSlice (List.range' start size) window).length =
      intervalLaneCount window.start window.stop := by
  simp only [IndexedStepRegisters.windowSlice, List.length_take, List.length_drop,
    List.length_range', intervalLaneCount]
  rw [Nat.min_eq_left]
  omega

private theorem productionRemainder_work1At_eq
    (window : ActiveWindow) (label : Nat)
    (hstart : 1 ≤ window.start) (hkK : window.start ≤ window.stop)
    (hstop : window.stop ≤ 259)
    (hlabel : label < intervalLaneCount window.start window.stop) :
    (indexedStepProductionRegisters.remainder window).work1.getD label 0 =
      window.start + 3 + label := by
  rw [show (indexedStepProductionRegisters.remainder window).work1 =
    IndexedStepRegisters.windowSlice indexedStepProductionRegisters.work1 window by rfl]
  change (IndexedStepRegisters.windowSlice (List.range' 4 259) window).getD label 0 = _
  have hlength := windowSlice_length 4 259 window hstart hkK hstop
  rw [List.getD_eq_getElem _ 0 (by omega)]
  simp only [IndexedStepRegisters.windowSlice]
  rw [List.getElem_take, List.getElem_drop, List.getElem_range'_1]
  have hcancel : window.start - 1 + 1 = window.start := Nat.sub_add_cancel hstart
  clear hlength hlabel hkK hstop
  calc
    4 + (window.start - 1 + label) =
        (window.start - 1 + 1) + 3 + label := by ring
    _ = window.start + 3 + label := by rw [hcancel]

private theorem productionRemainder_work2At_eq
    (window : ActiveWindow) (label : Nat)
    (hstart : 1 ≤ window.start) (hkK : window.start ≤ window.stop)
    (hstop : window.stop ≤ 259)
    (hlabel : label < intervalLaneCount window.start window.stop) :
    (indexedStepProductionRegisters.remainder window).work2.getD label 0 =
      262 + window.start + label := by
  rw [show (indexedStepProductionRegisters.remainder window).work2 =
    IndexedStepRegisters.windowSlice indexedStepProductionRegisters.work2 window by rfl]
  change (IndexedStepRegisters.windowSlice (List.range' 263 259) window).getD label 0 = _
  have hlength := windowSlice_length 263 259 window hstart hkK hstop
  rw [List.getD_eq_getElem _ 0 (by omega)]
  simp only [IndexedStepRegisters.windowSlice]
  rw [List.getElem_take, List.getElem_drop, List.getElem_range'_1]
  have hcancel : window.start - 1 + 1 = window.start := Nat.sub_add_cancel hstart
  clear hlength hlabel hkK hstop
  calc
    263 + (window.start - 1 + label) =
        262 + (window.start - 1 + 1) + label := by ring
    _ = 262 + window.start + label := by rw [hcancel]

private theorem productionRemainder_targetAt_eq
    (window : ActiveWindow) (label : Nat)
    (hstart : 1 ≤ window.start) (hkK : window.start ≤ window.stop)
    (hstop : window.stop ≤ 259)
    (hlabel : label < intervalLaneCount window.start window.stop) :
    (indexedStepProductionRegisters.remainder window).targetAt .work1 label =
      window.start + 3 + label := by
  exact productionRemainder_work1At_eq window label hstart hkK hstop hlabel

private theorem productionRemainder_addendAt_eq
    (window : ActiveWindow) (label : Nat)
    (hstart : 1 ≤ window.start) (hkK : window.start ≤ window.stop)
    (hstop : window.stop ≤ 259)
    (hlabel : label < intervalLaneCount window.start window.stop) :
    (indexedStepProductionRegisters.remainder window).addendAt .work1 label =
      262 + window.start + label := by
  exact productionRemainder_work2At_eq window label hstart hkK hstop hlabel

private theorem productionRemainder_rightIndex_eq
    (window : ActiveWindow) {bit : Nat} (hbit : bit < 9) :
    (indexedStepProductionRegisters.remainder window).rightIndex bit = 540 + bit := by
  change (List.range' 540 9).getD bit 0 = 540 + bit
  rw [List.getD_eq_getElem _ 0 (by simpa), List.getElem_range'_1]

private theorem productionRemainder_leftIndex_eq
    (window : ActiveWindow) {bit : Nat} (hbit : bit < 9) :
    (indexedStepProductionRegisters.remainder window).leftIndex bit = 531 + bit := by
  change (List.range' 531 9).getD bit 0 = 531 + bit
  rw [List.getD_eq_getElem _ 0 (by simpa), List.getElem_range'_1]

private theorem intervalTopSpecial_topBit_lt_nine
    {k K : Nat} (hcount : intervalLaneCount k K ≤ 259)
    (hspecial : intervalHasTopSpecial k K = true) :
    intervalTopBit k K < 9 := by
  have hcases := intervalTopSpecial_cases (intervalLaneCount k K) hcount (by
    simpa [intervalHasTopSpecial] using hspecial)
  rcases hcases with h | h | h | h | h | h | h | h | h
  all_goals simp [intervalTopBit, intervalTopRelative, h]
  all_goals decide

private theorem productionRemainder_rightTop_eq
    (window : ActiveWindow)
    (hcount : intervalLaneCount window.start window.stop ≤ 259)
    (hspecial : intervalHasTopSpecial window.start window.stop = true) :
    (indexedStepProductionRegisters.remainder window).rightTop
        window.start window.stop = 540 + intervalTopBit window.start window.stop := by
  rw [IntervalRegisters.rightTop, if_pos hspecial]
  change (List.range' 540 9).getD (intervalTopBit window.start window.stop) 0 = _
  rw [List.getD_eq_getElem _ 0 (by
    simpa using intervalTopSpecial_topBit_lt_nine hcount hspecial),
    List.getElem_range'_1]

private theorem productionRemainder_leftTop_eq
    (window : ActiveWindow)
    (hcount : intervalLaneCount window.start window.stop ≤ 259)
    (hspecial : intervalHasTopSpecial window.start window.stop = true) :
    (indexedStepProductionRegisters.remainder window).leftTop
        window.start window.stop = 531 + intervalTopBit window.start window.stop := by
  rw [IntervalRegisters.leftTop, if_pos hspecial]
  change (List.range' 531 9).getD (intervalTopBit window.start window.stop) 0 = _
  rw [List.getD_eq_getElem _ 0 (by
    simpa using intervalTopSpecial_topBit_lt_nine hcount hspecial),
    List.getElem_range'_1]

private theorem intervalTree_eq_leaf_zero_of_two
    (registers : IntervalRegisters) {k K : Nat}
    (hcount : intervalLaneCount k K = 2)
    (hspecial : intervalHasTopSpecial k K = true) :
    intervalTree registers k K = .leaf 0 := by
  simp [intervalTree, intervalMainLabels, hspecial, hcount,
    DualUnaryActionTree.buildSourceFromList, DualUnaryActionTree.buildSource,
    DualUnaryActionTree.sourceWidth, DualUnaryActionTree.build,
    DualUnaryActionTree.buildAt, DualUnaryActionTree.combine]

private theorem productionRemainder_indexA_ne_rightTop
    (window : ActiveWindow)
    (hcount : intervalLaneCount window.start window.stop ≤ 259)
    (hspecial : intervalHasTopSpecial window.start window.stop = true)
    {wire : Wire}
    (hwire : wire ∈ (intervalTree
      (indexedStepProductionRegisters.remainder window) window.start window.stop).indexAWires) :
    wire ≠ (indexedStepProductionRegisters.remainder window).rightTop
      window.start window.stop := by
  by_cases htwo : intervalLaneCount window.start window.stop = 2
  · rw [intervalTree_eq_leaf_zero_of_two _ htwo hspecial] at hwire
    simp [DualUnaryActionTree.indexAWires] at hwire
  · have hthree : 3 ≤ intervalLaneCount window.start window.stop := by
      have hsource : 1 < intervalLaneCount window.start window.stop := by
        have := of_decide_eq_true (show decide
          (1 < intervalLaneCount window.start window.stop ∧
            ((intervalLaneCount window.start window.stop - 1) &&&
              (intervalLaneCount window.start window.stop - 2)) = 0) = true by
            simpa [intervalHasTopSpecial] using hspecial)
        exact this.1
      omega
    obtain ⟨bit, hbit, heq⟩ := DualUnaryActionTree.build_indexAWires
      (indexedStepProductionRegisters.remainder window).rightIndex
      (indexedStepProductionRegisters.remainder window).leftIndex
      (DualUnaryActionTree.sourceWidth
        (intervalMainLabels window.start window.stop).toFinset)
      (intervalMainLabels window.start window.stop).toFinset
      (intervalTree (indexedStepProductionRegisters.remainder window)
        window.start window.stop) (by
          simpa [DualUnaryActionTree.buildSourceFromList,
            DualUnaryActionTree.buildSource] using
              intervalTree_built (indexedStepProductionRegisters.remainder window)
                window.start window.stop) hwire
    have hwidth := intervalTopSpecial_sourceWidth_le_topBit hcount hthree hspecial
    have hbitNine : bit < 9 := lt_of_lt_of_le hbit
      (intervalSourceWidth_le_nine hcount)
    rw [productionRemainder_rightIndex_eq window hbitNine] at heq
    rw [productionRemainder_rightTop_eq window hcount hspecial]
    intro heqTop
    have hnumeric : 540 + bit =
        540 + intervalTopBit window.start window.stop := heq.symm.trans heqTop
    have hbitTop : bit = intervalTopBit window.start window.stop :=
      Nat.add_left_cancel hnumeric
    omega

private theorem productionRemainder_indexB_ne_leftTop
    (window : ActiveWindow)
    (hcount : intervalLaneCount window.start window.stop ≤ 259)
    (hspecial : intervalHasTopSpecial window.start window.stop = true)
    {wire : Wire}
    (hwire : wire ∈ (intervalTree
      (indexedStepProductionRegisters.remainder window) window.start window.stop).indexBWires) :
    wire ≠ (indexedStepProductionRegisters.remainder window).leftTop
      window.start window.stop := by
  by_cases htwo : intervalLaneCount window.start window.stop = 2
  · rw [intervalTree_eq_leaf_zero_of_two _ htwo hspecial] at hwire
    simp [DualUnaryActionTree.indexBWires] at hwire
  · have hthree : 3 ≤ intervalLaneCount window.start window.stop := by
      have hsource : 1 < intervalLaneCount window.start window.stop := by
        have := of_decide_eq_true (show decide
          (1 < intervalLaneCount window.start window.stop ∧
            ((intervalLaneCount window.start window.stop - 1) &&&
              (intervalLaneCount window.start window.stop - 2)) = 0) = true by
            simpa [intervalHasTopSpecial] using hspecial)
        exact this.1
      omega
    obtain ⟨bit, hbit, heq⟩ := DualUnaryActionTree.build_indexBWires
      (indexedStepProductionRegisters.remainder window).rightIndex
      (indexedStepProductionRegisters.remainder window).leftIndex
      (DualUnaryActionTree.sourceWidth
        (intervalMainLabels window.start window.stop).toFinset)
      (intervalMainLabels window.start window.stop).toFinset
      (intervalTree (indexedStepProductionRegisters.remainder window)
        window.start window.stop) (by
          simpa [DualUnaryActionTree.buildSourceFromList,
            DualUnaryActionTree.buildSource] using
              intervalTree_built (indexedStepProductionRegisters.remainder window)
                window.start window.stop) hwire
    have hwidth := intervalTopSpecial_sourceWidth_le_topBit hcount hthree hspecial
    have hbitNine : bit < 9 := lt_of_lt_of_le hbit
      (intervalSourceWidth_le_nine hcount)
    rw [productionRemainder_leftIndex_eq window hbitNine] at heq
    rw [productionRemainder_leftTop_eq window hcount hspecial]
    intro heqTop
    have hnumeric : 531 + bit =
        531 + intervalTopBit window.start window.stop := heq.symm.trans heqTop
    have hbitTop : bit = intervalTopBit window.start window.stop :=
      Nat.add_left_cancel hnumeric
    omega

private theorem productionRemainder_roles_nodup
    (window : ActiveWindow) (label : Nat)
    (hstart : 1 ≤ window.start) (hkK : window.start ≤ window.stop)
    (hstop : window.stop ≤ 259)
    (hlabel : label < intervalLaneCount window.start window.stop) :
    [(indexedStepProductionRegisters.remainder window).rightTop
        window.start window.stop,
      (indexedStepProductionRegisters.remainder window).leftTop
        window.start window.stop,
      (indexedStepProductionRegisters.remainder window).accumulator
        window.start window.stop,
      (indexedStepProductionRegisters.remainder window).targetAt .work1 label,
      (indexedStepProductionRegisters.remainder window).addendAt .work1 label,
      (indexedStepProductionRegisters.remainder window).carry
        window.start window.stop,
      (indexedStepProductionRegisters.remainder window).cellScratch
        window.start window.stop].Nodup := by
  have hcount : intervalLaneCount window.start window.stop ≤ 259 := by
    simp only [intervalLaneCount]
    omega
  have htargetBound : window.start + label ≤ window.stop := by
    simp only [intervalLaneCount] at hlabel
    omega
  have hbase := productionRemainder_base_bounds window hcount
  rw [productionRemainder_accumulator_eq window hcount,
    productionRemainder_targetAt_eq window label hstart hkK hstop hlabel,
    productionRemainder_addendAt_eq window label hstart hkK hstop hlabel,
    productionRemainder_carry_eq window hcount,
    productionRemainder_cellScratch_eq window hcount]
  by_cases hspecial : intervalHasTopSpecial window.start window.stop = true
  · rw [productionRemainder_rightTop_eq window hcount hspecial,
      productionRemainder_leftTop_eq window hcount hspecial]
    have htop := intervalTopSpecial_topBit_lt_nine hcount hspecial
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    repeat' constructor
    all_goals first
      | exact Nat.ne_of_lt (by omega)
      | exact Nat.ne_of_gt (by omega)
      | simp
  · rw [IntervalRegisters.rightTop, if_neg hspecial,
      IntervalRegisters.leftTop, if_neg hspecial]
    change [522, 523,
      560 + intervalScratchBase (indexedStepProductionRegisters.remainder window)
        window.start window.stop,
      window.start + 3 + label, 262 + window.start + label,
      559 + intervalScratchBase (indexedStepProductionRegisters.remainder window)
        window.start window.stop,
      561 + intervalScratchBase (indexedStepProductionRegisters.remainder window)
        window.start window.stop].Nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    repeat' constructor
    all_goals first
      | exact Nat.ne_of_lt (by omega)
      | exact Nat.ne_of_gt (by omega)
      | simp

private theorem productionRemainder_decoder_cases
    (window : ActiveWindow)
    (hcount : intervalLaneCount window.start window.stop ≤ 259)
    {wire : Wire}
    (hwire : wire ∈ (intervalTree
      (indexedStepProductionRegisters.remainder window) window.start window.stop).decoderWires
        (indexedStepProductionRegisters.remainder window).control
        (indexedStepProductionRegisters.remainder window).control
        ((indexedStepProductionRegisters.remainder window).rightPaths
          window.start window.stop)
        ((indexedStepProductionRegisters.remainder window).leftPaths
          window.start window.stop)) :
    wire = 558 ∨
      (540 ≤ wire ∧ wire < 549 ∧
        (intervalHasTopSpecial window.start window.stop = true →
          wire ≠ (indexedStepProductionRegisters.remainder window).rightTop
            window.start window.stop)) ∨
      (531 ≤ wire ∧ wire < 540 ∧
        (intervalHasTopSpecial window.start window.stop = true →
          wire ≠ (indexedStepProductionRegisters.remainder window).leftTop
            window.start window.stop)) ∨
      (559 ≤ wire ∧ wire < 559 + 2 * intervalTreeDepth
        (indexedStepProductionRegisters.remainder window) window.start window.stop) := by
  let registers := indexedStepProductionRegisters.remainder window
  simp only [DualUnaryActionTree.decoderWires, List.mem_append,
    List.mem_dedup, List.mem_cons, List.not_mem_nil, or_false] at hwire
  rcases hwire with hcontrol | hindexA | hindexB | hright | hleft
  · left
    simpa [registers] using hcontrol
  · right; left
    obtain ⟨bit, hbit, heq⟩ := DualUnaryActionTree.build_indexAWires
      registers.rightIndex registers.leftIndex
      (DualUnaryActionTree.sourceWidth
        (intervalMainLabels window.start window.stop).toFinset)
      (intervalMainLabels window.start window.stop).toFinset
      (intervalTree registers window.start window.stop) (by
        simpa [DualUnaryActionTree.buildSourceFromList,
          DualUnaryActionTree.buildSource] using
            intervalTree_built registers window.start window.stop) hindexA
    have hbitNine : bit < 9 := lt_of_lt_of_le hbit
      (intervalSourceWidth_le_nine hcount)
    have hvalue := productionRemainder_rightIndex_eq window hbitNine
    have hwireEq : wire = 540 + bit := heq.trans hvalue
    refine ⟨?_, ?_, ?_⟩
    · rw [hwireEq]
      exact Nat.le_add_right 540 bit
    · rw [hwireEq]
      simpa only [Nat.add_comm] using Nat.add_lt_add_left hbitNine 540
    intro hspecial
    subst registers
    exact productionRemainder_indexA_ne_rightTop window hcount hspecial hindexA
  · right; right; left
    obtain ⟨bit, hbit, heq⟩ := DualUnaryActionTree.build_indexBWires
      registers.rightIndex registers.leftIndex
      (DualUnaryActionTree.sourceWidth
        (intervalMainLabels window.start window.stop).toFinset)
      (intervalMainLabels window.start window.stop).toFinset
      (intervalTree registers window.start window.stop) (by
        simpa [DualUnaryActionTree.buildSourceFromList,
          DualUnaryActionTree.buildSource] using
            intervalTree_built registers window.start window.stop) hindexB
    have hbitNine : bit < 9 := lt_of_lt_of_le hbit
      (intervalSourceWidth_le_nine hcount)
    have hvalue := productionRemainder_leftIndex_eq window hbitNine
    have hwireEq : wire = 531 + bit := heq.trans hvalue
    refine ⟨?_, ?_, ?_⟩
    · rw [hwireEq]
      exact Nat.le_add_right 531 bit
    · rw [hwireEq]
      simpa only [Nat.add_comm] using Nat.add_lt_add_left hbitNine 531
    intro hspecial
    subst registers
    exact productionRemainder_indexB_ne_leftTop window hcount hspecial hindexB
  · right; right; right
    rw [productionRemainder_rightPaths_eq window hcount] at hright
    have hrange := List.mem_range'_1.mp hright
    refine ⟨hrange.1, lt_of_lt_of_le hrange.2 ?_⟩
    apply Nat.add_le_add_left
    omega
  · right; right; right
    rw [productionRemainder_leftPaths_eq window hcount] at hleft
    have hrange := List.mem_range'_1.mp hleft
    refine ⟨le_trans (Nat.le_add_right 559 _) hrange.1, ?_⟩
    simpa only [two_mul, Nat.add_assoc] using hrange.2

private theorem productionRemainder_decoder_outside_roles
    (window : ActiveWindow) (label : Nat)
    (hstart : 1 ≤ window.start) (hkK : window.start ≤ window.stop)
    (hstop : window.stop ≤ 259)
    (hlabel : label < intervalLaneCount window.start window.stop) :
    DecoderOutsideIntervalRoles
      ((intervalTree (indexedStepProductionRegisters.remainder window)
        window.start window.stop).decoderWires
          (indexedStepProductionRegisters.remainder window).control
          (indexedStepProductionRegisters.remainder window).control
          ((indexedStepProductionRegisters.remainder window).rightPaths
            window.start window.stop)
          ((indexedStepProductionRegisters.remainder window).leftPaths
            window.start window.stop))
      ((indexedStepProductionRegisters.remainder window).rightTop
        window.start window.stop)
      ((indexedStepProductionRegisters.remainder window).leftTop
        window.start window.stop)
      ((indexedStepProductionRegisters.remainder window).accumulator
        window.start window.stop)
      ((indexedStepProductionRegisters.remainder window).targetAt .work1 label)
      ((indexedStepProductionRegisters.remainder window).addendAt .work1 label)
      ((indexedStepProductionRegisters.remainder window).carry
        window.start window.stop)
      ((indexedStepProductionRegisters.remainder window).cellScratch
        window.start window.stop) := by
  have hcount : intervalLaneCount window.start window.stop ≤ 259 := by
    simp only [intervalLaneCount]
    omega
  have htargetBound : window.start + label ≤ window.stop := by
    simp only [intervalLaneCount] at hlabel
    omega
  have hbase := productionRemainder_base_bounds window hcount
  rw [DecoderOutsideIntervalRoles, List.disjoint_left]
  intro wire hdecoder hrole
  have hcases := productionRemainder_decoder_cases window hcount hdecoder
  rw [productionRemainder_accumulator_eq window hcount,
    productionRemainder_targetAt_eq window label hstart hkK hstop hlabel,
    productionRemainder_addendAt_eq window label hstart hkK hstop hlabel,
    productionRemainder_carry_eq window hcount,
    productionRemainder_cellScratch_eq window hcount] at hrole
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrole
  dsimp only [Wire] at hcases hrole
  by_cases hspecial : intervalHasTopSpecial window.start window.stop = true
  · rw [productionRemainder_rightTop_eq window hcount hspecial,
      productionRemainder_leftTop_eq window hcount hspecial] at hrole
    have htop := intervalTopSpecial_topBit_lt_nine hcount hspecial
    rcases hcases with hcontrol | hindexA | hindexB | hpath
    · rcases hrole with hright | hleft | hacc | htarget | haddend | hcarry | hcell
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · have hne := hindexA.2.2 hspecial
      have hneNumeric : wire ≠ 540 + intervalTopBit window.start window.stop := by
        simpa only [productionRemainder_rightTop_eq window hcount hspecial] using hne
      rcases hrole with hright | hleft | hacc | htarget | haddend | hcarry | hcell
      · exact hneNumeric hright
      all_goals subst wire
      all_goals omega
    · have hne := hindexB.2.2 hspecial
      have hneNumeric : wire ≠ 531 + intervalTopBit window.start window.stop := by
        simpa only [productionRemainder_leftTop_eq window hcount hspecial] using hne
      rcases hrole with hright | hleft | hacc | htarget | haddend | hcarry | hcell
      · subst wire
        omega
      · exact hneNumeric hleft
      all_goals subst wire
      all_goals omega
    · rcases hrole with hright | hleft | hacc | htarget | haddend | hcarry | hcell <;>
        subst wire <;> omega
  · rw [IntervalRegisters.rightTop, if_neg hspecial,
      IntervalRegisters.leftTop, if_neg hspecial] at hrole
    have hrightTop :
        (indexedStepProductionRegisters.remainder window).lengthT.getD 0 0 = 522 := by
      rfl
    have hleftTop :
        (indexedStepProductionRegisters.remainder window).lengthT.getD 1 0 = 523 := by
      rfl
    rw [hrightTop, hleftTop] at hrole
    rcases hcases with hcontrol | hindexA | hindexB | hpath <;>
      rcases hrole with hright | hleft | hacc | htarget | haddend | hcarry | hcell <;>
      subst wire <;> omega

private theorem productionRemainder_endpoints_layout
    (window : ActiveWindow)
    (hcount : intervalLaneCount window.start window.stop ≤ 259) :
    IntervalEndpointLayout
      (indexedStepProductionRegisters.remainder window).lengthT
      (indexedStepProductionRegisters.remainder window).lengthQ
      (indexedStepProductionRegisters.remainder window).lengthS
      (indexedStepProductionRegisters.remainder window).endpointScratch
      ((indexedStepProductionRegisters.remainder window).carry
        window.start window.stop) := by
  rw [productionRemainder_endpointScratch_eq window hcount,
    productionRemainder_carry_eq window hcount]
  change IntervalEndpointLayout (List.range' 522 9) (List.range' 531 9)
    (List.range' 540 9) (List.range' 559 9)
    (559 + intervalScratchBase (indexedStepProductionRegisters.remainder window)
      window.start window.stop)
  rw [IntervalEndpointLayout, List.nodup_cons]
  constructor
  · intro hmem
    simp only [List.mem_append, List.mem_range'_1] at hmem
    have hbase := (productionRemainder_base_bounds window hcount).1
    rcases hmem with hmem | hmem | hmem | hmem <;> omega
  · decide

private theorem eqControlLayout_range
    (control registerStart scratchLength : Nat)
    (hregisterEnd : registerStart + 9 ≤ control)
    (hcontrolScratch : control < 559)
    (hscratchLength : 9 ≤ scratchLength) :
    EqControlLayout control (List.range' registerStart 9)
      (560 + scratchLength) (561 + scratchLength)
      (List.range' 559 scratchLength) := by
  rw [EqControlLayout]
  dsimp only [Wire] at *
  constructor
  · simp only [List.length_range']
    omega
  · apply List.nodup_cons.mpr
    constructor
    · intro hmem
      rcases List.mem_append.mp hmem with hleft | hright
      · rcases List.mem_cons.mp hleft with haccumulator | hregister
        · omega
        · have hregister := List.mem_range'_1.mp hregister
          omega
      · rcases List.mem_cons.mp hright with hflag | hscratch
        · omega
        · have hscratch := List.mem_range'_1.mp hscratch
          omega
    · apply List.nodup_cons.mpr
      constructor
      · intro hmem
        rcases List.mem_append.mp hmem with hregister | hright
        · have hregister := List.mem_range'_1.mp hregister
          omega
        · rcases List.mem_cons.mp hright with hflag | hscratch
          · omega
          · have hscratch := List.mem_range'_1.mp hscratch
            omega
      · apply List.nodup_append.mpr
        refine ⟨List.nodup_range', ?_, ?_⟩
        · apply List.nodup_cons.mpr
          constructor
          · intro hmem
            simp only [List.mem_range'_1] at hmem
            omega
          · exact List.nodup_range'
        · intro wire hregister other htail
          simp only [List.mem_range'_1] at hregister
          simp only [List.mem_cons, List.mem_range'_1] at htail
          rcases htail with htail | htail
          · subst other
            omega
          · intro equality
            omega

private theorem productionRemainder_right_eqControl_layout
    (window : ActiveWindow)
    (hcount : intervalLaneCount window.start window.stop ≤ 259) :
    EqControlLayout
      (indexedStepProductionRegisters.remainder window).control
      (indexedStepProductionRegisters.remainder window).lengthS
      ((indexedStepProductionRegisters.remainder window).accumulator
        window.start window.stop)
      ((indexedStepProductionRegisters.remainder window).cellScratch
        window.start window.stop)
      ((indexedStepProductionRegisters.remainder window).equalityScratch
        window.start window.stop) := by
  rw [productionRemainder_accumulator_eq window hcount,
    productionRemainder_cellScratch_eq window hcount,
    productionRemainder_equalityScratch_eq window hcount]
  rw [show (indexedStepProductionRegisters.remainder window).control = 558 by rfl,
    show (indexedStepProductionRegisters.remainder window).lengthS =
      List.range' 540 9 by rfl]
  exact eqControlLayout_range 558 540 _ (by decide) (by decide)
    (productionRemainder_base_bounds window hcount).1

private theorem productionRemainder_left_eqControl_layout
    (window : ActiveWindow)
    (hcount : intervalLaneCount window.start window.stop ≤ 259) :
    EqControlLayout
      (indexedStepProductionRegisters.remainder window).control
      (indexedStepProductionRegisters.remainder window).lengthQ
      ((indexedStepProductionRegisters.remainder window).accumulator
        window.start window.stop)
      ((indexedStepProductionRegisters.remainder window).cellScratch
        window.start window.stop)
      ((indexedStepProductionRegisters.remainder window).equalityScratch
        window.start window.stop) := by
  rw [productionRemainder_accumulator_eq window hcount,
    productionRemainder_cellScratch_eq window hcount,
    productionRemainder_equalityScratch_eq window hcount]
  rw [show (indexedStepProductionRegisters.remainder window).control = 558 by rfl,
    show (indexedStepProductionRegisters.remainder window).lengthQ =
      List.range' 531 9 by rfl]
  exact eqControlLayout_range 558 531 _ (by decide) (by decide)
    (productionRemainder_base_bounds window hcount).1

private theorem productionRemainder_topSpecial_layout
    (window : ActiveWindow)
    (hstart : 1 ≤ window.start) (hkK : window.start ≤ window.stop)
    (hstop : window.stop ≤ 259)
    (hspecial : intervalHasTopSpecial window.start window.stop = true) :
    TopSpecialLeafLayout
      (indexedStepProductionRegisters.remainder window).control
      (indexedStepProductionRegisters.remainder window).control
      (indexedStepProductionRegisters.remainder window).lengthS
      (indexedStepProductionRegisters.remainder window).lengthQ
      ((indexedStepProductionRegisters.remainder window).accumulator
        window.start window.stop)
      ((indexedStepProductionRegisters.remainder window).targetAt .work1
        (intervalTopRelative window.start window.stop))
      ((indexedStepProductionRegisters.remainder window).addendAt .work1
        (intervalTopRelative window.start window.stop))
      ((indexedStepProductionRegisters.remainder window).carry
        window.start window.stop)
      ((indexedStepProductionRegisters.remainder window).cellScratch
        window.start window.stop)
      ((indexedStepProductionRegisters.remainder window).cellScratch
        window.start window.stop)
      ((indexedStepProductionRegisters.remainder window).equalityScratch
        window.start window.stop) := by
  have hcount : intervalLaneCount window.start window.stop ≤ 259 := by
    simp only [intervalLaneCount]
    omega
  have hmore : 1 < intervalLaneCount window.start window.stop := by
    have hsource := of_decide_eq_true (show decide
      (1 < intervalLaneCount window.start window.stop ∧
        ((intervalLaneCount window.start window.stop - 1) &&&
          (intervalLaneCount window.start window.stop - 2)) = 0) = true by
        simpa [intervalHasTopSpecial] using hspecial)
    exact hsource.1
  have htopRelative : intervalTopRelative window.start window.stop <
      intervalLaneCount window.start window.stop := by
    simp only [intervalTopRelative]
    omega
  have htopAt : window.start + intervalTopRelative window.start window.stop =
      window.stop := by
    simp only [intervalTopRelative, intervalLaneCount]
    omega
  refine ⟨productionRemainder_right_eqControl_layout window hcount,
    productionRemainder_left_eqControl_layout window hcount, ?_, rfl, ?_⟩
  · have hall := productionRemainder_roles_nodup window
      (intervalTopRelative window.start window.stop) hstart hkK hstop htopRelative
    exact (List.nodup_cons.mp (List.nodup_cons.mp hall).2).2
  · rw [productionRemainder_equalityScratch_eq window hcount, List.disjoint_left]
    intro wire hscratch hrole
    have hscratchRange := List.mem_range'_1.mp hscratch
    have hbase := (productionRemainder_base_bounds window hcount).1
    rw [productionRemainder_accumulator_eq window hcount,
      productionRemainder_targetAt_eq window
        (intervalTopRelative window.start window.stop) hstart hkK hstop htopRelative,
      productionRemainder_addendAt_eq window
        (intervalTopRelative window.start window.stop) hstart hkK hstop htopRelative,
      productionRemainder_carry_eq window hcount,
      productionRemainder_cellScratch_eq window hcount] at hrole
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrole
    dsimp only [Wire] at hscratchRange hrole
    rcases hrole with haccumulator | htarget | haddend | hcarry | hcell <;>
      subst wire <;> omega

private theorem indexedStepProduction_remainder_layout_of_bounds
    (window : ActiveWindow)
    (hstart : 1 ≤ window.start) (hkK : window.start ≤ window.stop)
    (hstop : window.stop ≤ 259) :
    IntervalLayout (indexedStepProductionRegisters.remainder window)
      window.start window.stop .work1 := by
  let registers := indexedStepProductionRegisters.remainder window
  have hcount : intervalLaneCount window.start window.stop ≤ 259 := by
    simp only [intervalLaneCount]
    omega
  have hwidth : DualUnaryActionTree.sourceWidth
      (intervalMainLabels window.start window.stop).toFinset ≤ 9 :=
    intervalSourceWidth_le_nine hcount
  have hscratch : registers.scratch.length =
      intervalScratchBase registers window.start window.stop + 3 :=
    productionRemainder_scratch_length window hcount
  have hphysical : registers.allWires.Nodup :=
    indexedStepProduction_remainder_physical window
  refine {
    k_le_K := hkK
    work1_length := ?_
    work2_length := ?_
    lengthT_eq_lengthQ := by rfl
    lengthT_two_le := by
      change 2 ≤ (List.range' 522 9).length
      simp
    lengthS_two_le := by
      change 2 ≤ (List.range' 540 9).length
      simp
    right_index_capacity := by simpa [registers] using hwidth
    left_index_capacity := by simpa [registers] using hwidth
    right_top_capacity := ?_
    left_top_capacity := ?_
    scratch_length := hscratch
    physical := hphysical
    endpoints := productionRemainder_endpoints_layout window hcount
    traversal := ?_
    topSpecial := productionRemainder_topSpecial_layout window hstart hkK hstop }
  · change (IndexedStepRegisters.windowSlice (List.range' 4 259) window).length =
      intervalLaneCount window.start window.stop
    exact windowSlice_length 4 259 window hstart hkK hstop
  · change (IndexedStepRegisters.windowSlice (List.range' 263 259) window).length =
      intervalLaneCount window.start window.stop
    exact windowSlice_length 263 259 window hstart hkK hstop
  · intro hspecial
    simpa [registers] using intervalTopSpecial_topBit_lt_nine hcount hspecial
  · intro hspecial
    simpa [registers] using intervalTopSpecial_topBit_lt_nine hcount hspecial
  · refine ⟨intervalTree_layout_from_physical registers (by
        simpa [registers] using hwidth) (by
        simpa [registers] using hwidth) hscratch hphysical, ?_⟩
    intro label hlabel
    have hlabelBound := intervalTreeLabel_lt_laneCount registers hlabel
    exact ⟨productionRemainder_roles_nodup window label hstart hkK hstop hlabelBound,
      productionRemainder_decoder_outside_roles window label hstart hkK hstop hlabelBound⟩

private theorem quotientSwapSourceWidth_le_nine
    {k K : Nat} (hK : K ≤ 259) :
    DualUnaryActionTree.sourceWidth (quotientSwapLabels k K).toFinset ≤ 9 := by
  apply DualUnaryActionTree.sourceWidth_le _ 9 (by decide)
  intro label hlabel
  have hmem : label ∈ quotientSwapLabels k K := by simpa using hlabel
  simp only [quotientSwapLabels, List.mem_range'_1] at hmem
  norm_num
  omega

private theorem quotientSwapUnaryDepth_le_ten
    {k K : Nat} (hk : 1 ≤ k) (hK : K ≤ 259) :
    quotientSwapUnaryDepth k K ≤ 10 := by
  simp only [quotientSwapUnaryDepth]
  split
  · omega
  · have hbound : K - k + 1 - 1 ≤ 258 := by omega
    have hclog := Nat.clog_mono_right 2 hbound
    rw [show Nat.clog 2 258 = 9 by decide] at hclog
    omega

private theorem indexedStepProduction_quotient_layout_of_bounds
    (window : ActiveWindow)
    (hstart : 1 ≤ window.start) (hkK : window.start ≤ window.stop)
    (hstop : window.stop ≤ 259) :
    QuotientSwapLayout (indexedStepProductionRegisters.quotient window)
      window.start window.stop := by
  let registers := indexedStepProductionRegisters.quotient window
  have hwidth : DualUnaryActionTree.sourceWidth
      (quotientSwapLabels window.start window.stop).toFinset ≤ 9 :=
    quotientSwapSourceWidth_le_nine hstop
  have hdepth : quotientSwapUnaryDepth window.start window.stop ≤ 10 :=
    quotientSwapUnaryDepth_le_ten hstart hstop
  have hscratch : registers.scratch.length = registers.scratchBase
      window.start window.stop + 1 := by
    change ((List.range' 560 18).take
      (max 9 (quotientSwapUnaryDepth window.start window.stop) + 1)).length = _
    simp only [List.length_take, List.length_range']
    rw [Nat.min_eq_left]
    · rfl
    · omega
  have hphysical : registers.allWires.Nodup :=
    indexedStepProduction_quotient_physical window
  exact {
    k_le_K := hkK
    work1_length := by
      change (IndexedStepRegisters.windowSlice (List.range' 4 259) window).length =
        window.stop - window.start + 1
      simpa only [intervalLaneCount] using
        windowSlice_length 4 259 window hstart hkK hstop
    lengthT_eq_lengthQ := by rfl
    index_width := by simpa [registers] using hwidth
    scratch_length := hscratch
    physical := hphysical
    tree := quotientSwapTree_layout_from_physical registers hkK (by
      simpa [registers] using hwidth) hscratch hphysical }

private theorem indexedStepProduction_coefficient_layout_of_bounds
    (window : ActiveWindow)
    (hstart : 1 ≤ window.start) (hkK : window.start ≤ window.stop)
    (hstop : window.stop ≤ 259) :
    CoefficientPrefixLayout (indexedStepProductionRegisters.coefficient window)
      window.start window.stop := by
  let registers := indexedStepProductionRegisters.coefficient window
  have hwidth : DualUnaryActionTree.sourceWidth
      (quotientSwapLabels window.start window.stop).toFinset ≤ 9 :=
    quotientSwapSourceWidth_le_nine hstop
  have hdepth : quotientSwapUnaryDepth window.start window.stop ≤ 10 :=
    quotientSwapUnaryDepth_le_ten hstart hstop
  have hscratch : registers.scratch.length = registers.scratchBase
      window.start window.stop + 3 := by
    change ((List.range' 561 17).take
      (max (quotientSwapUnaryDepth window.start window.stop) 9 + 3)).length = _
    simp only [List.length_take, List.length_range']
    rw [Nat.min_eq_left]
    · rfl
    · omega
  have hphysical : registers.allWires.Nodup :=
    indexedStepProduction_coefficient_physical window
  exact {
    k_le_K := hkK
    work1_length := by
      change (IndexedStepRegisters.windowSlice (List.range' 4 259) window).length =
        window.stop - window.start + 1
      simpa only [intervalLaneCount] using
        windowSlice_length 4 259 window hstart hkK hstop
    work2_length := by
      change (IndexedStepRegisters.windowSlice (List.range' 263 259) window).length =
        window.stop - window.start + 1
      simpa only [intervalLaneCount] using
        windowSlice_length 263 259 window hstart hkK hstop
    index_width := by simpa [registers] using hwidth
    scratch_length := hscratch
    physical := hphysical
    tree := coefficientPrefixTree_layout_from_physical registers hkK (by
      simpa [registers] using hwidth) hscratch hphysical }

/-! ## Uniform production end-of-iteration geometry -/

private def productionEndRegisters (T : Nat) : EndIterationRegisters :=
  indexedStepProductionRegisters.endIteration 256 T

private def productionEndTreeRegisters (index : List Wire) : QuotientSwapRegisters where
  control := 0
  sign := 0
  work1 := []
  lengthT := []
  lengthQ := index
  scratch := []

private theorem productionEnd_upperTree_eq (T : Nat) (windows : EndIterationWindows) :
    (productionEndRegisters T).upperTree windows =
      quotientSwapTree (productionEndTreeRegisters
        (productionEndRegisters T).lengthRP) windows.k4 windows.K4 := by
  rfl

private theorem productionEnd_lowerTree_eq (T : Nat) (windows : EndIterationWindows) :
    (productionEndRegisters T).lowerTree 256 windows =
      quotientSwapTree (productionEndTreeRegisters
        (productionEndRegisters T).lengthT) windows.k5 (windows.K5Decode 256) := by
  rfl

private theorem productionEnd_scratchSize_le_twelve
    (T : Nat)
    (hk4 : 1 ≤ (endIterationWindowsAt 256 T).k4)
    (hK4 : (endIterationWindowsAt 256 T).K4 ≤ 259)
    (hk5 : 1 ≤ (endIterationWindowsAt 256 T).k5)
    (hK5 : (endIterationWindowsAt 256 T).K5Decode 256 ≤ 259) :
    endIterationScratchSize (productionEndRegisters T) 256
      (endIterationWindowsAt 256 T) ≤ 12 := by
  have hupper := quotientSwapUnaryDepth_le_ten hk4 hK4
  have hlower := quotientSwapUnaryDepth_le_ten hk5 hK5
  change max
    (max 10 (quotientSwapUnaryDepth (endIterationWindowsAt 256 T).k4
      (endIterationWindowsAt 256 T).K4 + 2))
    (max 10 (quotientSwapUnaryDepth (endIterationWindowsAt 256 T).k5
      ((endIterationWindowsAt 256 T).K5Decode 256) + 2)) ≤ 12
  omega

private theorem productionEnd_ten_le_scratchSize (T : Nat) :
    10 ≤ endIterationScratchSize (productionEndRegisters T) 256
      (endIterationWindowsAt 256 T) := by
  change 10 ≤ max
    (max 10 (quotientSwapUnaryDepth (endIterationWindowsAt 256 T).k4
      (endIterationWindowsAt 256 T).K4 + 2))
    (max 10 (quotientSwapUnaryDepth (endIterationWindowsAt 256 T).k5
      ((endIterationWindowsAt 256 T).K5Decode 256) + 2))
  omega

private theorem productionEnd_scratch_eq
    (T : Nat)
    (hk4 : 1 ≤ (endIterationWindowsAt 256 T).k4)
    (hK4 : (endIterationWindowsAt 256 T).K4 ≤ 259)
    (hk5 : 1 ≤ (endIterationWindowsAt 256 T).k5)
    (hK5 : (endIterationWindowsAt 256 T).K5Decode 256 ≤ 259) :
    (productionEndRegisters T).scratch =
      List.range' 562 (endIterationScratchSize (productionEndRegisters T) 256
        (endIterationWindowsAt 256 T)) := by
  have hsize := productionEnd_scratchSize_le_twelve T hk4 hK4 hk5 hK5
  change (List.range' 562 16).take
      (endIterationScratchSize (productionEndRegisters T) 256
        (endIterationWindowsAt 256 T)) = _
  exact take_range'_eq 562 16 _ (by omega)

private theorem productionEnd_path_eq
    (T k K : Nat)
    (hk4 : 1 ≤ (endIterationWindowsAt 256 T).k4)
    (hK4 : (endIterationWindowsAt 256 T).K4 ≤ 259)
    (hk5 : 1 ≤ (endIterationWindowsAt 256 T).k5)
    (hK5 : (endIterationWindowsAt 256 T).K5Decode 256 ≤ 259)
    (hfit : quotientSwapUnaryDepth k K ≤
      endIterationScratchSize (productionEndRegisters T) 256
        (endIterationWindowsAt 256 T)) :
    (productionEndRegisters T).path k K =
      List.range' 562 (quotientSwapUnaryDepth k K) := by
  rw [EndIterationRegisters.path,
    productionEnd_scratch_eq T hk4 hK4 hk5 hK5]
  exact take_range'_eq 562 _ _ hfit

private theorem productionEnd_range_eq
    (T k K : Nat)
    (hk4 : 1 ≤ (endIterationWindowsAt 256 T).k4)
    (hK4 : (endIterationWindowsAt 256 T).K4 ≤ 259)
    (hk5 : 1 ≤ (endIterationWindowsAt 256 T).k5)
    (hK5 : (endIterationWindowsAt 256 T).K5Decode 256 ≤ 259)
    (hfit : quotientSwapUnaryDepth k K + 2 ≤
      endIterationScratchSize (productionEndRegisters T) 256
        (endIterationWindowsAt 256 T)) :
    (productionEndRegisters T).rangeAccumulator k K =
      562 + quotientSwapUnaryDepth k K := by
  rw [EndIterationRegisters.rangeAccumulator, endIterationUnaryDepth,
    productionEnd_scratch_eq T hk4 hK4 hk5 hK5,
    List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range'_1]

private theorem productionEnd_temporary_eq
    (T k K : Nat)
    (hk4 : 1 ≤ (endIterationWindowsAt 256 T).k4)
    (hK4 : (endIterationWindowsAt 256 T).K4 ≤ 259)
    (hk5 : 1 ≤ (endIterationWindowsAt 256 T).k5)
    (hK5 : (endIterationWindowsAt 256 T).K5Decode 256 ≤ 259)
    (hfit : quotientSwapUnaryDepth k K + 2 ≤
      endIterationScratchSize (productionEndRegisters T) 256
        (endIterationWindowsAt 256 T)) :
    (productionEndRegisters T).temporary k K =
      563 + quotientSwapUnaryDepth k K := by
  rw [EndIterationRegisters.temporary, endIterationUnaryDepth,
    productionEnd_scratch_eq T hk4 hK4 hk5 hK5,
    List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range'_1]
  ring

private theorem productionEnd_constants_eq
    (T : Nat)
    (hk4 : 1 ≤ (endIterationWindowsAt 256 T).k4)
    (hK4 : (endIterationWindowsAt 256 T).K4 ≤ 259)
    (hk5 : 1 ≤ (endIterationWindowsAt 256 T).k5)
    (hK5 : (endIterationWindowsAt 256 T).K5Decode 256 ≤ 259) :
    (productionEndRegisters T).constants = List.range' 562 9 := by
  rw [EndIterationRegisters.constants,
    productionEnd_scratch_eq T hk4 hK4 hk5 hK5]
  change (List.range' 562
    (endIterationScratchSize (productionEndRegisters T) 256
      (endIterationWindowsAt 256 T))).take 9 = _
  exact take_range'_eq 562 _ 9 (productionEnd_ten_le_scratchSize T |>.trans' (by decide))

private theorem productionEnd_carry_eq
    (T : Nat)
    (hk4 : 1 ≤ (endIterationWindowsAt 256 T).k4)
    (hK4 : (endIterationWindowsAt 256 T).K4 ≤ 259)
    (hk5 : 1 ≤ (endIterationWindowsAt 256 T).k5)
    (hK5 : (endIterationWindowsAt 256 T).K5Decode 256 ≤ 259) :
    (productionEndRegisters T).carry = 571 := by
  rw [EndIterationRegisters.carry,
    productionEnd_scratch_eq T hk4 hK4 hk5 hK5]
  change (List.range' 562
    (endIterationScratchSize (productionEndRegisters T) 256
      (endIterationWindowsAt 256 T))).getD 9 0 = 571
  rw [List.getD_eq_getElem _ 0 (by
    simp only [List.length_range']
    exact lt_of_lt_of_le (by decide) (productionEnd_ten_le_scratchSize T)),
    List.getElem_range'_1]

private theorem productionEnd_work1At
    (T : Nat) {label : Nat} (hlow : 0 < label) (hhigh : label ≤ 259) :
    (productionEndRegisters T).work1At label = label + 3 := by
  change (List.range' 4 259).getD (label - 1) 0 = label + 3
  rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range'_1]
  omega

private theorem productionEnd_work2At
    (T : Nat) {label : Nat} (hlow : 0 < label) (hhigh : label ≤ 259) :
    (productionEndRegisters T).work2At label = 262 + label := by
  change (List.range' 263 259).getD (label - 1) 0 = 262 + label
  rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range'_1]
  omega

private theorem productionEnd_cell12
    (T : Nat) {k K label : Nat} {range temporary guard : Wire}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259)
    (hlabel : label ∈ zeroMapLabels k K)
    (hrangeLow : 562 ≤ range) (htemporaryLow : 562 ≤ temporary)
    (hrangeTemporary : range ≠ temporary)
    (hguard : guard = 558 ∨
      ∃ neighbour ∈ zeroMapLabels k K, neighbour ≠ label ∧
        guard = (productionEndRegisters T).work2At neighbour) :
    [range, (productionEndRegisters T).work1At label, guard,
      (productionEndRegisters T).work2At label, temporary].Nodup := by
  obtain ⟨hlabelLow, hlabelHigh⟩ := (mem_zeroMapLabels hkK).mp hlabel
  have hlabelPositive : 0 < label := lt_of_lt_of_le hkPositive hlabelLow
  have hlabelBound : label ≤ 259 := hlabelHigh.trans hK
  rw [productionEnd_work1At T hlabelPositive hlabelBound,
    productionEnd_work2At T hlabelPositive hlabelBound]
  rcases hguard with rfl | ⟨neighbour, hneighbour, hne, rfl⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_or, not_false_eq_true, and_true]
    dsimp only [Wire] at *
    repeat' apply And.intro
    all_goals omega
  · obtain ⟨hneighbourLow, hneighbourHigh⟩ := (mem_zeroMapLabels hkK).mp hneighbour
    rw [productionEnd_work2At T (lt_of_lt_of_le hkPositive hneighbourLow)
      (hneighbourHigh.trans hK)]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_or, not_false_eq_true, and_true]
    dsimp only [Wire] at *
    repeat' apply And.intro
    all_goals omega

private theorem productionEnd_cell21
    (T : Nat) {k K label : Nat} {range temporary guard : Wire}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259)
    (hlabel : label ∈ zeroMapLabels k K)
    (hrangeLow : 562 ≤ range) (htemporaryLow : 562 ≤ temporary)
    (hrangeTemporary : range ≠ temporary)
    (hguard : guard = 558 ∨
      ∃ neighbour ∈ zeroMapLabels k K, neighbour ≠ label ∧
        guard = (productionEndRegisters T).work1At neighbour) :
    [range, (productionEndRegisters T).work2At label, guard,
      (productionEndRegisters T).work1At label, temporary].Nodup := by
  obtain ⟨hlabelLow, hlabelHigh⟩ := (mem_zeroMapLabels hkK).mp hlabel
  have hlabelPositive : 0 < label := lt_of_lt_of_le hkPositive hlabelLow
  have hlabelBound : label ≤ 259 := hlabelHigh.trans hK
  rw [productionEnd_work1At T hlabelPositive hlabelBound,
    productionEnd_work2At T hlabelPositive hlabelBound]
  rcases hguard with rfl | ⟨neighbour, hneighbour, hne, rfl⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_or, not_false_eq_true, and_true]
    dsimp only [Wire] at *
    repeat' apply And.intro
    all_goals omega
  · obtain ⟨hneighbourLow, hneighbourHigh⟩ := (mem_zeroMapLabels hkK).mp hneighbour
    rw [productionEnd_work1At T (lt_of_lt_of_le hkPositive hneighbourLow)
      (hneighbourHigh.trans hK)]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_or, not_false_eq_true, and_true]
    dsimp only [Wire] at *
    repeat' apply And.intro
    all_goals omega

private theorem productionEnd_work1_map_nodup
    (T : Nat) {k K : Nat}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259) :
    ((zeroMapLabels k K).map (productionEndRegisters T).work1At).Nodup := by
  apply (zeroMapLabels_nodup k K).map_on
  intro left hleft right hright heq
  obtain ⟨hleftLow, hleftHigh⟩ := (mem_zeroMapLabels hkK).mp hleft
  obtain ⟨hrightLow, hrightHigh⟩ := (mem_zeroMapLabels hkK).mp hright
  rw [productionEnd_work1At T (lt_of_lt_of_le hkPositive hleftLow)
      (hleftHigh.trans hK),
    productionEnd_work1At T (lt_of_lt_of_le hkPositive hrightLow)
      (hrightHigh.trans hK)] at heq
  exact Nat.add_right_cancel heq

private theorem productionEnd_work2_map_nodup
    (T : Nat) {k K : Nat}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259) :
    ((zeroMapLabels k K).map (productionEndRegisters T).work2At).Nodup := by
  apply (zeroMapLabels_nodup k K).map_on
  intro left hleft right hright heq
  obtain ⟨hleftLow, hleftHigh⟩ := (mem_zeroMapLabels hkK).mp hleft
  obtain ⟨hrightLow, hrightHigh⟩ := (mem_zeroMapLabels hkK).mp hright
  rw [productionEnd_work2At T (lt_of_lt_of_le hkPositive hleftLow)
      (hleftHigh.trans hK),
    productionEnd_work2At T (lt_of_lt_of_le hkPositive hrightLow)
      (hrightHigh.trans hK)] at heq
  exact Nat.add_left_cancel heq

private theorem productionEnd_work_maps_disjoint
    (T : Nat) {k K : Nat}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259) :
    List.Disjoint ((zeroMapLabels k K).map (productionEndRegisters T).work1At)
      ((zeroMapLabels k K).map (productionEndRegisters T).work2At) := by
  apply List.disjoint_left.mpr
  intro wire hwork1 hwork2
  obtain ⟨label1, hlabel1, heq1⟩ := List.mem_map.mp hwork1
  obtain ⟨label2, hlabel2, heq2⟩ := List.mem_map.mp hwork2
  obtain ⟨hlabel1Low, hlabel1High⟩ := (mem_zeroMapLabels hkK).mp hlabel1
  obtain ⟨hlabel2Low, hlabel2High⟩ := (mem_zeroMapLabels hkK).mp hlabel2
  rw [productionEnd_work1At T (lt_of_lt_of_le hkPositive hlabel1Low)
      (hlabel1High.trans hK)] at heq1
  rw [productionEnd_work2At T (lt_of_lt_of_le hkPositive hlabel2Low)
      (hlabel2High.trans hK)] at heq2
  subst wire
  have hlt : label1 + 3 < 262 + label2 := by omega
  exact hlt.ne heq2.symm

private theorem productionEnd_work_maps_nodup
    (T : Nat) {k K : Nat}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259) :
    (((zeroMapLabels k K).map (productionEndRegisters T).work1At) ++
      (zeroMapLabels k K).map (productionEndRegisters T).work2At).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨productionEnd_work1_map_nodup T hkPositive hkK hK,
    productionEnd_work2_map_nodup T hkPositive hkK hK, ?_⟩
  intro left hleft right hright heq
  subst right
  exact List.disjoint_left.mp (productionEnd_work_maps_disjoint T hkPositive hkK hK)
    hleft hright

private theorem productionEnd_work_map_bounds
    (T : Nat) {k K wire : Nat}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259)
    (hwire : wire ∈
      ((zeroMapLabels k K).map (productionEndRegisters T).work1At) ++
        (zeroMapLabels k K).map (productionEndRegisters T).work2At) :
    4 ≤ wire ∧ wire ≤ 521 := by
  rcases List.mem_append.mp hwire with hwork1 | hwork2
  · obtain ⟨label, hlabel, rfl⟩ := List.mem_map.mp hwork1
    obtain ⟨hlabelLow, hlabelHigh⟩ := (mem_zeroMapLabels hkK).mp hlabel
    rw [productionEnd_work1At T (lt_of_lt_of_le hkPositive hlabelLow)
      (hlabelHigh.trans hK)]
    omega
  · obtain ⟨label, hlabel, rfl⟩ := List.mem_map.mp hwork2
    obtain ⟨hlabelLow, hlabelHigh⟩ := (mem_zeroMapLabels hkK).mp hlabel
    rw [productionEnd_work2At T (lt_of_lt_of_le hkPositive hlabelLow)
      (hlabelHigh.trans hK)]
    omega

private theorem productionEnd_zeroMap_tail_nodup
    (T : Nat) {k K : Nat} {range temporary : Wire}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259)
    (hrangeLow : 562 ≤ range) (htemporaryLow : 562 ≤ temporary)
    (hrangeTemporary : range ≠ temporary) :
    (range :: temporary ::
      (zeroMapLabels k K).map (productionEndRegisters T).work1At ++
      (zeroMapLabels k K).map (productionEndRegisters T).work2At).Nodup := by
  change (range :: temporary ::
    ((zeroMapLabels k K).map (productionEndRegisters T).work1At ++
      (zeroMapLabels k K).map (productionEndRegisters T).work2At)).Nodup
  rw [List.nodup_cons, List.nodup_cons]
  constructor
  · intro hmem
    rcases List.mem_cons.mp hmem with heq | hwork
    · exact hrangeTemporary heq
    · exact (not_lt_of_ge hrangeLow)
        ((productionEnd_work_map_bounds T hkPositive hkK hK hwork).2.trans_lt (by decide))
  · constructor
    · intro hwork
      exact (not_lt_of_ge htemporaryLow)
        ((productionEnd_work_map_bounds T hkPositive hkK hK hwork).2.trans_lt (by decide))
    · exact productionEnd_work_maps_nodup T hkPositive hkK hK

private theorem productionEnd_zeroMap_tail_reverse_nodup
    (T : Nat) {k K : Nat} {range temporary : Wire}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259)
    (hrangeLow : 562 ≤ range) (htemporaryLow : 562 ≤ temporary)
    (hrangeTemporary : range ≠ temporary) :
    (range :: temporary ::
      (zeroMapLabels k K).map (productionEndRegisters T).work2At ++
      (zeroMapLabels k K).map (productionEndRegisters T).work1At).Nodup := by
  change (range :: temporary ::
    ((zeroMapLabels k K).map (productionEndRegisters T).work2At ++
      (zeroMapLabels k K).map (productionEndRegisters T).work1At)).Nodup
  rw [List.nodup_cons, List.nodup_cons]
  constructor
  · intro hmem
    rcases List.mem_cons.mp hmem with heq | hwork
    · exact hrangeTemporary heq
    · have hwork' : range ∈
          ((zeroMapLabels k K).map (productionEndRegisters T).work1At) ++
            (zeroMapLabels k K).map (productionEndRegisters T).work2At := by
        rcases List.mem_append.mp hwork with hwork2 | hwork1
        · exact List.mem_append.mpr (Or.inr hwork2)
        · exact List.mem_append.mpr (Or.inl hwork1)
      exact (not_lt_of_ge hrangeLow)
        ((productionEnd_work_map_bounds T hkPositive hkK hK hwork').2.trans_lt (by decide))
  · constructor
    · intro hwork
      have hwork' : temporary ∈
          ((zeroMapLabels k K).map (productionEndRegisters T).work1At) ++
            (zeroMapLabels k K).map (productionEndRegisters T).work2At := by
        rcases List.mem_append.mp hwork with hwork2 | hwork1
        · exact List.mem_append.mpr (Or.inr hwork2)
        · exact List.mem_append.mpr (Or.inl hwork1)
      exact (not_lt_of_ge htemporaryLow)
        ((productionEnd_work_map_bounds T hkPositive hkK hK hwork').2.trans_lt (by decide))
    · apply List.nodup_append.mpr
      refine ⟨productionEnd_work2_map_nodup T hkPositive hkK hK,
        productionEnd_work1_map_nodup T hkPositive hkK hK, ?_⟩
      intro left hleft right hright heq
      subst right
      exact List.disjoint_left.mp
        (productionEnd_work_maps_disjoint T hkPositive hkK hK) hright hleft

private theorem productionEnd_protected_tail_disjoint
    (T : Nat) {k K : Nat} {tree : UnaryActionTree} {path : List Wire}
    {range temporary : Wire}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259)
    (hindex : ∀ wire ∈ tree.indexWires, 522 ≤ wire ∧ wire ≤ 557)
    (hpath : ∀ wire ∈ path, 562 ≤ wire ∧ wire < range)
    (hrangeLow : 562 ≤ range) (hrangeTemporary : range < temporary) :
    ∀ left ∈ zeroMapProtectedWires tree 558 path,
      ∀ right ∈ range :: temporary ::
        ((zeroMapLabels k K).map (productionEndRegisters T).work1At ++
          (zeroMapLabels k K).map (productionEndRegisters T).work2At),
        left ≠ right := by
  intro left hleft right hright
  have hleftClass : left = 558 ∨
      (522 ≤ left ∧ left ≤ 557) ∨
      (562 ≤ left ∧ left < range) := by
    rw [zeroMapProtectedWires] at hleft
    rcases List.mem_cons.mp hleft with rfl | hdecoder
    · exact Or.inl rfl
    rcases List.mem_append.mp hdecoder with hindexWire | hpathWire
    · exact Or.inr (Or.inl
        (hindex left (List.mem_dedup.mp hindexWire)))
    · exact Or.inr (Or.inr (hpath left hpathWire))
  have hrightClass : right = range ∨ right = temporary ∨
      (4 ≤ right ∧ right ≤ 521) := by
    have hright' : right ∈ range :: temporary ::
        (((zeroMapLabels k K).map (productionEndRegisters T).work1At) ++
          (zeroMapLabels k K).map (productionEndRegisters T).work2At) := by
      simpa using hright
    rcases List.mem_cons.mp hright' with rfl | hright'
    · exact Or.inl rfl
    rcases List.mem_cons.mp hright' with rfl | hwork
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr
        (productionEnd_work_map_bounds T hkPositive hkK hK hwork))
  intro heq
  subst right
  rcases hleftClass with hcontrol | hindexWire | hpathWire
  · subst left
    rcases hrightClass with hrange | htemporary | hwork <;>
      dsimp only [Wire] at * <;> omega
  · rcases hrightClass with hrange | htemporary | hwork <;>
      dsimp only [Wire] at * <;> omega
  · rcases hrightClass with hrange | htemporary | hwork <;>
      dsimp only [Wire] at * <;> omega

private theorem productionEnd_protected_tail_reverse_disjoint
    (T : Nat) {k K : Nat} {tree : UnaryActionTree} {path : List Wire}
    {range temporary : Wire}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259)
    (hindex : ∀ wire ∈ tree.indexWires, 522 ≤ wire ∧ wire ≤ 557)
    (hpath : ∀ wire ∈ path, 562 ≤ wire ∧ wire < range)
    (hrangeLow : 562 ≤ range) (hrangeTemporary : range < temporary) :
    ∀ left ∈ zeroMapProtectedWires tree 558 path,
      ∀ right ∈ range :: temporary ::
        ((zeroMapLabels k K).map (productionEndRegisters T).work2At ++
          (zeroMapLabels k K).map (productionEndRegisters T).work1At),
        left ≠ right := by
  intro left hleft right hright
  apply productionEnd_protected_tail_disjoint T hkPositive hkK hK hindex hpath
    hrangeLow hrangeTemporary left hleft right
  have hright' : right ∈ range :: temporary ::
      (((zeroMapLabels k K).map (productionEndRegisters T).work2At) ++
        (zeroMapLabels k K).map (productionEndRegisters T).work1At) := by
    simpa using hright
  rcases List.mem_cons.mp hright' with rfl | hright'
  · simp
  rcases List.mem_cons.mp hright' with rfl | hwork
  · simp
  have : right ∈ range :: temporary ::
      (((zeroMapLabels k K).map (productionEndRegisters T).work1At) ++
        (zeroMapLabels k K).map (productionEndRegisters T).work2At) := by
    simp only [List.mem_cons]
    apply Or.inr
    apply Or.inr
    rcases List.mem_append.mp hwork with hwork2 | hwork1
    · exact List.mem_append.mpr (Or.inr hwork2)
    · exact List.mem_append.mpr (Or.inl hwork1)
  simpa using this

private theorem productionEnd_target_disjoint
    {k K : Nat} {tree : UnaryActionTree} {path targets : List Wire}
    {range temporary : Wire} {firstAt secondAt : Nat → Wire}
    (htargetBounds : ∀ wire ∈ targets, 522 ≤ wire ∧ wire ≤ 557)
    (htargetIndex : ∀ wire ∈ targets, wire ∉ tree.indexWires)
    (hpathLow : ∀ wire ∈ path, 562 ≤ wire)
    (hrangeLow : 562 ≤ range) (htemporaryLow : 562 ≤ temporary)
    (hwork : ∀ wire ∈
      ((zeroMapLabels k K).map firstAt) ++
        (zeroMapLabels k K).map secondAt,
      4 ≤ wire ∧ wire ≤ 521) :
    List.Disjoint targets
      (zeroMapWires k K tree 558 range temporary path firstAt secondAt) := by
  apply List.disjoint_left.mpr
  intro wire htarget hzeroMap
  obtain ⟨htargetLow, htargetHigh⟩ := htargetBounds wire htarget
  simp only [zeroMapWires, zeroMapProtectedWires, List.mem_append,
    List.mem_cons, List.mem_dedup, List.mem_map] at hzeroMap
  rcases hzeroMap with hmain | ⟨label, hlabel, heq⟩
  · rcases hmain with hprotected | hrange | htemporary |
        ⟨label, hlabel, heq⟩
    · rcases hprotected with hdecoder | hpath
      · rcases hdecoder with hcontrol | hindex
        · dsimp only [Wire] at *
          omega
        · exact htargetIndex wire htarget hindex
      · have hpathBound := hpathLow wire hpath
        dsimp only [Wire] at *
        omega
    · dsimp only [Wire] at *
      omega
    · dsimp only [Wire] at *
      omega
    · have hmaps : wire ∈
          ((zeroMapLabels k K).map firstAt) ++
            (zeroMapLabels k K).map secondAt := by
        apply List.mem_append.mpr
        exact Or.inl (List.mem_map.mpr ⟨label, hlabel, heq⟩)
      obtain ⟨hworkLow, hworkHigh⟩ := hwork wire hmaps
      dsimp only [Wire] at *
      omega
  · have hmaps : wire ∈
        ((zeroMapLabels k K).map firstAt) ++
          (zeroMapLabels k K).map secondAt := by
      apply List.mem_append.mpr
      exact Or.inr (List.mem_map.mpr ⟨label, hlabel, heq⟩)
    obtain ⟨hworkLow, hworkHigh⟩ := hwork wire hmaps
    dsimp only [Wire] at *
    omega

private theorem productionEnd_nonAffine_disjoint
    (T : Nat) {k K : Nat} {path affineRegister target : List Wire}
    {range temporary : Wire}
    (haffineBounds : ∀ wire ∈ affineRegister,
      522 ≤ wire ∧ wire ≤ 557)
    (haffineTarget : List.Disjoint affineRegister target)
    (hpathLow : ∀ wire ∈ path, 562 ≤ wire)
    (hrangeLow : 562 ≤ range) (htemporaryLow : 562 ≤ temporary)
    (hwork : ∀ wire ∈
      ((zeroMapLabels k K).map (productionEndRegisters T).work1At) ++
        (zeroMapLabels k K).map (productionEndRegisters T).work2At,
      4 ≤ wire ∧ wire ≤ 521) :
    List.Disjoint affineRegister
      (lengthBlockNonAffineSupport k K 558 range temporary path
        (productionEndRegisters T).work1At (productionEndRegisters T).work2At target) := by
  apply List.disjoint_left.mpr
  intro wire haffine hsupport
  obtain ⟨haffineLow, haffineHigh⟩ := haffineBounds wire haffine
  simp only [lengthBlockNonAffineSupport, List.mem_append, List.mem_cons,
    List.mem_map] at hsupport
  rcases hsupport with hmain | ⟨label, hlabel, heq⟩
  · rcases hmain with hprefix | hrange | htemporary |
        ⟨label, hlabel, heq⟩
    · rcases hprefix with htarget | hcontrol | hpath
      · exact List.disjoint_left.mp haffineTarget haffine htarget
      · dsimp only [Wire] at *
        omega
      · have hpathBound := hpathLow wire hpath
        dsimp only [Wire] at *
        omega
    · dsimp only [Wire] at *
      omega
    · dsimp only [Wire] at *
      omega
    · have hmaps : wire ∈
          ((zeroMapLabels k K).map (productionEndRegisters T).work1At) ++
            (zeroMapLabels k K).map (productionEndRegisters T).work2At := by
        apply List.mem_append.mpr
        exact Or.inl (List.mem_map.mpr ⟨label, hlabel, heq⟩)
      obtain ⟨hworkLow, hworkHigh⟩ := hwork wire hmaps
      dsimp only [Wire] at *
      omega
  · have hmaps : wire ∈
        ((zeroMapLabels k K).map (productionEndRegisters T).work1At) ++
          (zeroMapLabels k K).map (productionEndRegisters T).work2At := by
      apply List.mem_append.mpr
      exact Or.inr (List.mem_map.mpr ⟨label, hlabel, heq⟩)
    obtain ⟨hworkLow, hworkHigh⟩ := hwork wire hmaps
    dsimp only [Wire] at *
    omega

private theorem productionEnd_constantCarry_target_disjoint
    (T : Nat)
    (hk4 : 1 ≤ (endIterationWindowsAt 256 T).k4)
    (hK4 : (endIterationWindowsAt 256 T).K4 ≤ 259)
    (hk5 : 1 ≤ (endIterationWindowsAt 256 T).k5)
    (hK5 : (endIterationWindowsAt 256 T).K5Decode 256 ≤ 259)
    {target : List Wire}
    (htarget : ∀ wire ∈ target, wire ≤ 557) :
    List.Disjoint
      ((productionEndRegisters T).constants ++ [(productionEndRegisters T).carry]) target := by
  apply List.disjoint_left.mpr
  intro wire hscratch htargetMem
  have htargetBound := htarget wire htargetMem
  rw [productionEnd_constants_eq T hk4 hK4 hk5 hK5,
    productionEnd_carry_eq T hk4 hK4 hk5 hK5] at hscratch
  simp only [List.mem_append, List.mem_singleton] at hscratch
  rcases hscratch with hconstant | rfl
  · have hscratchLow := (List.mem_range'_1.mp hconstant).1
    dsimp only [Wire] at *
    omega
  · dsimp only [Wire] at *
    omega

private theorem productionEnd_lengthT_eq (T : Nat) :
    (productionEndRegisters T).lengthT = List.range' 522 9 := by
  rfl

private theorem productionEnd_lengthRP_eq (T : Nat) :
    (productionEndRegisters T).lengthRP = List.range' 549 9 := by
  rfl

private theorem productionEnd_lengthT_bounds
    (T : Nat) {wire : Wire}
    (hwire : wire ∈ (productionEndRegisters T).lengthT) :
    522 ≤ wire ∧ wire ≤ 530 := by
  rw [productionEnd_lengthT_eq T] at hwire
  obtain ⟨hlow, hhigh⟩ := List.mem_range'_1.mp hwire
  dsimp only [Wire] at *
  omega

private theorem productionEnd_lengthRP_bounds
    (T : Nat) {wire : Wire}
    (hwire : wire ∈ (productionEndRegisters T).lengthRP) :
    549 ≤ wire ∧ wire ≤ 557 := by
  rw [productionEnd_lengthRP_eq T] at hwire
  obtain ⟨hlow, hhigh⟩ := List.mem_range'_1.mp hwire
  dsimp only [Wire] at *
  omega

private theorem productionEnd_lengthRP_disjoint_lengthT (T : Nat) :
    List.Disjoint (productionEndRegisters T).lengthRP
      (productionEndRegisters T).lengthT := by
  apply List.disjoint_left.mpr
  intro wire hrp ht
  obtain ⟨hrpLow, hrpHigh⟩ := productionEnd_lengthRP_bounds T hrp
  obtain ⟨htLow, htHigh⟩ := productionEnd_lengthT_bounds T ht
  dsimp only [Wire] at *
  omega

private theorem productionEnd_lengthT_disjoint_lengthRP (T : Nat) :
    List.Disjoint (productionEndRegisters T).lengthT
      (productionEndRegisters T).lengthRP :=
  (productionEnd_lengthRP_disjoint_lengthT T).symm

private theorem productionEnd_upper_fit (T : Nat) :
    quotientSwapUnaryDepth (endIterationWindowsAt 256 T).k4
        (endIterationWindowsAt 256 T).K4 + 2 ≤
      endIterationScratchSize (productionEndRegisters T) 256
        (endIterationWindowsAt 256 T) := by
  change quotientSwapUnaryDepth (endIterationWindowsAt 256 T).k4
      (endIterationWindowsAt 256 T).K4 + 2 ≤
    max
      (max 10 (quotientSwapUnaryDepth (endIterationWindowsAt 256 T).k4
        (endIterationWindowsAt 256 T).K4 + 2))
      (max 10 (quotientSwapUnaryDepth (endIterationWindowsAt 256 T).k5
        ((endIterationWindowsAt 256 T).K5Decode 256) + 2))
  omega

private theorem productionEnd_lower_fit (T : Nat) :
    quotientSwapUnaryDepth (endIterationWindowsAt 256 T).k5
        ((endIterationWindowsAt 256 T).K5Decode 256) + 2 ≤
      endIterationScratchSize (productionEndRegisters T) 256
        (endIterationWindowsAt 256 T) := by
  change quotientSwapUnaryDepth (endIterationWindowsAt 256 T).k5
      ((endIterationWindowsAt 256 T).K5Decode 256) + 2 ≤
    max
      (max 10 (quotientSwapUnaryDepth (endIterationWindowsAt 256 T).k4
        (endIterationWindowsAt 256 T).K4 + 2))
      (max 10 (quotientSwapUnaryDepth (endIterationWindowsAt 256 T).k5
        ((endIterationWindowsAt 256 T).K5Decode 256) + 2))
  omega

private theorem productionEnd_path_bounds
    (T k K : Nat)
    (hk4 : 1 ≤ (endIterationWindowsAt 256 T).k4)
    (hK4 : (endIterationWindowsAt 256 T).K4 ≤ 259)
    (hk5 : 1 ≤ (endIterationWindowsAt 256 T).k5)
    (hK5 : (endIterationWindowsAt 256 T).K5Decode 256 ≤ 259)
    (hfit : quotientSwapUnaryDepth k K + 2 ≤
      endIterationScratchSize (productionEndRegisters T) 256
        (endIterationWindowsAt 256 T))
    {wire : Wire} (hwire : wire ∈ (productionEndRegisters T).path k K) :
    562 ≤ wire ∧ wire < (productionEndRegisters T).rangeAccumulator k K := by
  rw [productionEnd_path_eq T k K hk4 hK4 hk5 hK5 (by omega)] at hwire
  rw [productionEnd_range_eq T k K hk4 hK4 hk5 hK5 hfit]
  exact List.mem_range'_1.mp hwire

private theorem productionEnd_tree_layout
    (T k K : Nat) (index : List Wire)
    (hk4 : 1 ≤ (endIterationWindowsAt 256 T).k4)
    (hK4 : (endIterationWindowsAt 256 T).K4 ≤ 259)
    (hk5 : 1 ≤ (endIterationWindowsAt 256 T).k5)
    (hK5 : (endIterationWindowsAt 256 T).K5Decode 256 ≤ 259)
    (hkK : k ≤ K)
    (hwidth : DualUnaryActionTree.sourceWidth
      (quotientSwapLabels k K).toFinset ≤ index.length)
    (hindexBounds : ∀ wire ∈ index, 522 ≤ wire ∧ wire ≤ 557)
    (hfit : quotientSwapUnaryDepth k K + 2 ≤
      endIterationScratchSize (productionEndRegisters T) 256
        (endIterationWindowsAt 256 T)) :
    (quotientSwapTree (productionEndTreeRegisters index) k K).Layout
      558 ((productionEndRegisters T).path k K) := by
  have hpathEq := productionEnd_path_eq T k K hk4 hK4 hk5 hK5 (by omega)
  apply quotientSwapTree_layout_of_separated
    (productionEndTreeRegisters index) hkK hwidth
  · rw [hpathEq]
    simp
  · intro hmem
    obtain ⟨hlow, hhigh⟩ := hindexBounds 558 hmem
    dsimp only [Wire] at *
    omega
  · intro hmem
    rw [hpathEq] at hmem
    obtain ⟨hlow, hhigh⟩ := List.mem_range'_1.mp hmem
    dsimp only [Wire] at *
    omega
  · rw [hpathEq]
    exact List.nodup_range'
  · apply List.disjoint_left.mpr
    intro wire hindex hpath
    obtain ⟨hindexLow, hindexHigh⟩ := hindexBounds wire hindex
    rw [hpathEq] at hpath
    obtain ⟨hpathLow, hpathHigh⟩ := List.mem_range'_1.mp hpath
    dsimp only [Wire] at *
    omega

set_option maxRecDepth 100000 in
private theorem productionEnd_upper_index_bounds
    (T : Nat)
    (hkK : (endIterationWindowsAt 256 T).k4 ≤
      (endIterationWindowsAt 256 T).K4)
    (hwidth : DualUnaryActionTree.sourceWidth
      (quotientSwapLabels (endIterationWindowsAt 256 T).k4
        (endIterationWindowsAt 256 T).K4).toFinset ≤ 9)
    {wire : Wire}
    (hwire : wire ∈
      ((productionEndRegisters T).upperTree
        (endIterationWindowsAt 256 T)).indexWires) :
    549 ≤ wire ∧ wire ≤ 557 := by
  rw [productionEnd_upperTree_eq] at hwire
  have hmem := quotientSwapTree_indexWires_mem_lengthQ
    (productionEndTreeRegisters (productionEndRegisters T).lengthRP)
    hkK (by simpa [productionEndTreeRegisters,
      productionEnd_lengthRP_eq T] using hwidth) wire hwire
  exact productionEnd_lengthRP_bounds T hmem

set_option maxRecDepth 100000 in
private theorem productionEnd_lower_index_bounds
    (T : Nat)
    (hkK : (endIterationWindowsAt 256 T).k5 ≤
      (endIterationWindowsAt 256 T).K5Decode 256)
    (hwidth : DualUnaryActionTree.sourceWidth
      (quotientSwapLabels (endIterationWindowsAt 256 T).k5
        ((endIterationWindowsAt 256 T).K5Decode 256)).toFinset ≤ 9)
    {wire : Wire}
    (hwire : wire ∈
      ((productionEndRegisters T).lowerTree 256
        (endIterationWindowsAt 256 T)).indexWires) :
    522 ≤ wire ∧ wire ≤ 530 := by
  rw [productionEnd_lowerTree_eq] at hwire
  have hmem := quotientSwapTree_indexWires_mem_lengthQ
    (productionEndTreeRegisters (productionEndRegisters T).lengthT)
    hkK (by simpa [productionEndTreeRegisters,
      productionEnd_lengthT_eq T] using hwidth) wire hwire
  exact productionEnd_lengthT_bounds T hmem

private theorem productionEnd_shared_layout
    (T k K : Nat) (tree : UnaryActionTree)
    (affineRegister target : List Wire)
    (hk4 : 1 ≤ (endIterationWindowsAt 256 T).k4)
    (hK4 : (endIterationWindowsAt 256 T).K4 ≤ 259)
    (hk5 : 1 ≤ (endIterationWindowsAt 256 T).k5)
    (hK5 : (endIterationWindowsAt 256 T).K5Decode 256 ≤ 259)
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259)
    (hfit : quotientSwapUnaryDepth k K + 2 ≤
      endIterationScratchSize (productionEndRegisters T) 256
        (endIterationWindowsAt 256 T))
    (hdecoder : tree.Layout (productionEndRegisters T).control
      ((productionEndRegisters T).path k K))
    (hindexBounds : ∀ wire ∈ tree.indexWires,
      522 ≤ wire ∧ wire ≤ 557)
    (htargetBounds : ∀ wire ∈ target, 522 ≤ wire ∧ wire ≤ 557)
    (htargetIndex : ∀ wire ∈ target, wire ∉ tree.indexWires)
    (htargetNodup : target.Nodup)
    (haffine : ConstantLayout affineRegister
      (productionEndRegisters T).constants (productionEndRegisters T).carry)
    (haffineBounds : ∀ wire ∈ affineRegister,
      522 ≤ wire ∧ wire ≤ 557)
    (haffineTarget : List.Disjoint affineRegister target) :
    SharedLengthBlockLayout k K tree (productionEndRegisters T).control
      ((productionEndRegisters T).rangeAccumulator k K)
      ((productionEndRegisters T).temporary k K)
      (productionEndRegisters T).carry
      ((productionEndRegisters T).path k K)
      (productionEndRegisters T).work1At
      (productionEndRegisters T).work2At
      affineRegister target (productionEndRegisters T).constants := by
  have hcontrol : (productionEndRegisters T).control = 558 := by rfl
  have hpathBounds : ∀ wire ∈ (productionEndRegisters T).path k K,
      562 ≤ wire ∧ wire < (productionEndRegisters T).rangeAccumulator k K := by
    intro wire hwire
    exact productionEnd_path_bounds T k K hk4 hK4 hk5 hK5 hfit hwire
  have hrangeEq := productionEnd_range_eq T k K hk4 hK4 hk5 hK5 hfit
  have htemporaryEq := productionEnd_temporary_eq T k K hk4 hK4 hk5 hK5 hfit
  have hrangeLow : 562 ≤ (productionEndRegisters T).rangeAccumulator k K := by
    rw [hrangeEq]
    dsimp only [Wire]
    omega
  have htemporaryLow : 562 ≤ (productionEndRegisters T).temporary k K := by
    rw [htemporaryEq]
    dsimp only [Wire]
    omega
  have hrangeTemporary : (productionEndRegisters T).rangeAccumulator k K <
      (productionEndRegisters T).temporary k K := by
    rw [hrangeEq, htemporaryEq]
    dsimp only [Wire]
    omega
  refine {
    affine := haffine
    work1Bits := ?_
    work2Bits := ?_
    affineRegisterDisjoint := ?_
    constantCarryDisjointTarget := ?_ }
  · refine {
      decoder := hdecoder
      wires := ?_
      cell := ?_
      targetNodup := htargetNodup
      targetDisjoint := ?_ }
    · apply List.nodup_append.mpr
      refine ⟨unaryLayout_decoderNodup hdecoder, ?_, ?_⟩
      · exact productionEnd_zeroMap_tail_nodup T hkPositive hkK hK
          hrangeLow htemporaryLow hrangeTemporary.ne
      · rw [hcontrol]
        exact productionEnd_protected_tail_disjoint T hkPositive hkK hK
          hindexBounds hpathBounds hrangeLow hrangeTemporary
    · intro label hlabel guard hguard
      apply productionEnd_cell12 T hkPositive hkK hK hlabel
        hrangeLow htemporaryLow hrangeTemporary.ne
      simpa only [hcontrol] using hguard
    · apply productionEnd_target_disjoint htargetBounds htargetIndex
        (fun wire hwire ↦ (hpathBounds wire hwire).1)
        hrangeLow htemporaryLow
      intro wire hwire
      exact productionEnd_work_map_bounds T hkPositive hkK hK hwire
  · refine {
      decoder := hdecoder
      wires := ?_
      cell := ?_
      targetNodup := htargetNodup
      targetDisjoint := ?_ }
    · apply List.nodup_append.mpr
      refine ⟨unaryLayout_decoderNodup hdecoder, ?_, ?_⟩
      · exact productionEnd_zeroMap_tail_reverse_nodup T hkPositive hkK hK
          hrangeLow htemporaryLow hrangeTemporary.ne
      · rw [hcontrol]
        exact productionEnd_protected_tail_reverse_disjoint T hkPositive hkK hK
          hindexBounds hpathBounds hrangeLow hrangeTemporary
    · intro label hlabel guard hguard
      apply productionEnd_cell21 T hkPositive hkK hK hlabel
        hrangeLow htemporaryLow hrangeTemporary.ne
      simpa only [hcontrol] using hguard
    · apply productionEnd_target_disjoint htargetBounds htargetIndex
        (fun wire hwire ↦ (hpathBounds wire hwire).1)
        hrangeLow htemporaryLow
      intro wire hwire
      apply productionEnd_work_map_bounds T hkPositive hkK hK
      rcases List.mem_append.mp hwire with hwork2 | hwork1
      · exact List.mem_append.mpr (Or.inr hwork2)
      · exact List.mem_append.mpr (Or.inl hwork1)
  · apply productionEnd_nonAffine_disjoint T haffineBounds haffineTarget
      (fun wire hwire ↦ (hpathBounds wire hwire).1)
      hrangeLow htemporaryLow
    intro wire hwire
    exact productionEnd_work_map_bounds T hkPositive hkK hK hwire
  · apply productionEnd_constantCarry_target_disjoint T hk4 hK4 hk5 hK5
    intro wire hwire
    exact (htargetBounds wire hwire).2

set_option maxRecDepth 100000 in
private theorem productionEnd_layout_of_bounds
    (T : Nat)
    (hk4Positive : 1 ≤ (endIterationWindowsAt 256 T).k4)
    (hk4K4 : (endIterationWindowsAt 256 T).k4 ≤
      (endIterationWindowsAt 256 T).K4)
    (hK4 : (endIterationWindowsAt 256 T).K4 ≤ 259)
    (hk5Positive : 1 ≤ (endIterationWindowsAt 256 T).k5)
    (hk5K5 : (endIterationWindowsAt 256 T).k5 ≤
      (endIterationWindowsAt 256 T).K5Decode 256)
    (hK5 : (endIterationWindowsAt 256 T).K5Decode 256 ≤ 259) :
    EndIterationLayout (productionEndRegisters T) 256
      (endIterationWindowsAt 256 T) := by
  let windows := endIterationWindowsAt 256 T
  have hupperWidth : DualUnaryActionTree.sourceWidth
      (quotientSwapLabels windows.k4 windows.K4).toFinset ≤ 9 :=
    quotientSwapSourceWidth_le_nine hK4
  have hlowerWidth : DualUnaryActionTree.sourceWidth
      (quotientSwapLabels windows.k5 (windows.K5Decode 256)).toFinset ≤ 9 :=
    quotientSwapSourceWidth_le_nine hK5
  have hupperDecoder :
      ((productionEndRegisters T).upperTree windows).Layout
        (productionEndRegisters T).control
        ((productionEndRegisters T).path windows.k4 windows.K4) := by
    rw [productionEnd_upperTree_eq]
    change (quotientSwapTree
      (productionEndTreeRegisters (productionEndRegisters T).lengthRP)
        windows.k4 windows.K4).Layout 558
      ((productionEndRegisters T).path windows.k4 windows.K4)
    exact productionEnd_tree_layout T windows.k4 windows.K4
      (productionEndRegisters T).lengthRP
      hk4Positive hK4 hk5Positive hK5 hk4K4
      (by simpa [productionEnd_lengthRP_eq T] using hupperWidth)
      (fun wire hwire ↦ by
        obtain ⟨hlow, hhigh⟩ := productionEnd_lengthRP_bounds T hwire
        dsimp only [Wire] at *
        omega)
      (productionEnd_upper_fit T)
  have hlowerDecoder :
      ((productionEndRegisters T).lowerTree 256 windows).Layout
        (productionEndRegisters T).control
        ((productionEndRegisters T).path windows.k5 (windows.K5Decode 256)) := by
    rw [productionEnd_lowerTree_eq]
    change (quotientSwapTree
      (productionEndTreeRegisters (productionEndRegisters T).lengthT)
        windows.k5 (windows.K5Decode 256)).Layout 558
      ((productionEndRegisters T).path windows.k5 (windows.K5Decode 256))
    exact productionEnd_tree_layout T windows.k5 (windows.K5Decode 256)
      (productionEndRegisters T).lengthT
      hk4Positive hK4 hk5Positive hK5 hk5K5
      (by simpa [productionEnd_lengthT_eq T] using hlowerWidth)
      (fun wire hwire ↦ by
        obtain ⟨hlow, hhigh⟩ := productionEnd_lengthT_bounds T hwire
        dsimp only [Wire] at *
        omega)
      (productionEnd_lower_fit T)
  have hupperAffine : ConstantLayout (productionEndRegisters T).lengthRP
      (productionEndRegisters T).constants (productionEndRegisters T).carry := by
    rw [ConstantLayout, productionEnd_constants_eq T hk4Positive hK4 hk5Positive hK5,
      productionEnd_carry_eq T hk4Positive hK4 hk5Positive hK5,
      productionEnd_lengthRP_eq T]
    decide
  have hlowerAffine : ConstantLayout (productionEndRegisters T).lengthT
      (productionEndRegisters T).constants (productionEndRegisters T).carry := by
    rw [ConstantLayout, productionEnd_constants_eq T hk4Positive hK4 hk5Positive hK5,
      productionEnd_carry_eq T hk4Positive hK4 hk5Positive hK5,
      productionEnd_lengthT_eq T]
    decide
  refine {
    k4_positive := hk4Positive
    k4_le_K4 := hk4K4
    K4_le_work := by simpa using hK4
    k5_positive := hk5Positive
    k5_le_decode := hk5K5
    work1_length := by rfl
    work2_length := by rfl
    width_positive := by
      change 0 < 9
      decide
    lengthRP_length := by rfl
    scratch_capacity := by
      rw [productionEnd_scratch_eq T hk4Positive hK4 hk5Positive hK5]
      simp
    physical := indexedStepProduction_endIteration_physical T
    upper := ?_
    lower := ?_ }
  · apply productionEnd_shared_layout T windows.k4 windows.K4
      ((productionEndRegisters T).upperTree windows)
      (productionEndRegisters T).lengthRP
      (productionEndRegisters T).lengthT
      hk4Positive hK4 hk5Positive hK5 hk4Positive hk4K4 hK4
      (productionEnd_upper_fit T) hupperDecoder
    · intro wire hwire
      obtain ⟨hlow, hhigh⟩ :=
        productionEnd_upper_index_bounds T hk4K4 hupperWidth hwire
      dsimp only [Wire] at *
      omega
    · intro wire hwire
      obtain ⟨hlow, hhigh⟩ := productionEnd_lengthT_bounds T hwire
      dsimp only [Wire] at *
      omega
    · intro wire htarget hindex
      obtain ⟨htargetLow, htargetHigh⟩ :=
        productionEnd_lengthT_bounds T htarget
      obtain ⟨hindexLow, hindexHigh⟩ :=
        productionEnd_upper_index_bounds T hk4K4 hupperWidth hindex
      dsimp only [Wire] at *
      omega
    · rw [productionEnd_lengthT_eq T]
      exact List.nodup_range'
    · exact hupperAffine
    · intro wire hwire
      obtain ⟨hlow, hhigh⟩ := productionEnd_lengthRP_bounds T hwire
      dsimp only [Wire] at *
      omega
    · exact productionEnd_lengthRP_disjoint_lengthT T
  · apply productionEnd_shared_layout T windows.k5 (windows.K5Decode 256)
      ((productionEndRegisters T).lowerTree 256 windows)
      (productionEndRegisters T).lengthT
      (productionEndRegisters T).lengthRP
      hk4Positive hK4 hk5Positive hK5 hk5Positive hk5K5 hK5
      (productionEnd_lower_fit T) hlowerDecoder
    · intro wire hwire
      obtain ⟨hlow, hhigh⟩ :=
        productionEnd_lower_index_bounds T hk5K5 hlowerWidth hwire
      dsimp only [Wire] at *
      omega
    · intro wire hwire
      obtain ⟨hlow, hhigh⟩ := productionEnd_lengthRP_bounds T hwire
      dsimp only [Wire] at *
      omega
    · intro wire htarget hindex
      obtain ⟨htargetLow, htargetHigh⟩ :=
        productionEnd_lengthRP_bounds T htarget
      obtain ⟨hindexLow, hindexHigh⟩ :=
        productionEnd_lower_index_bounds T hk5K5 hlowerWidth hindex
      dsimp only [Wire] at *
      omega
    · rw [productionEnd_lengthRP_eq T]
      exact List.nodup_range'
    · exact hlowerAffine
    · intro wire hwire
      obtain ⟨hlow, hhigh⟩ := productionEnd_lengthT_bounds T hwire
      dsimp only [Wire] at *
      omega
    · exact productionEnd_lengthT_disjoint_lengthRP T

/-! ## One fixed allocation over the entire schedule -/

private def indexedStepProductionLayoutCheck (T : Nat) : Bool :=
  let windows := certifiedActiveWindows 256 T
  decide (1 ≤ windows.remainder.start ∧
      windows.remainder.start ≤ windows.remainder.stop ∧
      windows.remainder.stop ≤ 259) &&
    (decide (1 ≤ windows.quotientSwap.start ∧
        windows.quotientSwap.start ≤ windows.quotientSwap.stop ∧
        windows.quotientSwap.stop ≤ 259) &&
      (decide (1 ≤ windows.coefficient.start ∧
        windows.coefficient.start ≤ windows.coefficient.stop ∧
          windows.coefficient.stop ≤ 259) &&
        if T % 4 = 0 then
          let endWindows := endIterationWindowsAt 256 T
          decide (1 ≤ endWindows.k4 ∧
            endWindows.k4 ≤ endWindows.K4 ∧
            endWindows.K4 ≤ 259 ∧
            1 ≤ endWindows.k5 ∧
            endWindows.k5 ≤ endWindows.K5Decode 256 ∧
            endWindows.K5Decode 256 ≤ 259)
        else true))

private theorem indexedStepProductionLayoutCheck_sound
    (T : Nat) (hcheck : indexedStepProductionLayoutCheck T = true) :
    IndexedStepLayout indexedStepProductionRegisters 256 T := by
  simp only [indexedStepProductionLayoutCheck, Bool.and_eq_true] at hcheck
  let base := indexedStepProduction_layout
  refine {
    aux_length := base.aux_length
    work1_length := base.work1_length
    work2_length := base.work2_length
    physical := base.physical
    terminalControl := base.terminalControl
    terminalPaddingCapacity := base.terminalPaddingCapacity
    terminalPadding := base.terminalPadding
    terminalPhase := base.terminalPhase
    terminalEpoch := base.terminalEpoch
    preShift := base.preShift
    remainderSub := base.remainderSub
    remainderPhase2 := base.remainderPhase2
    remainderRestoreCCX := base.remainderRestoreCCX
    controlSign := base.controlSign
    remainderRestore := base.remainderRestore
    remainder := by
      have hbounds := of_decide_eq_true hcheck.1
      exact indexedStepProduction_remainder_layout_of_bounds _
        hbounds.1 hbounds.2.1 hbounds.2.2
    lengthQ_positive := base.lengthQ_positive
    phase2Length := base.phase2Length
    phase3Length := base.phase3Length
    lengthCarryCapacity := base.lengthCarryCapacity
    lengthCarryPhysical := base.lengthCarryPhysical
    quotientControls := base.quotientControls
    quotient := by
      have hbounds := of_decide_eq_true hcheck.2.1
      exact indexedStepProduction_quotient_layout_of_bounds _
        hbounds.1 hbounds.2.1 hbounds.2.2
    coefficientTemporary := base.coefficientTemporary
    coefficientSub := base.coefficientSub
    coefficientAdd := base.coefficientAdd
    coefficientSign := base.coefficientSign
    tBoundary := base.tBoundary
    coefficient := by
      have hbounds := of_decide_eq_true hcheck.2.2.1
      exact indexedStepProduction_coefficient_layout_of_bounds _
        hbounds.1 hbounds.2.1 hbounds.2.2
    postShift := base.postShift
    phaseUpdate := base.phaseUpdate
    endQ := base.endQ
    endS := base.endS
    endControls := base.endControls
    endIteration := ?_ }
  intro hmod
  simp [hmod] at hcheck
  have hbounds := hcheck.2.2.2
  simpa only [productionEndRegisters] using productionEnd_layout_of_bounds T
    hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2.1
      hbounds.2.2.2.2.1 hbounds.2.2.2.2.2

private def indexedScheduleProductionLayoutCheck : Nat → Nat → Bool
  | _, 0 => true
  | start, count + 1 =>
      indexedStepProductionLayoutCheck start &&
        indexedScheduleProductionLayoutCheck (start + 1) count

private theorem indexedScheduleProductionLayoutCheck_sound
    (start count : Nat)
    (hcheck : indexedScheduleProductionLayoutCheck start count = true) :
    IndexedScheduleLayout indexedStepProductionRegisters 256 start count := by
  induction count generalizing start with
  | zero => exact .done start
  | succ count ih =>
      simp only [indexedScheduleProductionLayoutCheck, Bool.and_eq_true] at hcheck
      exact .step
        (indexedStepProductionLayoutCheck_sound start hcheck.1)
        (ih (start + 1) hcheck.2)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
private theorem secp256k1ScheduleLayoutCheck :
    indexedScheduleProductionLayoutCheck 1 secp256k1ScheduleLength = true := by
  rfl

/-- The same explicit repaired 580-role allocation satisfies every physical component contract
at all 1,620 one-based secp256k1 schedule indices. -/
theorem secp256k1ScheduleLayout_production :
    Secp256k1ScheduleLayout indexedStepProductionRegisters := by
  exact indexedScheduleProductionLayoutCheck_sound 1 secp256k1ScheduleLength
    secp256k1ScheduleLayoutCheck

set_option maxRecDepth 100000 in
/-- Closed non-vacuity witness for the complete fixed-horizon physical layout. -/
theorem secp256k1ScheduleLayout_inhabited :
    ∃ registers : IndexedStepRegisters,
      registers.allWires.length = 580 ∧ Secp256k1ScheduleLayout registers := by
  exact ⟨indexedStepProductionRegisters, by decide,
    secp256k1ScheduleLayout_production⟩

end

end ShorECDLP.Paper2607_13816
