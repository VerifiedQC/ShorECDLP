import ShorECDLP.Submission.«2607_13816».EEA.ScheduleLayout
/-!
# Physical support of the production EEA schedule

The component support proofs compose over the literal circuit and all 1,620
scheduled indices. Window slices and shared scratch stay within the fixed
580-wire allocation without expanding the decoder trees. The same support
witness yields the distinct-qubit bound, external frame and input locality.

This certificate concerns the coherent EEA schedule. The adaptive wrapper and
complete Figure 15 resource certificate require their remaining compositions.
-/

namespace ShorECDLP.Paper2607_13816
open Classical
private theorem support_to_580 (support : List Wire)
    (h : support.all (fun w => decide (w < 580)) = true) :
    ∀ w ∈ support, w ∈ List.range 580 := by
  intro w hw
  exact List.mem_range.mpr (of_decide_eq_true ((List.all_eq_true.mp h) w hw))

attribute [local irreducible] computeControl terminalPaddingForward preShiftUnitary terminalEpochSpill

private theorem production_blockA_support :
    PaperCircuitUsesOnly (List.range 580) (blockAForward indexedStepProductionRegisters) := by
  let r := indexedStepProductionRegisters
  have ht : PaperCircuitUsesOnly (List.range 580)
      (computeControl (r.phase1 :: r.lengthRPrime) (2^(r.lengthRPrime.length+1)-2)
        r.terminal r.blockScratch) :=
    (computeControl_usesOnly _ _ _ _).mono (support_to_580 _ (by decide +kernel))
  have hp := (terminalPaddingForward_usesOnly r.terminalPadding).mono
    (support_to_580 _ (by decide +kernel))
  have hh := (preShiftUnitary_usesOnly r.preShift).mono
    (support_to_580 _ (by decide +kernel))
  have he := (terminalEpochSpill_usesOnly r.terminal r.shiftEpoch r.quotientLow).mono
    (support_to_580 _ (by decide +kernel))
  have hx : PaperCircuitUsesOnly (List.range 580) ([.CX r.terminal r.phase1] : Circuit) := by
    intro g hg w hw
    simp only [List.mem_singleton] at hg
    subst g
    simp only [gateWires,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · exact List.mem_range.mpr (show (560 : Nat) < 580 by decide)
    · exact List.mem_range.mpr (show (0 : Nat) < 580 by decide)
  unfold blockAForward
  simpa only [List.append_assoc] using ht.append (hp.append (hx.append (hh.append (hx.append (he.append ht)))))

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

attribute [local irreducible] rControlNonterminal intervalAddSubUnitary

private theorem production_blockB_support (n : Nat) (window : ActiveWindow)
    (hlayout : IntervalLayout (indexedStepProductionRegisters.remainder window)
      window.start window.stop .work1) :
    PaperCircuitUsesOnly (List.range 580)
      (blockBForward indexedStepProductionRegisters n window) := by
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
  have hiSub := (intervalAddSubUnitary_usesOnly (r.remainder window) n window.start
    window.stop .sub true .work1 hlayout).mono (production_remainder_support window)
  have hiAdd := (intervalAddSubUnitary_usesOnly (r.remainder window) n window.start
    window.stop .add false .work1 hlayout).mono (production_remainder_support window)
  have hrestore := hc.append (hr.append hc)
  have h1 : PaperCircuitUsesOnly (List.range 580) (blockB1Forward r n window) := by
    unfold blockB1Forward
    exact (hs.append hiSub).append hs
  have h2 : PaperCircuitUsesOnly (List.range 580) (blockB2 r) := by
    unfold blockB2
    exact (hp.append hx).append hp
  have h3 : PaperCircuitUsesOnly (List.range 580) (blockB3Forward r n window) := by
    unfold blockB3Forward
    exact (hrestore.append hiAdd).append hrestore
  exact (h1.append h2).append h3

attribute [local irreducible] terminalEpochRestore postShiftUnitary phaseUpdateEpochUnitary

private theorem production_blockC_support :
    PaperCircuitUsesOnly (List.range 580) (blockCForward indexedStepProductionRegisters) := by
  let r := indexedStepProductionRegisters
  have ht := (computeControl_usesOnly (r.phase1 :: r.lengthRPrime)
    (2^(r.lengthRPrime.length+1)-2) r.terminal r.blockScratch).mono
    (support_to_580 _ (by decide +kernel))
  have he := (terminalEpochRestore_usesOnly r.terminal r.shiftEpoch r.quotientLow).mono
    (support_to_580 _ (by decide +kernel))
  exact (ht.append he).append ht

private theorem production_blockF_support :
    PaperCircuitUsesOnly (List.range 580) (blockFForward indexedStepProductionRegisters) :=
  (postShiftUnitary_usesOnly indexedStepProductionRegisters.postShift).mono
    (support_to_580 _ (by decide +kernel))

private theorem production_blockG_support :
    PaperCircuitUsesOnly (List.range 580) (blockGForward indexedStepProductionRegisters) :=
  (phaseUpdateEpochUnitary_usesOnly indexedStepProductionRegisters.phaseUpdate
    indexedStepProductionRegisters.shiftEpoch).mono (support_to_580 _ (by decide +kernel))

private theorem production_quotient_support (window : ActiveWindow) :
    ∀ w ∈ (indexedStepProductionRegisters.quotient window).allWires, w ∈ List.range 580 := by
  let r := indexedStepProductionRegisters
  intro w hw
  change w ∈ [r.control,r.sign] ++
    (IndexedStepRegisters.windowSlice r.work1 window ++ (r.lengthT ++ (r.lengthQ ++
    r.sourceScratch.take (max r.lengthQ.length (quotientSwapUnaryDepth window.start window.stop)+1)))) at hw
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with (hw | hw) | hw | hw | hw | hw
  · subst w; exact List.mem_range.mpr (show (558 : Nat) < 580 by decide)
  · subst w; exact List.mem_range.mpr (show (3 : Nat) < 580 by decide)
  · exact range580_of_closed r.work1 (by decide +kernel) w (window_mem hw)
  · exact range580_of_closed r.lengthT (by decide +kernel) w hw
  · exact range580_of_closed r.lengthQ (by decide +kernel) w hw
  · exact range580_of_closed r.sourceScratch (by decide +kernel) w (List.mem_of_mem_take hw)

attribute [local irreducible] quotientSwapUnitary controlledIncrement controlledDecrement

private theorem production_blockD_support (window : ActiveWindow)
    (hlayout : QuotientSwapLayout (indexedStepProductionRegisters.quotient window)
      window.start window.stop) :
    PaperCircuitUsesOnly (List.range 580)
      (blockDForward indexedStepProductionRegisters window) := by
  let r := indexedStepProductionRegisters
  have hp := (computeControl_usesOnly [r.phase1,r.phase2] 2 r.control r.sourceScratch).mono
    (support_to_580 _ (by decide +kernel))
  have hq := (computeControl_usesOnly [r.phase1,r.phase2] 1 r.control r.sourceScratch).mono
    (support_to_580 _ (by decide +kernel))
  have hi := (controlledIncrement_usesOnly r.control r.lengthQ
    (r.sourceScratch.take (r.lengthQ.length-1))).mono (support_to_580 _ (by decide +kernel))
  have hd := (controlledDecrement_usesOnly r.control r.lengthQ
    (r.sourceScratch.take (r.lengthQ.length-1))).mono (support_to_580 _ (by decide +kernel))
  have hx := gate_support_580 (.CX r.phase1 r.control) (by decide +kernel)
  have hy := gate_support_580 (.CX r.phase2 r.control) (by decide +kernel)
  have hs := (quotientSwapUnitary_usesOnly (r.quotient window) hlayout).mono
    (production_quotient_support window)
  have h1 : PaperCircuitUsesOnly (List.range 580) (blockD1Forward r) :=
    (hp.append hi).append hp
  have h2 : PaperCircuitUsesOnly (List.range 580) (blockD2Forward r window) :=
    ((hx.append hy).append hs).append (hy.append hx)
  have h3 : PaperCircuitUsesOnly (List.range 580) (blockD3Forward r) :=
    (hq.append hd).append hq
  exact (h1.append h2).append h3

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

attribute [local irreducible] coefficientPrefixUnitary prepareLatestPaperTBoundary restoreLatestPaperTBoundary

private theorem production_blockE_support (n : Nat) (window : ActiveWindow)
    (hlayout : CoefficientPrefixLayout (indexedStepProductionRegisters.coefficient window)
      window.start window.stop) :
    PaperCircuitUsesOnly (List.range 580)
      (blockEForward indexedStepProductionRegisters n window) := by
  let r := indexedStepProductionRegisters
  have ht := (computeControl_usesOnly [r.phase2,r.sign] 2 r.terminal r.blockScratch).mono
    (support_to_580 _ (by decide +kernel))
  have hs := (computeControl_usesOnly [r.phase1,r.terminal] 1 r.control r.blockScratch).mono
    (support_to_580 _ (by decide +kernel))
  have ha := (computeControl_usesOnly [r.phase1] 1 r.control r.blockScratch).mono
    (support_to_580 _ (by decide +kernel))
  have hp := (prepareLatestPaperTBoundary_usesOnly r.tBoundary n).mono
    (support_to_580 _ (by decide +kernel))
  have hr := (restoreLatestPaperTBoundary_usesOnly r.tBoundary n).mono
    (support_to_580 _ (by decide +kernel))
  have hsub := (coefficientPrefixUnitary_usesOnly (r.coefficient window)
    .sub false .work2 hlayout).mono (production_coefficient_support window)
  have hadd := (coefficientPrefixUnitary_usesOnly (r.coefficient window)
    .add true .work2 hlayout).mono (production_coefficient_support window)
  have hx := gate_support_580 (.CX r.phase1 r.sign) (by decide +kernel)
  have hprepare : PaperCircuitUsesOnly (List.range 580) (blockEPrepareForward r n) :=
    ((ht.append hs).append ht).append hp
  have hfirst : PaperCircuitUsesOnly (List.range 580) (blockESubtractForward r n window) :=
    (((hprepare.append hsub).append ht).append hs).append ht
  have hfinish : PaperCircuitUsesOnly (List.range 580) (blockEFinishForward r n window) :=
    (((hx.append ha).append hadd).append ha).append hr
  exact hfirst.append hfinish
private theorem getD_support (ws : List Wire) (i : Nat)
    (hws : ∀ w ∈ ws, w ∈ List.range 580) : ws.getD i 0 ∈ List.range 580 := by
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hws _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact List.mem_range.mpr (by decide)

private theorem length_support (k K : Nat) (tree : UnaryActionTree)
    (control acc temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire) (affine target constants : List Wire)
    (hc : control ∈ List.range 580) (ha : acc ∈ List.range 580)
    (ht : temporary ∈ List.range 580) (hcarry : carry ∈ List.range 580)
    (hp : ∀ w ∈ path, w ∈ List.range 580)
    (hi : ∀ w ∈ tree.indexWires, w ∈ List.range 580)
    (h1 : ∀ label, work1At label ∈ List.range 580)
    (h2 : ∀ label, work2At label ∈ List.range 580)
    (hf : ∀ w ∈ affine, w ∈ List.range 580)
    (hy : ∀ w ∈ target, w ∈ List.range 580)
    (hk : ∀ w ∈ constants, w ∈ List.range 580) :
    ∀ w ∈ lengthBlockSupport k K tree control acc temporary carry path
      work1At work2At affine target constants, w ∈ List.range 580 := by
  intro w hw
  simp only [lengthBlockSupport,lengthBlockWriterSupport,zeroMapProtectedWires,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_dedup,List.mem_map] at hw
  aesop

private theorem endpoint_width {k K : Nat} (hK : K ≤ 259) :
    DualUnaryActionTree.sourceWidth (quotientSwapLabels k K).toFinset ≤ 9 := by
  apply DualUnaryActionTree.sourceWidth_le _ 9 (by decide)
  intro label hlabel
  have hmem : label ∈ quotientSwapLabels k K := by simpa using hlabel
  simp only [quotientSwapLabels, List.mem_range'_1] at hmem
  norm_num
  omega

private theorem production_end_support (T : Nat)
    (hlayout : EndIterationLayout (indexedStepProductionRegisters.endIteration 256 T) 256
      (endIterationWindowsAt 256 T)) :
    ∀ w ∈ endIterationSupport (indexedStepProductionRegisters.endIteration 256 T) 256
      (endIterationWindowsAt 256 T), w ∈ List.range 580 := by
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
  have hu := length_support windows.k4 windows.K4 (r.upperTree windows) r.control
    (r.rangeAccumulator windows.k4 windows.K4) (r.temporary windows.k4 windows.K4) r.carry
    (r.path windows.k4 windows.K4) r.work1At r.work2At r.lengthRP r.lengthT r.constants
    hc (getD_support _ _ hs) (getD_support _ _ hs) (getD_support _ _ hs)
    (hpath _ _) huIndex (fun label => getD_support _ _ h1) (fun label => getD_support _ _ h2)
    hRP hT hconst
  have hl := length_support windows.k5 (windows.K5Decode 256) (r.lowerTree 256 windows) r.control
    (r.rangeAccumulator windows.k5 (windows.K5Decode 256))
    (r.temporary windows.k5 (windows.K5Decode 256)) r.carry
    (r.path windows.k5 (windows.K5Decode 256)) r.work1At r.work2At r.lengthT r.lengthRP r.constants
    hc (getD_support _ _ hs) (getD_support _ _ hs) (getD_support _ _ hs)
    (hpath _ _) hlIndex (fun label => getD_support _ _ h1) (fun label => getD_support _ _ h2)
    hT hRP hconst
  intro w hw
  change w ∈ (_ ++ _) ++ _ at hw
  rcases List.mem_append.mp hw with hw | hw
  · rcases List.mem_append.mp hw with hw | hw
    · change w ∈ (r.control :: r.work1) ++ r.work2 at hw
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_cons.mp hw with rfl | hw
        · exact hc
        · exact h1 w hw
      · exact h2 w hw
    · exact hu w hw
  · exact hl w hw
attribute [local irreducible] mcxVChain swapWorkAndLengthUnaryShared

private theorem production_blockH_support (T : Nat)
    (hlayout : T % 4 = 0 → EndIterationLayout
      (indexedStepProductionRegisters.endIteration 256 T) 256 (endIterationWindowsAt 256 T)) :
    PaperCircuitUsesOnly (List.range 580) (blockHForward indexedStepProductionRegisters 256 T) := by
  let r := indexedStepProductionRegisters
  unfold blockHForward
  split
  · rename_i hmod
    have he := hlayout hmod
    have hq := (mcxVChain_usesOnly r.lengthQ (r.sourceScratch.getD 0 0)
      (r.sourceScratch.drop 2)).mono (support_to_580 _ (by decide +kernel))
    have hs := (mcxVChain_usesOnly (r.lengthS ++ [r.shiftEpoch]) (r.sourceScratch.getD 1 0)
      (r.sourceScratch.drop 2)).mono (support_to_580 _ (by decide +kernel))
    have hx := gate_support_580 (.X r.shiftEpoch) (by decide +kernel)
    have hc := gate_support_580 (.CCX (r.sourceScratch.getD 0 0)
      (r.sourceScratch.getD 1 0) r.control) (by decide +kernel)
    have hi := gate_support_580 (.CX r.control r.iter) (by decide +kernel)
    have hw := (swapWorkAndLengthUnaryShared_usesOnly (r.endIteration 256 T) 256
      (endIterationWindowsAt 256 T) he.k4_le_K4 he.k5_le_decode).mono
      (production_end_support T he)
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using ((((((((((hq.append hx).append hs).append hx).append hc).append hw).append hi).append hc).append hx).append hs).append hx).append hq
  · intro g hg
    simp only [List.not_mem_nil] at hg

/-- Every gate in a physically valid production microstep uses one of the 580 assigned wires. -/
theorem indexedStepUnitary_production_usesOnly (T : Nat)
    (hlayout : IndexedStepLayout indexedStepProductionRegisters 256 T) :
    PaperCircuitUsesOnly (List.range 580)
      (indexedStepUnitary indexedStepProductionRegisters 256 T) := by
  have hB := production_blockB_support 256 _ hlayout.remainder
  have hD := production_blockD_support _ hlayout.quotient
  have hE := production_blockE_support 256 _ hlayout.coefficient
  have hH := production_blockH_support T hlayout.endIteration
  exact ((((((production_blockA_support.append hB).append production_blockC_support).append hD).append hE).append production_blockF_support).append production_blockG_support).append hH

attribute [local irreducible] indexedStepUnitary

/-- The complete physical support bound composes over the actual schedule stream. -/
theorem indexedScheduleUnitary_production_usesOnly (start count : Nat)
    (hlayout : IndexedScheduleLayout indexedStepProductionRegisters 256 start count) :
    PaperCircuitUsesOnly (List.range 580)
      (indexedScheduleUnitary indexedStepProductionRegisters 256 start count) := by
  induction hlayout with
  | done start => intro g hg; simp [indexedScheduleUnitary] at hg
  | step head tail ih => exact (indexedStepUnitary_production_usesOnly _ head).append ih

/-- All 1,620 production microsteps touch only the fixed 580 physical wires. -/
theorem secp256k1EEAForwardUnitary_production_usesOnly :
    PaperCircuitUsesOnly (List.range 580)
      (secp256k1EEAForwardUnitary indexedStepProductionRegisters) :=
  indexedScheduleUnitary_production_usesOnly 1 secp256k1ScheduleLength
    secp256k1ScheduleLayout_production

attribute [local irreducible] secp256k1EEAForwardUnitary

/-- The exact production schedule uses at most 580 distinct physical qubits. -/
theorem secp256k1EEAForwardUnitary_production_qubitCount :
    qubitCount (secp256k1EEAForwardUnitary indexedStepProductionRegisters) ≤ 580 := by
  have hsubset : (circuitWires (secp256k1EEAForwardUnitary indexedStepProductionRegisters)).dedup.toFinset
      ⊆ (List.range 580).toFinset := by
    intro w hw
    have hm : w ∈ circuitWires (secp256k1EEAForwardUnitary indexedStepProductionRegisters) := by
      simpa using hw
    obtain ⟨g,hg,hwg⟩ := List.mem_flatMap.mp hm
    exact List.mem_toFinset.mpr (secp256k1EEAForwardUnitary_production_usesOnly g hg w hwg)
  have hcard := Finset.card_le_card hsubset
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range (n := 580))] at hcard
  simpa only [qubitCount,List.length_range] using hcard

/-- An external retained register is unchanged by the full fixed-horizon EEA schedule. -/
theorem secp256k1EEAForwardUnitary_production_preservesOutside
    (s : BasisState) (w : Wire) (hw : 580 ≤ w) :
    run (secp256k1EEAForwardUnitary indexedStepProductionRegisters) s w = s w :=
  secp256k1EEAForwardUnitary_production_usesOnly.preservesOutside s
    (by simpa only [List.mem_range,not_lt] using hw)

/-- Inputs agreeing on the allocated EEA registers produce the same values on those registers. -/
theorem secp256k1EEAForwardUnitary_production_congrOn
    (s t : BasisState) (h : ∀ w, w < 580 → s w = t w) :
    ∀ w, w < 580 →
      run (secp256k1EEAForwardUnitary indexedStepProductionRegisters) s w =
      run (secp256k1EEAForwardUnitary indexedStepProductionRegisters) t w := by
  simpa only [List.mem_range] using
    secp256k1EEAForwardUnitary_production_usesOnly.run_congrOn s t (by
      simpa only [List.mem_range] using h)

attribute [local irreducible] intervalAddSubInverseUnitary coefficientPrefixInverseUnitary
  phaseUpdateEpochInverseUnitary terminalPaddingInverse swapWorkAndLengthUnarySharedInverse

/-- The literal reverse production step stays inside the same 580 physical roles. -/
theorem indexedStepInverseUnitary_production_usesOnly (T : Nat)
    (hlayout : IndexedStepLayout indexedStepProductionRegisters 256 T) :
    PaperCircuitUsesOnly (List.range 580)
      (indexedStepInverseUnitary indexedStepProductionRegisters 256 T) := by
  let r := indexedStepProductionRegisters
  let windows := certifiedActiveWindows 256 T
  have terminalTest := (computeControl_usesOnly (r.phase1 :: r.lengthRPrime)
    (2^(r.lengthRPrime.length+1)-2) r.terminal r.blockScratch).mono
    (support_to_580 _ (by decide +kernel))
  have terminalRestore := (terminalEpochRestore_usesOnly r.terminal r.shiftEpoch r.quotientLow).mono
    (support_to_580 _ (by decide +kernel))
  have terminalSpill := (terminalEpochSpill_usesOnly r.terminal r.shiftEpoch r.quotientLow).mono
    (support_to_580 _ (by decide +kernel))
  have phaseToggle := gate_support_580 (.CX r.terminal r.phase1) (by decide +kernel)
  have preShift := ((preShiftUnitary_usesOnly r.preShift).mono
    (support_to_580 _ (by decide +kernel))).adjoint
  have padding := (terminalPaddingInverse_usesOnly r.terminalPadding).mono
    (support_to_580 _ (by decide +kernel))
  have hA := (((((terminalTest.append terminalRestore).append phaseToggle).append preShift).append phaseToggle).append padding).append terminalTest
  have hC := (terminalTest.append terminalSpill).append terminalTest
  have hF := production_blockF_support.adjoint
  have hG := (phaseUpdateEpochInverseUnitary_usesOnly r.phaseUpdate r.shiftEpoch).mono
    (support_to_580 _ (by decide +kernel))
  have subControl := (rControlNonterminal_usesOnly [r.phase1] 0 r.control r.lengthRPrime
    r.terminal r.blockScratch).mono (support_to_580 _ (by decide +kernel))
  have restoreControl := (rControlNonterminal_usesOnly [r.phase1,r.terminal] 0 r.control r.lengthRPrime
    (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)).mono (support_to_580 _ (by decide +kernel))
  have terminalCCX := gate_support_580 (.CCX r.phase2 r.sign r.terminal) (by decide +kernel)
  have restore := (terminalCCX.append restoreControl).append terminalCCX
  have invSub := (intervalAddSubInverseUnitary_usesOnly (r.remainder windows.remainder) 256
    windows.remainder.start windows.remainder.stop .sub true .work1 hlayout.remainder).mono
    (production_remainder_support windows.remainder)
  have invAdd := (intervalAddSubInverseUnitary_usesOnly (r.remainder windows.remainder) 256
    windows.remainder.start windows.remainder.stop .add false .work1 hlayout.remainder).mono
    (production_remainder_support windows.remainder)
  have phaseControl := (rControlNonterminal_usesOnly [r.phase1,r.phase2] 2 r.control r.lengthRPrime
    r.terminal r.blockScratch).mono (support_to_580 _ (by decide +kernel))
  have signCX := gate_support_580 (.CX r.control r.sign) (by decide +kernel)
  have hB := (((restore.append invAdd).append restore).append
    ((phaseControl.append signCX).append phaseControl)).append
    ((subControl.append invSub).append subControl)
  have p2 := (computeControl_usesOnly [r.phase1,r.phase2] 2 r.control r.sourceScratch).mono
    (support_to_580 _ (by decide +kernel))
  have p3 := (computeControl_usesOnly [r.phase1,r.phase2] 1 r.control r.sourceScratch).mono
    (support_to_580 _ (by decide +kernel))
  have inc := (controlledIncrement_usesOnly r.control r.lengthQ
    (r.sourceScratch.take (r.lengthQ.length-1))).mono (support_to_580 _ (by decide +kernel))
  have dec := (controlledDecrement_usesOnly r.control r.lengthQ
    (r.sourceScratch.take (r.lengthQ.length-1))).mono (support_to_580 _ (by decide +kernel))
  have cx1 := gate_support_580 (.CX r.phase1 r.control) (by decide +kernel)
  have cx2 := gate_support_580 (.CX r.phase2 r.control) (by decide +kernel)
  have qs := (quotientSwapUnitary_usesOnly (r.quotient windows.quotientSwap) hlayout.quotient).mono
    (production_quotient_support windows.quotientSwap)
  have hD := (((p3.append inc).append p3).append
    (((cx1.append cx2).append qs).append (cx2.append cx1))).append ((p2.append dec).append p2)
  have temp := (computeControl_usesOnly [r.phase2,r.sign] 2 r.terminal r.blockScratch).mono
    (support_to_580 _ (by decide +kernel))
  have coefSub := (computeControl_usesOnly [r.phase1,r.terminal] 1 r.control r.blockScratch).mono
    (support_to_580 _ (by decide +kernel))
  have coefAdd := (computeControl_usesOnly [r.phase1] 1 r.control r.blockScratch).mono
    (support_to_580 _ (by decide +kernel))
  have prepare := (prepareLatestPaperTBoundary_usesOnly r.tBoundary 256).mono
    (support_to_580 _ (by decide +kernel))
  have finish := (restoreLatestPaperTBoundary_usesOnly r.tBoundary 256).mono
    (support_to_580 _ (by decide +kernel))
  have csub := (coefficientPrefixInverseUnitary_usesOnly (r.coefficient windows.coefficient)
    .sub false .work2 hlayout.coefficient).mono (production_coefficient_support windows.coefficient)
  have cadd := (coefficientPrefixInverseUnitary_usesOnly (r.coefficient windows.coefficient)
    .add true .work2 hlayout.coefficient).mono (production_coefficient_support windows.coefficient)
  have flipSign := gate_support_580 (.CX r.phase1 r.sign) (by decide +kernel)
  have hE := ((((((((((((prepare.append coefAdd).append cadd).append coefAdd).append flipSign).append temp).append coefSub).append temp).append csub).append temp).append coefSub).append temp).append finish)
  have hH : PaperCircuitUsesOnly (List.range 580) (
    if T % 4 = 0 then
        circuit! {
          mcxVChain r.lengthQ (r.sourceScratch.getD 0 0)
            (r.sourceScratch.drop 2);
          gate! Gate.X r.shiftEpoch;
          mcxVChain (r.lengthS ++ [r.shiftEpoch])
            (r.sourceScratch.getD 1 0) (r.sourceScratch.drop 2);
          gate! Gate.X r.shiftEpoch;
          gate! Gate.CCX (r.sourceScratch.getD 0 0)
            (r.sourceScratch.getD 1 0) r.control;
          gate! Gate.CX r.control r.iter;
          swapWorkAndLengthUnarySharedInverse (r.endIteration 256 T) 256
            (endIterationWindowsAt 256 T);
          gate! Gate.CCX (r.sourceScratch.getD 0 0)
            (r.sourceScratch.getD 1 0) r.control;
          gate! Gate.X r.shiftEpoch;
          mcxVChain (r.lengthS ++ [r.shiftEpoch])
            (r.sourceScratch.getD 1 0) (r.sourceScratch.drop 2);
          gate! Gate.X r.shiftEpoch;
          mcxVChain r.lengthQ (r.sourceScratch.getD 0 0)
            (r.sourceScratch.drop 2)
        }
      else []) := by
    split
    · rename_i hmod
      have he := hlayout.endIteration hmod
      have hq := (mcxVChain_usesOnly r.lengthQ (r.sourceScratch.getD 0 0)
        (r.sourceScratch.drop 2)).mono (support_to_580 _ (by decide +kernel))
      have hs := (mcxVChain_usesOnly (r.lengthS ++ [r.shiftEpoch]) (r.sourceScratch.getD 1 0)
        (r.sourceScratch.drop 2)).mono (support_to_580 _ (by decide +kernel))
      have hx := gate_support_580 (.X r.shiftEpoch) (by decide +kernel)
      have hc := gate_support_580 (.CCX (r.sourceScratch.getD 0 0)
        (r.sourceScratch.getD 1 0) r.control) (by decide +kernel)
      have hi := gate_support_580 (.CX r.control r.iter) (by decide +kernel)
      have hw := (swapWorkAndLengthUnarySharedInverse_usesOnly (r.endIteration 256 T) 256
        (endIterationWindowsAt 256 T) he.k4_le_K4 he.k5_le_decode).mono
        (production_end_support T he)
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using ((((((((((hq.append hx).append hs).append hx).append hc).append hi).append hw).append hc).append hx).append hs).append hx).append hq
    · intro g hg; simp only [List.not_mem_nil] at hg
  have hall := ((((((hH.append hG).append hF).append hE).append hD).append hC).append hB).append hA
  change PaperCircuitUsesOnly (List.range 580)
    (((if T % 4 = 0 then
    circuit! {
      mcxVChain r.lengthQ (r.sourceScratch.getD 0 0)
        (r.sourceScratch.drop 2);
      gate! Gate.X r.shiftEpoch;
      mcxVChain (r.lengthS ++ [r.shiftEpoch])
        (r.sourceScratch.getD 1 0) (r.sourceScratch.drop 2);
      gate! Gate.X r.shiftEpoch;
      gate! Gate.CCX (r.sourceScratch.getD 0 0)
        (r.sourceScratch.getD 1 0) r.control;
      gate! Gate.CX r.control r.iter;
      swapWorkAndLengthUnarySharedInverse (r.endIteration 256 T) 256
        (endIterationWindowsAt 256 T);
      gate! Gate.CCX (r.sourceScratch.getD 0 0)
        (r.sourceScratch.getD 1 0) r.control;
      gate! Gate.X r.shiftEpoch;
      mcxVChain (r.lengthS ++ [r.shiftEpoch])
        (r.sourceScratch.getD 1 0) (r.sourceScratch.drop 2);
      gate! Gate.X r.shiftEpoch;
      mcxVChain r.lengthQ (r.sourceScratch.getD 0 0)
        (r.sourceScratch.drop 2)
    }
  else []) ++ phaseUpdateEpochInverseUnitary r.phaseUpdate r.shiftEpoch ++
      (postShiftUnitary r.postShift).adjoint ++
      (circuit! {
        prepareLatestPaperTBoundary r.tBoundary 256;
        computeControl [r.phase1] 1 r.control r.blockScratch;
        coefficientPrefixInverseUnitary (r.coefficient windows.coefficient) windows.coefficient.start windows.coefficient.stop .add true .work2;
        computeControl [r.phase1] 1 r.control r.blockScratch;
        gate! Gate.CX r.phase1 r.sign;
        computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch;
        computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch;
        computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch;
        coefficientPrefixInverseUnitary (r.coefficient windows.coefficient) windows.coefficient.start windows.coefficient.stop .sub false .work2;
        computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch;
        computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch;
        computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch;
        restoreLatestPaperTBoundary r.tBoundary 256
      }) ++
      (circuit! {
        computeControl [r.phase1,r.phase2] 1 r.control r.sourceScratch;
        controlledIncrement r.control r.lengthQ (r.sourceScratch.take (r.lengthQ.length-1));
        computeControl [r.phase1,r.phase2] 1 r.control r.sourceScratch;
        [Gate.CX r.phase1 r.control,Gate.CX r.phase2 r.control];
        quotientSwapUnitary (r.quotient windows.quotientSwap) windows.quotientSwap.start windows.quotientSwap.stop;
        [Gate.CX r.phase2 r.control,Gate.CX r.phase1 r.control];
        computeControl [r.phase1,r.phase2] 2 r.control r.sourceScratch;
        controlledDecrement r.control r.lengthQ (r.sourceScratch.take (r.lengthQ.length-1));
        computeControl [r.phase1,r.phase2] 2 r.control r.sourceScratch
      }) ++
      (circuit! {
        computeControl (r.phase1::r.lengthRPrime) (2^(r.lengthRPrime.length+1)-2) r.terminal r.blockScratch;
        terminalEpochSpill r.terminal r.shiftEpoch r.quotientLow;
        computeControl (r.phase1::r.lengthRPrime) (2^(r.lengthRPrime.length+1)-2) r.terminal r.blockScratch
      }) ++
      ((circuit! {
        ([Gate.CCX r.phase2 r.sign r.terminal] ++
          rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1) ++
          [Gate.CCX r.phase2 r.sign r.terminal]);
        intervalAddSubInverseUnitary (r.remainder windows.remainder) 256 windows.remainder.start windows.remainder.stop .add false .work1;
        ([Gate.CCX r.phase2 r.sign r.terminal] ++
          rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1) ++
          [Gate.CCX r.phase2 r.sign r.terminal])
      }) ++ (circuit! {
        rControlNonterminal [r.phase1,r.phase2] 2 r.control r.lengthRPrime r.terminal r.blockScratch;
        [Gate.CX r.control r.sign];
        rControlNonterminal [r.phase1,r.phase2] 2 r.control r.lengthRPrime r.terminal r.blockScratch
      }) ++ (circuit! {
        rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch;
        intervalAddSubInverseUnitary (r.remainder windows.remainder) 256 windows.remainder.start windows.remainder.stop .sub true .work1;
        rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch
      })) ++
      (circuit! {
        computeControl (r.phase1::r.lengthRPrime) (2^(r.lengthRPrime.length+1)-2) r.terminal r.blockScratch;
        terminalEpochRestore r.terminal r.shiftEpoch r.quotientLow;
        [Gate.CX r.terminal r.phase1];
        (preShiftUnitary r.preShift).adjoint;
        [Gate.CX r.terminal r.phase1];
        terminalPaddingInverse r.terminalPadding;
        computeControl (r.phase1::r.lengthRPrime) (2^(r.lengthRPrime.length+1)-2) r.terminal r.blockScratch
      })))
  simpa only [blockFForward,List.append_assoc,List.cons_append,List.nil_append] using hall

end ShorECDLP.Paper2607_13816
