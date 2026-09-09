import ShorECDLP.Submission.«2607_13816».EEA.TopBoundary

/-! # Numeric main scans inside the physical interval body -/
namespace ShorECDLP.Paper2607_13816
open Classical

private def inputs (r : IntervalRegisters) : List Wire := r.control :: (r.lengthQ ++ r.lengthS)

private def sameInputs (r : IntervalRegisters) (s t : BasisState) : Prop :=
  ∀ w ∈ inputs r, s w = t w

private theorem top_first_inputs (r : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (state : BasisState) (h : IntervalLayout r k K target)
    (hc : Clean (r.cellScratch k K :: r.equalityScratch k K) state) :
    sameInputs r (run (intervalTopFirst r k K mode target) state) state := by
  rw [run_intervalTopFirst_state r k K mode target state h hc]
  intro w hw
  have hi := intervalTopInputs_disjoint_roles r k K target h
  have hn (v : Wire) (hv : v ∈ [r.accumulator k K, r.targetAt target (intervalTopRelative k K),
      r.addendAt target (intervalTopRelative k K), r.carry k K]) : w ≠ v :=
    fun he => hi v hv (he ▸ hw)
  have ha := hn _ (by simp : r.accumulator k K ∈ _)
  have ht := hn _ (by simp : r.targetAt target (intervalTopRelative k K) ∈ _)
  have hb := hn _ (by simp : r.addendAt target (intervalTopRelative k K) ∈ _)
  have hk := hn _ (by simp : r.carry k K ∈ _)
  unfold intervalTopFirstState
  split
  · simp [topSpecialFirstLeafState, writeRippleCell, upd, ha, ht, hb, hk]
  · rfl

private theorem inclusive_first_inputs (r : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (state : BasisState) (enabled : Bool) (L R j : Nat)
    (h : IntervalLayout r k K target) (hj : j < intervalLaneCount k K) :
    sameInputs r
      (intervalFirstInclusiveCell mode enabled (r.accumulator k K) (r.targetAt target j)
        (r.addendAt target j) (r.carry k K) L R j state) state := by
  intro w hw
  have hn (v : Wire) (hv : v ∈ [r.accumulator k K, r.targetAt target j, r.addendAt target j, r.carry k K]) : w ≠ v := by
    intro he
    exact List.disjoint_left.mp (intervalInputs_disjoint_workScratch r h.physical) (he ▸ hw)
      (intervalWrittenRoles_mem_workScratch r k K target h j hj v hv)
  have ha := hn _ (by simp : r.accumulator k K ∈ _)
  have ht := hn _ (by simp : r.targetAt target j ∈ _)
  have hb := hn _ (by simp : r.addendAt target j ∈ _)
  have hk := hn _ (by simp : r.carry k K ∈ _)
  simp [intervalFirstInclusiveCell, writeRippleCell, upd, ha, ht, hb, hk]

private theorem first_fold_inputs (r : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (state : BasisState) (enabled : Bool) (L R : Nat)
    (labels : List Nat) (h : IntervalLayout r k K target)
    (hlabels : ∀ j ∈ labels, j < intervalLaneCount k K) :
    sameInputs r (labels.foldl (fun s j => intervalFirstInclusiveCell mode enabled
      (r.accumulator k K) (r.targetAt target j) (r.addendAt target j) (r.carry k K) L R j s) state) state := by
  induction labels generalizing state with
  | nil => exact fun _ _ => rfl
  | cons j labels ih =>
    have hf := inclusive_first_inputs r k K mode target state enabled L R j h (hlabels j (by simp))
    have ht := ih (intervalFirstInclusiveCell mode enabled (r.accumulator k K)
      (r.targetAt target j) (r.addendAt target j) (r.carry k K) L R j state)
      (fun j hj => hlabels j (by simp [hj]))
    exact fun w hw => (ht w hw).trans (hf w hw)

private theorem inputs_values (r : IntervalRegisters) (s t : BasisState)
    (h : sameInputs r s t) :
    s r.control = t r.control ∧ wireValues r.lengthQ s = wireValues r.lengthQ t ∧
      wireValues r.lengthS s = wireValues r.lengthS t := by
  refine ⟨h _ (by simp [inputs]), ?_, ?_⟩
  · apply List.map_congr_left
    intro w hw
    exact h w (by simp [inputs, hw])
  · apply List.map_congr_left
    intro w hw
    exact h w (by simp [inputs, hw])

private theorem sign_inputs (r : IntervalRegisters) (k K : Nat) (signUpdate : Bool)
    (target : IntervalTarget) (state : BasisState) (h : IntervalLayout r k K target) :
    sameInputs r (run (intervalSignUpdate r k K signUpdate) state) state := by
  obtain ⟨hc, _, ht⟩ := List.nodup_append.mp h.physical
  intro w hw
  apply intervalSignUpdate_agreesOutsideSign r k K signUpdate state w
  simp only [List.mem_singleton]
  intro he
  subst w
  simp only [inputs, List.mem_cons, List.mem_append] at hw
  rcases hw with he | hq | hs
  · have hn := (List.nodup_cons.mp hc).1
    exact hn (by simp [he])
  · exact ht r.sign (by simp) r.sign (by simp [hq]) rfl
  · exact ht r.sign (by simp) r.sign (by simp [hs]) rfl

/-- The interval body with both main scans controlled by their numeric inclusive interval.
The separate top operations and sign update retain their actual circuits. -/
def intervalNumericBodyState (r : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) (state : BasisState) : BasisState :=
  let L := boolWordToNat (wireValues r.lengthQ state)
  let R := boolWordToNat (wireValues r.lengthS state)
  let afterTop := run (intervalTopFirst r k K mode target) state
  let afterFirst := ((intervalTree r k K).visitLabels .dec).foldl (fun s j =>
    intervalFirstInclusiveCell mode (state r.control) (r.accumulator k K)
      (r.targetAt target j) (r.addendAt target j) (r.carry k K) L R j s) afterTop
  let afterSign := run (intervalSignUpdate r k K signUpdate) afterFirst
  let afterSecond := ((intervalTree r k K).visitLabels .inc).foldl (fun s j =>
    intervalSecondInclusiveCell mode (state r.control) (r.accumulator k K)
      (r.targetAt target j) (r.addendAt target j) (r.carry k K) L R j s) afterSign
  run (intervalTopSecond r k K mode target) afterSecond

/-- The actual complete interval body executes the numeric scans, with no separate
pulse or incoming-scan-accumulator assumptions. -/
theorem run_intervalAddSubBody_numeric (r : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) (state : BasisState)
    (h : IntervalLayout r k K target)
    (hclean : Clean (r.cellScratch k K :: r.equalityScratch k K) state)
    (hacc : state (r.accumulator k K) = false)
    (hr : boolWordToNat (wireValues r.lengthS state) ≤ intervalTopRelative k K)
    (hl : boolWordToNat (wireValues r.lengthQ state) ≤ intervalTopRelative k K)
    (horder : boolWordToNat (wireValues r.lengthQ state) ≤ boolWordToNat (wireValues r.lengthS state)) :
    run (intervalAddSubBodyUnitary r k K mode signUpdate target) state =
      intervalNumericBodyState r k K mode signUpdate target state := by
  let first := intervalFirstTraversal mode (intervalHasTopSpecial k K) (r.rightTop k K)
    (r.leftTop k K) (r.accumulator k K) (r.carry k K) (r.cellScratch k K)
    (r.targetAt target) (r.addendAt target) (intervalTree r k K) r.control r.control
    (r.rightPaths k K) (r.leftPaths k K)
  let second := intervalSecondTraversal mode (intervalHasTopSpecial k K) (r.rightTop k K)
    (r.leftTop k K) (r.accumulator k K) (r.carry k K) (r.cellScratch k K)
    (r.targetAt target) (r.addendAt target) (intervalTree r k K) r.control r.control
    (r.rightPaths k K) (r.leftPaths k K)
  let afterTop := run (intervalTopFirst r k K mode target) state
  have htFrame := top_first_inputs r k K mode target state h hclean
  have htValues := inputs_values r afterTop state htFrame
  have htClean := intervalTopFirst_cleanTopScratch r k K mode target state h hclean
  have htPaths := intervalPaths_clean_of_topScratch r k K afterTop htClean
  have htCell : Clean [r.cellScratch k K] afterTop := fun w hw =>
    htClean w (List.mem_cons.mpr (Or.inl (by simpa using hw)))
  have htAcc := intervalTopFirst_accumulatorBoundary r k K mode target state h hclean hacc horder hr
  have hf := run_intervalFirstTraversal_numericScan r k K mode target afterTop h
    (by simpa only [htValues.2.2] using hr) (by simpa only [htValues.2.1] using hl)
    (by simpa only [htValues.2.1, htValues.2.2] using horder)
    htPaths.1 htPaths.2 htCell (by simpa only [htValues.1, htValues.2.1, htValues.2.2] using htAcc)
  simp only [htValues.1, htValues.2.1, htValues.2.2] at hf
  let afterFirst := run first afterTop
  have hfFrame : sameInputs r afterFirst state := by
    have hfold := first_fold_inputs r k K mode target afterTop (state r.control)
      (boolWordToNat (wireValues r.lengthQ state)) (boolWordToNat (wireValues r.lengthS state))
      ((intervalTree r k K).visitLabels .dec) h (by
        intro j hj
        apply intervalTree_label_lt_laneCount r k K j
        simpa only [DualUnaryActionTree.visitLabels_dec, List.mem_reverse] using hj)
    intro w hw
    change run first afterTop w = state w
    rw [show run first afterTop = _ from hf.1]
    exact (hfold w hw).trans (htFrame w hw)
  have hfClean := intervalFirstTraversal_cleanWithScratch mode (intervalHasTopSpecial k K)
    (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K) (r.cellScratch k K)
    (r.targetAt target) (r.addendAt target) (intervalTree r k K) r.control r.control
    (r.rightPaths k K) (r.leftPaths k K) afterTop h.traversal htPaths.1 htPaths.2 htCell
  let afterSign := run (intervalSignUpdate r k K signUpdate) afterFirst
  have hsFrame := sign_inputs r k K signUpdate target afterFirst h
  have hsValues := inputs_values r afterSign state (fun w hw => (hsFrame w hw).trans (hfFrame w hw))
  have hsClean (ws : List Wire) (hc : Clean ws afterFirst) (hm : ∀ w ∈ ws, w ∈ r.scratch) : Clean ws afterSign := by
    intro w hw
    rw [show afterSign w = afterFirst w from intervalSignUpdate_preservesScratch r k K signUpdate target afterFirst h w (hm w hw)]
    exact hc w hw
  have hsRight := hsClean (r.rightPaths k K) hfClean.1 (fun _ hw => List.mem_of_mem_take hw)
  have hsLeft := hsClean (r.leftPaths k K) hfClean.2.1 (fun _ hw => List.mem_of_mem_drop (List.mem_of_mem_take hw))
  have hsCell := hsClean [r.cellScratch k K] hfClean.2.2 (by
    intro w hw
    have he : w = r.cellScratch k K := by simpa using hw
    exact he ▸ intervalCellScratch_mem_scratch r k K target h)
  have hsAcc : afterSign (r.accumulator k K) = false := by
    rw [show afterSign (r.accumulator k K) = afterFirst (r.accumulator k K) from
      intervalSignUpdate_preservesScratch r k K signUpdate target afterFirst h _
        (intervalAccumulator_mem_scratch r k K target h)]
    simpa only [intervalAccumulatorBoundary, Nat.not_lt_zero, false_and, decide_false, Bool.and_false] using hf.2
  have hs := run_intervalSecondTraversal_numericScan r k K mode target afterSign h
    (by simpa only [hsValues.2.2] using hr) (by simpa only [hsValues.2.1] using hl)
    (by simpa only [hsValues.2.1, hsValues.2.2] using horder)
    hsRight hsLeft hsCell (by simpa [intervalAccumulatorBoundary] using hsAcc)
  simp only [hsValues.1, hsValues.2.1, hsValues.2.2] at hs
  have hfirst : run first afterTop = _ := hf.1
  have hsecond : run second afterSign = _ := hs.1
  simp only [intervalAddSubBodyUnitary, Classical.run_append]
  change run (intervalTopSecond r k K mode target) (run second afterSign) = _
  rw [hsecond]
  simp only [intervalNumericBodyState]
  dsimp only [afterSign, afterFirst]
  rw [hfirst]

/-- The complete source interval, including actual endpoint preparation and restoration,
executes the numeric body when its prepared endpoints are ordered and in range. -/
theorem run_intervalAddSubUnitary_numeric (r : IntervalRegisters) (n k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget) (state : BasisState)
    (h : IntervalLayout r k K target) (hready : IntervalReady r state)
    (hvalues : let p := run (prepareIntervalEndpoints r.lengthT r.lengthQ r.lengthS
        r.endpointScratch (r.carry k K) n k) state
      boolWordToNat (wireValues r.lengthS p) ≤ intervalTopRelative k K ∧
        boolWordToNat (wireValues r.lengthQ p) ≤ boolWordToNat (wireValues r.lengthS p)) :
    run (intervalAddSubUnitary r n k K mode signUpdate target) state =
      let p := run (prepareIntervalEndpoints r.lengthT r.lengthQ r.lengthS
        r.endpointScratch (r.carry k K) n k) state
      run (restoreIntervalEndpoints r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) n k)
        (intervalNumericBodyState r k K mode signUpdate target p) := by
  let p := run (prepareIntervalEndpoints r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) n k) state
  have hc : Clean r.scratch p := intervalPrepare_cleanScratch r n k K target state h hready
  have hv : boolWordToNat (wireValues r.lengthS p) ≤ intervalTopRelative k K ∧
      boolWordToNat (wireValues r.lengthQ p) ≤ boolWordToNat (wireValues r.lengthS p) := hvalues
  have hb := run_intervalAddSubBody_numeric r k K mode signUpdate target p h
    (fun w hw => hc w (intervalTopScratch_mem_scratch r k K target h w hw))
    (hc _ (intervalAccumulator_mem_scratch r k K target h)) hv.1 (hv.2.trans hv.1) hv.2
  have hshape : intervalAddSubUnitary r n k K mode signUpdate target =
      prepareIntervalEndpoints r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) n k ++
        intervalAddSubBodyUnitary r k K mode signUpdate target ++
          restoreIntervalEndpoints r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) n k := by
    simp only [intervalAddSubUnitary, intervalAddSubBodyUnitary, List.append_assoc]
  rw [hshape, Classical.run_append, Classical.run_append]
  exact congrArg (run (restoreIntervalEndpoints r.lengthT r.lengthQ r.lengthS r.endpointScratch
    (r.carry k K) n k)) hb

end ShorECDLP.Paper2607_13816
