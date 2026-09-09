import ShorECDLP.Submission.«2607_13816».EEA.TopInclusive
import ShorECDLP.Submission.«2607_13816».EEA.InclusiveWords

/-! # Word semantics of the complete physical interval body -/
namespace ShorECDLP.Paper2607_13816
open Classical

private theorem map_getD_range (ws : List Wire) :
    (List.range ws.length).map (fun i => ws.getD i 0) = ws := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem ws 0 hj

private theorem word_layout (r : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (h : IntervalLayout r k K target) :
    (r.accumulator k K :: r.carry k K ::
      ((List.range (intervalLaneCount k K)).map (r.targetAt target) ++
        (List.range (intervalLaneCount k K)).map (r.addendAt target))).Nodup := by
  obtain ⟨j,hj⟩ := List.exists_mem_of_ne_nil (intervalMainLabels k K) (intervalMainLabels_nonempty k K)
  have hj' : j ∈ (intervalTree r k K).labels := by
    simpa [intervalTree_labels] using hj
  have hn := (h.traversal.2 j hj').1
  have ha := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2).1
  have hac : r.accumulator k K ≠ r.carry k K := by
    intro he
    apply ha
    simp [he]
  have ham := intervalAccumulator_mem_scratch r k K target h
  have hcm := intervalCarry_mem_scratch r k K target h
  have ha1 := intervalScratch_not_mem_work1 r k K target h ham
  have ha2 := intervalScratch_not_mem_work2 r k K target h ham
  have hc1 := intervalScratch_not_mem_work1 r k K target h hcm
  have hc2 := intervalScratch_not_mem_work2 r k K target h hcm
  have h1 := intervalWork1_nodup r k K target h
  have h2 := intervalWork2_nodup r k K target h
  have hd := intervalWork1_disjoint_work2 r k K target h
  cases target with
  | work1 =>
    have ht : (List.range (intervalLaneCount k K)).map (r.targetAt .work1) = r.work1 := by
      simpa only [IntervalRegisters.targetAt, ← h.work1_length] using map_getD_range r.work1
    have hb : (List.range (intervalLaneCount k K)).map (r.addendAt .work1) = r.work2 := by
      simpa only [IntervalRegisters.addendAt, ← h.work2_length] using map_getD_range r.work2
    rw [ht,hb]
    simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or]
    exact ⟨⟨hac,ha1,ha2⟩,⟨hc1,hc2⟩, List.nodup_append.mpr ⟨h1,h2,fun a ha b hb he => hd ha (he ▸ hb)⟩⟩
  | work2 =>
    have ht : (List.range (intervalLaneCount k K)).map (r.targetAt .work2) = r.work2 := by
      simpa only [IntervalRegisters.targetAt, ← h.work2_length] using map_getD_range r.work2
    have hb : (List.range (intervalLaneCount k K)).map (r.addendAt .work2) = r.work1 := by
      simpa only [IntervalRegisters.addendAt, ← h.work1_length] using map_getD_range r.work1
    rw [ht,hb]
    simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or]
    exact ⟨⟨hac,ha2,ha1⟩,⟨hc2,hc1⟩, List.nodup_append.mpr ⟨h2,h1,fun a ha b hb he => hd hb (he ▸ ha)⟩⟩

private theorem cell_preserves (second : Bool) (mode : RippleMode) (enabled : Bool)
    (acc t a c L R j : Nat) (state : BasisState) (w : Wire) (hw : w ∉ [acc,t,a,c]) :
    (if second then intervalSecondInclusiveCell mode enabled acc t a c L R j state
      else intervalFirstInclusiveCell mode enabled acc t a c L R j state) w = state w := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
  cases second <;> simp [intervalFirstInclusiveCell, intervalSecondInclusiveCell,
    writeRippleCell, upd, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2]

private theorem fold_preserves (second : Bool) (mode : RippleMode) (enabled : Bool)
    (acc c L R : Nat) (t a : Nat → Wire) (labels : List Nat) (state : BasisState) (w : Wire)
    (hw : ∀ j ∈ labels, w ∉ [acc,t j,a j,c]) :
    (labels.foldl (fun s j => if second then intervalSecondInclusiveCell mode enabled acc (t j) (a j) c L R j s
      else intervalFirstInclusiveCell mode enabled acc (t j) (a j) c L R j s) state) w = state w := by
  induction labels generalizing state with
  | nil => rfl
  | cons j labels ih =>
    rw [List.foldl_cons, ih _ (fun i hi => hw i (by simp [hi]))]
    exact cell_preserves second mode enabled acc (t j) (a j) c L R j state w (hw j (by simp))

private theorem topScratch_outside (r : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (h : IntervalLayout r k K target) (hspecial : intervalHasTopSpecial k K = true)
    (j : Nat) (hj : j ∈ (intervalTree r k K).labels) :
    ∀ w ∈ r.cellScratch k K :: r.equalityScratch k K,
      w ∉ [r.accumulator k K, r.targetAt target j, r.addendAt target j, r.carry k K] := by
  intro w hw hr
  rcases List.mem_cons.mp hw with hw | hw
  · subst w
    have hn := (h.traversal.2 j hj).1
    have hc := List.nodup_append.mp (show
      ([r.rightTop k K,r.leftTop k K,r.accumulator k K,r.targetAt target j,r.addendAt target j,r.carry k K] ++
        [r.cellScratch k K]).Nodup from hn)
    exact hc.2.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
      _ (by simp) rfl
  · apply intervalEqualityScratch_outsideLeafRoles r k K j target h hspecial hj w hw
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_left [r.cellScratch k K] hr))

private theorem input_outside (r : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (h : IntervalLayout r k K target) (j : Nat) (hj : j < intervalLaneCount k K) :
    ∀ w ∈ r.control :: (r.lengthQ ++ r.lengthS),
      w ∉ [r.accumulator k K, r.targetAt target j, r.addendAt target j, r.carry k K] := by
  intro w hw hr
  exact List.disjoint_left.mp (intervalInputs_disjoint_workScratch r h.physical) hw
    (intervalWrittenRoles_mem_workScratch r k K target h j hj w hr)

private theorem input_values (r : IntervalRegisters) (s u : BasisState)
    (h : ∀ w ∈ r.control :: (r.lengthQ ++ r.lengthS), s w = u w) :
    s r.control = u r.control ∧ wireValues r.lengthQ s = wireValues r.lengthQ u ∧
      wireValues r.lengthS s = wireValues r.lengthS u := by
  refine ⟨h _ (by simp), ?_, ?_⟩
  · apply List.map_congr_left
    exact fun w hw => h w (by simp [hw])
  · apply List.map_congr_left
    exact fun w hw => h w (by simp [hw])

private theorem tree_labels_main (r : IntervalRegisters) (k K : Nat) :
    (intervalTree r k K).labels = intervalMainLabels k K := by
  rw [intervalTree_labels]
  unfold intervalMainLabels
  have hr (n : Nat) : (List.range n).toFinset = Finset.range n := by
    ext i
    simp
  split <;> rw [hr, Finset.sort_range]

private theorem main_range (k K : Nat) :
    intervalMainLabels k K = List.range (intervalMainLabels k K).length := by
  unfold intervalMainLabels
  split <;> simp

private theorem full_range (k K : Nat) (hs : intervalHasTopSpecial k K = true) :
    List.range (intervalLaneCount k K) = intervalMainLabels k K ++ [intervalTopRelative k K] := by
  have hn : intervalLaneCount k K = (intervalLaneCount k K - 1) + 1 := by
    simp [intervalLaneCount]
  rw [show List.range (intervalLaneCount k K) = List.range ((intervalLaneCount k K - 1)+1) from congrArg List.range hn,
    List.range_succ]
  simp [intervalMainLabels, hs, intervalTopRelative]

private def firstMain (r : IntervalRegisters) (k K : Nat) (mode : RippleMode) (target : IntervalTarget)
    (enabled : Bool) (L R : Nat) (state : BasisState) : BasisState :=
  (intervalMainLabels k K).reverse.foldl (fun s j => intervalFirstInclusiveCell mode enabled
    (r.accumulator k K) (r.targetAt target j) (r.addendAt target j) (r.carry k K) L R j s) state

private def secondMain (r : IntervalRegisters) (k K : Nat) (mode : RippleMode) (target : IntervalTarget)
    (enabled : Bool) (L R : Nat) (state : BasisState) : BasisState :=
  (intervalMainLabels k K).foldl (fun s j => intervalSecondInclusiveCell mode enabled
    (r.accumulator k K) (r.targetAt target j) (r.addendAt target j) (r.carry k K) L R j s) state

private theorem first_full (r : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (state : BasisState) (h : IntervalLayout r k K target)
    (hc : Clean (r.cellScratch k K :: r.equalityScratch k K) state)
    (ha : state (r.accumulator k K) = false)
    (hr : boolWordToNat (wireValues r.lengthS state) ≤ intervalTopRelative k K)
    (ho : boolWordToNat (wireValues r.lengthQ state) ≤ boolWordToNat (wireValues r.lengthS state)) :
    firstMain r k K mode target (state r.control) (boolWordToNat (wireValues r.lengthQ state))
      (boolWordToNat (wireValues r.lengthS state)) (run (intervalTopFirst r k K mode target) state) =
      (List.range (intervalLaneCount k K)).reverse.foldl (fun s j => intervalFirstInclusiveCell mode
        (state r.control) (r.accumulator k K) (r.targetAt target j) (r.addendAt target j) (r.carry k K)
        (boolWordToNat (wireValues r.lengthQ state)) (boolWordToNat (wireValues r.lengthS state)) j s) state := by
  by_cases hs : intervalHasTopSpecial k K = true
  · rw [run_intervalTopFirst_inclusive r k K mode target state h hs hc ha hr ho, full_range k K hs]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.foldl_append, List.foldl_cons, List.foldl_nil, firstMain]
  · simp [firstMain, intervalTopFirst, intervalMainLabels, hs, Classical.run]

private theorem secondMain_acc (r : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (enabled : Bool) (L R : Nat) (state : BasisState) :
    secondMain r k K mode target enabled L R state (r.accumulator k K) =
      intervalAccumulatorBoundary enabled L R (intervalMainLabels k K).length := by
  have hn : 0 < (intervalMainLabels k K).length := List.length_pos_iff.mpr (intervalMainLabels_nonempty k K)
  have he : (intervalMainLabels k K).length = ((intervalMainLabels k K).length-1)+1 := by omega
  unfold secondMain
  rw [main_range k K]
  rw [show List.range (intervalMainLabels k K).length =
      List.range (((intervalMainLabels k K).length-1)+1) from congrArg List.range he,
    List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp [intervalSecondInclusiveCell, upd]

private theorem second_full (r : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (state : BasisState) (h : IntervalLayout r k K target)
    (hc : intervalHasTopSpecial k K = true → Clean (r.cellScratch k K :: r.equalityScratch k K) state)
    (hr : boolWordToNat (wireValues r.lengthS state) ≤ intervalTopRelative k K)
    (ho : boolWordToNat (wireValues r.lengthQ state) ≤ boolWordToNat (wireValues r.lengthS state)) :
    run (intervalTopSecond r k K mode target)
      (secondMain r k K mode target (state r.control) (boolWordToNat (wireValues r.lengthQ state))
        (boolWordToNat (wireValues r.lengthS state)) state) =
      (List.range (intervalLaneCount k K)).foldl (fun s j => intervalSecondInclusiveCell mode
        (state r.control) (r.accumulator k K) (r.targetAt target j) (r.addendAt target j) (r.carry k K)
        (boolWordToNat (wireValues r.lengthQ state)) (boolWordToNat (wireValues r.lengthS state)) j s) state := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · let afterMain := secondMain r k K mode target (state r.control)
      (boolWordToNat (wireValues r.lengthQ state)) (boolWordToNat (wireValues r.lengthS state)) state
    have hinputs : ∀ w ∈ r.control :: (r.lengthQ ++ r.lengthS), afterMain w = state w := by
      intro w hw
      have hp := fold_preserves true mode (state r.control) (r.accumulator k K) (r.carry k K)
        (boolWordToNat (wireValues r.lengthQ state)) (boolWordToNat (wireValues r.lengthS state))
        (r.targetAt target) (r.addendAt target) (intervalMainLabels k K) state w (by
          intro j hj
          apply input_outside r k K target h j _ w hw
          exact intervalTree_label_lt_laneCount r k K j (by rw [tree_labels_main]; exact hj))
      simpa only [afterMain, secondMain, reduceIte] using hp
    have hv := input_values r afterMain state hinputs
    have hclean : Clean (r.cellScratch k K :: r.equalityScratch k K) afterMain := by
      intro w hw
      have hp := fold_preserves true mode (state r.control) (r.accumulator k K) (r.carry k K)
        (boolWordToNat (wireValues r.lengthQ state)) (boolWordToNat (wireValues r.lengthS state))
        (r.targetAt target) (r.addendAt target) (intervalMainLabels k K) state w (by
          intro j hj
          exact topScratch_outside r k K target h hspecial j (by rw [tree_labels_main]; exact hj) w hw)
      have he : afterMain w = state w := by simpa only [afterMain, secondMain, reduceIte] using hp
      rw [he]
      exact hc hspecial w hw
    have ha : afterMain (r.accumulator k K) = intervalAccumulatorBoundary (afterMain r.control)
        (boolWordToNat (wireValues r.lengthQ afterMain)) (boolWordToNat (wireValues r.lengthS afterMain))
        (intervalTopRelative k K) := by
      rw [hv.1,hv.2.1,hv.2.2]
      simpa only [intervalMainLabels, hspecial, reduceIte, List.length_range, intervalTopRelative] using
        secondMain_acc r k K mode target (state r.control) (boolWordToNat (wireValues r.lengthQ state))
          (boolWordToNat (wireValues r.lengthS state)) state
    have hs := run_intervalTopSecond_inclusive r k K mode target afterMain h hspecial hclean ha
      (by simpa only [hv.2.2] using hr) (by simpa only [hv.2.1,hv.2.2] using ho)
    simp only [hv.1,hv.2.1,hv.2.2] at hs
    rw [show run (intervalTopSecond r k K mode target) afterMain = _ from hs, full_range k K hspecial]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, afterMain, secondMain]
  · simp [secondMain, intervalTopSecond, intervalMainLabels, hspecial, Classical.run]

private theorem fold_preserves_sign (second : Bool) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) (enabled : Bool) (L R : Nat)
    (labels : List Nat) (state : BasisState) (h : IntervalLayout r k K target)
    (hl : ∀ j ∈ labels, j < intervalLaneCount k K) :
    (labels.foldl (fun s j => if second then intervalSecondInclusiveCell mode enabled
      (r.accumulator k K) (r.targetAt target j) (r.addendAt target j) (r.carry k K) L R j s
      else intervalFirstInclusiveCell mode enabled (r.accumulator k K) (r.targetAt target j)
        (r.addendAt target j) (r.carry k K) L R j s) state) r.sign = state r.sign := by
  apply fold_preserves
  intro j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨Ne.symm (intervalScratch_ne_sign r k K target h (intervalAccumulator_mem_scratch r k K target h)),
    Ne.symm (intervalTargetAt_ne_sign r k K j target h (hl j hj)),
    Ne.symm (intervalAddendAt_ne_sign r k K j target h (hl j hj)),
    Ne.symm (intervalScratch_ne_sign r k K target h (intervalCarry_mem_scratch r k K target h))⟩

/-- The actual complete interval body produces the masked arithmetic word and
restores its addend and incoming carry, including the separate top operations.
The optional sign update uses the first pass's outgoing carry/borrow. -/
theorem run_intervalAddSubBody_words (r : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) (state : BasisState)
    (h : IntervalLayout r k K target)
    (hc : Clean (r.cellScratch k K :: r.equalityScratch k K) state)
    (ha : state (r.accumulator k K) = false)
    (hr : boolWordToNat (wireValues r.lengthS state) ≤ intervalTopRelative k K)
    (ho : boolWordToNat (wireValues r.lengthQ state) ≤ boolWordToNat (wireValues r.lengthS state)) :
    let labels := List.range (intervalLaneCount k K)
    let ts := labels.map (r.targetAt target)
    let ads := labels.map (r.addendAt target)
    let final := run (intervalAddSubBodyUnitary r k K mode signUpdate target) state
    let expected := maskedRippleExpectedWords mode
      (labels.map (fun j => state r.control && decide (boolWordToNat (wireValues r.lengthQ state) ≤ j ∧
        j ≤ boolWordToNat (wireValues r.lengthS state))))
      (wireValues ts state) (wireValues ads state) (state (r.carry k K))
    (wireValues ts final, wireValues ads final, final (r.carry k K)) =
      (expected.1, wireValues ads state, state (r.carry k K)) ∧
      final r.sign = (if signUpdate then state r.sign ^^ expected.2 else state r.sign) := by
  let labels := List.range (intervalLaneCount k K)
  let L := boolWordToNat (wireValues r.lengthQ state)
  let R := boolWordToNat (wireValues r.lengthS state)
  let afterFirst := labels.reverse.foldl (fun s j => intervalFirstInclusiveCell mode (state r.control)
    (r.accumulator k K) (r.targetAt target j) (r.addendAt target j) (r.carry k K) L R j s) state
  let afterSign := run (intervalSignUpdate r k K signUpdate) afterFirst
  have hfirst := first_full r k K mode target state h hc ha hr ho
  have hinputsFirst : ∀ w ∈ r.control :: (r.lengthQ ++ r.lengthS), afterFirst w = state w := by
    intro w hw
    have hp := fold_preserves false mode (state r.control) (r.accumulator k K) (r.carry k K) L R
      (r.targetAt target) (r.addendAt target) labels.reverse state w (by
        intro j hj
        apply input_outside r k K target h j _ w hw
        simpa only [labels, List.mem_reverse, List.mem_range] using hj)
    simpa only [afterFirst, reduceIte] using hp
  have hinputsSign : ∀ w ∈ r.control :: (r.lengthQ ++ r.lengthS), afterSign w = state w := by
    intro w hw
    exact (intervalSignUpdate_preservesInputs r k K signUpdate target afterFirst h w hw).trans (hinputsFirst w hw)
  have hv := input_values r afterSign state hinputsSign
  have hcleanFirst (hspecial : intervalHasTopSpecial k K = true) :
      Clean (r.cellScratch k K :: r.equalityScratch k K) afterFirst := by
    have ht := intervalTopFirst_cleanTopScratch r k K mode target state h hc
    intro w hw
    have hp := fold_preserves false mode (state r.control) (r.accumulator k K) (r.carry k K) L R
      (r.targetAt target) (r.addendAt target) (intervalMainLabels k K).reverse
      (run (intervalTopFirst r k K mode target) state) w (by
        intro j hj
        exact topScratch_outside r k K target h hspecial j (by
          rw [tree_labels_main]
          simpa only [List.mem_reverse] using hj) w hw)
    have he : firstMain r k K mode target (state r.control) L R
        (run (intervalTopFirst r k K mode target) state) w =
        run (intervalTopFirst r k K mode target) state w := by
      simpa only [firstMain, reduceIte] using hp
    rw [hfirst] at he
    exact he.trans (ht w hw)
  have hcleanSign (hspecial : intervalHasTopSpecial k K = true) :
      Clean (r.cellScratch k K :: r.equalityScratch k K) afterSign := by
    intro w hw
    exact (intervalSignUpdate_preservesScratch r k K signUpdate target afterFirst h w
      (intervalTopScratch_mem_scratch r k K target h w hw)).trans (hcleanFirst hspecial w hw)
  have hsecond := second_full r k K mode target afterSign h hcleanSign
    (by simpa only [hv.2.2] using hr) (by simpa only [hv.2.1,hv.2.2] using ho)
  simp only [hv.1,hv.2.1,hv.2.2] at hsecond
  have hbody : run (intervalAddSubBodyUnitary r k K mode signUpdate target) state =
      labels.foldl (fun s j => intervalSecondInclusiveCell mode (state r.control)
        (r.accumulator k K) (r.targetAt target j) (r.addendAt target j) (r.carry k K) L R j s) afterSign := by
    rw [run_intervalAddSubBody_numeric r k K mode signUpdate target state h hc ha hr (ho.trans hr) ho]
    simp only [intervalNumericBodyState, DualUnaryActionTree.visitLabels_dec,
      DualUnaryActionTree.visitLabels_inc, tree_labels_main]
    change run (intervalTopSecond r k K mode target)
      (secondMain r k K mode target (state r.control) L R
        (run (intervalSignUpdate r k K signUpdate)
          (firstMain r k K mode target (state r.control) L R
            (run (intervalTopFirst r k K mode target) state)))) = _
    rw [hfirst]
    exact hsecond
  have hnd := word_layout r k K target h
  have hf := intervalFirstInclusiveFold_words mode (state r.control) (r.accumulator k K)
    (r.carry k K) L R (r.targetAt target) (r.addendAt target) labels state hnd
  have hs := intervalSecondInclusiveFold_words mode (state r.control) (r.accumulator k K)
    (r.carry k K) L R (r.targetAt target) (r.addendAt target) labels afterSign hnd
  have hsignT : wireValues (labels.map (r.targetAt target)) afterSign =
      wireValues (labels.map (r.targetAt target)) afterFirst := by
    apply List.map_congr_left
    intro w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
    apply intervalSignUpdate_agreesOutsideSign r k K signUpdate afterFirst
    simpa only [List.mem_singleton] using intervalTargetAt_ne_sign r k K j target h
      (by simpa only [labels,List.mem_range] using hj)
  have hsignA : wireValues (labels.map (r.addendAt target)) afterSign =
      wireValues (labels.map (r.addendAt target)) afterFirst := by
    apply List.map_congr_left
    intro w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
    apply intervalSignUpdate_agreesOutsideSign r k K signUpdate afterFirst
    simpa only [List.mem_singleton] using intervalAddendAt_ne_sign r k K j target h
      (by simpa only [labels,List.mem_range] using hj)
  have hsignC : afterSign (r.carry k K) = afterFirst (r.carry k K) :=
    intervalSignUpdate_preservesScratch r k K signUpdate target afterFirst h _
      (intervalCarry_mem_scratch r k K target h)
  have hT := congrArg (fun x : List Bool × List Bool × Bool => x.1) hf
  have hA := congrArg (fun x : List Bool × List Bool × Bool => x.2.1) hf
  have hC := congrArg (fun x : List Bool × List Bool × Bool => x.2.2) hf
  change wireValues (labels.map (r.targetAt target)) afterFirst = _ at hT
  change wireValues (labels.map (r.addendAt target)) afterFirst = _ at hA
  change afterFirst (r.carry k K) = _ at hC
  dsimp only at hs
  rw [hsignT,hsignA,hsignC,hT,hA,hC] at hs
  have hm := maskedRippleWords_fusion mode
    (labels.map (fun j => state r.control && decide (L ≤ j ∧ j ≤ R)))
    (wireValues (labels.map (r.targetAt target)) state)
    (wireValues (labels.map (r.addendAt target)) state) (state (r.carry k K))
    (by simp [wireValues]) (by simp [wireValues])
  have hfirstSign : afterFirst r.sign = state r.sign := by
    have hp := fold_preserves_sign false r k K mode target (state r.control) L R labels.reverse state h
      (by intro j hj; simpa only [labels,List.mem_reverse,List.mem_range] using hj)
    simpa only [afterFirst, reduceIte] using hp
  have hsecondSign := fold_preserves_sign true r k K mode target (state r.control) L R labels afterSign h
    (by intro j hj; simpa only [labels,List.mem_range] using hj)
  have hcarryOut := hC.trans hm.2
  dsimp only
  constructor
  · rw [hbody]
    exact hs.trans hm.1
  · rw [hbody]
    rw [show (labels.foldl (fun s j => intervalSecondInclusiveCell mode (state r.control)
      (r.accumulator k K) (r.targetAt target j) (r.addendAt target j) (r.carry k K) L R j s) afterSign) r.sign =
        afterSign r.sign by simpa only [reduceIte] using hsecondSign]
    cases signUpdate <;> simp [afterSign, intervalSignUpdate, Classical.run, Classical.applyGate,
      hfirstSign, hcarryOut]
    rfl

end ShorECDLP.Paper2607_13816
