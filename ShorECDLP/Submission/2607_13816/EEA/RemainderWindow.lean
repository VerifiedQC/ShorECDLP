import ShorECDLP.Submission.«2607_13816».EEA.EndpointNumeric
import ShorECDLP.Submission.«2607_13816».EEA.IndexedStep
/-! # Remainder interval arithmetic in full-bank coordinates -/
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem map_range_getD (ws : List Wire) :
    (List.range ws.length).map (fun j => ws.getD j 0) = ws := by
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp only [List.getElem_map,List.getElem_range]
    exact List.getD_eq_getElem ws 0 hk

private theorem nested_slice (xs : List Bool) (start count L width : Nat)
    (hfit : L+width ≤ count) :
    ((((xs.drop start).take count).drop L).take width) = (xs.drop (start+L)).take width := by
  rw [List.drop_take,List.drop_drop,List.take_take,Nat.min_eq_left (by omega)]

private theorem window_target_words (r : IndexedStepRegisters) (w : ActiveWindow)
    (target : IntervalTarget) (state : BasisState)
    (h : IntervalLayout (r.remainder w) w.start w.stop target) :
    wireValues ((List.range (intervalLaneCount w.start w.stop)).map ((r.remainder w).targetAt target)) state =
      ((wireValues (match target with | .work1 => r.work1 | .work2 => r.work2) state).drop (w.start-1)).take (w.stop-w.start+1) := by
  cases target with
  | work1 =>
    change wireValues ((List.range (intervalLaneCount w.start w.stop)).map (fun j => (r.remainder w).work1.getD j 0)) state = _
    rw [← h.work1_length,map_range_getD]
    change wireValues (IndexedStepRegisters.windowSlice r.work1 w) state = _
    simp only [IndexedStepRegisters.windowSlice,wireValues,List.map_take,List.map_drop]
  | work2 =>
    change wireValues ((List.range (intervalLaneCount w.start w.stop)).map (fun j => (r.remainder w).work2.getD j 0)) state = _
    rw [← h.work2_length,map_range_getD]
    change wireValues (IndexedStepRegisters.windowSlice r.work2 w) state = _
    simp only [IndexedStepRegisters.windowSlice,wireValues,List.map_take,List.map_drop]

private theorem window_addend_words (r : IndexedStepRegisters) (w : ActiveWindow)
    (target : IntervalTarget) (state : BasisState)
    (h : IntervalLayout (r.remainder w) w.start w.stop target) :
    wireValues ((List.range (intervalLaneCount w.start w.stop)).map ((r.remainder w).addendAt target)) state =
      ((wireValues (match target with | .work1 => r.work2 | .work2 => r.work1) state).drop (w.start-1)).take (w.stop-w.start+1) := by
  cases target with
  | work1 =>
    change wireValues ((List.range (intervalLaneCount w.start w.stop)).map (fun j => (r.remainder w).work2.getD j 0)) state = _
    rw [← h.work2_length,map_range_getD]
    change wireValues (IndexedStepRegisters.windowSlice r.work2 w) state = _
    simp only [IndexedStepRegisters.windowSlice,wireValues,List.map_take,List.map_drop]
  | work2 =>
    change wireValues ((List.range (intervalLaneCount w.start w.stop)).map (fun j => (r.remainder w).work1.getD j 0)) state = _
    rw [← h.work1_length,map_range_getD]
    change wireValues (IndexedStepRegisters.windowSlice r.work1 w) state = _
    simp only [IndexedStepRegisters.windowSlice,wireValues,List.map_take,List.map_drop]


private theorem take_join (xs : List Bool) (a b : Nat) :
    xs.take a ++ (xs.drop a).take b = xs.take (a+b) := by
  rw [List.take_drop]
  have hh := List.take_append_drop a (xs.take (a+b))
  simpa only [List.take_take,Nat.min_eq_left (Nat.le_add_right a b)] using hh

private theorem remainder_prefix_frame (r : IndexedStepRegisters) (n index : Nat)
    (mode : RippleMode) (signUpdate : Bool) (state : BasisState)
    (h : IndexedStepLayout r n index)
    (hc : IntervalReady (r.remainder (certifiedActiveWindows n index).remainder) state) :
    let w := (certifiedActiveWindows n index).remainder
    (wireValues r.work1 (run (intervalAddSubUnitary (r.remainder w) n w.start w.stop mode signUpdate .work1) state)).take (w.start-1) =
      (wireValues r.work1 state).take (w.start-1) := by
  dsimp only
  let w := (certifiedActiveWindows n index).remainder
  have hf := intervalAddSubUnitary_preservesOutsideTarget (r.remainder w) n w.start w.stop mode signUpdate .work1 state h.remainder hc
  have hp := h.physical
  simp only [IndexedStepRegisters.allWires,List.append_assoc] at hp
  have hd := (List.nodup_append.mp hp).2.2
  have hn := (List.nodup_append.mp (List.nodup_append.mp hp).2.1).1
  have ht := List.disjoint_take_drop (l := r.work1) (m := w.start-1) (n := w.start-1) hn (Nat.le_refl _)
  simp only [wireValues,← List.map_take]
  apply List.map_congr_left
  intro wire hw
  apply hf wire
  simp only [ite_true,List.mem_cons]
  intro hm
  rcases hm with hs | hs
  · have hw' := List.mem_of_mem_take hw
    change wire = r.sign at hs
    subst wire
    exact hd r.sign (by simp) r.sign (List.mem_append_left _ hw') rfl
  · change wire ∈ ((r.work1.drop (w.start-1)).take (w.stop-w.start+1)) at hs
    exact ht hw (List.mem_of_mem_take hs)

/-- The indexed remainder interval operates on the corresponding field of the
full work banks. Its local offset cancels the one-based window start, placing
the selected field immediately after the coefficient and quotient prefix. -/
theorem run_remainderInterval_logicalValues (r : IndexedStepRegisters) (w : ActiveWindow)
    (n T Q shift : Nat) (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (state : BasisState) (h : IntervalLayout (r.remainder w) w.start w.stop target)
    (hw : 1 ≤ w.start) (hready : IntervalReady (r.remainder w) state) (he : state r.control = true)
    (ht : boolWordToNat (wireValues r.lengthT state) = truthMinusOneValue r.lengthQ.length T)
    (hq : boolWordToNat (wireValues r.lengthQ state) = truthMinusOneValue r.lengthQ.length Q)
    (hs : boolWordToNat (wireValues r.lengthS state) = truthMinusOneValue r.lengthS.length shift)
    (hleftLow : w.start ≤ T+Q+2) (hleftHigh : T+Q+2-w.start < 2^r.lengthQ.length)
    (hrightLow : shift+w.start ≤ n+3) (hrightHigh : n+3-shift-w.start < 2^r.lengthS.length)
    (hrange : n+3-shift-w.start ≤ intervalTopRelative w.start w.stop)
    (horder : T+Q+2-w.start ≤ n+3-shift-w.start) :
    let width := n+3-shift-(T+Q+2)+1
    let ts := match target with | .work1 => r.work1 | .work2 => r.work2
    let ads := match target with | .work1 => r.work2 | .work2 => r.work1
    let value := fun ws s => boolWordToNat ((((wireValues ws s).drop (T+Q+1)).take width).reverse)
    value ts (run (intervalAddSubUnitary (r.remainder w) n w.start w.stop mode signUpdate target) state) =
      (match mode with
      | .add => value ts state + value ads state
      | .sub => value ts state + 2^width - value ads state) % 2^width := by
  have hb := run_intervalAddSubUnitary_logicalValues (r.remainder w) n w.start w.stop T Q shift
    mode signUpdate target state h hready he ht hq hs hleftLow hleftHigh hrightLow hrightHigh hrange horder
  have hwidth : n+3-shift-w.start-(T+Q+2-w.start)+1 = n+3-shift-(T+Q+2)+1 := by omega
  have hstart : w.start-1+(T+Q+2-w.start) = T+Q+1 := by omega
  have hfit : T+Q+2-w.start+(n+3-shift-w.start-(T+Q+2-w.start)+1) ≤ w.stop-w.start+1 := by
    simp only [intervalTopRelative,intervalLaneCount] at hrange
    omega
  have hnest (xs : List Bool) := nested_slice xs (w.start-1) (w.stop-w.start+1)
    (T+Q+2-w.start) (n+3-shift-w.start-(T+Q+2-w.start)+1) hfit
  dsimp only at hb ⊢
  rw [window_target_words r w target _ h,window_target_words r w target state h,
    window_addend_words r w target state h] at hb
  simp only [hnest] at hb
  simpa only [hstart,hwidth] using hb
/-- The remainder interval sign is the unsigned borrow of its full-bank field. -/
theorem run_remainderInterval_logicalBorrow (r : IndexedStepRegisters) (w : ActiveWindow)
    (n T Q shift : Nat) (target : IntervalTarget)
    (state : BasisState) (h : IntervalLayout (r.remainder w) w.start w.stop target)
    (hw : 1 ≤ w.start) (hready : IntervalReady (r.remainder w) state) (he : state r.control = true)
    (ht : boolWordToNat (wireValues r.lengthT state) = truthMinusOneValue r.lengthQ.length T)
    (hq : boolWordToNat (wireValues r.lengthQ state) = truthMinusOneValue r.lengthQ.length Q)
    (hs : boolWordToNat (wireValues r.lengthS state) = truthMinusOneValue r.lengthS.length shift)
    (hleftLow : w.start ≤ T+Q+2) (hleftHigh : T+Q+2-w.start < 2^r.lengthQ.length)
    (hrightLow : shift+w.start ≤ n+3) (hrightHigh : n+3-shift-w.start < 2^r.lengthS.length)
    (hrange : n+3-shift-w.start ≤ intervalTopRelative w.start w.stop)
    (horder : T+Q+2-w.start ≤ n+3-shift-w.start) :
    let width := n+3-shift-(T+Q+2)+1
    let ts := match target with | .work1 => r.work1 | .work2 => r.work2
    let ads := match target with | .work1 => r.work2 | .work2 => r.work1
    let value := fun ws s => boolWordToNat ((((wireValues ws s).drop (T+Q+1)).take width).reverse)
    run (intervalAddSubUnitary (r.remainder w) n w.start w.stop .sub true target) state r.sign =
      (state r.sign ^^ decide (value ts state < value ads state)) := by
  have hb := run_intervalAddSubUnitary_logicalBorrow (r.remainder w) n w.start w.stop T Q shift
    target state h hready he ht hq hs hleftLow hleftHigh hrightLow hrightHigh hrange horder
  have hwidth : n+3-shift-w.start-(T+Q+2-w.start)+1 = n+3-shift-(T+Q+2)+1 := by omega
  have hstart : w.start-1+(T+Q+2-w.start) = T+Q+1 := by omega
  have hfit : T+Q+2-w.start+(n+3-shift-w.start-(T+Q+2-w.start)+1) ≤ w.stop-w.start+1 := by
    simp only [intervalTopRelative,intervalLaneCount] at hrange
    omega
  have hnest (xs : List Bool) := nested_slice xs (w.start-1) (w.stop-w.start+1)
    (T+Q+2-w.start) (n+3-shift-w.start-(T+Q+2-w.start)+1) hfit
  dsimp only at hb ⊢
  rw [window_target_words r w target state h,
    window_addend_words r w target state h] at hb
  simp only [hnest] at hb
  simpa only [hstart,hwidth] using hb
/-- The actual remainder interval updates only the selected logical field of
work1, preserving the complete coefficient prefix and low remainder suffix. -/
theorem run_remainderInterval_logicalSlices (r : IndexedStepRegisters) (n index T Q shift : Nat)
    (mode : RippleMode) (signUpdate : Bool) (state : BasisState)
    (h : IndexedStepLayout r n index)
    (hready : IntervalReady (r.remainder (certifiedActiveWindows n index).remainder) state)
    (ht : boolWordToNat (wireValues r.lengthT state) = truthMinusOneValue r.lengthQ.length T)
    (hq : boolWordToNat (wireValues r.lengthQ state) = truthMinusOneValue r.lengthQ.length Q)
    (hs : boolWordToNat (wireValues r.lengthS state) = truthMinusOneValue r.lengthS.length shift)
    (hleftLow : (certifiedActiveWindows n index).remainder.start ≤ T+Q+2) (hleftHigh : T+Q+2-(certifiedActiveWindows n index).remainder.start < 2^r.lengthQ.length)
    (hrightLow : shift+(certifiedActiveWindows n index).remainder.start ≤ n+3) (hrightHigh : n+3-shift-(certifiedActiveWindows n index).remainder.start < 2^r.lengthS.length)
    (hrange : n+3-shift-(certifiedActiveWindows n index).remainder.start ≤ intervalTopRelative (certifiedActiveWindows n index).remainder.start (certifiedActiveWindows n index).remainder.stop)
    (horder : T+Q+2-(certifiedActiveWindows n index).remainder.start ≤ n+3-shift-(certifiedActiveWindows n index).remainder.start) :
    let w := (certifiedActiveWindows n index).remainder
    let start := T+Q+1
    let width := n+3-shift-(T+Q+2)+1
    let before := wireValues r.work1 state
    let addend := wireValues r.work2 state
    let result := uniformRippleExpectedWords mode (state r.control)
      ((before.drop start).take width) ((addend.drop start).take width) false
    let final := run (intervalAddSubUnitary (r.remainder w) n w.start w.stop mode signUpdate .work1) state
    wireValues r.work1 final = before.take start ++ result.1 ++ before.drop (n+3-shift) ∧
    final r.sign = (if signUpdate then state r.sign ^^ result.2 else state r.sign) := by
  let w := (certifiedActiveWindows n index).remainder
  have hw : 1 ≤ w.start := by simp only [w,certifiedActiveWindows,certifiedRemainderWindow]; omega
  change w.start ≤ T+Q+2 at hleftLow
  change shift+w.start ≤ n+3 at hrightLow
  change T+Q+2-w.start ≤ n+3-shift-w.start at horder
  have hstop : w.stop = n+3 := rfl
  have hb := run_intervalAddSubUnitary_logicalSlices (r.remainder w) n w.start w.stop T Q shift
    mode signUpdate .work1 state h.remainder hready ht hq hs hleftLow hleftHigh hrightLow hrightHigh hrange horder
  have hpre := remainder_prefix_frame r n index mode signUpdate state h hready
  have hwidth : n+3-shift-w.start-(T+Q+2-w.start)+1 = n+3-shift-(T+Q+2)+1 := by omega
  have hstart : w.start-1+(T+Q+2-w.start) = T+Q+1 := by omega
  have hend : (w.start-1)+(n+3-shift-w.start+1) = n+3-shift := by omega
  have htail (ws : List Wire) (hl : ws.length = n+3) (st : BasisState) :
      ((wireValues ws st).drop (w.start-1)).take (w.stop-w.start+1) = (wireValues ws st).drop (w.start-1) := by
    apply (List.take_eq_self_iff _).mpr
    simp only [List.length_drop,wireValues,List.length_map,hl,hstop]
    omega
  dsimp only at hb hpre ⊢
  rw [window_target_words r w .work1 _ h.remainder,window_target_words r w .work1 state h.remainder,
    window_addend_words r w .work1 state h.remainder] at hb
  simp only [htail r.work1 h.work1_length,htail r.work2 h.work2_length,List.drop_drop,hstart,hwidth,hend] at hb
  refine ⟨?_,hb.2⟩
  have hh := congrArg Prod.fst hb.1
  dsimp only at hh
  rw [← List.take_append_drop (w.start-1) (wireValues r.work1 (run (intervalAddSubUnitary (r.remainder w) n w.start w.stop mode signUpdate .work1) state)),hpre,hh]
  rw [← List.append_assoc,← List.append_assoc,take_join,hstart]
  rfl

end ShorECDLP.Paper2607_13816
