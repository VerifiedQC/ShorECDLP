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
end ShorECDLP.Paper2607_13816
