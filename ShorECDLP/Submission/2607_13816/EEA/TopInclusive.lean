import ShorECDLP.Submission.«2607_13816».EEA.IntervalNumeric
/-! # The separately decoded top lane executes the same inclusive ripple cells -/
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem first_outside_acc (mode : RippleMode) (value : Nat)
    (rs ls : List Wire) (acc t a c root : Wire) (state : BasisState)
    (hc : t ≠ acc ∧ a ≠ acc ∧ c ≠ acc)
    (hacc : state acc = false) (enabled : Bool)
    (he : (state root && registerMatches rs value state) = enabled) :
    AgreesOutside [acc] (topSpecialFirstLeafState mode value rs ls acc t a c root root state)
      (writeRippleCell t a c (rippleFirstBits mode enabled (readRippleCell t a c state)) state) := by
  intro w hw
  have hw' : w ≠ acc := by simpa using hw
  simp only [topSpecialFirstLeafState, readRippleCell, upd, hacc, Bool.false_xor, he]
  simp [writeRippleCell, upd, hw', hc.1, hc.2.1, hc.2.2]
/-- The separate first top-lane circuit is the numeric inclusive first cell. -/
theorem run_intervalTopFirst_inclusive (r : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (state : BasisState) (h : IntervalLayout r k K target)
    (hspecial : intervalHasTopSpecial k K = true)
    (hclean : Clean (r.cellScratch k K :: r.equalityScratch k K) state)
    (hacc : state (r.accumulator k K) = false)
    (hr : boolWordToNat (wireValues r.lengthS state) ≤ intervalTopRelative k K)
    (horder : boolWordToNat (wireValues r.lengthQ state) ≤ boolWordToNat (wireValues r.lengthS state)) :
    run (intervalTopFirst r k K mode target) state =
      intervalFirstInclusiveCell mode (state r.control) (r.accumulator k K)
        (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K))
        (r.carry k K) (boolWordToNat (wireValues r.lengthQ state))
        (boolWordToNat (wireValues r.lengthS state)) (intervalTopRelative k K) state := by
  have hn := (List.nodup_cons.mp (h.topSpecial hspecial).2.2.1).1
  have hc : r.targetAt target (intervalTopRelative k K) ≠ r.accumulator k K ∧
      r.addendAt target (intervalTopRelative k K) ≠ r.accumulator k K ∧
      r.carry k K ≠ r.accumulator k K := by
    refine ⟨?_,?_,?_⟩ <;> intro he <;> apply hn <;> simp [he]
  have he : (state r.control && registerMatches r.lengthS (intervalTopRelative k K) state) =
      (state r.control && decide (boolWordToNat (wireValues r.lengthQ state) ≤ intervalTopRelative k K ∧
        intervalTopRelative k K ≤ boolWordToNat (wireValues r.lengthS state))) := by
    rw [registerMatches_eq_numeric r.lengthS _ state (by
      rw [intervalTopRelative_eq_pow_topBit k K hspecial]
      exact Nat.pow_lt_pow_right (by decide) (h.right_top_capacity hspecial))]
    apply congrArg (fun b : Bool => state r.control && b)
    simp only [decide_eq_decide]
    omega
  funext w
  by_cases hw : w = r.accumulator k K
  · subst w
    rw [intervalTopFirst_accumulatorBoundary r k K mode target state h hclean hacc horder hr]
    simp [intervalFirstInclusiveCell, intervalMainLabels, hspecial, intervalTopRelative]
  · rw [run_intervalTopFirst_state r k K mode target state h hclean,
      intervalTopFirstState, if_pos hspecial]
    have hf := first_outside_acc mode (intervalTopRelative k K) r.lengthS r.lengthQ
      (r.accumulator k K) (r.targetAt target (intervalTopRelative k K))
      (r.addendAt target (intervalTopRelative k K)) (r.carry k K) r.control state hc hacc _ he w
      (by simpa using hw)
    simpa [intervalFirstInclusiveCell, upd, hw] using hf
private theorem second_outside_acc (mode : RippleMode) (value : Nat)
    (rs ls : List Wire) (acc t a c root : Wire) (state : BasisState)
    (hc : t ≠ acc ∧ a ≠ acc ∧ c ≠ acc) (enabled : Bool)
    (he : (state acc ^^ (state root && registerMatches ls value state)) = enabled) :
    AgreesOutside [acc] (topSpecialSecondLeafState mode value rs ls acc t a c root root state)
      (writeRippleCell t a c (rippleSecondBits mode enabled (readRippleCell t a c state)) state) := by
  intro w hw
  have hw' : w ≠ acc := by simpa using hw
  simp only [topSpecialSecondLeafState, readRippleCell, upd, he]
  simp [writeRippleCell, upd, hw', hc.1, hc.2.1, hc.2.2]

/-- The separate second top-lane circuit is the numeric inclusive second cell. -/
theorem run_intervalTopSecond_inclusive (r : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (state : BasisState) (h : IntervalLayout r k K target)
    (hspecial : intervalHasTopSpecial k K = true)
    (hclean : Clean (r.cellScratch k K :: r.equalityScratch k K) state)
    (hacc : state (r.accumulator k K) = intervalAccumulatorBoundary (state r.control)
      (boolWordToNat (wireValues r.lengthQ state)) (boolWordToNat (wireValues r.lengthS state))
      (intervalTopRelative k K))
    (hr : boolWordToNat (wireValues r.lengthS state) ≤ intervalTopRelative k K)
    (horder : boolWordToNat (wireValues r.lengthQ state) ≤ boolWordToNat (wireValues r.lengthS state)) :
    run (intervalTopSecond r k K mode target) state =
      intervalSecondInclusiveCell mode (state r.control) (r.accumulator k K)
        (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K))
        (r.carry k K) (boolWordToNat (wireValues r.lengthQ state))
        (boolWordToNat (wireValues r.lengthS state)) (intervalTopRelative k K) state := by
  have hn := (List.nodup_cons.mp (h.topSpecial hspecial).2.2.1).1
  have hc : r.targetAt target (intervalTopRelative k K) ≠ r.accumulator k K ∧
      r.addendAt target (intervalTopRelative k K) ≠ r.accumulator k K ∧
      r.carry k K ≠ r.accumulator k K := by
    refine ⟨?_,?_,?_⟩ <;> intro he <;> apply hn <;> simp [he]
  have he : (state (r.accumulator k K) ^^ (state r.control && registerMatches r.lengthQ (intervalTopRelative k K) state)) =
      (state r.control && decide (boolWordToNat (wireValues r.lengthQ state) ≤ intervalTopRelative k K ∧
        intervalTopRelative k K ≤ boolWordToNat (wireValues r.lengthS state))) := by
    rw [registerMatches_eq_numeric r.lengthQ _ state (by
      rw [intervalTopRelative_eq_pow_topBit k K hspecial]
      exact Nat.pow_lt_pow_right (by decide) (h.left_top_capacity hspecial)), hacc]
    have hl := horder.trans hr
    cases hen : state r.control <;>
      by_cases hL : boolWordToNat (wireValues r.lengthQ state) = intervalTopRelative k K <;>
      by_cases hR : boolWordToNat (wireValues r.lengthS state) = intervalTopRelative k K <;>
      simp_all [intervalAccumulatorBoundary] <;> omega
  funext w
  by_cases hw : w = r.accumulator k K
  · subst w
    rw [intervalTopSecond_accumulatorClean r k K mode target state h hclean (by
      simpa [intervalMainLabels, hspecial, intervalTopRelative] using hacc) horder hr]
    simp [intervalSecondInclusiveCell, intervalAccumulatorBoundary, show ¬ intervalTopRelative k K + 1 ≤ boolWordToNat (wireValues r.lengthS state) by omega]
  · rw [run_intervalTopSecond_state r k K mode target state h (fun _ => hclean),
      intervalTopSecondState, if_pos hspecial]
    have hf := second_outside_acc mode (intervalTopRelative k K) r.lengthS r.lengthQ
      (r.accumulator k K) (r.targetAt target (intervalTopRelative k K))
      (r.addendAt target (intervalTopRelative k K)) (r.carry k K) r.control state hc _ he w
      (by simpa using hw)
    simpa [intervalSecondInclusiveCell, upd, hw] using hf
end ShorECDLP.Paper2607_13816
