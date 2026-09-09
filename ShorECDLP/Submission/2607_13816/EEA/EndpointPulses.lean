import ShorECDLP.Submission.«2607_13816».EEA.IntervalScan
import Init.Data.Nat.Power2.Lemmas

/-! # Numeric endpoint pulses, including the special top alias -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section

theorem intervalTopRelative_eq_pow_topBit (k K : Nat) (h : intervalHasTopSpecial k K = true) :
    intervalTopRelative k K = 2^intervalTopBit k K := by
  have hh : 1 < intervalLaneCount k K ∧
      ((intervalLaneCount k K-1) &&& (intervalLaneCount k K-2)) = 0 := by
    simpa [intervalHasTopSpecial] using h
  have he : intervalLaneCount k K-2 = (intervalLaneCount k K-1)-1 := by omega
  rw [he] at hh
  obtain ⟨d, hd⟩ := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo (by omega)).mp hh.2
  simp [intervalTopRelative, intervalTopBit, hd]

private theorem masked_pulse (enabled : Bool) (d value label : Nat)
    (hv : value ≤ 2^d) (hj : label < 2^d) :
    ((enabled && decide (label = value % 2^d)) &&
      if label = 0 then !value.testBit d else true) = (enabled && decide (label=value)) := by
  by_cases he : value = 2^d
  · subst value
    have hjn : label ≠ 2^d := by omega
    simp [hjn]
  · have hl : value < 2^d := by omega
    have hb := Nat.testBit_lt_two_pow hl
    simp [Nat.mod_eq_of_lt hl, hb]

private theorem wire_bit (register : List Wire) (state : BasisState) (bit : Nat)
    (hbit : bit < register.length) :
    state (register.getD bit 0) = (boolWordToNat (wireValues register state)).testBit bit := by
  have hv : bit < (wireValues register state).length := by simpa [wireValues] using hbit
  rw [← getD_false_eq_testBit_boolWordToNat _ hv,
    List.getD_eq_getElem _ _ hbit, List.getD_eq_getElem _ _ hv]
  simp [wireValues]

/-- Both actual decoder pulses select the full numeric endpoint, including the special
upper endpoint whose low route aliases zero. The zero-leaf mask removes that alias. -/
theorem intervalTree_numericEndpointPulses
    (registers : IntervalRegisters) (k K : Nat) (state : BasisState)
    (hrWidth : DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset ≤ registers.lengthS.length)
    (hlWidth : DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset ≤ registers.lengthQ.length)
    (hrTop : intervalHasTopSpecial k K = true → intervalTopBit k K < registers.lengthS.length)
    (hlTop : intervalHasTopSpecial k K = true → intervalTopBit k K < registers.lengthQ.length)
    (hrValue : boolWordToNat (wireValues registers.lengthS state) ≤ intervalTopRelative k K)
    (hlValue : boolWordToNat (wireValues registers.lengthQ state) ≤ intervalTopRelative k K) :
    ∀ j ∈ intervalMainLabels k K,
      (((state registers.control && decide (j = ((intervalTree registers k K).project false).routeLabel state)) &&
        if maskedZeroLeaf (intervalHasTopSpecial k K) j then !state (registers.rightTop k K) else true) =
          (state registers.control && decide (j = boolWordToNat (wireValues registers.lengthS state)))) ∧
      (((state registers.control && decide (j = ((intervalTree registers k K).project true).routeLabel state)) &&
        if maskedZeroLeaf (intervalHasTopSpecial k K) j then !state (registers.leftTop k K) else true) =
          (state registers.control && decide (j = boolWordToNat (wireValues registers.lengthQ state)))) := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · have hp := intervalTopRelative_eq_pow_topBit k K hspecial
    have hm : intervalMainLabels k K = List.range (2^intervalTopBit k K) := by
      simp only [intervalMainLabels, hspecial, ↓reduceIte]
      exact congrArg List.range hp
    have hr := hrValue.trans_eq hp
    have hl := hlValue.trans_eq hp
    have route (second : Bool) :
        ((intervalTree registers k K).project second).routeLabel state =
          boolWordToNat (wireValues (if second then registers.lengthQ else registers.lengthS) state) %
            2^intervalTopBit k K := by
      by_cases hz : intervalTopBit k K = 0
      · rw [hz] at hm ⊢
        simp only [Nat.pow_zero, Nat.mod_one]
        exact intervalTree_singleton_route registers k K state second (by simpa using hm)
      · have hsource := DualUnaryActionTree.sourceWidth_le (intervalMainLabels k K).toFinset
          (intervalTopBit k K) (by omega) (by intro j hj; simpa [hm] using hj)
        apply sourceTree_routeResidue registers.rightIndex registers.leftIndex _ _
          (if second then registers.lengthQ else registers.lengthS) second (intervalTopBit k K) state
          (intervalTree_built registers k K)
        · intro bit; cases second <;> rfl
        · exact hsource
        · cases second
          · exact Nat.le_of_lt (hrTop hspecial)
          · exact Nat.le_of_lt (hlTop hspecial)
        · simpa [hm] using Nat.mod_lt
            (boolWordToNat (wireValues (if second then registers.lengthQ else registers.lengthS) state))
            (Nat.two_pow_pos (intervalTopBit k K))
    intro j hj
    have hjb : j < 2^intervalTopBit k K := by simpa [hm] using hj
    rw [route false, route true]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [IntervalRegisters.rightTop, IntervalRegisters.leftTop, if_pos hspecial, if_pos hspecial,
      wire_bit _ state _ (hrTop hspecial), wire_bit _ state _ (hlTop hspecial)]
    simpa [maskedZeroLeaf, hspecial] using
      And.intro (masked_pulse (state registers.control) _ _ j hr hjb)
        (masked_pulse (state registers.control) _ _ j hl hjb)
  · have hm : intervalMainLabels k K = List.range (intervalLaneCount k K) := by
      simp [intervalMainLabels, hspecial]
    have hrm : boolWordToNat (wireValues registers.lengthS state) ∈ intervalMainLabels k K := by
      rw [hm, List.mem_range]
      simp only [intervalTopRelative, intervalLaneCount] at hrValue ⊢
      omega
    have hlm : boolWordToNat (wireValues registers.lengthQ state) ∈ intervalMainLabels k K := by
      rw [hm, List.mem_range]
      simp only [intervalTopRelative, intervalLaneCount] at hlValue ⊢
      omega
    have hroutes := intervalTree_routeLabels registers k K state hrWidth hlWidth hrm hlm
    intro j hj
    simp [hroutes.1, hroutes.2, maskedZeroLeaf, hspecial]

private theorem main_labels_range (k K : Nat) :
    intervalMainLabels k K = List.range' 0 (intervalMainLabels k K).length := by
  unfold intervalMainLabels
  split <;> simp [List.range_eq_range']

private theorem tree_labels_range (registers : IntervalRegisters) (k K : Nat) :
    (intervalTree registers k K).labels = List.range' 0 (intervalMainLabels k K).length := by
  rw [intervalTree_labels, main_labels_range, ← List.range_eq_range']
  simpa only [List.toFinset_range, ← List.range_eq_range', List.length_range] using
    Finset.sort_range (intervalMainLabels k K).length

/-- Concrete first scan with numeric endpoints: only their bounds, order and the
incoming accumulator remain; routed-pulse interpretation is derived from the register bits. -/
theorem run_intervalFirstTraversal_numericScan
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode) (target : IntervalTarget)
    (state : BasisState) (hlayout : IntervalLayout registers k K target)
    (hrValue : boolWordToNat (wireValues registers.lengthS state) ≤ intervalTopRelative k K)
    (hlValue : boolWordToNat (wireValues registers.lengthQ state) ≤ intervalTopRelative k K)
    (horder : boolWordToNat (wireValues registers.lengthQ state) ≤ boolWordToNat (wireValues registers.lengthS state))
    (hcleanR : Clean (registers.rightPaths k K) state)
    (hcleanL : Clean (registers.leftPaths k K) state)
    (hcleanScratch : Clean [registers.cellScratch k K] state)
    (hacc : state (registers.accumulator k K) = intervalAccumulatorBoundary (state registers.control)
      (boolWordToNat (wireValues registers.lengthQ state)) (boolWordToNat (wireValues registers.lengthS state))
      (intervalMainLabels k K).length) :
    let L := boolWordToNat (wireValues registers.lengthQ state)
    let R := boolWordToNat (wireValues registers.lengthS state)
    let result := run (intervalFirstTraversal mode (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K) (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control (registers.rightPaths k K)
      (registers.leftPaths k K)) state
    result = ((intervalTree registers k K).visitLabels .dec).foldl (fun s j =>
      intervalFirstInclusiveCell mode (state registers.control) (registers.accumulator k K)
        (registers.targetAt target j) (registers.addendAt target j) (registers.carry k K) L R j s) state ∧
      result (registers.accumulator k K) = intervalAccumulatorBoundary (state registers.control) L R 0 := by
  have hp := intervalTree_numericEndpointPulses registers k K state
    hlayout.right_index_capacity hlayout.left_index_capacity hlayout.right_top_capacity
    hlayout.left_top_capacity hrValue hlValue
  have hm : ∀ j, 0 ≤ j → j < 0+(intervalMainLabels k K).length → j ∈ intervalMainLabels k K := by
    intro j _ hj
    rw [main_labels_range, List.mem_range']
    exact ⟨j, by omega, by omega⟩
  have hs := run_intervalFirstTraversal_inclusiveScan mode (intervalHasTopSpecial k K) (state registers.control)
    (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
    (registers.carry k K) (registers.cellScratch k K)
    (boolWordToNat (wireValues registers.lengthQ state)) (boolWordToNat (wireValues registers.lengthS state))
    0 (intervalMainLabels k K).length (registers.targetAt target) (registers.addendAt target)
    (intervalTree registers k K) registers.control registers.control (registers.rightPaths k K)
    (registers.leftPaths k K) state hlayout.traversal (tree_labels_range registers k K) horder
    hcleanR hcleanL hcleanScratch (by simpa using hacc)
    (fun j h1 h2 => (hp j (hm j h1 h2)).1) (fun j h1 h2 => (hp j (hm j h1 h2)).2)
  simpa only [DualUnaryActionTree.visitLabels_dec, tree_labels_range, Nat.zero_add] using hs

/-- Concrete second scan with numeric endpoints: only their bounds, order and the
incoming accumulator remain; routed-pulse interpretation is derived from the register bits. -/
theorem run_intervalSecondTraversal_numericScan
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode) (target : IntervalTarget)
    (state : BasisState) (hlayout : IntervalLayout registers k K target)
    (hrValue : boolWordToNat (wireValues registers.lengthS state) ≤ intervalTopRelative k K)
    (hlValue : boolWordToNat (wireValues registers.lengthQ state) ≤ intervalTopRelative k K)
    (horder : boolWordToNat (wireValues registers.lengthQ state) ≤ boolWordToNat (wireValues registers.lengthS state))
    (hcleanR : Clean (registers.rightPaths k K) state)
    (hcleanL : Clean (registers.leftPaths k K) state)
    (hcleanScratch : Clean [registers.cellScratch k K] state)
    (hacc : state (registers.accumulator k K) = intervalAccumulatorBoundary (state registers.control)
      (boolWordToNat (wireValues registers.lengthQ state)) (boolWordToNat (wireValues registers.lengthS state))
      0) :
    let L := boolWordToNat (wireValues registers.lengthQ state)
    let R := boolWordToNat (wireValues registers.lengthS state)
    let result := run (intervalSecondTraversal mode (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K) (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control (registers.rightPaths k K)
      (registers.leftPaths k K)) state
    result = ((intervalTree registers k K).visitLabels .inc).foldl (fun s j =>
      intervalSecondInclusiveCell mode (state registers.control) (registers.accumulator k K)
        (registers.targetAt target j) (registers.addendAt target j) (registers.carry k K) L R j s) state ∧
      result (registers.accumulator k K) = intervalAccumulatorBoundary (state registers.control) L R (intervalMainLabels k K).length := by
  have hp := intervalTree_numericEndpointPulses registers k K state
    hlayout.right_index_capacity hlayout.left_index_capacity hlayout.right_top_capacity
    hlayout.left_top_capacity hrValue hlValue
  have hm : ∀ j, 0 ≤ j → j < 0+(intervalMainLabels k K).length → j ∈ intervalMainLabels k K := by
    intro j _ hj
    rw [main_labels_range, List.mem_range']
    exact ⟨j, by omega, by omega⟩
  have hs := run_intervalSecondTraversal_inclusiveScan mode (intervalHasTopSpecial k K) (state registers.control)
    (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
    (registers.carry k K) (registers.cellScratch k K)
    (boolWordToNat (wireValues registers.lengthQ state)) (boolWordToNat (wireValues registers.lengthS state))
    0 (intervalMainLabels k K).length (registers.targetAt target) (registers.addendAt target)
    (intervalTree registers k K) registers.control registers.control (registers.rightPaths k K)
    (registers.leftPaths k K) state hlayout.traversal (tree_labels_range registers k K) horder
    hcleanR hcleanL hcleanScratch (by simpa using hacc)
    (fun j h1 h2 => (hp j (hm j h1 h2)).1) (fun j h1 h2 => (hp j (hm j h1 h2)).2)
  simpa only [DualUnaryActionTree.visitLabels_inc, tree_labels_range, Nat.zero_add] using hs

end
end ShorECDLP.Paper2607_13816
