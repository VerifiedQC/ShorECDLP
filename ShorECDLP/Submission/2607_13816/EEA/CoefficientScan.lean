import ShorECDLP.Submission.«2607_13816».EEA.CoefficientPrefix

/-! # Inclusive arithmetic masks of the physical coefficient prefix scans -/
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem prefix_pulses (r : CoefficientPrefixRegisters) (k K : Nat)
    (h : CoefficientPrefixLayout r k K) (s : BasisState) (order : UnaryOrder)
    (hv : boolWordToNat (wireValues r.boundary s) ∈ quotientSwapLabels k K) :
    (coefficientPrefixTree r k K).visitPulses order (s r.control) s =
      ((coefficientPrefixTree r k K).visitLabels order).map
        (fun j => (j,s r.control && decide (j = boolWordToNat (wireValues r.boundary s)))) := by
  rw [UnaryActionTree.visitPulses_eq_route order _ _ _ (by rw [coefficientPrefixTree_labels r h]; exact Finset.sort_nodup _ _),
    coefficientPrefixTree_routeLabel_eq r s h hv]


private theorem prefix_labels (r : CoefficientPrefixRegisters) (k K : Nat)
    (h : CoefficientPrefixLayout r k K) :
    (coefficientPrefixTree r k K).labels = List.range' k (K-k+1) := by
  rw [coefficientPrefixTree_labels r h]
  unfold quotientSwapLabels
  rw [show K+1-k = K-k+1 by have := h.k_le_K; omega]
  apply (List.toFinset_sort (· ≤ ·) (List.nodup_range' 1 (by decide))).mpr
  exact (List.pairwise_lt_range').imp (fun h => Nat.le_of_lt h)

/-- The first prefix cell uses the inclusive boundary, then advances the accumulator. -/
def coefficientFirstPrefixCell (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (enabled : Bool) (B j : Nat)
    (s : BasisState) : BasisState :=
  (writeRippleCell (r.targetAt target k j) (r.addendAt target k j) (r.carry k K)
    (rippleFirstBits mode (enabled && decide (j ≤ B))
      (readRippleCell (r.targetAt target k j) (r.addendAt target k j) (r.carry k K) s)) s)
    [r.accumulator k K ↦ enabled && decide (j+1 ≤ B)]

/-- The reverse prefix cell restores the accumulator at the current boundary. -/
def coefficientSecondPrefixCell (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (enabled : Bool) (B j : Nat)
    (s : BasisState) : BasisState :=
  (writeRippleCell (r.targetAt target k j) (r.addendAt target k j) (r.carry k K)
    (rippleSecondBits mode (enabled && decide (j ≤ B))
      (readRippleCell (r.targetAt target k j) (r.addendAt target k j) (r.carry k K) s)) s)
    [r.accumulator k K ↦ enabled && decide (j ≤ B)]

private theorem prefix_toggle (enabled : Bool) (B j : Nat) :
    ((enabled && decide (j ≤ B)) ^^ (enabled && decide (j=B))) =
      (enabled && decide (j+1 ≤ B)) := by
  cases enabled <;> by_cases hj : j < B <;> by_cases he : j=B <;> simp_all <;> omega

private theorem first_cell (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (enabled : Bool) (B j : Nat)
    (s : BasisState)
    (hn : [r.accumulator k K,r.targetAt target k j,r.addendAt target k j,r.carry k K].Nodup)
    (ha : s (r.accumulator k K) = (enabled && decide (j ≤ B))) :
    coefficientPrefixFirstLeafState r k K mode target j (enabled && decide (j=B)) s =
      coefficientFirstPrefixCell r k K mode target enabled B j s := by
  have hs := (List.nodup_cons.mp hn).1
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hs
  simp only [coefficientPrefixFirstLeafState,coefficientFirstPrefixCell,ha]
  simp only [writeRippleCell,upd,hs.1,hs.2.1,hs.2.2,if_false,ha,prefix_toggle]

private theorem second_cell (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (enabled : Bool) (B j : Nat)
    (s : BasisState)
    (hn : [r.accumulator k K,r.targetAt target k j,r.addendAt target k j,r.carry k K].Nodup)
    (ha : s (r.accumulator k K) = (enabled && decide (j+1 ≤ B))) :
    coefficientPrefixSecondLeafState r k K mode target j (enabled && decide (j=B)) s =
      coefficientSecondPrefixCell r k K mode target enabled B j s := by
  have hs := (List.nodup_cons.mp hn).1
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hs
  have ht : ((enabled && decide (j+1 ≤ B)) ^^ (enabled && decide (j=B))) =
      (enabled && decide (j ≤ B)) := by
    have hh := congrArg (fun x => x ^^ (enabled && decide (j=B))) (prefix_toggle enabled B j)
    simpa using hh.symm
  simp only [coefficientPrefixSecondLeafState,coefficientSecondPrefixCell,ha]
  simp only [readRippleCell,upd,Ne.symm hs.1,Ne.symm hs.2.1,Ne.symm hs.2.2,if_false,if_true,ha,ht]
  funext wire
  by_cases hw : wire = r.accumulator k K
  · subst wire
    simp [writeRippleCell,upd,hs]
  · simp [writeRippleCell,upd,hw]


private theorem scan_first (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (enabled : Bool) (B lo count : Nat)
    (s : BasisState)
    (hn : ∀ j, lo ≤ j → j < lo+count →
      [r.accumulator k K,r.targetAt target k j,r.addendAt target k j,r.carry k K].Nodup)
    (ha : s (r.accumulator k K) = (enabled && decide (lo ≤ B))) :
    let final := (List.range' lo count).foldl (fun next j =>
      coefficientPrefixFirstLeafState r k K mode target j (enabled && decide (j=B)) next) s
    final = (List.range' lo count).foldl (fun next j =>
      coefficientFirstPrefixCell r k K mode target enabled B j next) s ∧
      final (r.accumulator k K) = (enabled && decide (lo+count ≤ B)) := by
  induction count generalizing lo s with
  | zero => simpa using And.intro (rfl : s = s) ha
  | succ count ih =>
    have hc := first_cell r k K mode target enabled B lo s (hn lo (by omega) (by omega)) ha
    have hh := ih (lo+1) (coefficientFirstPrefixCell r k K mode target enabled B lo s)
      (fun j h1 h2 => hn j (by omega) (by omega))
      (by simp [coefficientFirstPrefixCell,upd])
    simpa only [List.range'_succ,List.foldl_cons,hc,Nat.add_assoc,Nat.add_comm 1 count] using hh

private theorem scan_second (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (enabled : Bool) (B lo count : Nat)
    (s : BasisState)
    (hn : ∀ j, lo ≤ j → j < lo+count →
      [r.accumulator k K,r.targetAt target k j,r.addendAt target k j,r.carry k K].Nodup)
    (ha : s (r.accumulator k K) = (enabled && decide (lo+count ≤ B))) :
    let final := (List.range' lo count).reverse.foldl (fun next j =>
      coefficientPrefixSecondLeafState r k K mode target j (enabled && decide (j=B)) next) s
    final = (List.range' lo count).reverse.foldl (fun next j =>
      coefficientSecondPrefixCell r k K mode target enabled B j next) s ∧
      final (r.accumulator k K) = (enabled && decide (lo ≤ B)) := by
  induction count generalizing s with
  | zero => simpa using And.intro (rfl : s = s) ha
  | succ count ih =>
    have hc := second_cell r k K mode target enabled B (lo+count) s
      (hn (lo+count) (by omega) (by omega)) (by simpa only [Nat.add_assoc] using ha)
    have hh := ih (coefficientSecondPrefixCell r k K mode target enabled B (lo+count) s)
      (fun j h1 h2 => hn j h1 (by omega)) (by simp [coefficientSecondPrefixCell,upd])
    simpa only [List.range'_concat,Nat.one_mul,List.reverse_append,List.reverse_cons,
      List.reverse_nil,List.cons_append,List.nil_append,List.foldl_cons,hc] using hh


private theorem cell_layout (r : CoefficientPrefixRegisters) (k K j : Nat)
    (target : CoefficientTarget) (h : CoefficientPrefixLayout r k K)
    (hj : k ≤ j) (hj' : j ≤ K) :
    [r.accumulator k K,r.targetAt target k j,r.addendAt target k j,r.carry k K].Nodup := by
  have hp : (r.work1 ++ (r.work2 ++ (r.boundary ++ r.scratch))).Nodup :=
    (List.nodup_append.mp h.physical).2.1
  have h1 := List.nodup_append.mp hp
  have h2 := List.nodup_append.mp h1.2.1
  have hscr := (List.nodup_append.mp h2.2.1).2.1
  have haidx : r.scratchBase k K+1 < r.scratch.length := by rw [h.scratch_length]; omega
  have hcidx : r.scratchBase k K < r.scratch.length := by rw [h.scratch_length]; omega
  have ham : r.accumulator k K ∈ r.scratch := by
    unfold CoefficientPrefixRegisters.accumulator
    rw [List.getD_eq_getElem _ _ haidx]
    exact List.getElem_mem _
  have hcm : r.carry k K ∈ r.scratch := by
    unfold CoefficientPrefixRegisters.carry
    rw [List.getD_eq_getElem _ _ hcidx]
    exact List.getElem_mem _
  have hac : r.accumulator k K ≠ r.carry k K := by
    unfold CoefficientPrefixRegisters.accumulator CoefficientPrefixRegisters.carry
    rw [List.getD_eq_getElem _ _ haidx,List.getD_eq_getElem _ _ hcidx]
    intro he
    have := hscr.getElem_inj_iff.mp he
    omega
  have hm1 : r.work1At k j ∈ r.work1 := by
    unfold CoefficientPrefixRegisters.work1At CoefficientPrefixRegisters.laneAt
    rw [List.getD_eq_getElem _ _ (by rw [h.work1_length]; omega)]
    exact List.getElem_mem _
  have hm2 : r.work2At k j ∈ r.work2 := by
    unfold CoefficientPrefixRegisters.work2At CoefficientPrefixRegisters.laneAt
    rw [List.getD_eq_getElem _ _ (by rw [h.work2_length]; omega)]
    exact List.getElem_mem _
  have h12 : r.work1At k j ≠ r.work2At k j :=
    h1.2.2 _ hm1 _ (List.mem_append_left _ hm2)
  have h1a : r.work1At k j ≠ r.accumulator k K :=
    h1.2.2 _ hm1 _ (List.mem_append_right _ (List.mem_append_right _ ham))
  have h1c : r.work1At k j ≠ r.carry k K :=
    h1.2.2 _ hm1 _ (List.mem_append_right _ (List.mem_append_right _ hcm))
  have h2a : r.work2At k j ≠ r.accumulator k K :=
    h2.2.2 _ hm2 _ (List.mem_append_right _ ham)
  have h2c : r.work2At k j ≠ r.carry k K :=
    h2.2.2 _ hm2 _ (List.mem_append_right _ hcm)
  cases target <;> simp [CoefficientPrefixRegisters.targetAt,CoefficientPrefixRegisters.addendAt,
    Ne.symm h1a,Ne.symm h2a,hac,h12,Ne.symm h12,h1c,h2c]

/-- An in-range prepared boundary makes the increasing physical prefix traversal
use precisely the inclusive prefix, with the accumulator cleared at its end. -/
theorem run_coefficientPrefixFirstTraversal_scan (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (s : BasisState)
    (h : CoefficientPrefixLayout r k K)
    (hc : Clean (r.path k K) s) (hcell : s (r.cellScratch k K) = false)
    (hv : boolWordToNat (wireValues r.boundary s) ∈ quotientSwapLabels k K)
    (ha : s (r.accumulator k K) = s r.control) :
    let B := boolWordToNat (wireValues r.boundary s)
    let final := run (unaryActionUnitary .inc (coefficientPrefixFirstLeaf r k K mode target)
      (coefficientPrefixTree r k K) r.control (r.path k K)) s
    final = (List.range' k (K-k+1)).foldl (fun next j =>
      coefficientFirstPrefixCell r k K mode target (s r.control) B j next) s ∧
      final (r.accumulator k K) = false := by
  have hb : k ≤ boolWordToNat (wireValues r.boundary s) ∧
      boolWordToNat (wireValues r.boundary s) ≤ K := by
    simp only [quotientSwapLabels,List.mem_range'] at hv
    omega
  have hh := scan_first r k K mode target (s r.control) (boolWordToNat (wireValues r.boundary s)) k (K-k+1) s
    (fun j h1 h2 => cell_layout r k K j target h h1 (by omega)) (by simpa [hb.1] using ha)
  dsimp only
  rw [run_coefficientPrefixFirstTraversal_state r mode target s h hc hcell]
  simpa only [coefficientPrefixFirstTraversalState,prefix_pulses r k K h s .inc hv,
    UnaryActionTree.visitLabels_inc,prefix_labels r k K h,List.foldl_map,
    show decide (k+(K-k+1) ≤ boolWordToNat (wireValues r.boundary s)) = false by
      exact decide_eq_false (by omega),Bool.and_false] using hh

/-- The reverse physical traversal uses the same inclusive prefix and restores
the accumulator to the external control. -/
theorem run_coefficientPrefixSecondTraversal_scan (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (s : BasisState)
    (h : CoefficientPrefixLayout r k K)
    (hc : Clean (r.path k K) s) (hcell : s (r.cellScratch k K) = false)
    (hv : boolWordToNat (wireValues r.boundary s) ∈ quotientSwapLabels k K)
    (ha : s (r.accumulator k K) = false) :
    let B := boolWordToNat (wireValues r.boundary s)
    let final := run (unaryActionUnitary .dec (coefficientPrefixSecondLeaf r k K mode target)
      (coefficientPrefixTree r k K) r.control (r.path k K)) s
    final = (List.range' k (K-k+1)).reverse.foldl (fun next j =>
      coefficientSecondPrefixCell r k K mode target (s r.control) B j next) s ∧
      final (r.accumulator k K) = s r.control := by
  have hb : k ≤ boolWordToNat (wireValues r.boundary s) ∧
      boolWordToNat (wireValues r.boundary s) ≤ K := by
    simp only [quotientSwapLabels,List.mem_range'] at hv
    omega
  have he : decide (k+(K-k+1) ≤ boolWordToNat (wireValues r.boundary s)) = false := by
    exact decide_eq_false (by omega)
  have hh := scan_second r k K mode target (s r.control) (boolWordToNat (wireValues r.boundary s)) k (K-k+1) s
    (fun j h1 h2 => cell_layout r k K j target h h1 (by omega)) (by simpa only [he,Bool.and_false] using ha)
  dsimp only
  rw [run_coefficientPrefixSecondTraversal_state r mode target s h hc hcell]
  simpa only [coefficientPrefixSecondTraversalState,prefix_pulses r k K h s .dec hv,
    UnaryActionTree.visitLabels_dec,prefix_labels r k K h,List.foldl_map,
    show decide (k ≤ boolWordToNat (wireValues r.boundary s)) = true from decide_eq_true hb.1,
    Bool.and_true] using hh
end ShorECDLP.Paper2607_13816
