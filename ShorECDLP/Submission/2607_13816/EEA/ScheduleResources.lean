import ShorECDLP.Submission.«2607_13816».EEA.ScheduleLayout
import ShorECDLP.Submission.«2607_13816».Arithmetic.ModularAdd
/-! Exact finite-sum resource formulas for both adaptive EEA directions. -/
namespace ShorECDLP.Paper2607_13816
open Quantum
private theorem seq_T (a b : AdaptiveCircuit) : (a.seq b).tCount=a.tCount+b.tCount := by
  simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b
theorem indexedScheduleAdaptive_tCount (r : IndexedStepRegisters) (n start count : Nat)
    (hl : IndexedScheduleLayout r n start count) :
    (indexedScheduleAdaptive r n start count).tCount =
      ((List.range' start count).map (indexedStepAdaptiveTFormula r n)).sum := by
  induction hl with
  | done start => rfl
  | @step start count head tail ih =>
    rw [indexedScheduleAdaptive, seq_T, indexedStepAdaptive_tCount r n start head, ih]
    simp only [List.range'_succ, List.map_cons, List.sum_cons]

theorem indexedScheduleAdaptive_measurementCount (r : IndexedStepRegisters) (n start count : Nat)
    (hl : IndexedScheduleLayout r n start count) :
    (indexedScheduleAdaptive r n start count).measurementCount =
      ((List.range' start count).map (indexedStepAdaptiveMeasurementFormula r n)).sum := by
  induction hl with
  | done start => rfl
  | @step start count head tail ih =>
    rw [indexedScheduleAdaptive, modularMeasurements_seq, indexedStepAdaptive_measurementCount r n start head, ih]
    simp only [List.range'_succ, List.map_cons, List.sum_cons]

theorem indexedScheduleInverseAdaptive_tCount (r : IndexedStepRegisters) (n start count : Nat)
    (hl : IndexedScheduleLayout r n start count) :
    (indexedScheduleInverseAdaptive r n start count).tCount =
      ((List.range' start count).map (indexedStepInverseAdaptiveTFormula r n)).sum := by
  induction hl with
  | done start => rfl
  | @step start count head tail ih =>
    rw [indexedScheduleInverseAdaptive, seq_T, indexedStepInverseAdaptive_tCount r n start head, ih]
    simp only [List.range'_succ, List.map_cons, List.sum_cons]
    omega
theorem indexedScheduleInverseAdaptive_measurementCount (r : IndexedStepRegisters) (n start count : Nat)
    (hl : IndexedScheduleLayout r n start count) :
    (indexedScheduleInverseAdaptive r n start count).measurementCount =
      ((List.range' start count).map (indexedStepAdaptiveMeasurementFormula r n)).sum := by
  induction hl with
  | done start => rfl
  | @step start count head tail ih =>
    rw [indexedScheduleInverseAdaptive, modularMeasurements_seq, indexedStepInverseAdaptive_measurementCount r n start head, ih]
    simp only [List.range'_succ, List.map_cons, List.sum_cons]
    omega
private theorem dual_leaves (t : DualUnaryActionTree) : t.leaves=t.labels.length := by
  induction t with
  | leaf => rfl
  | node a b z o hz ho => simp [DualUnaryActionTree.leaves,DualUnaryActionTree.labels,hz,ho]
private theorem dual_nodes (t : DualUnaryActionTree) : t.internalNodes+1=t.leaves := by
  induction t with
  | leaf => rfl
  | node a b z o hz ho => simp only [DualUnaryActionTree.leaves,DualUnaryActionTree.internalNodes]; omega
private theorem unary_leaves (t : UnaryActionTree) : t.leaves=t.labels.length := by
  induction t with
  | leaf => rfl
  | node a z o hz ho => simp [UnaryActionTree.leaves,UnaryActionTree.labels,hz,ho]
private theorem unary_nodes (t : UnaryActionTree) : t.internalNodes+1=t.leaves := by
  induction t with
  | leaf => rfl
  | node a z o hz ho => simp only [UnaryActionTree.leaves,UnaryActionTree.internalNodes]; omega
private theorem dual_const {t : DualUnaryActionTree} {a b : Wire} {pa pb : List Wire}
    (h : t.Layout a b pa pb) : t.leafCostSum (fun _ _ _ => 1) a b pa pb=t.leaves := by
  induction h with
  | leaf => rfl
  | node a b c d e f z o pa pb hn hz ho ihz iho =>
    simp only [DualUnaryActionTree.leafCostSum,DualUnaryActionTree.leaves,ihz,iho]
private theorem interval_leaf_count (r : IntervalRegisters) (k K : Nat) :
    (intervalTree r k K).leaves = (intervalMainLabels k K).length := by
  rw [dual_leaves,intervalTree_labels,Finset.length_sort]
  apply List.toFinset_card_of_nodup
  unfold intervalMainLabels
  split <;> exact List.nodup_range
private theorem coefficient_leaf_count (r : CoefficientPrefixRegisters) (k K : Nat)
    (h : CoefficientPrefixLayout r k K) : (coefficientPrefixTree r k K).leaves=K+1-k := by
  rw [unary_leaves,coefficientPrefixTree_labels r h,Finset.length_sort]
  simpa only [quotientSwapLabels,List.length_range'] using
    List.toFinset_card_of_nodup (show (List.range' k (K+1-k)).Nodup from List.nodup_range')
private theorem interval_scalar (r : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (h : IntervalLayout r k K target) :
    intervalMeasurementFormula r k K =
      2 * (intervalMainLabels k K).length + 4 * ((intervalMainLabels k K).length-1) +
      (if intervalHasTopSpecial k K then
        4 * mcxVChainMeasurementCost r.lengthS.length +
        4 * mcxVChainMeasurementCost r.lengthQ.length + 2 else 0) := by
  have hn := dual_nodes (intervalTree r k K)
  rw [interval_leaf_count] at hn
  have he : (intervalTree r k K).internalNodes=(intervalMainLabels k K).length-1 := by omega
  simp only [intervalMeasurementFormula]
  rw [dual_const h.traversal.1,interval_leaf_count,he]
/-- Integer-only measurement formula, with the certified decoder labels counted directly. -/
def secp256k1StepMeasurements (T : Nat) : Nat :=
  let w := certifiedActiveWindows 256 T
  let special := intervalHasTopSpecial w.remainder.start w.remainder.stop
  let count := intervalLaneCount w.remainder.start w.remainder.stop
  let leaves := if special then count-1 else count
  let coefficient := w.coefficient.stop+1-w.coefficient.start
  2 * (2*leaves+4*(leaves-1)+(if special then 58 else 0))+
    4*coefficient+4*(coefficient-1)+44

theorem secp256k1StepMeasurements_eq (T : Nat)
    (h : IndexedStepLayout indexedStepProductionRegisters 256 T) :
    indexedStepAdaptiveMeasurementFormula indexedStepProductionRegisters 256 T =
      secp256k1StepMeasurements T := by
  let w := certifiedActiveWindows 256 T
  have hc := coefficient_leaf_count (indexedStepProductionRegisters.coefficient w.coefficient)
    w.coefficient.start w.coefficient.stop h.coefficient
  have hn := unary_nodes (coefficientPrefixTree (indexedStepProductionRegisters.coefficient w.coefficient)
    w.coefficient.start w.coefficient.stop)
  rw [hc] at hn
  have he : (coefficientPrefixTree (indexedStepProductionRegisters.coefficient w.coefficient)
    w.coefficient.start w.coefficient.stop).internalNodes=w.coefficient.stop+1-w.coefficient.start-1 := by omega
  simp only [indexedStepAdaptiveMeasurementFormula]
  rw [interval_scalar _ _ _ .work1 h.remainder,hc,he]
  by_cases hs : intervalHasTopSpecial w.remainder.start w.remainder.stop = true
  · simp only [secp256k1StepMeasurements, intervalMainLabels, show intervalHasTopSpecial
      (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop = true from hs,
      ↓reduceIte,List.length_range]
    rfl
  · simp only [secp256k1StepMeasurements, intervalMainLabels, show ¬intervalHasTopSpecial
      (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop = true from hs,
      Bool.false_eq_true,↓reduceIte,List.length_range]
    rfl
theorem secp256k1StepMeasurements_sum :
    ((List.range' 1 1620).map secp256k1StepMeasurements).sum = 5278832 := by decide +kernel

private theorem layout_sum_congr (r : IndexedStepRegisters) (n start count : Nat)
    (f g : Nat → Nat) (heq : ∀ T, IndexedStepLayout r n T → f T=g T)
    (h : IndexedScheduleLayout r n start count) :
    ((List.range' start count).map f).sum = ((List.range' start count).map g).sum := by
  induction h with
  | done => rfl
  | @step start count head tail ih =>
    simp only [List.range'_succ,List.map_cons,List.sum_cons,heq start head,ih]
private theorem production_measurement_sum (start count : Nat)
    (h : IndexedScheduleLayout indexedStepProductionRegisters 256 start count) :
    ((List.range' start count).map (indexedStepAdaptiveMeasurementFormula indexedStepProductionRegisters 256)).sum =
      ((List.range' start count).map secp256k1StepMeasurements).sum :=
  layout_sum_congr _ _ _ _ _ _ secp256k1StepMeasurements_eq h

/-- Exact measurements of all 1,620 forward EEA steps on the physical production layout. -/
theorem secp256k1EEAForwardAdaptive_measurementCount :
    (secp256k1EEAForwardAdaptive indexedStepProductionRegisters).measurementCount=5278832 :=
  (indexedScheduleAdaptive_measurementCount _ _ _ _ secp256k1ScheduleLayout_production).trans
    ((production_measurement_sum _ _ secp256k1ScheduleLayout_production).trans secp256k1StepMeasurements_sum)
/-- The descending inverse visits the same measured trees exactly once per step. -/
theorem secp256k1EEAReverseAdaptive_measurementCount :
    (secp256k1EEAReverseAdaptive indexedStepProductionRegisters).measurementCount=5278832 :=
  (indexedScheduleInverseAdaptive_measurementCount _ _ _ _ secp256k1ScheduleLayout_production).trans
    ((production_measurement_sum _ _ secp256k1ScheduleLayout_production).trans secp256k1StepMeasurements_sum)
private theorem dual_label_sum {t : DualUnaryActionTree} {a b : Wire} {pa pb : List Wire}
    (h : t.Layout a b pa pb) (f : Nat → Nat) :
    t.leafCostSum (fun l _ _ => f l) a b pa pb=(t.labels.map f).sum := by
  induction h with
  | leaf => simp [DualUnaryActionTree.leafCostSum,DualUnaryActionTree.labels]
  | node a b c d e f z o pa pb hn hz ho ihz iho =>
    simp only [DualUnaryActionTree.leafCostSum,DualUnaryActionTree.labels,List.map_append,List.sum_append,ihz,iho]
private theorem interval_label_sum (r : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (h : IntervalLayout r k K target) (f : Nat → Nat) :
    (intervalTree r k K).leafCostSum (fun l _ _ => f l) r.control r.control
      (r.rightPaths k K) (r.leftPaths k K) = ((intervalMainLabels k K).map f).sum := by
  rw [dual_label_sum h.traversal.1,intervalTree_labels]
  unfold intervalMainLabels
  split <;> rw [(List.toFinset_sort (· ≤ ·) List.nodup_range).mpr (List.pairwise_lt_range.imp (fun h => Nat.le_of_lt h))]
private theorem range_zero_cost (n base bonus : Nat) :
    ((List.range n).map (fun i => base + if i=0 then bonus else 0)).sum =
      n*base + if n=0 then 0 else bonus := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.map_append,List.sum_append,ih]
    cases n <;> simp [Nat.add_mul]
    omega
private theorem interval_cost_sum (r : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (h : IntervalLayout r k K target) (c : Nat) :
    (intervalTree r k K).leafCostSum
      (fun label _ _ => 7*(c + if maskedZeroLeaf (intervalHasTopSpecial k K) label then 2 else 0))
      r.control r.control (r.rightPaths k K) (r.leftPaths k K) =
      (intervalMainLabels k K).length * (7*c) +
        if intervalHasTopSpecial k K then 14 else 0 := by
  rw [interval_label_sum r k K target h]
  by_cases hs : intervalHasTopSpecial k K = true
  · have hp : 1 < intervalLaneCount k K := by
      have hh := hs
      simp only [intervalHasTopSpecial,decide_eq_true_eq] at hh
      exact hh.1
    simp only [intervalMainLabels,hs,↓reduceIte,List.length_range,maskedZeroLeaf,Bool.true_and,
      decide_eq_true_eq,Nat.mul_add]
    simp only [show (fun label => 7*c + 7*(if label=0 then 2 else 0)) =
      (fun label => 7*c + if label=0 then 14 else 0) by funext label; split <;> rfl]
    rw [range_zero_cost]
    simp [show intervalLaneCount k K - 1 ≠ 0 by omega]
  · have hf : intervalHasTopSpecial k K = false := Bool.eq_false_iff.mpr hs
    simp only [intervalMainLabels,hf,Bool.false_eq_true,↓reduceIte,List.length_range,
      maskedZeroLeaf,Bool.false_and,Nat.add_zero]
    simp
private theorem dual_nodes_labels (t : DualUnaryActionTree) : t.internalNodes+1=t.labels.length := by
  induction t with
  | leaf => rfl
  | node a b z o hz ho =>
    simp only [DualUnaryActionTree.internalNodes,DualUnaryActionTree.labels,List.length_append]
    omega
/-- Scalar T cost of both ripple directions, including the special top lane. -/
def intervalScalarTFormula (r : IntervalRegisters) (k K : Nat) : Nat :=
  let count := (intervalMainLabels k K).length
  2*intervalEndpointTFormula r.lengthT.length r.lengthQ.length r.lengthS.length +
    35*count +28*(count-1) +
    if intervalHasTopSpecial k K then
      28*mcxVChainAdaptiveToffoliCost r.lengthS.length +
      28*mcxVChainAdaptiveToffoliCost r.lengthQ.length +91 else 0

theorem intervalAdaptiveTFormula_scalar (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) (h : IntervalLayout r k K target) :
    intervalAdaptiveTFormula r k K mode = intervalScalarTFormula r k K := by
  have hn := dual_nodes_labels (intervalTree r k K)
  rw [intervalTree_labels,Finset.length_sort] at hn
  have hl : (intervalMainLabels k K).toFinset.card = (intervalMainLabels k K).length := by
    apply List.toFinset_card_of_nodup
    unfold intervalMainLabels
    split <;> exact List.nodup_range
  rw [hl] at hn
  have he : (intervalTree r k K).internalNodes=(intervalMainLabels k K).length-1 := by omega
  simp only [intervalAdaptiveTFormula]
  rw [interval_cost_sum r k K target h,interval_cost_sum r k K target h,he]
  cases mode <;> simp only [rippleFirstCellToffoliCost,rippleSecondCellToffoliCost,intervalScalarTFormula]
  all_goals split <;> omega

private theorem quotient_leaf_count (r : QuotientSwapRegisters) (k K : Nat)
    (h : QuotientSwapLayout r k K) : (quotientSwapTree r k K).leaves=K+1-k := by
  rw [unary_leaves,quotientSwapTree_labels r h.k_le_K,Finset.length_sort]
  simpa only [quotientSwapLabels,List.length_range'] using
    List.toFinset_card_of_nodup (show (List.range' k (K+1-k)).Nodup from List.nodup_range')
/-- Integer-only production T formula; no gates or decoder trees are expanded. -/
def secp256k1StepTCount (T : Nat) : Nat :=
  let w := certifiedActiveWindows 256 T
  let special := intervalHasTopSpecial w.remainder.start w.remainder.stop
  let count := intervalLaneCount w.remainder.start w.remainder.stop
  let leaves := if special then count-1 else count
  let c := w.coefficient.stop+1-w.coefficient.start
  let q := w.quotientSwap.stop+1-w.quotientSwap.start
  14189+2*(1456+35*leaves+28*(leaves-1)+(if special then 539 else 0))+
    70*c+28*(c-1)+7*q+14*(q-1)+
    if T%4=0 then 462+endIterationTFormula 259 9 256 (endIterationWindowsAt 256 T) else 0
private theorem interval_scalar_nine (r : IntervalRegisters) (k K : Nat)
    (ht : r.lengthT.length=9) (hq : r.lengthQ.length=9) (hs : r.lengthS.length=9) :
    intervalScalarTFormula r k K = 1456+35*(intervalMainLabels k K).length+
      28*((intervalMainLabels k K).length-1)+(if intervalHasTopSpecial k K then 539 else 0) := by
  simp only [intervalScalarTFormula,ht,hq,hs,intervalEndpointTFormula,mcxVChainAdaptiveToffoliCost]
theorem productionStepTComponents_eq (T : Nat)
    (h : IndexedStepLayout indexedStepProductionRegisters 256 T) :
    productionStepTComponents T = secp256k1StepTCount T := by
  let r := indexedStepProductionRegisters
  let w := certifiedActiveWindows 256 T
  have hc := coefficient_leaf_count (r.coefficient w.coefficient) w.coefficient.start w.coefficient.stop h.coefficient
  have hq := quotient_leaf_count (r.quotient w.quotientSwap) w.quotientSwap.start w.quotientSwap.stop h.quotient
  have hn := unary_nodes (coefficientPrefixTree (r.coefficient w.coefficient) w.coefficient.start w.coefficient.stop)
  have hm := unary_nodes (quotientSwapTree (r.quotient w.quotientSwap) w.quotientSwap.start w.quotientSwap.stop)
  rw [hc] at hn
  rw [hq] at hm
  have he : (coefficientPrefixTree (r.coefficient w.coefficient) w.coefficient.start w.coefficient.stop).internalNodes=
      w.coefficient.stop+1-w.coefficient.start-1 := by omega
  have hf : (quotientSwapTree (r.quotient w.quotientSwap) w.quotientSwap.start w.quotientSwap.stop).internalNodes=
      w.quotientSwap.stop+1-w.quotientSwap.start-1 := by omega
  dsimp only [productionStepTComponents]
  rw [intervalAdaptiveTFormula_scalar _ _ _ .sub .work1 h.remainder,
    intervalAdaptiveTFormula_scalar _ _ _ .add .work1 h.remainder,hc,hq,he,hf]
  have hscalar : intervalScalarTFormula (r.remainder w.remainder) w.remainder.start w.remainder.stop =
      1456+35*(intervalMainLabels w.remainder.start w.remainder.stop).length+
      28*((intervalMainLabels w.remainder.start w.remainder.stop).length-1)+
      if intervalHasTopSpecial w.remainder.start w.remainder.stop then 539 else 0 :=
    interval_scalar_nine _ _ _ (by rfl) (by rfl) (by rfl)
  rw [hscalar]
  dsimp only [secp256k1StepTCount,intervalMainLabels,w]
  by_cases hs : intervalHasTopSpecial w.remainder.start w.remainder.stop = true
  · simp only [show intervalHasTopSpecial (certifiedActiveWindows 256 T).remainder.start
      (certifiedActiveWindows 256 T).remainder.stop = true from hs,↓reduceIte,List.length_range]
    omega
  · simp only [show ¬intervalHasTopSpecial (certifiedActiveWindows 256 T).remainder.start
      (certifiedActiveWindows 256 T).remainder.stop = true from hs,Bool.false_eq_true,↓reduceIte,List.length_range]
    omega

theorem secp256k1StepTCount_sum : ((List.range' 1 1620).map secp256k1StepTCount).sum=122179575 := by decide +kernel

private theorem production_forward_T_sum (start count : Nat)
    (h : IndexedScheduleLayout indexedStepProductionRegisters 256 start count) :
    ((List.range' start count).map (indexedStepAdaptiveTFormula indexedStepProductionRegisters 256)).sum =
      ((List.range' start count).map secp256k1StepTCount).sum :=
  layout_sum_congr _ _ _ _ _ _
    (fun T ht => (indexedStepAdaptiveTFormula_components T ht).trans (productionStepTComponents_eq T ht)) h
private theorem production_reverse_T_sum (start count : Nat)
    (h : IndexedScheduleLayout indexedStepProductionRegisters 256 start count) :
    ((List.range' start count).map (indexedStepInverseAdaptiveTFormula indexedStepProductionRegisters 256)).sum =
      ((List.range' start count).map secp256k1StepTCount).sum :=
  layout_sum_congr _ _ _ _ _ _
    (fun T ht => (indexedStepInverseAdaptiveTFormula_components T ht).trans (productionStepTComponents_eq T ht)) h
/-- Exact worst-branch T count of the complete 1,620-step forward adaptive EEA schedule. -/
theorem secp256k1EEAForwardAdaptive_tCount :
    (secp256k1EEAForwardAdaptive indexedStepProductionRegisters).tCount=122179575 :=
  (indexedScheduleAdaptive_tCount _ _ _ _ secp256k1ScheduleLayout_production).trans
    ((production_forward_T_sum _ _ secp256k1ScheduleLayout_production).trans secp256k1StepTCount_sum)
/-- The literal inverse schedule has the same worst-branch T count, derived from its own blocks. -/
theorem secp256k1EEAReverseAdaptive_tCount :
    (secp256k1EEAReverseAdaptive indexedStepProductionRegisters).tCount=122179575 :=
  (indexedScheduleInverseAdaptive_tCount _ _ _ _ secp256k1ScheduleLayout_production).trans
    ((production_reverse_T_sum _ _ secp256k1ScheduleLayout_production).trans secp256k1StepTCount_sum)
end ShorECDLP.Paper2607_13816
