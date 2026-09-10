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
end ShorECDLP.Paper2607_13816
