import ShorECDLP.Submission.«2607_13816».EEA.MeasuredZeroMap
import ShorECDLP.Submission.«2607_13816».EEA.DecoderPrimitiveCounts

namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section

/-- The actual lowered recurrence cell: two Toffolis, two X gates, and corrected AND erasure. -/
theorem measuredZeroCell_primitive (base : Bool) (a b g d t : Wire) :
    primitiveResources (measuredZeroCell base a b g d t) = ⟨2,2,1,2,0,1⟩ := by
  cases base <;> rfl

private theorem cx_toffoli (a b : Wire) (next : AdaptiveCircuit) :
    (primitiveResources (.unitary [.CX a b] next)).toffoli =
      (primitiveResources next).toffoli := by
  simp [primitiveResources, gidneyToffoliCount, gidneyGateCount]

private theorem measuredRangeLeaf_toffoli (after : Bool) (r : Wire)
    (leaf : Nat → Wire → AdaptiveCircuit) (l : Nat) (d : Wire) :
    (primitiveResources (measuredRangeLeaf after r leaf l d)).toffoli =
      (primitiveResources (leaf l r)).toffoli := by
  cases after
  · exact cx_toffoli _ _ _
  · simp only [measuredRangeLeaf, ↓reduceIte, primitiveResources_seq, PrimitiveResources.add]
    simp [primitiveResources, gidneyToffoliCount, gidneyGateCount]

/-- The range wrapper adds one Toffoli for each internal decoder node, with no Toffoli
in the selected cleanup branch. -/
theorem measuredRangeScan_toffoli
    (after : Bool) (order : UnaryOrder) (tree : UnaryActionTree) (q r : Wire)
    (path : List Wire) (leaf : Nat → Wire → AdaptiveCircuit) (hl : tree.Layout q path) :
    (primitiveResources (measuredRangeScan after order tree q r path leaf)).toffoli =
      tree.leafCostSum (fun l _ => (primitiveResources (leaf l r)).toffoli) q path +
        tree.internalNodes := by
  have hb := congrArg PrimitiveResources.toffoli
    (unaryAdaptiveAction_primitive order (measuredRangeLeaf after r leaf) tree q path hl)
  simp only [measuredRangeLeaf_toffoli] at hb
  cases after
  · simp only [measuredRangeScan, Bool.false_eq_true, ↓reduceIte, primitiveResources_seq, PrimitiveResources.add]
    simpa [primitiveResources, gidneyToffoliCount, gidneyGateCount] using hb
  · exact (cx_toffoli _ _ _).trans hb

private theorem labels_cost (tree : UnaryActionTree) (q : Wire) (path : List Wire)
    (cost : Nat → Nat) (hl : tree.Layout q path) :
    tree.leafCostSum (fun l _ => cost l) q path = (tree.labels.map cost).sum := by
  induction hl with
  | leaf => rfl
  | node i q w z o rest hn hz ho iz io =>
      simp [UnaryActionTree.leafCostSum, UnaryActionTree.labels, iz, io]

private theorem node_count (tree : UnaryActionTree) : tree.internalNodes + 1 = tree.labels.length := by
  induction tree with
  | leaf => rfl
  | node i z o iz io => simp only [UnaryActionTree.internalNodes, UnaryActionTree.labels,
      List.length_append]; omega

/-- Exact constructor-derived count, valid even when the tree contains labels outside the window. -/
theorem measuredUpperZeroMap_toffoli
    (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (hl : tree.Layout control path) :
    (primitiveResources (measuredUpperZeroMap k K tree control r t path bitAt dirtyAt)).toffoli =
      (tree.labels.map (fun l => if k ≤ l ∧ l ≤ K then 2 else 0)).sum +
      (tree.labels.map (fun l => if k ≤ l ∧ l < K then 2 else 0)).sum + 2*tree.internalNodes := by
  have hf : (fun l _ => (primitiveResources
      (measuredUpperForwardLeaf k K control t bitAt dirtyAt l r)).toffoli) =
      (fun l (_ : Wire) => if k ≤ l ∧ l ≤ K then 2 else 0) := by
    funext l d
    simp only [measuredUpperForwardLeaf]
    split
    · split <;> rw [measuredZeroCell_primitive]
    · rfl
  have hr : (fun l _ => (primitiveResources
      (measuredUpperReverseLeaf k K t bitAt dirtyAt l r)).toffoli) =
      (fun l (_ : Wire) => if k ≤ l ∧ l < K then 2 else 0) := by
    funext l d
    simp only [measuredUpperReverseLeaf]
    split
    · rw [measuredZeroCell_primitive]
    · rfl
  simp only [measuredUpperZeroMap, primitiveResources_seq, PrimitiveResources.add,
    measuredRangeScan_toffoli _ _ _ _ _ _ _ hl, hf, hr, labels_cost _ _ _ _ hl]
  omega

/-- Lower-map mirror, retaining the first-lane base rather than the last-lane base. -/
theorem measuredLowerZeroMap_toffoli
    (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (hl : tree.Layout control path) :
    (primitiveResources (measuredLowerZeroMap k K tree control r t path bitAt dirtyAt)).toffoli =
      (tree.labels.map (fun l => if k ≤ l ∧ l ≤ K then 2 else 0)).sum +
      (tree.labels.map (fun l => if k < l ∧ l ≤ K then 2 else 0)).sum + 2*tree.internalNodes := by
  have hf : (fun l _ => (primitiveResources
      (measuredLowerForwardLeaf k K control t bitAt dirtyAt l r)).toffoli) =
      (fun l (_ : Wire) => if k ≤ l ∧ l ≤ K then 2 else 0) := by
    funext l d
    simp only [measuredLowerForwardLeaf]
    split
    · split <;> rw [measuredZeroCell_primitive]
    · rfl
  have hr : (fun l _ => (primitiveResources
      (measuredLowerReverseLeaf k K t bitAt dirtyAt l r)).toffoli) =
      (fun l (_ : Wire) => if k < l ∧ l ≤ K then 2 else 0) := by
    funext l d
    simp only [measuredLowerReverseLeaf]
    split
    · rw [measuredZeroCell_primitive]
    · rfl
  simp only [measuredLowerZeroMap, primitiveResources_seq, PrimitiveResources.add,
    measuredRangeScan_toffoli _ _ _ _ _ _ _ hl, hf, hr, labels_cost _ _ _ _ hl]
  omega

private theorem measured_sum_map_const
    (labels : List Nat) (cost : Nat) :
    (labels.map fun _ ↦ cost).sum = labels.length * cost := by
  induction labels with
  | nil => simp
  | cons label labels ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      simp [Nat.succ_mul, Nat.add_comm]

private theorem measured_sum_last_zero
    (k K cost : Nat) (hkK : k ≤ K) :
    ((zeroMapLabels k K).map fun label ↦
      if label = K then 0 else cost).sum = cost * (K - k) := by
  induction K, hkK using Nat.le_induction with
  | base => simp
  | succ K hkK ih =>
      rw [zeroMapLabels_snoc hkK]
      simp only [List.map_append, List.sum_append, List.map_singleton,
        List.sum_singleton]
      have hmap :
          (zeroMapLabels k K).map
              (fun label ↦ if label = K + 1 then 0 else cost) =
            (zeroMapLabels k K).map (fun _ ↦ cost) := by
        apply List.map_congr_left
        intro label hlabel
        have hle : label ≤ K := (mem_zeroMapLabels hkK).mp hlabel |>.2
        simp [show label ≠ K + 1 by omega]
      rw [hmap, measured_sum_map_const]
      simp [zeroMapLabels, Nat.mul_comm]

private theorem measured_sum_first_zero
    (k K cost : Nat) (hkK : k ≤ K) :
    ((zeroMapLabels k K).map fun label ↦
      if label = k then 0 else cost).sum = cost * (K - k) := by
  by_cases heq : k = K
  · subst K
    simp
  · have hlt : k < K := by omega
    rw [zeroMapLabels_cons hlt]
    simp only [List.map_cons, List.sum_cons]
    simp only [if_true, zero_add]
    have hmap :
        (zeroMapLabels (k + 1) K).map
            (fun label ↦ if label = k then 0 else cost) =
          (zeroMapLabels (k + 1) K).map (fun _ ↦ cost) := by
      apply List.map_congr_left
      intro label hlabel
      have hge : k + 1 ≤ label :=
        (mem_zeroMapLabels (show k + 1 ≤ K by omega)).mp hlabel |>.1
      simp [show label ≠ k by omega]
    rw [hmap, measured_sum_map_const]
    simp [zeroMapLabels, Nat.mul_comm]

/-- On the source window tree, measured cleanup reduces `10*M-7` Toffolis to `6*M-4`. -/
theorem measuredUpperZeroMap_toffoli_closed
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree) (control r t : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire) (hl : tree.Layout control path)
    (hlabels : tree.labels = zeroMapLabels k K) :
    (primitiveResources (measuredUpperZeroMap k K tree control r t path bitAt dirtyAt)).toffoli =
      6*(K+1-k)-4 := by
  rw [measuredUpperZeroMap_toffoli _ _ _ _ _ _ _ _ _ hl, hlabels]
  have hf : (zeroMapLabels k K).map (fun l => if k ≤ l ∧ l ≤ K then 2 else 0) =
      (zeroMapLabels k K).map (fun _ => 2) := by
    apply List.map_congr_left
    intro l hh
    simp [(mem_zeroMapLabels hkK).mp hh]
  have hr : (zeroMapLabels k K).map (fun l => if k ≤ l ∧ l < K then 2 else 0) =
      (zeroMapLabels k K).map (fun l => if l = K then 0 else 2) := by
    apply List.map_congr_left
    intro l hh
    have hwindow := (mem_zeroMapLabels hkK).mp hh
    by_cases heq : l = K
    · simp [heq]
    · simp [heq, show k ≤ l ∧ l < K by omega]
  rw [hf, hr, measured_sum_map_const, measured_sum_last_zero _ _ _ hkK]
  have hn := node_count tree
  rw [hlabels] at hn
  simp only [zeroMapLabels, List.length_map, List.length_range] at hn ⊢
  omega

/-- On the source window tree, measured cleanup reduces `10*M-7` Toffolis to `6*M-4`. -/
theorem measuredLowerZeroMap_toffoli_closed
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree) (control r t : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire) (hl : tree.Layout control path)
    (hlabels : tree.labels = zeroMapLabels k K) :
    (primitiveResources (measuredLowerZeroMap k K tree control r t path bitAt dirtyAt)).toffoli =
      6*(K+1-k)-4 := by
  rw [measuredLowerZeroMap_toffoli _ _ _ _ _ _ _ _ _ hl, hlabels]
  have hf : (zeroMapLabels k K).map (fun l => if k ≤ l ∧ l ≤ K then 2 else 0) =
      (zeroMapLabels k K).map (fun _ => 2) := by
    apply List.map_congr_left
    intro l hh
    simp [(mem_zeroMapLabels hkK).mp hh]
  have hr : (zeroMapLabels k K).map (fun l => if k < l ∧ l ≤ K then 2 else 0) =
      (zeroMapLabels k K).map (fun l => if l = k then 0 else 2) := by
    apply List.map_congr_left
    intro l hh
    have hwindow := (mem_zeroMapLabels hkK).mp hh
    by_cases heq : l = k
    · simp [heq]
    · simp [heq, show k < l ∧ l ≤ K by omega]
  rw [hf, hr, measured_sum_map_const, measured_sum_first_zero _ _ _ hkK]
  have hn := node_count tree
  rw [hlabels] at hn
  simp only [zeroMapLabels, List.length_map, List.length_range] at hn ⊢
  omega

end
end ShorECDLP.Paper2607_13816
