import ShorECDLP.Submission.«2607_13816».EEA.ZeroMap
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredAnd

/-!
# Measurement-assisted zero-map recurrence cells

The temporary AND in each source length-refresh leaf is erased by X measurement and its
selected controlled-Z correction. The borrowed dirty target is never measured. The source's
base-cell control order is retained, including when the external block control is zero.
-/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section

/-- Source prefix before erasing the temporary AND. -/
def measuredZeroPrefix (base : Bool) (rangeControl bit guard target temporary : Wire) : Circuit :=
  [.CCX rangeControl bit temporary, .X temporary] ++
    (if base then [.CCX guard temporary target] else [.CCX temporary guard target]) ++
      [.X temporary]

/-- Two Toffolis and corrected X erasure replace the three-Toffoli recurrence cell. -/
def measuredZeroCell (base : Bool) (rangeControl bit guard target temporary : Wire) :
    AdaptiveCircuit :=
  .unitary (measuredZeroPrefix base rangeControl bit guard target temporary)
    (measuredAndErase rangeControl bit temporary)

private theorem coherent_seq_classical
    {first second : AdaptiveCircuit} {a b : Circuit} {P Q : BasisState → Prop}
    (ha : CoherentlyImplementsOn first (Quantum.run a) P)
    (hb : CoherentlyImplementsOn second (Quantum.run b) Q)
    (hclassical : HPFree a) (hnext : ∀ s, P s → Q (Classical.run a s)) :
    CoherentlyImplementsOn (first.seq second) (Quantum.run (a ++ b)) P := by
  have h := ha.seq hb (by
    intro s hs
    rw [run_ket_agrees_classical a s hclassical]
    exact supportedOn_ket Q _ (hnext s hs))
  apply h.congrIdeal
  intro s _
  exact (Quantum.run_append a b (ket s)).symm

/-- The middle operation changes only the dirty target, so the temporary still holds its AND. -/
theorem measuredZeroPrefix_computed (base : Bool)
    (rangeControl bit guard target temporary : Wire)
    (hlayout : [rangeControl, bit, guard, target, temporary].Nodup)
    (s : BasisState) (hclean : s temporary = false) :
    PathAndComputed rangeControl bit temporary
      (Classical.run (measuredZeroPrefix base rangeControl bit guard target temporary) s) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hlayout
  cases base <;> cases hc : s rangeControl <;> cases hb : s bit <;>
    simp_all [measuredZeroPrefix, PathAndComputed, Classical.run, Classical.applyGate, upd, ne_comm]

/-- Every corrected measurement branch implements the strict source cell with a coefficient
independent of all input bits, including arbitrary dirty data. -/
theorem measuredZeroCell_coherent (base : Bool)
    (rangeControl bit guard target temporary : Wire)
    (hlayout : [rangeControl, bit, guard, target, temporary].Nodup) :
    CoherentlyImplementsOn (measuredZeroCell base rangeControl bit guard target temporary)
      (Quantum.run (measuredZeroPrefix base rangeControl bit guard target temporary ++
        [.CCX rangeControl bit temporary])) (fun s => s temporary = false) := by
  have hparts := hlayout
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hparts
  apply coherent_seq_classical
    (CoherentlyImplementsOn.unitary _ (fun s => s temporary = false))
    (measuredAndErase_coherent_uncompute rangeControl bit temporary
      hparts.1.1 hparts.1.2.2.2 hparts.2.1.2.2)
  · cases base <;> simp [measuredZeroPrefix]
  · exact measuredZeroPrefix_computed base rangeControl bit guard target temporary hlayout

/-- Physical well-formedness includes the conditional correction gate. -/
theorem measuredZeroCell_wellFormed (base : Bool)
    (rangeControl bit guard target temporary : Wire)
    (hlayout : [rangeControl, bit, guard, target, temporary].Nodup) :
    (measuredZeroCell base rangeControl bit guard target temporary).WellFormed := by
  have hparts := hlayout
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hparts
  refine ⟨?_, measuredAndErase_wellFormed rangeControl bit temporary hparts.1.1⟩
  cases base <;> simp_all [measuredZeroPrefix, CircuitWellFormed, Gate.WellFormed, ne_comm]

@[simp] theorem measuredZeroCell_measurementCount (base : Bool)
    (rangeControl bit guard target temporary : Wire) :
    (measuredZeroCell base rangeControl bit guard target temporary).measurementCount = 1 := by
  simp [measuredZeroCell, AdaptiveCircuit.measurementCount]

@[simp] theorem measuredZeroCell_tCount (base : Bool)
    (rangeControl bit guard target temporary : Wire) :
    (measuredZeroCell base rangeControl bit guard target temporary).tCount = 14 := by
  cases base <;> simp [measuredZeroCell, measuredZeroPrefix, AdaptiveCircuit.tCount,
    ShorECDLP.tCount, tCost]

/-- Increasing upper-map leaf, including the root-controlled last lane. -/
def measuredUpperForwardLeaf (k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (rangeAccumulator : Wire) : AdaptiveCircuit :=
  if k ≤ label ∧ label ≤ K then
    if label = K then
      measuredZeroCell true rangeAccumulator (bitAt label) control (dirtyAt label) temporary
    else measuredZeroCell false rangeAccumulator (bitAt label) (dirtyAt (label + 1))
      (dirtyAt label) temporary
  else .done

/-- Decreasing upper-map leaf; the base is skipped. -/
def measuredUpperReverseLeaf (k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (rangeAccumulator : Wire) : AdaptiveCircuit :=
  if k ≤ label ∧ label < K then
    measuredZeroCell false rangeAccumulator (bitAt label) (dirtyAt (label + 1))
      (dirtyAt label) temporary
  else .done

/-- Decreasing lower-map leaf, including the root-controlled first lane. -/
def measuredLowerForwardLeaf (k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (rangeAccumulator : Wire) : AdaptiveCircuit :=
  if k ≤ label ∧ label ≤ K then
    if label = k then
      measuredZeroCell true rangeAccumulator (bitAt label) control (dirtyAt label) temporary
    else measuredZeroCell false rangeAccumulator (bitAt label) (dirtyAt (label - 1))
      (dirtyAt label) temporary
  else .done

/-- Increasing lower-map leaf; the base is skipped. -/
def measuredLowerReverseLeaf (k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (rangeAccumulator : Wire) : AdaptiveCircuit :=
  if k < label ∧ label ≤ K then
    measuredZeroCell false rangeAccumulator (bitAt label) (dirtyAt (label - 1))
      (dirtyAt label) temporary
  else .done

/-- The actual upper forward adaptive leaf coherently refines its source leaf. -/
theorem measuredUpperForwardLeaf_coherent
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) :
    CoherentlyImplementsOn (measuredUpperForwardLeaf k K control temporary bitAt dirtyAt label rangeAccumulator)
      (Quantum.run (upperZeroForwardLeaf k K control temporary bitAt dirtyAt label rangeAccumulator)) (fun s => s temporary = false) := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · rw [measuredUpperForwardLeaf, upperZeroForwardLeaf, if_pos hwindow, if_pos hwindow]
    have hlabel := (mem_zeroMapLabels hkK).2 (show k ≤ label ∧ label ≤ K by omega)
    by_cases hbase : label = K
    · rw [if_pos hbase, if_pos hbase]
      exact measuredZeroCell_coherent true rangeAccumulator (bitAt label) control
        (dirtyAt label) temporary (hlayout.cell label hlabel control (Or.inl rfl))
    · rw [if_neg hbase, if_neg hbase]
      apply measuredZeroCell_coherent false
      apply hlayout.cell label hlabel (dirtyAt (label + 1))
      exact Or.inr ⟨label + 1, (mem_zeroMapLabels hkK).2 (by omega), by omega, rfl⟩
  · simpa [measuredUpperForwardLeaf, upperZeroForwardLeaf, hwindow] using
      (CoherentlyImplementsOn.unitary [] (fun s => s temporary = false))

/-- The actual upper reverse adaptive leaf coherently refines its source leaf. -/
theorem measuredUpperReverseLeaf_coherent
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) :
    CoherentlyImplementsOn (measuredUpperReverseLeaf k K temporary bitAt dirtyAt label rangeAccumulator)
      (Quantum.run (upperZeroReverseLeaf k K temporary bitAt dirtyAt label rangeAccumulator)) (fun s => s temporary = false) := by
  by_cases hwindow : k ≤ label ∧ label < K
  · rw [measuredUpperReverseLeaf, upperZeroReverseLeaf, if_pos hwindow, if_pos hwindow]
    have hlabel := (mem_zeroMapLabels hkK).2 (show k ≤ label ∧ label ≤ K by omega)
    apply measuredZeroCell_coherent false
    apply hlayout.cell label hlabel (dirtyAt (label + 1))
    exact Or.inr ⟨label + 1, (mem_zeroMapLabels hkK).2 (by omega), by omega, rfl⟩
  · simpa [measuredUpperReverseLeaf, upperZeroReverseLeaf, hwindow] using
      (CoherentlyImplementsOn.unitary [] (fun s => s temporary = false))

/-- The actual lower forward adaptive leaf coherently refines its source leaf. -/
theorem measuredLowerForwardLeaf_coherent
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) :
    CoherentlyImplementsOn (measuredLowerForwardLeaf k K control temporary bitAt dirtyAt label rangeAccumulator)
      (Quantum.run (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt label rangeAccumulator)) (fun s => s temporary = false) := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · rw [measuredLowerForwardLeaf, lowerZeroForwardLeaf, if_pos hwindow, if_pos hwindow]
    have hlabel := (mem_zeroMapLabels hkK).2 (show k ≤ label ∧ label ≤ K by omega)
    by_cases hbase : label = k
    · rw [if_pos hbase, if_pos hbase]
      exact measuredZeroCell_coherent true rangeAccumulator (bitAt label) control
        (dirtyAt label) temporary (hlayout.cell label hlabel control (Or.inl rfl))
    · rw [if_neg hbase, if_neg hbase]
      apply measuredZeroCell_coherent false
      apply hlayout.cell label hlabel (dirtyAt (label - 1))
      exact Or.inr ⟨label - 1, (mem_zeroMapLabels hkK).2 (by omega), by omega, rfl⟩
  · simpa [measuredLowerForwardLeaf, lowerZeroForwardLeaf, hwindow] using
      (CoherentlyImplementsOn.unitary [] (fun s => s temporary = false))

/-- The actual lower reverse adaptive leaf coherently refines its source leaf. -/
theorem measuredLowerReverseLeaf_coherent
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) :
    CoherentlyImplementsOn (measuredLowerReverseLeaf k K temporary bitAt dirtyAt label rangeAccumulator)
      (Quantum.run (lowerZeroReverseLeaf k K temporary bitAt dirtyAt label rangeAccumulator)) (fun s => s temporary = false) := by
  by_cases hwindow : k < label ∧ label ≤ K
  · rw [measuredLowerReverseLeaf, lowerZeroReverseLeaf, if_pos hwindow, if_pos hwindow]
    have hlabel := (mem_zeroMapLabels hkK).2 (show k ≤ label ∧ label ≤ K by omega)
    apply measuredZeroCell_coherent false
    apply hlayout.cell label hlabel (dirtyAt (label - 1))
    exact Or.inr ⟨label - 1, (mem_zeroMapLabels hkK).2 (by omega), by omega, rfl⟩
  · simpa [measuredLowerReverseLeaf, lowerZeroReverseLeaf, hwindow] using
      (CoherentlyImplementsOn.unitary [] (fun s => s temporary = false))

/-- The equality pulse remains before/after the adaptive payload in source order. -/
def measuredRangeLeaf (toggleAfter : Bool) (rangeAccumulator : Wire)
    (leaf : Nat → Wire → AdaptiveCircuit) (label : Nat) (dynamic : Wire) : AdaptiveCircuit :=
  if toggleAfter then
    (leaf label rangeAccumulator).seq (.unitary [.CX dynamic rangeAccumulator] .done)
  else .unitary [.CX dynamic rangeAccumulator] (leaf label rangeAccumulator)

/-- The full source range traversal uses measured decoder cleanup and measured payloads. -/
def measuredRangeScan (toggleAfter : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control rangeAccumulator : Wire) (path : List Wire)
    (leaf : Nat → Wire → AdaptiveCircuit) : AdaptiveCircuit :=
  if toggleAfter then
    .unitary [.CX control rangeAccumulator]
      (unaryAdaptiveAction order (measuredRangeLeaf true rangeAccumulator leaf) tree control path)
  else
    (unaryAdaptiveAction order (measuredRangeLeaf false rangeAccumulator leaf) tree control path).seq
      (.unitary [.CX control rangeAccumulator] .done)

private theorem coherent_mono {a : AdaptiveCircuit} {u : State →ₗ[ℂ] State}
    {P Q : BasisState → Prop} (h : CoherentlyImplementsOn a u P) (hsub : ∀ s, Q s → P s) :
    CoherentlyImplementsOn a u Q := by
  rcases h with ⟨c, hc, hm⟩
  exact ⟨c, hc.imp (fun _ _ hb s hs => hb s (hsub s hs)), hm⟩

/-- Reusable scan theorem: the clean temporary is preserved between all leaves. The range
accumulator itself may start dirty; this theorem compares exactly the corresponding strict scan. -/
theorem measuredRangeScan_coherent
    (toggleAfter : Bool) (order : UnaryOrder) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (leaf : Nat → Wire → AdaptiveCircuit) (strict : Nat → Wire → Circuit)
    (hlayout : tree.Layout control path)
    (hfull : ((control :: tree.indexWires.dedup ++ path) ++ [rangeAccumulator, temporary]).Nodup)
    (hp : ∀ label, HPFree (strict label rangeAccumulator))
    (hpres : ∀ label s wire, wire ∈ (control :: tree.indexWires.dedup ++ path) ++ [temporary] →
      Classical.run (strict label rangeAccumulator) s wire = s wire)
    (hc : ∀ label ∈ tree.labels, CoherentlyImplementsOn (leaf label rangeAccumulator)
      (Quantum.run (strict label rangeAccumulator)) (fun s => s temporary = false)) :
    CoherentlyImplementsOn
      (measuredRangeScan toggleAfter order tree control rangeAccumulator path leaf)
      (Quantum.run (rangeScanUnitary toggleAfter order tree control rangeAccumulator path strict))
      (fun s => Clean path s ∧ s temporary = false) := by
  let decoder := control :: tree.indexWires.dedup ++ path
  have hdis := List.disjoint_of_nodup_append hfull
  have hrange : ∀ w, w ∈ decoder ++ [temporary] → w ≠ rangeAccumulator := by
    intro w hw heq
    subst w
    rcases List.mem_append.mp hw with hd | ht
    · exact List.disjoint_left.mp hdis hd (by simp)
    · have hrt := hfull.of_append_right
      simp only [List.mem_singleton] at ht
      subst temporary
      simp at hrt
  have hshort : (decoder ++ [temporary]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hfull.of_append_left, by simp, ?_⟩
    intro a ha b hb hab
    have hb' : b = temporary := List.mem_singleton.mp hb
    subst b
    subst a
    exact List.disjoint_left.mp hdis ha (by simp)
  have hcx : ∀ dynamic s w, w ∈ decoder ++ [temporary] →
      Classical.run [.CX dynamic rangeAccumulator] s w = s w := by
    intro dynamic s w hw
    simp [Classical.run, Classical.applyGate, upd, hrange w hw]
  have hwrappedHP : UnaryLeafHPFree (rangeScanLeafAction toggleAfter rangeAccumulator strict) := by
    intro label dynamic
    cases toggleAfter <;> simp [rangeScanLeafAction, hp]
  have hwrappedPres : UnaryLeafPreserves (rangeScanLeafAction toggleAfter rangeAccumulator strict)
      (decoder ++ [temporary]) := by
    intro label dynamic hd s w hw
    cases toggleAfter <;>
      simp only [rangeScanLeafAction, Bool.false_eq_true, ↓reduceIte, Classical.run_append]
    · rw [hpres label _ w hw, hcx dynamic s w hw]
    · rw [hcx dynamic _ w hw, hpres label s w hw]
  have hwrappedC : UnaryAdaptiveLeafCoherentOn
      (measuredRangeLeaf toggleAfter rangeAccumulator leaf)
      (rangeScanLeafAction toggleAfter rangeAccumulator strict) tree.labels (decoder) ([temporary]) := by
    intro label hl dynamic hd
    apply coherent_mono (P := fun s => s temporary = false)
    · cases toggleAfter
      · apply coherent_seq_classical (CoherentlyImplementsOn.unitary _ _) (hc label hl)
        · simp
        · intro s hs
          rw [hcx dynamic s temporary (by simp)]
          exact hs
      · apply coherent_seq_classical (hc label hl) (CoherentlyImplementsOn.unitary _ (fun _ => True))
        · exact hp label
        · intro _ _; trivial
    · intro s hs
      exact hs temporary (by simp)
  have hbody := unaryAdaptiveAction_coherent_on order
    (measuredRangeLeaf toggleAfter rangeAccumulator leaf)
    (rangeScanLeafAction toggleAfter rangeAccumulator strict) tree control (path) ([temporary])
    hlayout hshort hwrappedPres hwrappedC hwrappedHP
  have hbody' := coherent_mono hbody (fun s (hs : Clean path s ∧ s temporary = false) =>
    ⟨hs.1, by intro w hw; simpa using (List.mem_singleton.mp hw ▸ hs.2)⟩)
  cases toggleAfter
  · exact coherent_seq_classical hbody'
      (CoherentlyImplementsOn.unitary _ (fun _ => True))
      (unaryActionUnitary_HPFree _ _ _ _ _ hwrappedHP) (by intro _ _; trivial)
  · apply coherent_seq_classical (CoherentlyImplementsOn.unitary _ _) hbody'
    · simp
    · intro s hs
      constructor
      · intro w hw
        rw [hcx control s w (by simp [decoder, hw])]
        exact hs.1 w hw
      · rw [hcx control s temporary (by simp)]
        exact hs.2


private theorem zeroReference_preserves (base : Bool)
    (rangeControl bit guard target temporary : Wire)
    (hlayout : [rangeControl, bit, guard, target, temporary].Nodup)
    (s : BasisState) (w : Wire) (hw : w ≠ target) :
    Classical.run (measuredZeroPrefix base rangeControl bit guard target temporary ++
      [.CCX rangeControl bit temporary]) s w = s w := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hlayout
  by_cases ht : w = temporary
  · subst w
    cases base <;> cases hc : s rangeControl <;> cases hb : s bit <;>
      cases ha : s temporary <;>
      simp_all [measuredZeroPrefix, Classical.run, Classical.applyGate, upd, ne_comm]
  · cases base <;> simp [measuredZeroPrefix, Classical.run, Classical.applyGate, upd, ht, hw]

private theorem zeroLayout_protected_ne_dirty
    {k K : Nat} {tree : UnaryActionTree} {control rangeAccumulator temporary : Wire}
    {path : List Wire} {bitAt dirtyAt : Nat → Wire}
    (h : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (hl : label ∈ zeroMapLabels k K) (w : Wire)
    (hw : w ∈ zeroMapProtectedWires tree control path ++ [temporary]) : w ≠ dirtyAt label := by
  rcases List.mem_append.mp hw with hw | hw
  · intro heq
    exact List.disjoint_left.mp (List.disjoint_of_nodup_append h.wires) hw (by
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_append_right _ (List.mem_map.mpr ⟨label, hl, heq.symm⟩))))
  · have heq := List.mem_singleton.mp hw
    subst w
    exact h.temporary_ne_dirty hl

private theorem measuredUpperForwardLeaf_preserves
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (s : BasisState) (w : Wire)
    (hw : w ∈ zeroMapProtectedWires tree control path ++ [temporary]) :
    Classical.run (upperZeroForwardLeaf k K control temporary bitAt dirtyAt label rangeAccumulator) s w = s w := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · rw [upperZeroForwardLeaf, if_pos hwindow]
    have hlabel := (mem_zeroMapLabels hkK).2 (show k ≤ label ∧ label ≤ K by omega)
    have hwd := zeroLayout_protected_ne_dirty hlayout label hlabel w hw
    by_cases hbase : label = K
    · rw [if_pos hbase]
      exact zeroReference_preserves true rangeAccumulator (bitAt label) control
        (dirtyAt label) temporary (hlayout.cell label hlabel control (Or.inl rfl)) s w hwd
    · rw [if_neg hbase]
      apply zeroReference_preserves false _ _ _ _ _ ?_ s w hwd
      apply hlayout.cell label hlabel (dirtyAt (label + 1))
      exact Or.inr ⟨label + 1, (mem_zeroMapLabels hkK).2 (by omega), by omega, rfl⟩
  · simp [upperZeroForwardLeaf, hwindow]

private theorem measuredUpperReverseLeaf_preserves
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (s : BasisState) (w : Wire)
    (hw : w ∈ zeroMapProtectedWires tree control path ++ [temporary]) :
    Classical.run (upperZeroReverseLeaf k K temporary bitAt dirtyAt label rangeAccumulator) s w = s w := by
  by_cases hwindow : k ≤ label ∧ label < K
  · rw [upperZeroReverseLeaf, if_pos hwindow]
    have hlabel := (mem_zeroMapLabels hkK).2 (show k ≤ label ∧ label ≤ K by omega)
    have hwd := zeroLayout_protected_ne_dirty hlayout label hlabel w hw
    apply zeroReference_preserves false _ _ _ _ _ ?_ s w hwd
    apply hlayout.cell label hlabel (dirtyAt (label + 1))
    exact Or.inr ⟨label + 1, (mem_zeroMapLabels hkK).2 (by omega), by omega, rfl⟩
  · simp [upperZeroReverseLeaf, hwindow]

private theorem measuredLowerForwardLeaf_preserves
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (s : BasisState) (w : Wire)
    (hw : w ∈ zeroMapProtectedWires tree control path ++ [temporary]) :
    Classical.run (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt label rangeAccumulator) s w = s w := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · rw [lowerZeroForwardLeaf, if_pos hwindow]
    have hlabel := (mem_zeroMapLabels hkK).2 (show k ≤ label ∧ label ≤ K by omega)
    have hwd := zeroLayout_protected_ne_dirty hlayout label hlabel w hw
    by_cases hbase : label = k
    · rw [if_pos hbase]
      exact zeroReference_preserves true rangeAccumulator (bitAt label) control
        (dirtyAt label) temporary (hlayout.cell label hlabel control (Or.inl rfl)) s w hwd
    · rw [if_neg hbase]
      apply zeroReference_preserves false _ _ _ _ _ ?_ s w hwd
      apply hlayout.cell label hlabel (dirtyAt (label - 1))
      exact Or.inr ⟨label - 1, (mem_zeroMapLabels hkK).2 (by omega), by omega, rfl⟩
  · simp [lowerZeroForwardLeaf, hwindow]

private theorem measuredLowerReverseLeaf_preserves
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (s : BasisState) (w : Wire)
    (hw : w ∈ zeroMapProtectedWires tree control path ++ [temporary]) :
    Classical.run (lowerZeroReverseLeaf k K temporary bitAt dirtyAt label rangeAccumulator) s w = s w := by
  by_cases hwindow : k < label ∧ label ≤ K
  · rw [lowerZeroReverseLeaf, if_pos hwindow]
    have hlabel := (mem_zeroMapLabels hkK).2 (show k ≤ label ∧ label ≤ K by omega)
    have hwd := zeroLayout_protected_ne_dirty hlayout label hlabel w hw
    apply zeroReference_preserves false _ _ _ _ _ ?_ s w hwd
    apply hlayout.cell label hlabel (dirtyAt (label - 1))
    exact Or.inr ⟨label - 1, (mem_zeroMapLabels hkK).2 (by omega), by omega, rfl⟩
  · simp [lowerZeroReverseLeaf, hwindow]


private theorem zeroLayout_scan_layout
    {k K : Nat} {tree : UnaryActionTree} {control rangeAccumulator temporary : Wire}
    {path : List Wire} {bitAt dirtyAt : Nat → Wire}
    (h : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt) :
    ((control :: tree.indexWires.dedup ++ path) ++ [rangeAccumulator, temporary]).Nodup := by
  have h' : (((control :: tree.indexWires.dedup ++ path) ++ [rangeAccumulator, temporary]) ++
      ((zeroMapLabels k K).map bitAt ++ (zeroMapLabels k K).map dirtyAt)).Nodup := by
    simpa [zeroMapProtectedWires, List.append_assoc] using h.wires
  exact h'.of_append_left

/-- Both measured source passes, including measured decoder-path cleanup. -/
def measuredUpperZeroMap (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) : AdaptiveCircuit :=
  (measuredRangeScan true .inc tree control rangeAccumulator path
    (measuredUpperForwardLeaf k K control temporary bitAt dirtyAt)).seq
  (measuredRangeScan false .dec tree control rangeAccumulator path
    (measuredUpperReverseLeaf k K temporary bitAt dirtyAt))

/-- The complete measured upper map coherently implements the strict two-pass map on clean
scratch. All dirty-word inputs and both external-control values are retained. -/
theorem measuredUpperZeroMap_coherent
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt) :
    CoherentlyImplementsOn
      (measuredUpperZeroMap k K tree control rangeAccumulator temporary path bitAt dirtyAt)
      (Quantum.run (upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt))
      (fun s => Clean path s ∧ s temporary = false) := by
  have hf : CoherentlyImplementsOn
      (measuredRangeScan true .inc tree control rangeAccumulator path
        (measuredUpperForwardLeaf k K control temporary bitAt dirtyAt))
      (Quantum.run (rangeScanUnitary true .inc tree control rangeAccumulator path
        (upperZeroForwardLeaf k K control temporary bitAt dirtyAt)))
      (fun s => Clean path s ∧ s temporary = false) := by
    apply measuredRangeScan_coherent _ _ _ _ _ _ _ _ _ hlayout.decoder (zeroLayout_scan_layout hlayout)
    · intro label
      exact upperZeroForwardLeaf_HPFree k K control rangeAccumulator temporary bitAt dirtyAt label
    · exact measuredUpperForwardLeaf_preserves k K hkK tree control rangeAccumulator temporary
        path bitAt dirtyAt hlayout
    · intro label _
      exact measuredUpperForwardLeaf_coherent k K hkK tree control rangeAccumulator temporary
        path bitAt dirtyAt hlayout label
  have hr : CoherentlyImplementsOn
      (measuredRangeScan false .dec tree control rangeAccumulator path
        (measuredUpperReverseLeaf k K temporary bitAt dirtyAt))
      (Quantum.run (rangeScanUnitary false .dec tree control rangeAccumulator path
        (upperZeroReverseLeaf k K temporary bitAt dirtyAt)))
      (fun s => Clean path s ∧ s temporary = false) := by
    apply measuredRangeScan_coherent _ _ _ _ _ _ _ _ _ hlayout.decoder (zeroLayout_scan_layout hlayout)
    · intro label
      exact upperZeroReverseLeaf_HPFree k K rangeAccumulator temporary bitAt dirtyAt label
    · exact measuredUpperReverseLeaf_preserves k K hkK tree control rangeAccumulator temporary
        path bitAt dirtyAt hlayout
    · intro label _
      exact measuredUpperReverseLeaf_coherent k K hkK tree control rangeAccumulator temporary
        path bitAt dirtyAt hlayout label
  apply coherent_seq_classical hf hr
  · simp only [rangeScanUnitary, ↓reduceIte]
    rw [hpFree_append]
    refine ⟨by simp, ?_⟩
    apply unaryActionUnitary_HPFree
    intro label dynamic
    simp [rangeScanLeafAction]
  · intro state hs
    exact upperZeroForwardScan_scratch k K hkK tree control rangeAccumulator temporary path
      bitAt dirtyAt hlayout state hs.1 hs.2

/-- Both measured source passes, including measured decoder-path cleanup. -/
def measuredLowerZeroMap (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) : AdaptiveCircuit :=
  (measuredRangeScan true .dec tree control rangeAccumulator path
    (measuredLowerForwardLeaf k K control temporary bitAt dirtyAt)).seq
  (measuredRangeScan false .inc tree control rangeAccumulator path
    (measuredLowerReverseLeaf k K temporary bitAt dirtyAt))

/-- The complete measured lower map coherently implements the strict two-pass map on clean
scratch. All dirty-word inputs and both external-control values are retained. -/
theorem measuredLowerZeroMap_coherent
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt) :
    CoherentlyImplementsOn
      (measuredLowerZeroMap k K tree control rangeAccumulator temporary path bitAt dirtyAt)
      (Quantum.run (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt))
      (fun s => Clean path s ∧ s temporary = false) := by
  have hf : CoherentlyImplementsOn
      (measuredRangeScan true .dec tree control rangeAccumulator path
        (measuredLowerForwardLeaf k K control temporary bitAt dirtyAt))
      (Quantum.run (rangeScanUnitary true .dec tree control rangeAccumulator path
        (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt)))
      (fun s => Clean path s ∧ s temporary = false) := by
    apply measuredRangeScan_coherent _ _ _ _ _ _ _ _ _ hlayout.decoder (zeroLayout_scan_layout hlayout)
    · intro label
      exact lowerZeroForwardLeaf_HPFree k K control rangeAccumulator temporary bitAt dirtyAt label
    · exact measuredLowerForwardLeaf_preserves k K hkK tree control rangeAccumulator temporary
        path bitAt dirtyAt hlayout
    · intro label _
      exact measuredLowerForwardLeaf_coherent k K hkK tree control rangeAccumulator temporary
        path bitAt dirtyAt hlayout label
  have hr : CoherentlyImplementsOn
      (measuredRangeScan false .inc tree control rangeAccumulator path
        (measuredLowerReverseLeaf k K temporary bitAt dirtyAt))
      (Quantum.run (rangeScanUnitary false .inc tree control rangeAccumulator path
        (lowerZeroReverseLeaf k K temporary bitAt dirtyAt)))
      (fun s => Clean path s ∧ s temporary = false) := by
    apply measuredRangeScan_coherent _ _ _ _ _ _ _ _ _ hlayout.decoder (zeroLayout_scan_layout hlayout)
    · intro label
      exact lowerZeroReverseLeaf_HPFree k K rangeAccumulator temporary bitAt dirtyAt label
    · exact measuredLowerReverseLeaf_preserves k K hkK tree control rangeAccumulator temporary
        path bitAt dirtyAt hlayout
    · intro label _
      exact measuredLowerReverseLeaf_coherent k K hkK tree control rangeAccumulator temporary
        path bitAt dirtyAt hlayout label
  apply coherent_seq_classical hf hr
  · simp only [rangeScanUnitary, ↓reduceIte]
    rw [hpFree_append]
    refine ⟨by simp, ?_⟩
    apply unaryActionUnitary_HPFree
    intro label dynamic
    simp [rangeScanLeafAction]
  · intro state hs
    exact lowerZeroForwardScan_scratch k K hkK tree control rangeAccumulator temporary path
      bitAt dirtyAt hlayout state hs.1 hs.2

private theorem measuredUpperForwardLeaf_wellFormed
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) : (measuredUpperForwardLeaf k K control temporary bitAt dirtyAt label rangeAccumulator).WellFormed := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · rw [measuredUpperForwardLeaf, if_pos hwindow]
    have hlabel := (mem_zeroMapLabels hkK).2 (show k ≤ label ∧ label ≤ K by omega)
    by_cases hbase : label = K
    · rw [if_pos hbase]
      exact measuredZeroCell_wellFormed true _ _ _ _ _ (hlayout.cell label hlabel control (Or.inl rfl))
    · rw [if_neg hbase]
      apply measuredZeroCell_wellFormed
      apply hlayout.cell label hlabel (dirtyAt (label + 1))
      exact Or.inr ⟨label + 1, (mem_zeroMapLabels hkK).2 (by omega), by omega, rfl⟩
  · simp [measuredUpperForwardLeaf, hwindow, AdaptiveCircuit.WellFormed]

private theorem measuredUpperReverseLeaf_wellFormed
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) : (measuredUpperReverseLeaf k K temporary bitAt dirtyAt label rangeAccumulator).WellFormed := by
  by_cases hwindow : k ≤ label ∧ label < K
  · rw [measuredUpperReverseLeaf, if_pos hwindow]
    have hlabel := (mem_zeroMapLabels hkK).2 (show k ≤ label ∧ label ≤ K by omega)
    apply measuredZeroCell_wellFormed
    apply hlayout.cell label hlabel (dirtyAt (label + 1))
    exact Or.inr ⟨label + 1, (mem_zeroMapLabels hkK).2 (by omega), by omega, rfl⟩
  · simp [measuredUpperReverseLeaf, hwindow, AdaptiveCircuit.WellFormed]

private theorem measuredLowerForwardLeaf_wellFormed
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) : (measuredLowerForwardLeaf k K control temporary bitAt dirtyAt label rangeAccumulator).WellFormed := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · rw [measuredLowerForwardLeaf, if_pos hwindow]
    have hlabel := (mem_zeroMapLabels hkK).2 (show k ≤ label ∧ label ≤ K by omega)
    by_cases hbase : label = k
    · rw [if_pos hbase]
      exact measuredZeroCell_wellFormed true _ _ _ _ _ (hlayout.cell label hlabel control (Or.inl rfl))
    · rw [if_neg hbase]
      apply measuredZeroCell_wellFormed
      apply hlayout.cell label hlabel (dirtyAt (label - 1))
      exact Or.inr ⟨label - 1, (mem_zeroMapLabels hkK).2 (by omega), by omega, rfl⟩
  · simp [measuredLowerForwardLeaf, hwindow, AdaptiveCircuit.WellFormed]

private theorem measuredLowerReverseLeaf_wellFormed
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) : (measuredLowerReverseLeaf k K temporary bitAt dirtyAt label rangeAccumulator).WellFormed := by
  by_cases hwindow : k < label ∧ label ≤ K
  · rw [measuredLowerReverseLeaf, if_pos hwindow]
    have hlabel := (mem_zeroMapLabels hkK).2 (show k ≤ label ∧ label ≤ K by omega)
    apply measuredZeroCell_wellFormed
    apply hlayout.cell label hlabel (dirtyAt (label - 1))
    exact Or.inr ⟨label - 1, (mem_zeroMapLabels hkK).2 (by omega), by omega, rfl⟩
  · simp [measuredLowerReverseLeaf, hwindow, AdaptiveCircuit.WellFormed]

private theorem measuredRangeScan_wellFormed
    (toggleAfter : Bool) (order : UnaryOrder) (tree : UnaryActionTree)
    (control rangeAccumulator : Wire) (path : List Wire)
    (leaf : Nat → Wire → AdaptiveCircuit) (hlayout : tree.Layout control path)
    (hr : rangeAccumulator ∉ control :: tree.indexWires.dedup ++ path)
    (hl : ∀ label ∈ tree.labels, (leaf label rangeAccumulator).WellFormed) :
    (measuredRangeScan toggleAfter order tree control rangeAccumulator path leaf).WellFormed := by
  have hcx : ∀ dynamic, dynamic ∈ control :: tree.indexWires.dedup ++ path →
      CircuitWellFormed [.CX dynamic rangeAccumulator] := by
    intro dynamic hd
    have hne : dynamic ≠ rangeAccumulator := by intro h; subst dynamic; exact hr hd
    simp [CircuitWellFormed, Gate.WellFormed, hne]
  have hleaf : UnaryAdaptiveLeafWellFormed (measuredRangeLeaf toggleAfter rangeAccumulator leaf)
      tree (control :: tree.indexWires.dedup ++ path) := by
    intro label hh dynamic hd
    cases toggleAfter
    · exact ⟨hcx dynamic hd, hl label hh⟩
    · exact (hl label hh).seq ⟨hcx dynamic hd, trivial⟩
  have hb := unaryAdaptiveAction_wellFormed order
    (measuredRangeLeaf toggleAfter rangeAccumulator leaf) tree control path hlayout hleaf
  cases toggleAfter
  · exact hb.seq ⟨hcx control (by simp), trivial⟩
  · exact ⟨hcx control (by simp), hb⟩

/-- Every gate and every feed-forward branch in the full measured upper map is well formed. -/
theorem measuredUpperZeroMap_wellFormed
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt) :
    (measuredUpperZeroMap k K tree control rangeAccumulator temporary path bitAt dirtyAt).WellFormed := by
  apply AdaptiveCircuit.WellFormed.seq
  · apply measuredRangeScan_wellFormed _ _ _ _ _ _ _ hlayout.decoder hlayout.range_not_protected
    intro label _
    exact measuredUpperForwardLeaf_wellFormed k K hkK tree control rangeAccumulator temporary path
      bitAt dirtyAt hlayout label
  · apply measuredRangeScan_wellFormed _ _ _ _ _ _ _ hlayout.decoder hlayout.range_not_protected
    intro label _
    exact measuredUpperReverseLeaf_wellFormed k K hkK tree control rangeAccumulator temporary path
      bitAt dirtyAt hlayout label

/-- Every gate and every feed-forward branch in the full measured lower map is well formed. -/
theorem measuredLowerZeroMap_wellFormed
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt) :
    (measuredLowerZeroMap k K tree control rangeAccumulator temporary path bitAt dirtyAt).WellFormed := by
  apply AdaptiveCircuit.WellFormed.seq
  · apply measuredRangeScan_wellFormed _ _ _ _ _ _ _ hlayout.decoder hlayout.range_not_protected
    intro label _
    exact measuredLowerForwardLeaf_wellFormed k K hkK tree control rangeAccumulator temporary path
      bitAt dirtyAt hlayout label
  · apply measuredRangeScan_wellFormed _ _ _ _ _ _ _ hlayout.decoder hlayout.range_not_protected
    intro label _
    exact measuredLowerReverseLeaf_wellFormed k K hkK tree control rangeAccumulator temporary path
      bitAt dirtyAt hlayout label

end
end ShorECDLP.Paper2607_13816
