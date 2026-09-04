import ShorECDLP.Submission.«2607_13816».EEA.TreeBuilder
import ShorECDLP.Submission.«2607_13816».EEA.WordNat
import Mathlib.Data.List.GetD

/-!
# Location-controlled quotient/sign swap

This module implements the pinned supplement's Figure-9 / Algorithm-3
`lc_swap_unary_gate`.  The stored truth-minus-one length words are temporarily transformed by

`l_q := l_q + l_t; l_q := l_q + 3`,

the source-built increasing unary traversal swaps `Sign` with the selected `Work1` lane, and the
two affine updates are then undone in reverse order.  The coherent reference and its
measurement-uncomputed realization share the same source block order.
-/

namespace ShorECDLP.Paper2607_13816

open Classical Quantum

noncomputable section

/-! ## Source labels and tree -/

/-- Inclusive source labels `k, ..., K`. -/
def quotientSwapLabels (k K : Nat) : List Nat :=
  List.range' k (K + 1 - k)

private theorem quotientSwapLabels_nonempty {k K : Nat} (hkK : k ≤ K) :
    quotientSwapLabels k K ≠ [] := by
  simp [quotientSwapLabels]
  omega

private theorem mem_quotientSwapLabels {k K label : Nat} :
    label ∈ quotientSwapLabels k K ↔ k ≤ label ∧ label ≤ K := by
  simp [quotientSwapLabels]
  omega

/-- Python's `unary_depth(K-k+1)`, used only to size the source scratch prefix. -/
def quotientSwapUnaryDepth (k K : Nat) : Nat :=
  let count := K - k + 1
  if count ≤ 1 then 0 else Nat.clog 2 (count - 1) + 1

private def quotientProjectA : DualUnaryActionTree → UnaryActionTree
  | .leaf label => .leaf label
  | .node indexBitA _ zero one =>
      .node indexBitA (quotientProjectA zero) (quotientProjectA one)

@[simp]
private theorem quotientProjectA_labels (tree : DualUnaryActionTree) :
    (quotientProjectA tree).labels = tree.labels := by
  induction tree with
  | leaf => rfl
  | node indexBitA indexBitB zero one ihZero ihOne =>
      simp [quotientProjectA, UnaryActionTree.labels,
        DualUnaryActionTree.labels, ihZero, ihOne]

@[simp]
private theorem quotientProjectA_indexWires (tree : DualUnaryActionTree) :
    (quotientProjectA tree).indexWires = tree.indexAWires := by
  induction tree with
  | leaf => rfl
  | node indexBitA indexBitB zero one ihZero ihOne =>
      simp [quotientProjectA, UnaryActionTree.indexWires,
        DualUnaryActionTree.indexAWires, ihZero, ihOne]

@[simp]
private theorem quotientProjectA_internalNodes (tree : DualUnaryActionTree) :
    (quotientProjectA tree).internalNodes = tree.internalNodes := by
  induction tree with
  | leaf => rfl
  | node indexBitA indexBitB zero one ihZero ihOne =>
      simp [quotientProjectA, UnaryActionTree.internalNodes,
        DualUnaryActionTree.internalNodes, ihZero, ihOne]

@[simp]
private theorem quotientProjectA_leaves (tree : DualUnaryActionTree) :
    (quotientProjectA tree).leaves = tree.leaves := by
  induction tree with
  | leaf => rfl
  | node indexBitA indexBitB zero one ihZero ihOne =>
      simp [quotientProjectA, UnaryActionTree.leaves,
        DualUnaryActionTree.leaves, ihZero, ihOne]

private theorem testBit_of_aligned_block
    {value base depth : Nat}
    (hbase : base % 2 ^ (depth + 1) = 0)
    (hlow : base ≤ value)
    (hhigh : value < base + 2 ^ (depth + 1)) :
    value.testBit depth = decide (base + 2 ^ depth ≤ value) := by
  have hoffset : value - base < 2 ^ (depth + 1) := by omega
  have hmod : value % 2 ^ (depth + 1) = value - base := by
    calc
      value % 2 ^ (depth + 1) =
          ((value - base) + base) % 2 ^ (depth + 1) := by
            rw [Nat.sub_add_cancel hlow]
      _ = ((value - base) % 2 ^ (depth + 1) +
          base % 2 ^ (depth + 1)) % 2 ^ (depth + 1) := by
            rw [Nat.add_mod]
      _ = (value - base) % 2 ^ (depth + 1) := by rw [hbase]; simp
      _ = value - base := Nat.mod_eq_of_lt hoffset
  have htest : (value % 2 ^ (depth + 1)).testBit depth =
      value.testBit depth := by
    rw [Nat.testBit_mod_two_pow]
    simp
  rw [hmod] at htest
  rw [← htest]
  by_cases hright : base + 2 ^ depth ≤ value
  · have hdiv : (value - base) / 2 ^ depth = 1 := by
      apply Nat.div_eq_of_lt_le
      · omega
      · rw [Nat.pow_succ] at hhigh
        omega
    simp [hright, Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
  · have hlt : value - base < 2 ^ depth := by omega
    rw [Nat.testBit_lt_two_pow hlt]
    simp [hright]

private theorem getD_false_eq_testBit_boolWordToNat
    (bits : List Bool) {bit : Nat} (hbit : bit < bits.length) :
    bits.getD bit false = (boolWordToNat bits).testBit bit := by
  induction bits generalizing bit with
  | nil => simp at hbit
  | cons head tail ih =>
      cases bit with
      | zero =>
          rw [List.getD_cons_zero]
          rw [show boolWordToNat (head :: tail) =
              Nat.bit head (boolWordToNat tail) by
            cases head
            · simp [boolWordToNat, Nat.bit]
            · simp [boolWordToNat, Nat.bit]
              omega]
          exact Nat.testBit_bit_zero head (boolWordToNat tail) |>.symm
      | succ bit =>
          rw [List.getD_cons_succ]
          rw [show boolWordToNat (head :: tail) =
              Nat.bit head (boolWordToNat tail) by
            cases head
            · simp [boolWordToNat, Nat.bit]
            · simp [boolWordToNat, Nat.bit]
              omega]
          rw [Nat.testBit_bit_succ]
          apply ih
          simpa using hbit

private theorem sourceBuilt_label_bounds
    {indexA indexB : Nat → Wire} {labels : Finset Nat}
    {depth base : Nat} {tree : DualUnaryActionTree}
    (hbuilt : DualUnaryActionTree.SourceBuilt indexA indexB labels depth base tree) :
    ∀ {label}, label ∈ tree.labels →
      base ≤ label ∧ label < base + 2 ^ depth := by
  induction hbuilt with
  | leaf base hbase =>
      intro label hlabel
      simp [DualUnaryActionTree.labels] at hlabel
      subst label
      simp
  | onlyZero depth base zero hzero hone ih =>
      intro label hlabel
      have hb := ih hlabel
      rw [Nat.pow_succ]
      omega
  | onlyOne depth base one hzero hone ih =>
      intro label hlabel
      have hb := ih hlabel
      rw [Nat.pow_succ]
      omega
  | node depth base zero one hzero hone ihZero ihOne =>
      intro label hlabel
      simp only [DualUnaryActionTree.labels, List.mem_append] at hlabel
      rcases hlabel with hlabel | hlabel
      · have hb := ihZero hlabel
        rw [Nat.pow_succ]
        omega
      · have hb := ihOne hlabel
        rw [Nat.pow_succ]
        omega

private theorem aligned_zero_child
    {base depth : Nat} (hbase : base % 2 ^ (depth + 1) = 0) :
    base % 2 ^ depth = 0 := by
  apply Nat.mod_eq_zero_of_dvd
  exact dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_succ depth))
    (Nat.dvd_of_mod_eq_zero hbase)

private theorem aligned_one_child
    {base depth : Nat} (hbase : base % 2 ^ (depth + 1) = 0) :
    (base + 2 ^ depth) % 2 ^ depth = 0 := by
  rw [Nat.add_mod, aligned_zero_child hbase]
  simp

private theorem quotientProjectA_routeLabel_of_sourceBuilt
    {indexA indexB : Nat → Wire} {labels : Finset Nat}
    {depth base : Nat} {tree : DualUnaryActionTree}
    (hbuilt : DualUnaryActionTree.SourceBuilt indexA indexB labels depth base tree)
    (hbase : base % 2 ^ depth = 0)
    (state : BasisState) {label : Nat} (hlabel : label ∈ tree.labels)
    (hstate : ∀ bit, bit < depth →
      state (indexA bit) = label.testBit bit) :
    (quotientProjectA tree).routeLabel state = label := by
  induction hbuilt with
  | leaf base hbaseMem =>
      simp only [DualUnaryActionTree.labels, List.mem_singleton] at hlabel
      subst label
      rfl
  | onlyZero depth base zero hzero hone ih =>
      apply ih (aligned_zero_child hbase) hlabel
      intro bit hbit
      exact hstate bit (Nat.lt_succ_of_lt hbit)
  | onlyOne depth base one hzero hone ih =>
      apply ih (aligned_one_child hbase) hlabel
      intro bit hbit
      exact hstate bit (Nat.lt_succ_of_lt hbit)
  | node depth base zero one hzero hone ihZero ihOne =>
      simp only [DualUnaryActionTree.labels, List.mem_append] at hlabel
      rcases hlabel with hlabel | hlabel
      · have hb := sourceBuilt_label_bounds hzero hlabel
        have hbit : label.testBit depth = false := by
          rw [testBit_of_aligned_block hbase hb.1 (by
            rw [Nat.pow_succ]
            omega)]
          simp only [decide_eq_false_iff_not]
          omega
        have hroute : state (indexA depth) = false := by
          rw [hstate depth (Nat.lt_succ_self depth), hbit]
        simp only [quotientProjectA, UnaryActionTree.routeLabel, hroute,
          Bool.false_eq_true, if_false]
        apply ihZero (aligned_zero_child hbase) hlabel
        intro bit hbit
        exact hstate bit (Nat.lt_succ_of_lt hbit)
      · have hb := sourceBuilt_label_bounds hone hlabel
        have hbit : label.testBit depth = true := by
          rw [testBit_of_aligned_block hbase (by omega) (by
            rw [Nat.pow_succ]
            omega)]
          simp only [decide_eq_true_eq]
          exact hb.1
        have hroute : state (indexA depth) = true := by
          rw [hstate depth (Nat.lt_succ_self depth), hbit]
        simp only [quotientProjectA, UnaryActionTree.routeLabel, hroute, if_true]
        apply ihOne (aligned_one_child hbase) hlabel
        intro bit hbit
        exact hstate bit (Nat.lt_succ_of_lt hbit)

/-! ## Physical registers -/

/-- Physical registers of one `lc_swap_unary_gate` instance. -/
structure QuotientSwapRegisters where
  control : Wire
  sign : Wire
  work1 : List Wire
  lengthT : List Wire
  lengthQ : List Wire
  scratch : List Wire
deriving Repr

def QuotientSwapRegisters.index
    (registers : QuotientSwapRegisters) (bit : Nat) : Wire :=
  registers.lengthQ.getD bit 0

private def quotientSwapDualTree
    (registers : QuotientSwapRegisters) (k K : Nat) : DualUnaryActionTree :=
  (DualUnaryActionTree.buildSourceFromList registers.index registers.index
    (quotientSwapLabels k K)).getD (.leaf k)

/-- The exact highest-varying-bit tree built by the pinned unary traversal. -/
def quotientSwapTree
    (registers : QuotientSwapRegisters) (k K : Nat) : UnaryActionTree :=
  quotientProjectA (quotientSwapDualTree registers k K)

def QuotientSwapRegisters.path
    (registers : QuotientSwapRegisters) (k K : Nat) : List Wire :=
  registers.scratch.take (quotientSwapUnaryDepth k K)

def QuotientSwapRegisters.constantScratch
    (registers : QuotientSwapRegisters) : List Wire :=
  registers.scratch.take registers.lengthQ.length

def QuotientSwapRegisters.scratchBase
    (registers : QuotientSwapRegisters) (k K : Nat) : Nat :=
  max registers.lengthQ.length (quotientSwapUnaryDepth k K)

def QuotientSwapRegisters.carry
    (registers : QuotientSwapRegisters) (k K : Nat) : Wire :=
  registers.scratch.getD (registers.scratchBase k K) 0

def QuotientSwapRegisters.workAt
    (registers : QuotientSwapRegisters) (k label : Nat) : Wire :=
  registers.work1.getD (label - k) (registers.work1.getD 0 0)

def QuotientSwapRegisters.allWires
    (registers : QuotientSwapRegisters) : List Wire :=
  [registers.control, registers.sign] ++
    (registers.work1 ++
      (registers.lengthT ++ (registers.lengthQ ++ registers.scratch)))

private theorem quotientSwapDualTree_built
    (registers : QuotientSwapRegisters) {k K : Nat} (hkK : k ≤ K) :
    DualUnaryActionTree.buildSourceFromList registers.index registers.index
        (quotientSwapLabels k K) =
      some (quotientSwapDualTree registers k K) := by
  have hnonempty : (quotientSwapLabels k K).toFinset.Nonempty := by
    simpa using quotientSwapLabels_nonempty hkK
  obtain ⟨tree, htree⟩ := DualUnaryActionTree.buildSource_exists
    registers.index registers.index (quotientSwapLabels k K).toFinset hnonempty
  change DualUnaryActionTree.buildSource registers.index registers.index
      (quotientSwapLabels k K).toFinset =
    some ((DualUnaryActionTree.buildSource registers.index registers.index
      (quotientSwapLabels k K).toFinset).getD (.leaf k))
  rw [htree]
  rfl

theorem quotientSwapTree_labels
    (registers : QuotientSwapRegisters) {k K : Nat} (hkK : k ≤ K) :
    (quotientSwapTree registers k K).labels =
      (quotientSwapLabels k K).toFinset.sort (· ≤ ·) := by
  rw [quotientSwapTree, quotientProjectA_labels]
  exact DualUnaryActionTree.buildSource_labels_eq_sort
    registers.index registers.index (quotientSwapLabels k K).toFinset
    (quotientSwapDualTree registers k K) (by
      simpa [DualUnaryActionTree.buildSourceFromList] using
        quotientSwapDualTree_built registers hkK)

private theorem quotientSwapTree_labels_nodup
    (registers : QuotientSwapRegisters) {k K : Nat} (hkK : k ≤ K) :
    (quotientSwapTree registers k K).labels.Nodup := by
  rw [quotientSwapTree_labels registers hkK]
  exact Finset.sort_nodup _ _

private theorem quotientSwapTree_label_bounds
    (registers : QuotientSwapRegisters) {k K label : Nat} (hkK : k ≤ K)
    (hlabel : label ∈ (quotientSwapTree registers k K).labels) :
    k ≤ label ∧ label ≤ K := by
  rw [quotientSwapTree_labels registers hkK] at hlabel
  have : label ∈ quotientSwapLabels k K := by simpa using hlabel
  exact mem_quotientSwapLabels.mp this

/-- Source-level physical contract.  The path-layout field captures the pinned builder's scratch
capacity; all remaining fields are ordinary register widths and global role separation. -/
structure QuotientSwapLayout
    (registers : QuotientSwapRegisters) (k K : Nat) : Prop where
  k_le_K : k ≤ K
  work1_length : registers.work1.length = K - k + 1
  lengthT_eq_lengthQ : registers.lengthT.length = registers.lengthQ.length
  index_width : DualUnaryActionTree.sourceWidth
    (quotientSwapLabels k K).toFinset ≤ registers.lengthQ.length
  scratch_length : registers.scratch.length = registers.scratchBase k K + 1
  physical : registers.allWires.Nodup
  tree : (quotientSwapTree registers k K).Layout registers.control
    (registers.path k K)

/-- Clean shared scratch at the source block boundary. -/
def QuotientSwapReady
    (registers : QuotientSwapRegisters) (state : BasisState) : Prop :=
  Clean registers.scratch state

/-- On an in-range quotient value, the source-built decision tree routes to that exact numeric
label.  This is the semantic bridge from the little-endian `lengthQ` word to the selected
`Work1[label-k]` lane. -/
theorem quotientSwapTree_routeLabel_eq
    (registers : QuotientSwapRegisters) {k K : Nat}
    (state : BasisState) (hlayout : QuotientSwapLayout registers k K)
    (hvalue : boolWordToNat (wireValues registers.lengthQ state) ∈
      quotientSwapLabels k K) :
    (quotientSwapTree registers k K).routeLabel state =
      boolWordToNat (wireValues registers.lengthQ state) := by
  let labels := (quotientSwapLabels k K).toFinset
  let value := boolWordToNat (wireValues registers.lengthQ state)
  have hbuildList := quotientSwapDualTree_built registers hlayout.k_le_K
  have hbuildSource : DualUnaryActionTree.buildSource
      registers.index registers.index labels =
        some (quotientSwapDualTree registers k K) := by
    simpa only [DualUnaryActionTree.buildSourceFromList, labels] using hbuildList
  have hbuild : DualUnaryActionTree.build registers.index registers.index
      (DualUnaryActionTree.sourceWidth labels) labels =
        some (quotientSwapDualTree registers k K) := by
    simpa only [DualUnaryActionTree.buildSource] using hbuildSource
  have hsource := DualUnaryActionTree.build_sourceBuilt
    registers.index registers.index
    (DualUnaryActionTree.sourceWidth labels) labels
    (quotientSwapDualTree registers k K) hbuild
  change (quotientProjectA (quotientSwapDualTree registers k K)).routeLabel state = value
  apply quotientProjectA_routeLabel_of_sourceBuilt hsource (by simp) state
  · have hlabels := DualUnaryActionTree.buildSource_labels_eq_sort
      registers.index registers.index labels
      (quotientSwapDualTree registers k K) hbuildSource
    rw [hlabels]
    simpa only [Finset.mem_sort, List.mem_toFinset, labels, value] using hvalue
  · intro bit hbit
    have hbitQ : bit < registers.lengthQ.length :=
      lt_of_lt_of_le hbit hlayout.index_width
    have hbitValues : bit < (wireValues registers.lengthQ state).length := by
      simpa only [wireValues, List.length_map] using hbitQ
    calc
      state (registers.index bit) =
          state (registers.lengthQ.getD bit 0) := rfl
      _ = (wireValues registers.lengthQ state).getD bit false := by
        rw [List.getD_eq_getElem _ _ hbitQ,
          List.getD_eq_getElem _ _ hbitValues]
        simp only [wireValues, List.getElem_map]
      _ = value.testBit bit :=
        getD_false_eq_testBit_boolWordToNat
          (wireValues registers.lengthQ state) hbitValues

private theorem list_getD_mem
    (list : List α) (index : Nat) (fallback : α)
    (hindex : index < list.length) :
    list.getD index fallback ∈ list := by
  rw [List.getD_eq_getElem list fallback hindex]
  exact List.getElem_mem hindex

private theorem quotientSwap_workAt_mem
    (registers : QuotientSwapRegisters) {k K label : Nat}
    (hlayout : QuotientSwapLayout registers k K)
    (hlabel : label ∈ (quotientSwapTree registers k K).labels) :
    registers.workAt k label ∈ registers.work1 := by
  have hb := quotientSwapTree_label_bounds registers hlayout.k_le_K hlabel
  have hindex : label - k < registers.work1.length := by
    rw [hlayout.work1_length]
    omega
  exact list_getD_mem registers.work1 (label - k)
    (registers.work1.getD 0 0) hindex

private theorem quotientSwap_firstWork_mem
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) :
    registers.work1.getD 0 0 ∈ registers.work1 := by
  have hpositive : 0 < registers.work1.length := by
    rw [hlayout.work1_length]
    omega
  exact list_getD_mem registers.work1 0 0 hpositive

/-- The total Lean definition uses the first work lane as its unreachable out-of-range fallback.
Thus every leaf term is physically meaningful, while source-built reachable labels still select
exactly lane `label-k`. -/
private theorem quotientSwap_workAt_mem_any
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) (label : Nat) :
    registers.workAt k label ∈ registers.work1 := by
  by_cases hindex : label - k < registers.work1.length
  · exact list_getD_mem registers.work1 (label - k)
      (registers.work1.getD 0 0) hindex
  · rw [QuotientSwapRegisters.workAt,
      List.getD_eq_default registers.work1 (registers.work1.getD 0 0)
        (Nat.le_of_not_gt hindex)]
    exact quotientSwap_firstWork_mem registers hlayout

private theorem quotientSwap_path_mem_scratch
    (registers : QuotientSwapRegisters) (k K : Nat) :
    ∀ wire, wire ∈ registers.path k K → wire ∈ registers.scratch := by
  intro wire hwire
  exact List.mem_of_mem_take hwire

private theorem quotientSwapTree_indexWires_mem_lengthQ
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) :
    ∀ wire, wire ∈ (quotientSwapTree registers k K).indexWires →
      wire ∈ registers.lengthQ := by
  intro wire hwire
  rw [quotientSwapTree, quotientProjectA_indexWires] at hwire
  obtain ⟨bit, hbit, rfl⟩ := DualUnaryActionTree.build_indexAWires
    registers.index registers.index
    (DualUnaryActionTree.sourceWidth (quotientSwapLabels k K).toFinset)
    (quotientSwapLabels k K).toFinset
    (quotientSwapDualTree registers k K) (by
      simpa [DualUnaryActionTree.buildSourceFromList,
        DualUnaryActionTree.buildSource] using
          quotientSwapDualTree_built registers hlayout.k_le_K) hwire
  have hindex : bit < registers.lengthQ.length :=
    lt_of_lt_of_le hbit hlayout.index_width
  exact list_getD_mem registers.lengthQ bit 0 hindex

private theorem quotientSwap_decoder_classify
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) :
    ∀ wire,
      wire ∈ registers.control ::
          (quotientSwapTree registers k K).indexWires.dedup ++
            registers.path k K →
      wire = registers.control ∨
        wire ∈ registers.lengthQ ∨ wire ∈ registers.scratch := by
  intro wire hwire
  simp only [List.mem_cons, List.mem_append] at hwire
  rcases hwire with (rfl | hindex) | hpath
  · exact Or.inl rfl
  · exact Or.inr (Or.inl <|
      quotientSwapTree_indexWires_mem_lengthQ registers hlayout wire
        (by simpa using hindex))
  · exact Or.inr (Or.inr <|
      quotientSwap_path_mem_scratch registers k K wire hpath)

private theorem quotientSwap_physical_parts
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) :
    [registers.control, registers.sign].Nodup ∧
      registers.work1.Nodup ∧
      (registers.lengthT ++ (registers.lengthQ ++ registers.scratch)).Nodup ∧
      (∀ fixed ∈ [registers.control, registers.sign],
        ∀ wire ∈ registers.work1 ++
          (registers.lengthT ++ (registers.lengthQ ++ registers.scratch)),
          fixed ≠ wire) ∧
      (∀ work ∈ registers.work1,
        ∀ wire ∈ registers.lengthT ++ (registers.lengthQ ++ registers.scratch),
          work ≠ wire) := by
  have hphysical := hlayout.physical
  rw [QuotientSwapRegisters.allWires] at hphysical
  obtain ⟨hfixed, hrest, hfixedCross⟩ := List.nodup_append.mp hphysical
  obtain ⟨hwork, harithmetic, hworkCross⟩ := List.nodup_append.mp hrest
  exact ⟨hfixed, hwork, harithmetic, hfixedCross, hworkCross⟩

private theorem quotientSwap_carry_mem_scratch
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) :
    registers.carry k K ∈ registers.scratch := by
  apply list_getD_mem registers.scratch (registers.scratchBase k K) 0
  rw [hlayout.scratch_length]
  omega

private theorem quotientSwap_constantScratch_length
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) :
    registers.constantScratch.length = registers.lengthQ.length := by
  simp only [QuotientSwapRegisters.constantScratch, List.length_take]
  rw [Nat.min_eq_left]
  rw [hlayout.scratch_length]
  have hbase :
      registers.lengthQ.length ≤ registers.scratchBase k K := by
    simp [QuotientSwapRegisters.scratchBase]
  exact le_trans hbase (Nat.le_succ _)

private theorem quotientSwap_carry_not_mem_constantScratch
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) :
    registers.carry k K ∉ registers.constantScratch := by
  have harithmetic := (quotientSwap_physical_parts registers hlayout).2.2.1
  have hscratch : registers.scratch.Nodup :=
    (List.nodup_append.mp
      (List.nodup_append.mp harithmetic).2.1).2.1
  have hbase : registers.scratchBase k K < registers.scratch.length := by
    rw [hlayout.scratch_length]
    omega
  intro hmem
  rw [QuotientSwapRegisters.constantScratch,
    List.mem_take_iff_getElem] at hmem
  obtain ⟨index, hindex, heq⟩ := hmem
  have hindexLengthQ : index < registers.lengthQ.length :=
    lt_of_lt_of_le hindex (Nat.min_le_left _ _)
  have hlengthBase :
      registers.lengthQ.length ≤ registers.scratchBase k K := by
    simp [QuotientSwapRegisters.scratchBase]
  have hindexBase : index < registers.scratchBase k K :=
    lt_of_lt_of_le hindexLengthQ hlengthBase
  rw [QuotientSwapRegisters.carry,
    List.getD_eq_getElem registers.scratch 0 hbase] at heq
  have : index = registers.scratchBase k K :=
    (hscratch.getElem_inj_iff).mp heq
  omega

private theorem quotientSwap_cuccaroLayout
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) :
    (registers.carry k K :: registers.lengthT ++ registers.lengthQ).Nodup := by
  have harithmetic := (quotientSwap_physical_parts registers hlayout).2.2.1
  obtain ⟨ht, hqs, htCross⟩ := List.nodup_append.mp harithmetic
  obtain ⟨hq, hs, hqCross⟩ := List.nodup_append.mp hqs
  have hcarry := quotientSwap_carry_mem_scratch registers hlayout
  apply List.nodup_cons.mpr
  constructor
  · intro hmem
    rcases List.mem_append.mp hmem with htMem | hqMem
    · exact htCross (registers.carry k K) htMem
        (registers.carry k K) (by simp [hcarry]) rfl
    · exact hqCross (registers.carry k K) hqMem
        (registers.carry k K) hcarry rfl
  · exact List.nodup_append.mpr ⟨ht, hq, fun left hleft right hright =>
      htCross left hleft right (by simp [hright])⟩

private theorem quotientSwap_constantLayout
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) :
    ConstantLayout registers.lengthQ registers.constantScratch
      (registers.carry k K) := by
  have harithmetic := (quotientSwap_physical_parts registers hlayout).2.2.1
  obtain ⟨ht, hqs, htCross⟩ := List.nodup_append.mp harithmetic
  obtain ⟨hq, hs, hqCross⟩ := List.nodup_append.mp hqs
  have hconstants : registers.constantScratch.Nodup :=
    (List.take_sublist registers.lengthQ.length registers.scratch).nodup hs
  have hcarry := quotientSwap_carry_mem_scratch registers hlayout
  have hcarryNotConstants :=
    quotientSwap_carry_not_mem_constantScratch registers hlayout
  apply List.nodup_cons.mpr
  constructor
  · intro hmem
    rcases List.mem_append.mp hmem with hconstant | hregister
    · exact hcarryNotConstants hconstant
    · exact hqCross (registers.carry k K) hregister
        (registers.carry k K) hcarry rfl
  · apply List.nodup_append.mpr
    exact ⟨hconstants, hq, by
      intro constant hconstant register hregister equality
      exact hqCross register hregister constant
        (List.mem_of_mem_take hconstant) equality.symm⟩

private theorem quotientSwap_sign_ne_workAt
    (registers : QuotientSwapRegisters) {k K label : Nat}
    (hlayout : QuotientSwapLayout registers k K)
    (hlabel : label ∈ (quotientSwapTree registers k K).labels) :
    registers.sign ≠ registers.workAt k label := by
  have htarget := quotientSwap_workAt_mem registers hlayout hlabel
  exact (quotientSwap_physical_parts registers hlayout).2.2.2.1
    registers.sign (by simp) (registers.workAt k label)
      (by simp [htarget])

private theorem quotientSwap_decoder_ne_sign
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) {wire : Wire}
    (hwire : wire ∈ registers.control ::
      (quotientSwapTree registers k K).indexWires.dedup ++
        registers.path k K) :
    wire ≠ registers.sign := by
  rcases quotientSwap_decoder_classify registers hlayout wire hwire with
    rfl | hlength | hscratch
  · simpa using (List.nodup_cons.mp
      (quotientSwap_physical_parts registers hlayout).1).1
  · exact fun equality ↦
      (quotientSwap_physical_parts registers hlayout).2.2.2.1
        registers.sign (by simp) wire (by
          simp [hlength]) equality.symm
  · exact fun equality ↦
      (quotientSwap_physical_parts registers hlayout).2.2.2.1
        registers.sign (by simp) wire (by
          simp [hscratch]) equality.symm

private theorem quotientSwap_decoder_ne_workAt
    (registers : QuotientSwapRegisters) {k K label : Nat}
    (hlayout : QuotientSwapLayout registers k K)
    (hlabel : label ∈ (quotientSwapTree registers k K).labels)
    {wire : Wire}
    (hwire : wire ∈ registers.control ::
      (quotientSwapTree registers k K).indexWires.dedup ++
        registers.path k K) :
    wire ≠ registers.workAt k label := by
  have htarget := quotientSwap_workAt_mem registers hlayout hlabel
  rcases quotientSwap_decoder_classify registers hlayout wire hwire with
    rfl | hlength | hscratch
  · exact fun equality ↦
      (quotientSwap_physical_parts registers hlayout).2.2.2.1
        registers.control (by simp) (registers.workAt k label)
          (by simp [htarget]) equality
  · exact fun equality ↦
      (quotientSwap_physical_parts registers hlayout).2.2.2.2
        (registers.workAt k label) htarget wire (by
          simp [hlength]) equality.symm
  · exact fun equality ↦
      (quotientSwap_physical_parts registers hlayout).2.2.2.2
        (registers.workAt k label) htarget wire (by
          simp [hscratch]) equality.symm

private theorem quotientSwap_decoder_ne_workAt_any
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) (label : Nat)
    {wire : Wire}
    (hwire : wire ∈ registers.control ::
      (quotientSwapTree registers k K).indexWires.dedup ++
        registers.path k K) :
    wire ≠ registers.workAt k label := by
  have htarget := quotientSwap_workAt_mem_any registers hlayout label
  rcases quotientSwap_decoder_classify registers hlayout wire hwire with
    rfl | hlength | hscratch
  · exact fun equality ↦
      (quotientSwap_physical_parts registers hlayout).2.2.2.1
        registers.control (by simp) (registers.workAt k label)
          (by simp [htarget]) equality
  · exact fun equality ↦
      (quotientSwap_physical_parts registers hlayout).2.2.2.2
        (registers.workAt k label) htarget wire (by
          simp [hlength]) equality.symm
  · exact fun equality ↦
      (quotientSwap_physical_parts registers hlayout).2.2.2.2
        (registers.workAt k label) htarget wire (by
          simp [hscratch]) equality.symm

private theorem quotientSwap_sign_ne_workAt_any
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) (label : Nat) :
    registers.sign ≠ registers.workAt k label := by
  have htarget := quotientSwap_workAt_mem_any registers hlayout label
  exact (quotientSwap_physical_parts registers hlayout).2.2.2.1
    registers.sign (by simp) (registers.workAt k label) (by simp [htarget])

/-! ## Circuit and direct state action -/

def quotientSwapLeaf
    (registers : QuotientSwapRegisters) (k label : Nat)
    (equality : Wire) : Circuit :=
  controlledSwap equality registers.sign (registers.workAt k label)

def quotientSwapState
    (registers : QuotientSwapRegisters) (k label : Nat)
    (enabled : Bool) (state : BasisState) : BasisState :=
  if enabled then
    state[registers.sign ↦ state (registers.workAt k label)]
      [registers.workAt k label ↦ state registers.sign]
  else state

@[simp]
private theorem quotientSwapState_false
    (registers : QuotientSwapRegisters) (k label : Nat)
    (state : BasisState) :
    quotientSwapState registers k label false state = state := rfl

private theorem foldl_quotientSwapState_not_mem
    (registers : QuotientSwapRegisters) (k route : Nat)
    (labels : List Nat) (state : BasisState)
    (hroute : route ∉ labels) :
    (labels.map fun label => (label, decide (label = route))).foldl
        (fun current pulse =>
          quotientSwapState registers k pulse.1 pulse.2 current) state = state := by
  induction labels generalizing state with
  | nil => rfl
  | cons label labels ih =>
      simp only [List.mem_cons, not_or] at hroute
      have hlabel : label ≠ route := fun equality => hroute.1 equality.symm
      simp only [List.map_cons, List.foldl_cons, hlabel, decide_false,
        quotientSwapState_false]
      exact ih state hroute.2

private theorem foldl_quotientSwapState_false
    (registers : QuotientSwapRegisters) (k : Nat)
    (labels : List Nat) (state : BasisState) :
    (labels.map fun label => (label, false)).foldl
        (fun current pulse =>
          quotientSwapState registers k pulse.1 pulse.2 current) state = state := by
  induction labels generalizing state with
  | nil => rfl
  | cons label labels ih =>
      simp only [List.map_cons, List.foldl_cons, quotientSwapState_false]
      exact ih state

/-- A duplicate-free unary pulse trace applies the quotient/sign swap exactly at its selected
label and nowhere else. -/
private theorem foldl_quotientSwapState_selected
    (registers : QuotientSwapRegisters) (k route : Nat)
    (labels : List Nat) (active : Bool) (state : BasisState)
    (hnodup : labels.Nodup) (hroute : route ∈ labels) :
    (labels.map fun label =>
        (label, active && decide (label = route))).foldl
        (fun current pulse =>
          quotientSwapState registers k pulse.1 pulse.2 current) state =
      quotientSwapState registers k route active state := by
  cases active with
  | false =>
      exact foldl_quotientSwapState_false registers k labels state
  | true =>
      induction labels generalizing state with
      | nil => simp at hroute
      | cons label labels ih =>
          simp only [List.nodup_cons] at hnodup
          obtain ⟨hlabel, hlabels⟩ := hnodup
          simp only [List.mem_cons] at hroute
          by_cases heq : label = route
          · subst label
            simp only [decide_true, Bool.true_and, List.map_cons, List.foldl_cons]
            exact foldl_quotientSwapState_not_mem registers k route labels
              (quotientSwapState registers k route true state) hlabel
          · have htail : route ∈ labels := hroute.resolve_left (Ne.symm heq)
            simp only [heq, decide_false, Bool.and_false,
              List.map_cons, List.foldl_cons, quotientSwapState_false]
            exact ih state hlabels htail

private theorem quotientSwapLeaf_preserves
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) :
    UnaryLeafPreserves (quotientSwapLeaf registers k)
      (registers.control ::
        (quotientSwapTree registers k K).indexWires.dedup ++
          registers.path k K) := by
  intro label equality hequality state wire hwire
  have heqSign : equality ≠ registers.sign :=
    quotientSwap_decoder_ne_sign registers hlayout hequality
  have heqWork : equality ≠ registers.workAt k label :=
    quotientSwap_decoder_ne_workAt_any registers hlayout label hequality
  have hsignWork : registers.sign ≠ registers.workAt k label :=
    quotientSwap_sign_ne_workAt_any registers hlayout label
  have hwireSign : wire ≠ registers.sign :=
    quotientSwap_decoder_ne_sign registers hlayout hwire
  have hwireWork : wire ≠ registers.workAt k label :=
    quotientSwap_decoder_ne_workAt_any registers hlayout label hwire
  rw [quotientSwapLeaf,
    run_controlledSwap equality registers.sign (registers.workAt k label)
      state heqSign heqWork hsignWork]
  cases state equality <;>
    simp [upd, hwireSign, hwireWork]

private theorem quotientSwapLeaf_wellFormed
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) :
    UnaryLeafWellFormed (quotientSwapLeaf registers k)
      (quotientSwapTree registers k K)
      (registers.control ::
        (quotientSwapTree registers k K).indexWires.dedup ++
          registers.path k K) := by
  intro label hlabel equality hequality
  exact controlledSwap_wellFormed equality registers.sign
    (registers.workAt k label)
    (quotientSwap_decoder_ne_sign registers hlayout hequality)
    (quotientSwap_decoder_ne_workAt registers hlayout hlabel hequality)
    (quotientSwap_sign_ne_workAt registers hlayout hlabel)

private theorem quotientSwapLeaf_HPFree
    (registers : QuotientSwapRegisters) (k : Nat) :
    UnaryLeafHPFree (quotientSwapLeaf registers k) := by
  intro label equality
  exact controlledSwap_HPFree equality registers.sign
    (registers.workAt k label)

private theorem run_quotientSwapTraversal
    (registers : QuotientSwapRegisters) {k K : Nat}
    (state : BasisState) (hlayout : QuotientSwapLayout registers k K)
    (hclean : Clean (registers.path k K) state) :
    Classical.run
        (unaryActionUnitary .inc (quotientSwapLeaf registers k)
          (quotientSwapTree registers k K) registers.control
          (registers.path k K)) state =
      quotientSwapState registers k
        ((quotientSwapTree registers k K).routeLabel state)
        (state registers.control) state := by
  let protectedWires := registers.control ::
    (quotientSwapTree registers k K).indexWires.dedup ++ registers.path k K
  let physicalLeafState := fun label equality state' =>
    Classical.run (quotientSwapLeaf registers k label equality) state'
  have hruns : UnaryLeafRunsAs
      (quotientSwapLeaf registers k) physicalLeafState := by
    intro label equality state'
    rfl
  have hlogical : UnaryLeafRunsLogically physicalLeafState
      (quotientSwapState registers k) protectedWires := by
    intro label equality hequality state'
    have heqSign : equality ≠ registers.sign :=
      quotientSwap_decoder_ne_sign registers hlayout hequality
    have heqWork : equality ≠ registers.workAt k label :=
      quotientSwap_decoder_ne_workAt_any registers hlayout label hequality
    have hsignWork : registers.sign ≠ registers.workAt k label :=
      quotientSwap_sign_ne_workAt_any registers hlayout label
    simpa only [physicalLeafState, quotientSwapLeaf, quotientSwapState] using
      run_controlledSwap equality registers.sign (registers.workAt k label)
        state' heqSign heqWork hsignWork
  have hleaf : UnaryLeafPreserves
      (quotientSwapLeaf registers k) protectedWires :=
    quotientSwapLeaf_preserves registers hlayout
  have hlogicalPreserves : LogicalLeafPreserves
      (quotientSwapState registers k) protectedWires := by
    intro label active state' wire hwire
    have hwireSign : wire ≠ registers.sign :=
      quotientSwap_decoder_ne_sign registers hlayout hwire
    have hwireWork : wire ≠ registers.workAt k label :=
      quotientSwap_decoder_ne_workAt_any registers hlayout label hwire
    cases active <;> simp [quotientSwapState, upd, hwireSign, hwireWork]
  have hsignOutside : registers.sign ∉ protectedWires := by
    intro hsign
    exact (quotientSwap_decoder_ne_sign registers hlayout hsign) rfl
  have hlogicalOutside : LogicalLeafRespectsOutside
      (quotientSwapState registers k) protectedWires registers.control := by
    intro label active left right houtside _
    have hworkOutside : registers.workAt k label ∉ protectedWires := by
      intro hwork
      exact (quotientSwap_decoder_ne_workAt_any registers hlayout label hwork) rfl
    cases active with
    | false => exact houtside
    | true =>
        intro wire hwire
        by_cases hsign : wire = registers.sign
        · subst wire
          simp [quotientSwapState, upd,
            quotientSwap_sign_ne_workAt_any registers hlayout label,
            houtside (registers.workAt k label) hworkOutside]
        · by_cases hwork : wire = registers.workAt k label
          · subst wire
            simp [quotientSwapState, upd,
              houtside registers.sign hsignOutside]
          · simp [quotientSwapState, upd, hsign, hwork, houtside wire hwire]
  have htrace := run_unaryActionUnitary_as_runLogicalTree .inc
    (quotientSwapLeaf registers k) physicalLeafState
    (quotientSwapState registers k) (quotientSwapTree registers k K)
    registers.control (registers.path k K) protectedWires state
    hlayout.tree hruns hlogical hleaf hlogicalPreserves hlogicalOutside
    (by intro wire hwire; exact hwire) hclean
  rw [htrace, UnaryActionTree.runLogicalTree_eq_foldl,
    UnaryActionTree.visitPulses_eq_route .inc
      (quotientSwapTree registers k K) (state registers.control) state
      (quotientSwapTree_labels_nodup registers hlayout.k_le_K),
    UnaryActionTree.visitLabels_inc]
  exact foldl_quotientSwapState_selected registers k
    ((quotientSwapTree registers k K).routeLabel state)
    (quotientSwapTree registers k K).labels (state registers.control) state
    (quotientSwapTree_labels_nodup registers hlayout.k_le_K)
    ((quotientSwapTree registers k K).routeLabel_mem_labels state)

private theorem run_quotientSwapState_commute
    (support : List Wire) (circuit : Circuit)
    (registers : QuotientSwapRegisters) (k label : Nat)
    (active : Bool) (state : BasisState)
    (huses : PaperCircuitUsesOnly support circuit)
    (hsign : registers.sign ∉ support)
    (hwork : registers.workAt k label ∉ support)
    (hsignWork : registers.sign ≠ registers.workAt k label) :
    Classical.run circuit
        (quotientSwapState registers k label active state) =
      quotientSwapState registers k label active
        (Classical.run circuit state) := by
  cases active with
  | false => rfl
  | true =>
      funext wire
      by_cases hwireSign : wire = registers.sign
      · subst wire
        simp only [quotientSwapState, if_true]
        rw [huses.preservesOutside _ hsign,
          huses.preservesOutside state hwork]
        simp [upd, hsignWork]
      · by_cases hwireWork : wire = registers.workAt k label
        · subst wire
          simp only [quotientSwapState, if_true]
          rw [huses.preservesOutside _ hwork,
            huses.preservesOutside state hsign]
          simp [upd]
        · by_cases hwireSupport : wire ∈ support
          · have hagree : ∀ used, used ∈ support →
                quotientSwapState registers k label true state used = state used := by
              intro used hused
              have husedSign : used ≠ registers.sign := by
                intro equality
                subst used
                exact hsign hused
              have husedWork : used ≠ registers.workAt k label := by
                intro equality
                subst used
                exact hwork hused
              simp [quotientSwapState, upd, husedSign, husedWork]
            simpa [quotientSwapState, upd, hwireSign, hwireWork] using
              huses.run_congrOn
                (quotientSwapState registers k label true state) state
                hagree wire hwireSupport
          · have hleft := huses.preservesOutside
              (quotientSwapState registers k label true state) hwireSupport
            have hright := huses.preservesOutside state hwireSupport
            rw [hleft]
            simpa [quotientSwapState, upd, hwireSign, hwireWork] using hright.symm

/-- Literal coherent source stream. -/
def quotientSwapUnitary
    (registers : QuotientSwapRegisters) (k K : Nat) : Circuit :=
  cuccaroAdd registers.lengthT registers.lengthQ (registers.carry k K) ++
    addConstant registers.lengthQ registers.constantScratch
      (registers.carry k K) 3 ++
    unaryActionUnitary .inc (quotientSwapLeaf registers k)
      (quotientSwapTree registers k K) registers.control (registers.path k K) ++
    subConstant registers.lengthQ registers.constantScratch
      (registers.carry k K) 3 ++
    cuccaroSub registers.lengthT registers.lengthQ (registers.carry k K)

/-- Direct Figure-9 semantics.  The theorem exposes both the exact source-selected lane and the
prepared quotient word which drives that selection; the affine prefix and suffix are restored in
the returned whole state. -/
theorem quotientSwapUnitary_correct
    (registers : QuotientSwapRegisters) {k K : Nat}
    (state : BasisState) (hlayout : QuotientSwapLayout registers k K)
    (hready : QuotientSwapReady registers state) :
    let afterAdd := Classical.run
      (cuccaroAdd registers.lengthT registers.lengthQ
        (registers.carry k K)) state
    let prepared := Classical.run
      (addConstant registers.lengthQ registers.constantScratch
        (registers.carry k K) 3) afterAdd
    let selected := (quotientSwapTree registers k K).routeLabel prepared
    Classical.run (quotientSwapUnitary registers k K) state =
        quotientSwapState registers k selected
          (state registers.control) state ∧
      Clean registers.scratch prepared ∧
      wireValues registers.lengthQ prepared =
        cuccaroAddBits false
          (constantBits registers.constantScratch.length 3)
          (cuccaroAddBits false (wireValues registers.lengthT state)
            (wireValues registers.lengthQ state)) ∧
      k ≤ selected ∧ selected ≤ K := by
  let afterAdd := Classical.run
    (cuccaroAdd registers.lengthT registers.lengthQ
      (registers.carry k K)) state
  let prepared := Classical.run
    (addConstant registers.lengthQ registers.constantScratch
      (registers.carry k K) 3) afterAdd
  let selected := (quotientSwapTree registers k K).routeLabel prepared
  have hcuccaro := quotientSwap_cuccaroLayout registers hlayout
  have hconstant := quotientSwap_constantLayout registers hlayout
  have hconstantLength :=
    quotientSwap_constantScratch_length registers hlayout
  have hcarryFalse : state (registers.carry k K) = false :=
    hready (registers.carry k K)
      (quotientSwap_carry_mem_scratch registers hlayout)
  have hadd := cuccaroAdd_correct registers.lengthT registers.lengthQ
    (registers.carry k K) state hlayout.lengthT_eq_lengthQ hcuccaro
  have hscratchAfterAdd : Clean registers.scratch afterAdd := by
    intro wire hwire
    rw [show afterAdd wire = state wire by
      exact hadd.2.2 wire (by
        intro hlengthQ
        have hqs := (List.nodup_append.mp
          (List.nodup_append.mp
            (quotientSwap_physical_parts registers hlayout).2.2.1).2.1).2.2
        exact hqs wire hlengthQ wire hwire rfl)]
    exact hready wire hwire
  have hconstantClean : Clean
      (registers.constantScratch ++ [registers.carry k K]) afterAdd := by
    intro wire hwire
    rcases List.mem_append.mp hwire with hconstantWire | hcarryWire
    · exact hscratchAfterAdd wire (List.mem_of_mem_take hconstantWire)
    · simp only [List.mem_singleton] at hcarryWire
      subst wire
      exact hscratchAfterAdd (registers.carry k K)
        (quotientSwap_carry_mem_scratch registers hlayout)
  have haddedConstant := addConstant_correct registers.lengthQ
    registers.constantScratch (registers.carry k K) 3 afterAdd
    hconstantLength hconstant hconstantClean
  have hscratchPrepared : Clean registers.scratch prepared := by
    intro wire hwire
    rw [show prepared wire = afterAdd wire by
      exact haddedConstant.2.2 wire (by
        intro hlengthQ
        have hqs := (List.nodup_append.mp
          (List.nodup_append.mp
            (quotientSwap_physical_parts registers hlayout).2.2.1).2.1).2.2
        exact hqs wire hlengthQ wire hwire rfl)]
    exact hscratchAfterAdd wire hwire
  have hpathPrepared : Clean (registers.path k K) prepared := by
    intro wire hwire
    exact hscratchPrepared wire
      (quotientSwap_path_mem_scratch registers k K wire hwire)
  have hcontrolNotQ : registers.control ∉ registers.lengthQ := by
    intro hmem
    exact (quotientSwap_physical_parts registers hlayout).2.2.2.1
      registers.control (by simp) registers.control (by simp [hmem]) rfl
  have hcontrolAfterAdd : afterAdd registers.control = state registers.control :=
    hadd.2.2 registers.control hcontrolNotQ
  have hcontrolPrepared : prepared registers.control = state registers.control := by
    rw [show prepared registers.control = afterAdd registers.control by
      exact haddedConstant.2.2 registers.control hcontrolNotQ,
      hcontrolAfterAdd]
  have htraversal := run_quotientSwapTraversal registers prepared hlayout
    hpathPrepared
  simp only [quotientSwapUnitary, Classical.run_append]
  rw [htraversal]
  rw [← Classical.run_append]
  have hrestoreUses : PaperCircuitUsesOnly
      (registers.lengthT ++ (registers.lengthQ ++ registers.scratch))
      (subConstant registers.lengthQ registers.constantScratch
          (registers.carry k K) 3 ++
        cuccaroSub registers.lengthT registers.lengthQ
          (registers.carry k K)) := by
    apply PaperCircuitUsesOnly.append
    · apply (subConstant_usesOnly registers.lengthQ
        registers.constantScratch (registers.carry k K) 3).mono
      intro wire hwire
      rcases List.mem_append.mp hwire with hprefix | hcarryWire
      · rcases List.mem_append.mp hprefix with hconstantWire | hlengthQ
        · simp [List.mem_of_mem_take hconstantWire]
        · simp [hlengthQ]
      · simp only [List.mem_singleton] at hcarryWire
        subst wire
        simp [quotientSwap_carry_mem_scratch registers hlayout]
    · apply (cuccaroSub_usesOnly registers.lengthT registers.lengthQ
        (registers.carry k K)).mono
      intro wire hwire
      rcases List.mem_cons.mp hwire with rfl | hwire
      · simp [quotientSwap_carry_mem_scratch registers hlayout]
      · rcases List.mem_append.mp hwire with hlengthT | hlengthQ
        · simp [hlengthT]
        · simp [hlengthQ]
  have hsignOutside : registers.sign ∉
      registers.lengthT ++ (registers.lengthQ ++ registers.scratch) := by
    intro hmem
    exact (quotientSwap_physical_parts registers hlayout).2.2.2.1
      registers.sign (by simp) registers.sign (by simp [hmem]) rfl
  have hworkOutside : registers.workAt k selected ∉
      registers.lengthT ++ (registers.lengthQ ++ registers.scratch) := by
    intro hmem
    exact (quotientSwap_physical_parts registers hlayout).2.2.2.2
      (registers.workAt k selected)
      (quotientSwap_workAt_mem_any registers hlayout selected)
      (registers.workAt k selected) hmem rfl
  rw [run_quotientSwapState_commute
    (registers.lengthT ++ (registers.lengthQ ++ registers.scratch)) _
    registers k selected (prepared registers.control) prepared hrestoreUses
    hsignOutside hworkOutside
    (quotientSwap_sign_ne_workAt_any registers hlayout selected)]
  have hrestore : Classical.run
      (subConstant registers.lengthQ registers.constantScratch
          (registers.carry k K) 3 ++
        cuccaroSub registers.lengthT registers.lengthQ
          (registers.carry k K)) prepared = state := by
    simp only [Classical.run_append, prepared, afterAdd]
    rw [run_subConstant_after_add registers.lengthQ
      registers.constantScratch (registers.carry k K) 3 afterAdd
      hconstantLength hconstant,
      run_cuccaroSub_after_add registers.lengthT registers.lengthQ
        (registers.carry k K) state hlayout.lengthT_eq_lengthQ hcuccaro]
  rw [hrestore, hcontrolPrepared]
  constructor
  · rfl
  · constructor
    · exact hscratchPrepared
    · constructor
      · rw [show wireValues registers.lengthQ prepared =
        cuccaroAddBits false
          (constantBits registers.constantScratch.length 3)
          (wireValues registers.lengthQ afterAdd) by
          exact haddedConstant.1]
        rw [show wireValues registers.lengthQ afterAdd =
        cuccaroAddBits false (wireValues registers.lengthT state)
          (wireValues registers.lengthQ state) by
          simpa only [hcarryFalse] using hadd.2.1]
      · exact quotientSwapTree_label_bounds registers hlayout.k_le_K
          ((quotientSwapTree registers k K).routeLabel_mem_labels prepared)

/-- The temporary quotient word is the stored length sum plus the source's `+3`, modulo the
fixed word width.  Since the stored fields are truth-minus-one, this is the source quantity
`J = ell_t + ell_q + 1` used by the unary selector. -/
theorem quotientSwap_prepared_value
    (registers : QuotientSwapRegisters) {k K : Nat}
    (state : BasisState) (hlayout : QuotientSwapLayout registers k K)
    (hready : QuotientSwapReady registers state) :
    let afterAdd := Classical.run
      (cuccaroAdd registers.lengthT registers.lengthQ
        (registers.carry k K)) state
    let prepared := Classical.run
      (addConstant registers.lengthQ registers.constantScratch
        (registers.carry k K) 3) afterAdd
    boolWordToNat (wireValues registers.lengthQ prepared) =
      (boolWordToNat (wireValues registers.lengthT state) +
          boolWordToNat (wireValues registers.lengthQ state) + 3) %
        2 ^ registers.lengthQ.length := by
  let afterAdd := Classical.run
    (cuccaroAdd registers.lengthT registers.lengthQ
      (registers.carry k K)) state
  let prepared := Classical.run
    (addConstant registers.lengthQ registers.constantScratch
      (registers.carry k K) 3) afterAdd
  change boolWordToNat (wireValues registers.lengthQ prepared) =
    (boolWordToNat (wireValues registers.lengthT state) +
        boolWordToNat (wireValues registers.lengthQ state) + 3) %
      2 ^ registers.lengthQ.length
  have hword :=
    (quotientSwapUnitary_correct registers state hlayout hready).2.2.1
  rw [hword]
  have hconstantLength :=
    quotientSwap_constantScratch_length registers hlayout
  rw [boolWordToNat_cuccaroAddBits false _ _ (by
    simp only [constantBits_length, cuccaroAddBits_length,
      wireValues, List.length_map, hconstantLength,
      hlayout.lengthT_eq_lengthQ])]
  rw [boolWordToNat_constantBits]
  rw [boolWordToNat_cuccaroAddBits false _ _ (by
    simp only [wireValues, List.length_map, hlayout.lengthT_eq_lengthQ])]
  simp only [Bool.toNat_false, Nat.zero_add, constantBits_length,
    hconstantLength, wireValues, List.length_map,
    hlayout.lengthT_eq_lengthQ]
  simp only [Nat.add_mod, Nat.mod_mod]
  ac_rfl

/-- Direct in-range source semantics: when the prepared quotient value lies in `k, ..., K`, the
controlled swap uses exactly that numeric value as its `Work1[value-k]` label. -/
theorem quotientSwapUnitary_correct_in_range
    (registers : QuotientSwapRegisters) {k K : Nat}
    (state : BasisState) (hlayout : QuotientSwapLayout registers k K)
    (hready : QuotientSwapReady registers state) :
    let afterAdd := Classical.run
      (cuccaroAdd registers.lengthT registers.lengthQ
        (registers.carry k K)) state
    let prepared := Classical.run
      (addConstant registers.lengthQ registers.constantScratch
        (registers.carry k K) 3) afterAdd
    boolWordToNat (wireValues registers.lengthQ prepared) ∈
        quotientSwapLabels k K →
      Classical.run (quotientSwapUnitary registers k K) state =
        quotientSwapState registers k
          (boolWordToNat (wireValues registers.lengthQ prepared))
          (state registers.control) state := by
  let afterAdd := Classical.run
    (cuccaroAdd registers.lengthT registers.lengthQ
      (registers.carry k K)) state
  let prepared := Classical.run
    (addConstant registers.lengthQ registers.constantScratch
      (registers.carry k K) 3) afterAdd
  change boolWordToNat (wireValues registers.lengthQ prepared) ∈
      quotientSwapLabels k K →
    Classical.run (quotientSwapUnitary registers k K) state =
      quotientSwapState registers k
        (boolWordToNat (wireValues registers.lengthQ prepared))
        (state registers.control) state
  intro hvalue
  have hcorrect := quotientSwapUnitary_correct registers state hlayout hready
  rw [hcorrect.1]
  rw [quotientSwapTree_routeLabel_eq registers prepared hlayout hvalue]

/-- Measurement-uncomputed realization of the same source block. -/
def quotientSwap
    (registers : QuotientSwapRegisters) (k K : Nat) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary
      (cuccaroAdd registers.lengthT registers.lengthQ (registers.carry k K) ++
        addConstant registers.lengthQ registers.constantScratch
          (registers.carry k K) 3) .done).seq
    ((unaryAction .inc (quotientSwapLeaf registers k)
      (quotientSwapTree registers k K) registers.control
      (registers.path k K)).seq
    (AdaptiveCircuit.unitary
      (subConstant registers.lengthQ registers.constantScratch
          (registers.carry k K) 3 ++
        cuccaroSub registers.lengthT registers.lengthQ
          (registers.carry k K)) .done))

/-- The literal coherent source block restores the complete shared scratch bank. -/
theorem quotientSwapUnitary_clean
    (registers : QuotientSwapRegisters) {k K : Nat}
    (state : BasisState) (hlayout : QuotientSwapLayout registers k K)
    (hready : QuotientSwapReady registers state) :
    Clean registers.scratch
      (Classical.run (quotientSwapUnitary registers k K) state) := by
  have hcorrect := quotientSwapUnitary_correct registers state hlayout hready
  rw [hcorrect.1]
  intro wire hwire
  have hwireSign : wire ≠ registers.sign := by
    intro equality
    subst wire
    exact (quotientSwap_physical_parts registers hlayout).2.2.2.1
      registers.sign (by simp) registers.sign (by simp [hwire]) rfl
  have hwireWork : wire ≠ registers.workAt k
      ((quotientSwapTree registers k K).routeLabel
        (Classical.run
          (addConstant registers.lengthQ registers.constantScratch
            (registers.carry k K) 3)
          (Classical.run
            (cuccaroAdd registers.lengthT registers.lengthQ
              (registers.carry k K)) state))) := by
    intro equality
    subst wire
    exact (quotientSwap_physical_parts registers hlayout).2.2.2.2
      (registers.workAt k
        ((quotientSwapTree registers k K).routeLabel
          (Classical.run
            (addConstant registers.lengthQ registers.constantScratch
              (registers.carry k K) 3)
            (Classical.run
              (cuccaroAdd registers.lengthT registers.lengthQ
                (registers.carry k K)) state))))
      (quotientSwap_workAt_mem_any registers hlayout _)
      (registers.workAt k
        ((quotientSwapTree registers k K).routeLabel
          (Classical.run
            (addConstant registers.lengthQ registers.constantScratch
              (registers.carry k K) 3)
            (Classical.run
              (cuccaroAdd registers.lengthT registers.lengthQ
                (registers.carry k K)) state))))
      (List.mem_append_right registers.lengthT
        (List.mem_append_right registers.lengthQ hwire)) rfl
  cases state registers.control <;>
    simp [quotientSwapState, upd, hwireSign, hwireWork, hready wire hwire]

/-- The coherent source block contains no Hadamard or phase gates. -/
@[simp]
theorem quotientSwapUnitary_HPFree
    (registers : QuotientSwapRegisters) (k K : Nat) :
    HPFree (quotientSwapUnitary registers k K) := by
  simp [quotientSwapUnitary,
    unaryActionUnitary_HPFree .inc (quotientSwapLeaf registers k)
      (quotientSwapTree registers k K) registers.control
      (registers.path k K) (quotientSwapLeaf_HPFree registers k)]

/-- Physical well-formedness of the literal coherent source block. -/
theorem quotientSwapUnitary_wellFormed
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) :
    CircuitWellFormed (quotientSwapUnitary registers k K) := by
  have hcuccaro := quotientSwap_cuccaroLayout registers hlayout
  have hconstant := quotientSwap_constantLayout registers hlayout
  have hlength := quotientSwap_constantScratch_length registers hlayout
  have htraversal := unaryActionUnitary_wellFormed .inc
    (quotientSwapLeaf registers k) (quotientSwapTree registers k K)
    registers.control (registers.path k K) hlayout.tree
    (quotientSwapLeaf_wellFormed registers hlayout)
  simp only [quotientSwapUnitary, circuitWellFormed_append]
  exact ⟨⟨⟨⟨
    cuccaroAdd_wellFormed registers.lengthT registers.lengthQ
      (registers.carry k K) hlayout.lengthT_eq_lengthQ hcuccaro,
    addConstant_wellFormed registers.lengthQ registers.constantScratch
      (registers.carry k K) 3 hlength hconstant⟩,
    htraversal⟩,
    subConstant_wellFormed registers.lengthQ registers.constantScratch
      (registers.carry k K) 3 hlength hconstant⟩,
    cuccaroSub_wellFormed registers.lengthT registers.lengthQ
      (registers.carry k K) hlayout.lengthT_eq_lengthQ hcuccaro⟩

/-- Every branch of the measurement-uncomputed source block is physically well formed. -/
theorem quotientSwap_wellFormed
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) :
    (quotientSwap registers k K).WellFormed := by
  have hcuccaro := quotientSwap_cuccaroLayout registers hlayout
  have hconstant := quotientSwap_constantLayout registers hlayout
  have hlength := quotientSwap_constantScratch_length registers hlayout
  have hprepare : CircuitWellFormed
      (cuccaroAdd registers.lengthT registers.lengthQ (registers.carry k K) ++
        addConstant registers.lengthQ registers.constantScratch
          (registers.carry k K) 3) := by
    exact (circuitWellFormed_append _ _).2 ⟨
      cuccaroAdd_wellFormed registers.lengthT registers.lengthQ
        (registers.carry k K) hlayout.lengthT_eq_lengthQ hcuccaro,
      addConstant_wellFormed registers.lengthQ registers.constantScratch
        (registers.carry k K) 3 hlength hconstant⟩
  have htraversal := unaryAction_wellFormed .inc
    (quotientSwapLeaf registers k) (quotientSwapTree registers k K)
    registers.control (registers.path k K) hlayout.tree
    (quotientSwapLeaf_wellFormed registers hlayout)
  have hrestore : CircuitWellFormed
      (subConstant registers.lengthQ registers.constantScratch
          (registers.carry k K) 3 ++
        cuccaroSub registers.lengthT registers.lengthQ
          (registers.carry k K)) := by
    exact (circuitWellFormed_append _ _).2 ⟨
      subConstant_wellFormed registers.lengthQ registers.constantScratch
        (registers.carry k K) 3 hlength hconstant,
      cuccaroSub_wellFormed registers.lengthT registers.lengthQ
        (registers.carry k K) hlayout.lengthT_eq_lengthQ hcuccaro⟩
  rw [quotientSwap]
  exact ⟨hprepare,
    AdaptiveCircuit.WellFormed.seq (by trivial)
      (AdaptiveCircuit.WellFormed.seq htraversal ⟨hrestore, trivial⟩)⟩

private theorem quotientUnaryActionUnitary_usesOnly_of
    (order : UnaryOrder) (leafAction : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire) (path support : List Wire)
    (hcontrol : control ∈ support)
    (hindices : ∀ wire, wire ∈ tree.indexWires → wire ∈ support)
    (hpath : ∀ wire, wire ∈ path → wire ∈ support)
    (hleaf : ∀ label, label ∈ tree.labels → ∀ dynamic,
      dynamic ∈ support →
        PaperCircuitUsesOnly support (leafAction label dynamic)) :
    PaperCircuitUsesOnly support
      (unaryActionUnitary order leafAction tree control path) := by
  induction tree generalizing control path with
  | leaf label =>
      exact hleaf label (by simp [UnaryActionTree.labels]) control hcontrol
  | node indexBit zero one ihZero ihOne =>
      cases path with
      | nil => simp [unaryActionUnitary, PaperCircuitUsesOnly]
      | cons path rest =>
          have hindex : indexBit ∈ support :=
            hindices indexBit (by simp [UnaryActionTree.indexWires])
          have hpathHead : path ∈ support := hpath path (by simp)
          have hrest : ∀ wire, wire ∈ rest → wire ∈ support := by
            intro wire hwire
            exact hpath wire (by simp [hwire])
          have hzeroIndices : ∀ wire, wire ∈ zero.indexWires →
              wire ∈ support := by
            intro wire hwire
            exact hindices wire (by simp [UnaryActionTree.indexWires, hwire])
          have honeIndices : ∀ wire, wire ∈ one.indexWires →
              wire ∈ support := by
            intro wire hwire
            exact hindices wire (by simp [UnaryActionTree.indexWires, hwire])
          have hzeroLeaf : ∀ label, label ∈ zero.labels → ∀ dynamic,
              dynamic ∈ support →
                PaperCircuitUsesOnly support (leafAction label dynamic) := by
            intro label hlabel dynamic hdynamic
            exact hleaf label (by
              simp [UnaryActionTree.labels, hlabel]) dynamic hdynamic
          have honeLeaf : ∀ label, label ∈ one.labels → ∀ dynamic,
              dynamic ∈ support →
                PaperCircuitUsesOnly support (leafAction label dynamic) := by
            intro label hlabel dynamic hdynamic
            exact hleaf label (by
              simp [UnaryActionTree.labels, hlabel]) dynamic hdynamic
          have hzero := ihZero path rest hpathHead hzeroIndices hrest hzeroLeaf
          have hone := ihOne path rest hpathHead honeIndices hrest honeLeaf
          have hcompute : PaperCircuitUsesOnly support
              (computeZeroAnd control indexBit path) := by
            simp [computeZeroAnd, PaperCircuitUsesOnly, PaperGateUsesOnly,
              gateWires, hcontrol, hindex, hpathHead]
          have htoggle : PaperCircuitUsesOnly support
              ([.CX control path] : Circuit) := by
            simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires,
              hcontrol, hpathHead]
          cases order with
          | inc =>
              rw [unaryActionUnitary]
              have hempty : PaperCircuitUsesOnly support ([] : Circuit) := by
                simp [PaperCircuitUsesOnly]
              exact hcompute.append
                (((((hempty.append hzero).append htoggle).append hone).append
                  htoggle).append hcompute)
          | dec =>
              rw [unaryActionUnitary]
              have hempty : PaperCircuitUsesOnly support ([] : Circuit) := by
                simp [PaperCircuitUsesOnly]
              exact hcompute.append
                (((((hempty.append htoggle).append hone).append htoggle).append
                  hzero).append hcompute)

/-- Every gate in the literal coherent block stays within the declared physical registers. -/
theorem quotientSwapUnitary_usesOnly
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) :
    PaperCircuitUsesOnly registers.allWires
      (quotientSwapUnitary registers k K) := by
  have hcarry := quotientSwap_carry_mem_scratch registers hlayout
  have hadd : PaperCircuitUsesOnly registers.allWires
      (cuccaroAdd registers.lengthT registers.lengthQ
        (registers.carry k K)) :=
    (cuccaroAdd_usesOnly registers.lengthT registers.lengthQ
      (registers.carry k K)).mono (by
      intro wire hwire
      simp only [List.mem_cons, List.mem_append] at hwire
      rcases hwire with (rfl | hlengthT) | hlengthQ
      · simp [QuotientSwapRegisters.allWires, hcarry]
      · simp [QuotientSwapRegisters.allWires, hlengthT]
      · simp [QuotientSwapRegisters.allWires, hlengthQ])
  have haddConstant : PaperCircuitUsesOnly registers.allWires
      (addConstant registers.lengthQ registers.constantScratch
        (registers.carry k K) 3) :=
    (addConstant_usesOnly registers.lengthQ
      registers.constantScratch (registers.carry k K) 3).mono (by
      intro wire hwire
      rcases List.mem_append.mp hwire with hprefix | hcarryWire
      · rcases List.mem_append.mp hprefix with hconstant | hlengthQ
        · simp [QuotientSwapRegisters.allWires,
            List.mem_of_mem_take hconstant]
        · simp [QuotientSwapRegisters.allWires, hlengthQ]
      · simp only [List.mem_singleton] at hcarryWire
        subst wire
        simp [QuotientSwapRegisters.allWires, hcarry])
  have htraversal : PaperCircuitUsesOnly registers.allWires
      (unaryActionUnitary .inc (quotientSwapLeaf registers k)
        (quotientSwapTree registers k K) registers.control
        (registers.path k K)) := by
    apply quotientUnaryActionUnitary_usesOnly_of
    · simp [QuotientSwapRegisters.allWires]
    · intro wire hwire
      have hlengthQ := quotientSwapTree_indexWires_mem_lengthQ
        registers hlayout wire hwire
      simp [QuotientSwapRegisters.allWires, hlengthQ]
    · intro wire hwire
      have hscratch := quotientSwap_path_mem_scratch registers k K wire hwire
      simp [QuotientSwapRegisters.allWires, hscratch]
    · intro label hlabel dynamic hdynamic
      apply (controlledSwap_usesOnly dynamic registers.sign
        (registers.workAt k label)).mono
      intro wire hwire
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
      rcases hwire with rfl | rfl | rfl
      · exact hdynamic
      · simp [QuotientSwapRegisters.allWires]
      · have hwork := quotientSwap_workAt_mem registers hlayout hlabel
        simp [QuotientSwapRegisters.allWires, hwork]
  have hsubConstant : PaperCircuitUsesOnly registers.allWires
      (subConstant registers.lengthQ registers.constantScratch
        (registers.carry k K) 3) :=
    (subConstant_usesOnly registers.lengthQ
      registers.constantScratch (registers.carry k K) 3).mono (by
      intro wire hwire
      rcases List.mem_append.mp hwire with hprefix | hcarryWire
      · rcases List.mem_append.mp hprefix with hconstant | hlengthQ
        · simp [QuotientSwapRegisters.allWires,
            List.mem_of_mem_take hconstant]
        · simp [QuotientSwapRegisters.allWires, hlengthQ]
      · simp only [List.mem_singleton] at hcarryWire
        subst wire
        simp [QuotientSwapRegisters.allWires, hcarry])
  have hsub : PaperCircuitUsesOnly registers.allWires
      (cuccaroSub registers.lengthT registers.lengthQ
        (registers.carry k K)) :=
    (cuccaroSub_usesOnly registers.lengthT registers.lengthQ
      (registers.carry k K)).mono (by
      intro wire hwire
      simp only [List.mem_cons, List.mem_append] at hwire
      rcases hwire with (rfl | hlengthT) | hlengthQ
      · simp [QuotientSwapRegisters.allWires, hcarry]
      · simp [QuotientSwapRegisters.allWires, hlengthT]
      · simp [QuotientSwapRegisters.allWires, hlengthQ])
  rw [quotientSwapUnitary]
  exact (((hadd.append haddConstant).append htraversal).append
    hsubConstant).append hsub

/-- Whole-state locality outside the declared physical register union. -/
theorem quotientSwapUnitary_preservesOutside
    (registers : QuotientSwapRegisters) {k K : Nat}
    (state : BasisState) (hlayout : QuotientSwapLayout registers k K)
    {wire : Wire} (hwire : wire ∉ registers.allWires) :
    Classical.run (quotientSwapUnitary registers k K) state wire = state wire :=
  (quotientSwapUnitary_usesOnly registers hlayout).preservesOutside state hwire

private theorem quotientSwap_coherent_seq_circuits
    {first second : AdaptiveCircuit}
    {firstCircuit secondCircuit : Circuit}
    {FirstValid SecondValid : BasisState → Prop}
    (hfirst : CoherentlyImplementsOn first
      (Quantum.run firstCircuit) FirstValid)
    (hsecond : CoherentlyImplementsOn second
      (Quantum.run secondCircuit) SecondValid)
    (hfirstClassical : HPFree firstCircuit)
    (hvalid : ∀ state, FirstValid state →
      SecondValid (Classical.run firstCircuit state)) :
    CoherentlyImplementsOn (first.seq second)
      (Quantum.run (firstCircuit ++ secondCircuit)) FirstValid := by
  have hseq := hfirst.seq hsecond (by
    intro state hstate
    rw [Quantum.run_ket_agrees_classical firstCircuit state hfirstClassical]
    exact Quantum.supportedOn_ket SecondValid _ (hvalid state hstate))
  apply hseq.congrIdeal
  intro state _
  exact (Quantum.run_append firstCircuit secondCircuit
    (Quantum.ket state)).symm

/-- Measurement-uncomputation coherently refines the literal Figure-9 unitary on every clean
source-boundary input. -/
theorem quotientSwap_coherent
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) :
    CoherentlyImplementsOn (quotientSwap registers k K)
      (Quantum.run (quotientSwapUnitary registers k K))
      (QuotientSwapReady registers) := by
  let prepare :=
    cuccaroAdd registers.lengthT registers.lengthQ (registers.carry k K) ++
      addConstant registers.lengthQ registers.constantScratch
        (registers.carry k K) 3
  let traversal := unaryActionUnitary .inc (quotientSwapLeaf registers k)
    (quotientSwapTree registers k K) registers.control (registers.path k K)
  let adaptiveTraversal := unaryAction .inc (quotientSwapLeaf registers k)
    (quotientSwapTree registers k K) registers.control (registers.path k K)
  let restore :=
    subConstant registers.lengthQ registers.constantScratch
        (registers.carry k K) 3 ++
      cuccaroSub registers.lengthT registers.lengthQ (registers.carry k K)
  have htraversal : CoherentlyImplementsOn adaptiveTraversal
      (Quantum.run traversal) (Clean (registers.path k K)) := by
    exact unaryAction_coherent .inc (quotientSwapLeaf registers k)
      (quotientSwapTree registers k K) registers.control
      (registers.path k K) hlayout.tree
      (quotientSwapLeaf_preserves registers hlayout)
      (quotientSwapLeaf_HPFree registers k)
  have htraversalHPFree : HPFree traversal := by
    exact unaryActionUnitary_HPFree .inc (quotientSwapLeaf registers k)
      (quotientSwapTree registers k K) registers.control
      (registers.path k K) (quotientSwapLeaf_HPFree registers k)
  have hmiddle : CoherentlyImplementsOn
      (adaptiveTraversal.seq (AdaptiveCircuit.unitary restore .done))
      (Quantum.run (traversal ++ restore))
      (Clean (registers.path k K)) := by
    apply quotientSwap_coherent_seq_circuits htraversal
      (CoherentlyImplementsOn.unitary restore (fun _ => True))
      htraversalHPFree
    intro state hstate
    trivial
  have hprepare : CoherentlyImplementsOn
      (AdaptiveCircuit.unitary prepare .done) (Quantum.run prepare)
      (QuotientSwapReady registers) :=
    CoherentlyImplementsOn.unitary prepare (QuotientSwapReady registers)
  have hprepareHPFree : HPFree prepare := by
    simp [prepare]
  have hprepareReady : ∀ state, QuotientSwapReady registers state →
      Clean (registers.path k K) (Classical.run prepare state) := by
    intro state hready wire hwire
    have hcorrect := quotientSwapUnitary_correct registers state hlayout hready
    simpa only [prepare, Classical.run_append] using
      hcorrect.2.1 wire
        (quotientSwap_path_mem_scratch registers k K wire hwire)
  have hall := quotientSwap_coherent_seq_circuits hprepare hmiddle
    hprepareHPFree hprepareReady
  simpa only [quotientSwap, quotientSwapUnitary, prepare, traversal,
    adaptiveTraversal, restore, List.append_assoc] using hall

private theorem unaryActionTree_leafCostSum_const
    (tree : UnaryActionTree) (control : Wire) (path : List Wire)
    (cost : Nat) (hlayout : tree.Layout control path) :
    tree.leafCostSum (fun _ _ => cost) control path = cost * tree.leaves := by
  induction hlayout with
  | leaf label control path hlocal =>
      simp [UnaryActionTree.leafCostSum, UnaryActionTree.leaves]
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      simp only [UnaryActionTree.leafCostSum, UnaryActionTree.leaves,
        ihZero, ihOne]
      rw [Nat.mul_add]

/-- Constructor-derived coherent Toffoli count for the literal Figure-9 block. -/
theorem quotientSwapUnitary_toffoliCount
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) :
    eeaToffoliCount (quotientSwapUnitary registers k K) =
      8 * registers.lengthT.length +
        (quotientSwapTree registers k K).leaves +
        2 * (quotientSwapTree registers k K).internalNodes := by
  have hconstantLength :=
    quotientSwap_constantScratch_length registers hlayout
  have hleaf : (quotientSwapTree registers k K).leafCostSum
      (fun label wire => eeaToffoliCount
        (quotientSwapLeaf registers k label wire))
      registers.control (registers.path k K) =
        (quotientSwapTree registers k K).leaves := by
    simpa [quotientSwapLeaf] using
      unaryActionTree_leafCostSum_const (quotientSwapTree registers k K)
        registers.control (registers.path k K) 1 hlayout.tree
  simp only [quotientSwapUnitary, eeaToffoliCount_append]
  rw [cuccaroAdd_toffoliCount registers.lengthT registers.lengthQ
      (registers.carry k K) hlayout.lengthT_eq_lengthQ,
    addConstant_toffoliCount registers.lengthQ registers.constantScratch
      (registers.carry k K) 3 hconstantLength,
    unaryActionUnitary_toffoliCount .inc (quotientSwapLeaf registers k)
      (quotientSwapTree registers k K) registers.control
      (registers.path k K) hlayout.tree,
    subConstant_toffoliCount registers.lengthQ registers.constantScratch
      (registers.carry k K) 3 hconstantLength,
    cuccaroSub_toffoliCount registers.lengthT registers.lengthQ
      (registers.carry k K) hlayout.lengthT_eq_lengthQ,
    hleaf, ← hlayout.lengthT_eq_lengthQ]
  omega

/-- Constructor-derived coherent CNOT count for the literal Figure-9 block. -/
theorem quotientSwapUnitary_cnotCount
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) :
    eeaCnotCount (quotientSwapUnitary registers k K) =
      16 * registers.lengthT.length +
        2 * (quotientSwapTree registers k K).leaves +
        2 * (quotientSwapTree registers k K).internalNodes := by
  have hconstantLength :=
    quotientSwap_constantScratch_length registers hlayout
  have hleaf : (quotientSwapTree registers k K).leafCostSum
      (fun label wire => eeaCnotCount
        (quotientSwapLeaf registers k label wire))
      registers.control (registers.path k K) =
        2 * (quotientSwapTree registers k K).leaves := by
    simpa [quotientSwapLeaf] using
      unaryActionTree_leafCostSum_const (quotientSwapTree registers k K)
        registers.control (registers.path k K) 2 hlayout.tree
  simp only [quotientSwapUnitary, eeaCnotCount_append]
  rw [cuccaroAdd_cnotCount registers.lengthT registers.lengthQ
      (registers.carry k K) hlayout.lengthT_eq_lengthQ,
    addConstant_cnotCount registers.lengthQ registers.constantScratch
      (registers.carry k K) 3 hconstantLength,
    unaryActionUnitary_cnotCount .inc (quotientSwapLeaf registers k)
      (quotientSwapTree registers k K) registers.control
      (registers.path k K) hlayout.tree,
    subConstant_cnotCount registers.lengthQ registers.constantScratch
      (registers.carry k K) 3 hconstantLength,
    cuccaroSub_cnotCount registers.lengthT registers.lengthQ
      (registers.carry k K) hlayout.lengthT_eq_lengthQ,
    hleaf, ← hlayout.lengthT_eq_lengthQ]
  omega

/-- Constructor-derived coherent T count for the literal Figure-9 block. -/
theorem quotientSwapUnitary_tCount
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) :
    ShorECDLP.tCount (quotientSwapUnitary registers k K) =
      56 * registers.lengthT.length +
        7 * (quotientSwapTree registers k K).leaves +
        14 * (quotientSwapTree registers k K).internalNodes := by
  have hconstantLength :=
    quotientSwap_constantScratch_length registers hlayout
  have hleaf : (quotientSwapTree registers k K).leafCostSum
      (fun label wire => ShorECDLP.tCount
        (quotientSwapLeaf registers k label wire))
      registers.control (registers.path k K) =
        7 * (quotientSwapTree registers k K).leaves := by
    simpa [quotientSwapLeaf] using
      unaryActionTree_leafCostSum_const (quotientSwapTree registers k K)
        registers.control (registers.path k K) 7 hlayout.tree
  simp only [quotientSwapUnitary, tCount_append]
  rw [cuccaroAdd_tCount registers.lengthT registers.lengthQ
      (registers.carry k K) hlayout.lengthT_eq_lengthQ,
    addConstant_tCount registers.lengthQ registers.constantScratch
      (registers.carry k K) 3 hconstantLength,
    unaryActionUnitary_tCount .inc (quotientSwapLeaf registers k)
      (quotientSwapTree registers k K) registers.control
      (registers.path k K) hlayout.tree,
    subConstant_tCount registers.lengthQ registers.constantScratch
      (registers.carry k K) 3 hconstantLength,
    cuccaroSub_tCount registers.lengthT registers.lengthQ
      (registers.carry k K) hlayout.lengthT_eq_lengthQ,
    hleaf, ← hlayout.lengthT_eq_lengthQ]
  omega

private theorem quotientSwap_measurementCount_seq
    (first second : AdaptiveCircuit) :
    (first.seq second).measurementCount =
      first.measurementCount + second.measurementCount := by
  induction first with
  | done => simp [AdaptiveCircuit.seq, AdaptiveCircuit.measurementCount]
  | unitary circuit next ih =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.measurementCount, ih]
  | xMeasureReset target onFalse onTrue ihFalse ihTrue =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.measurementCount,
        ihFalse, ihTrue, Nat.add_max_add_right, Nat.add_assoc]

private theorem quotientSwap_tCount_seq
    (first second : AdaptiveCircuit) :
    (first.seq second).tCount = first.tCount + second.tCount := by
  induction first with
  | done => simp [AdaptiveCircuit.seq, AdaptiveCircuit.tCount]
  | unitary circuit next ih =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.tCount, ih, Nat.add_assoc]
  | xMeasureReset target onFalse onTrue ihFalse ihTrue =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.tCount,
        ihFalse, ihTrue, Nat.add_max_add_right]

/-- Exactly one path-AND is measured at each source-tree decision node. -/
theorem quotientSwap_measurementCount
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) :
    (quotientSwap registers k K).measurementCount =
      (quotientSwapTree registers k K).internalNodes := by
  rw [quotientSwap, quotientSwap_measurementCount_seq,
    quotientSwap_measurementCount_seq]
  simp [AdaptiveCircuit.measurementCount,
    unaryAction_measurementCount .inc (quotientSwapLeaf registers k)
      (quotientSwapTree registers k K) registers.control
      (registers.path k K) hlayout.tree]

/-- Measurement-uncomputation removes one reverse-decoder Toffoli per internal node. -/
theorem quotientSwap_tCount
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) :
    (quotientSwap registers k K).tCount =
      56 * registers.lengthT.length +
        7 * (quotientSwapTree registers k K).leaves +
        7 * (quotientSwapTree registers k K).internalNodes := by
  have hconstantLength :=
    quotientSwap_constantScratch_length registers hlayout
  have hleaf : (quotientSwapTree registers k K).leafCostSum
      (fun label wire => ShorECDLP.tCount
        (quotientSwapLeaf registers k label wire))
      registers.control (registers.path k K) =
        7 * (quotientSwapTree registers k K).leaves := by
    simpa [quotientSwapLeaf] using
      unaryActionTree_leafCostSum_const (quotientSwapTree registers k K)
        registers.control (registers.path k K) 7 hlayout.tree
  rw [quotientSwap, quotientSwap_tCount_seq, quotientSwap_tCount_seq]
  simp only [AdaptiveCircuit.tCount, tCount_append]
  rw [cuccaroAdd_tCount registers.lengthT registers.lengthQ
      (registers.carry k K) hlayout.lengthT_eq_lengthQ,
    addConstant_tCount registers.lengthQ registers.constantScratch
      (registers.carry k K) 3 hconstantLength,
    unaryAction_tCount .inc (quotientSwapLeaf registers k)
      (quotientSwapTree registers k K) registers.control
      (registers.path k K) hlayout.tree,
    subConstant_tCount registers.lengthQ registers.constantScratch
      (registers.carry k K) 3 hconstantLength,
    cuccaroSub_tCount registers.lengthT registers.lengthQ
      (registers.carry k K) hlayout.lengthT_eq_lengthQ,
    hleaf, ← hlayout.lengthT_eq_lengthQ]
  omega

/-- The literal coherent source block has the expected whole-state inverse. -/
theorem quotientSwapUnitary_adjoint_roundtrip
    (registers : QuotientSwapRegisters) {k K : Nat}
    (state : BasisState) (hlayout : QuotientSwapLayout registers k K) :
    Classical.run (quotientSwapUnitary registers k K).adjoint
        (Classical.run (quotientSwapUnitary registers k K) state) = state := by
  exact run_adjoint_run_classical (quotientSwapUnitary registers k K)
    (quotientSwapUnitary_wellFormed registers hlayout) state

/-! ## Pinned-source regressions -/

private def quotientSwapSmallRegisters : QuotientSwapRegisters where
  control := 0
  sign := 1
  work1 := [2, 3, 4, 5]
  lengthT := [6, 7, 8]
  lengthQ := [9, 10, 11]
  scratch := [12, 13, 14, 15]

/-- Exact highest-varying-bit tree for source labels `2,3,4,5`.  The common middle bit is
correctly skipped, and the low bit is reused in the two disjoint branches. -/
theorem quotientSwapSmall_tree_regression :
    quotientSwapTree quotientSwapSmallRegisters 2 5 =
      .node 11 (.node 9 (.leaf 2) (.leaf 3))
        (.node 9 (.leaf 4) (.leaf 5)) := by
  decide

private theorem quotientSwapSmall_layout :
    QuotientSwapLayout quotientSwapSmallRegisters 2 5 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, ?_⟩
  rw [quotientSwapSmall_tree_regression]
  change (UnaryActionTree.node 11
      (UnaryActionTree.node 9 (.leaf 2) (.leaf 3))
      (UnaryActionTree.node 9 (.leaf 4) (.leaf 5))).Layout
    0 ([12, 13, 14] : List Wire)
  exact .node 11 0 12 _ _ ([13, 14] : List Wire) (by decide)
    (.node 9 12 13 _ _ ([14] : List Wire) (by decide)
      (.leaf 2 13 ([14] : List Wire) (by decide))
      (.leaf 3 13 ([14] : List Wire) (by decide)))
    (.node 9 12 13 _ _ ([14] : List Wire) (by decide)
      (.leaf 4 13 ([14] : List Wire) (by decide))
      (.leaf 5 13 ([14] : List Wire) (by decide)))

/-- Closed `k=2`, `K=5`, width-three resource regression derived from the literal constructors. -/
theorem quotientSwapSmall_resources :
    eeaToffoliCount (quotientSwapUnitary quotientSwapSmallRegisters 2 5) = 34 ∧
      eeaCnotCount (quotientSwapUnitary quotientSwapSmallRegisters 2 5) = 62 ∧
      ShorECDLP.tCount (quotientSwapUnitary quotientSwapSmallRegisters 2 5) = 238 ∧
      (quotientSwap quotientSwapSmallRegisters 2 5).measurementCount = 3 ∧
      (quotientSwap quotientSwapSmallRegisters 2 5).tCount = 217 := by
  rw [quotientSwapUnitary_toffoliCount quotientSwapSmallRegisters
      quotientSwapSmall_layout,
    quotientSwapUnitary_cnotCount quotientSwapSmallRegisters
      quotientSwapSmall_layout,
    quotientSwapUnitary_tCount quotientSwapSmallRegisters
      quotientSwapSmall_layout,
    quotientSwap_measurementCount quotientSwapSmallRegisters
      quotientSwapSmall_layout,
    quotientSwap_tCount quotientSwapSmallRegisters quotientSwapSmall_layout,
    quotientSwapSmall_tree_regression]
  norm_num [quotientSwapSmallRegisters, UnaryActionTree.leaves,
    UnaryActionTree.internalNodes]

set_option maxRecDepth 10000 in
/-- Direct small-instance source regression for the Clifford-X count and exact touched-wire set. -/
theorem quotientSwapSmall_surface_regression :
    eeaXCount (quotientSwapUnitary quotientSwapSmallRegisters 2 5) = 20 ∧
      qubitCount (quotientSwapUnitary quotientSwapSmallRegisters 2 5) = 16 := by
  decide

end

end ShorECDLP.Paper2607_13816
