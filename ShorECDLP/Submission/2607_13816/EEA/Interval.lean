import ShorECDLP.Submission.«2607_13816».EEA.Endpoint
import ShorECDLP.Submission.«2607_13816».EEA.IntervalLeaf
import Mathlib.Data.Nat.Bitwise

/-!
# Complete source-shaped interval arithmetic

This module instantiates the pinned supplement's remainder-window block.  The label set and its
highest-varying-bit tree are built from the physical endpoint registers, the two decoder stacks and
all arithmetic roles are cut from one shared scratch register, and every relative label is bound to
the corresponding `Work1`/`Work2` lane.  The executable order is exactly

`prepare endpoints; top-first; decreasing dual scan; sign update; increasing dual scan;
top-second; restore endpoints`.

Both the coherent reference and the measurement-uncomputed adaptive program are exposed.  The
inverse aggregate and the four-phase indexed EEA step remain later composition boundaries.
-/

namespace ShorECDLP.Paper2607_13816

open Classical Quantum

noncomputable section

/-- Which physical work bank receives the location-controlled add/subtract. -/
inductive IntervalTarget where
  | work1
  | work2
deriving DecidableEq, Repr

/-- Physical registers of one `lc_interval_addsub_unary_gate` instance. -/
structure IntervalRegisters where
  control : Wire
  sign : Wire
  work1 : List Wire
  work2 : List Wire
  lengthT : List Wire
  lengthQ : List Wire
  lengthS : List Wire
  scratch : List Wire
deriving Repr

/-- Number of physical quotient lanes in the inclusive source window `[k,K]`. -/
def intervalLaneCount (k K : Nat) : Nat := K - k + 1

/-- Relative index of the last physical quotient lane. -/
def intervalTopRelative (k K : Nat) : Nat := intervalLaneCount k K - 1

/-- The source special-cases `[0,2^d]`: one more label than a power of two. -/
def intervalHasTopSpecial (k K : Nat) : Bool :=
  let count := intervalLaneCount k K
  decide (1 < count ∧ ((count - 1) &&& (count - 2)) = 0)

/-- Main labels passed to `_tight_unary_depth_for_labels`, after removing the special top label. -/
def intervalMainLabels (k K : Nat) : List Nat :=
  let count := intervalLaneCount k K
  if intervalHasTopSpecial k K then List.range (count - 1) else List.range count

def IntervalRegisters.rightIndex (registers : IntervalRegisters) (bit : Nat) : Wire :=
  registers.lengthS.getD bit 0

def IntervalRegisters.leftIndex (registers : IntervalRegisters) (bit : Nat) : Wire :=
  registers.lengthQ.getD bit 0

/-- The executable tree returned by the certified source builder.  The default branch is unreachable
because `intervalMainLabels` is nonempty; `intervalTree_built` below records that fact. -/
def intervalTree (registers : IntervalRegisters) (k K : Nat) : DualUnaryActionTree :=
  (DualUnaryActionTree.buildSourceFromList registers.rightIndex registers.leftIndex
    (intervalMainLabels k K)).getD (.leaf 0)

theorem intervalMainLabels_nonempty (k K : Nat) : intervalMainLabels k K ≠ [] := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · have hcount : 1 < intervalLaneCount k K := by
      have hsource : 1 < intervalLaneCount k K ∧
          ((intervalLaneCount k K - 1) &&& (intervalLaneCount k K - 2)) = 0 := by
        simpa [intervalHasTopSpecial] using hspecial
      exact hsource.1
    simp [intervalMainLabels, hspecial]
    omega
  · simp [intervalMainLabels, hspecial, intervalLaneCount]

/-- The default branch in `intervalTree` is unreachable: the concrete source builder succeeds. -/
theorem intervalTree_built (registers : IntervalRegisters) (k K : Nat) :
    DualUnaryActionTree.buildSourceFromList registers.rightIndex registers.leftIndex
        (intervalMainLabels k K) =
      some (intervalTree registers k K) := by
  have hnonempty : (intervalMainLabels k K).toFinset.Nonempty := by
    simpa using intervalMainLabels_nonempty k K
  obtain ⟨tree, htree⟩ := DualUnaryActionTree.buildSource_exists
    registers.rightIndex registers.leftIndex
      (intervalMainLabels k K).toFinset hnonempty
  change DualUnaryActionTree.buildSource registers.rightIndex registers.leftIndex
      (intervalMainLabels k K).toFinset =
    some ((DualUnaryActionTree.buildSource registers.rightIndex registers.leftIndex
      (intervalMainLabels k K).toFinset).getD (.leaf 0))
  rw [htree]
  rfl

theorem intervalTree_visitLabels_inc (registers : IntervalRegisters) (k K : Nat) :
    (intervalTree registers k K).visitLabels .inc =
      (intervalMainLabels k K).toFinset.sort (· ≤ ·) :=
  DualUnaryActionTree.buildSourceFromList_visitLabels_inc
    registers.rightIndex registers.leftIndex (intervalMainLabels k K)
      (intervalTree registers k K) (intervalTree_built registers k K)

theorem intervalTree_visitLabels_dec (registers : IntervalRegisters) (k K : Nat) :
    (intervalTree registers k K).visitLabels .dec =
      ((intervalMainLabels k K).toFinset.sort (· ≤ ·)).reverse :=
  DualUnaryActionTree.buildSourceFromList_visitLabels_dec
    registers.rightIndex registers.leftIndex (intervalMainLabels k K)
      (intervalTree registers k K) (intervalTree_built registers k K)

theorem intervalTree_labels (registers : IntervalRegisters) (k K : Nat) :
    (intervalTree registers k K).labels =
      (intervalMainLabels k K).toFinset.sort (· ≤ ·) := by
  exact DualUnaryActionTree.buildSource_labels_eq_sort
    registers.rightIndex registers.leftIndex (intervalMainLabels k K).toFinset
    (intervalTree registers k K) (by
      simpa [DualUnaryActionTree.buildSourceFromList] using
        intervalTree_built registers k K)

private theorem intervalTree_label_lt_laneCount
    (registers : IntervalRegisters) (k K label : Nat)
    (hlabel : label ∈ (intervalTree registers k K).labels) :
    label < intervalLaneCount k K := by
  rw [intervalTree_labels] at hlabel
  have hmain : label ∈ intervalMainLabels k K := by
    simpa using hlabel
  by_cases hspecial : intervalHasTopSpecial k K = true
  · simp [intervalMainLabels, hspecial] at hmain
    omega
  · simp [intervalMainLabels, hspecial] at hmain
    exact hmain

/-- Tight number of simultaneously live decoder paths, computed from the concrete source tree. -/
def intervalTreeDepth (registers : IntervalRegisters) (k K : Nat) : Nat :=
  (intervalTree registers k K).pathDepth

/-- Width of the prefix reserved for endpoint arithmetic. -/
def intervalEndpointWidth (registers : IntervalRegisters) : Nat :=
  max registers.lengthQ.length registers.lengthS.length

/-- First scratch position after both decoder paths and the endpoint-arithmetic prefix. -/
def intervalScratchBase (registers : IntervalRegisters) (k K : Nat) : Nat :=
  max (2 * intervalTreeDepth registers k K) (intervalEndpointWidth registers)

def IntervalRegisters.rightPaths (registers : IntervalRegisters) (k K : Nat) : List Wire :=
  registers.scratch.take (intervalTreeDepth registers k K)

def IntervalRegisters.leftPaths (registers : IntervalRegisters) (k K : Nat) : List Wire :=
  (registers.scratch.drop (intervalTreeDepth registers k K)).take
    (intervalTreeDepth registers k K)

def IntervalRegisters.endpointScratch (registers : IntervalRegisters) : List Wire :=
  registers.scratch.take (intervalEndpointWidth registers)

def IntervalRegisters.equalityScratch (registers : IntervalRegisters) (k K : Nat) : List Wire :=
  registers.scratch.take (intervalScratchBase registers k K)

def IntervalRegisters.carry (registers : IntervalRegisters) (k K : Nat) : Wire :=
  registers.scratch.getD (intervalScratchBase registers k K) 0

def IntervalRegisters.accumulator (registers : IntervalRegisters) (k K : Nat) : Wire :=
  registers.scratch.getD (intervalScratchBase registers k K + 1) 0

def IntervalRegisters.cellScratch (registers : IntervalRegisters) (k K : Nat) : Wire :=
  registers.scratch.getD (intervalScratchBase registers k K + 2) 0

def intervalTopBit (k K : Nat) : Nat := (intervalTopRelative k K).log2

/-- The top endpoint wires are real endpoint bits in the special case.  Outside that case the
leaf constructor never emits them; two `lengthT` wires serve only as distinct proof roles. -/
def IntervalRegisters.rightTop (registers : IntervalRegisters) (k K : Nat) : Wire :=
  if intervalHasTopSpecial k K then
    registers.lengthS.getD (intervalTopBit k K) 0
  else registers.lengthT.getD 0 0

def IntervalRegisters.leftTop (registers : IntervalRegisters) (k K : Nat) : Wire :=
  if intervalHasTopSpecial k K then
    registers.lengthQ.getD (intervalTopBit k K) 0
  else registers.lengthT.getD 1 0

def IntervalRegisters.targetAt
    (registers : IntervalRegisters) (target : IntervalTarget) (label : Nat) : Wire :=
  match target with
  | .work1 => registers.work1.getD label 0
  | .work2 => registers.work2.getD label 0

def IntervalRegisters.addendAt
    (registers : IntervalRegisters) (target : IntervalTarget) (label : Nat) : Wire :=
  match target with
  | .work1 => registers.work2.getD label 0
  | .work2 => registers.work1.getD label 0

/-- Registers in the source constructor's physical order. -/
def IntervalRegisters.allWires (registers : IntervalRegisters) : List Wire :=
  [registers.control, registers.sign] ++
    (registers.work1 ++ (registers.work2 ++
      (registers.lengthT ++ (registers.lengthQ ++
        (registers.lengthS ++ registers.scratch)))))

/-- Exact source register sizes plus the component layouts induced by the physical lanes. -/
structure IntervalLayout (registers : IntervalRegisters) (k K : Nat)
    (target : IntervalTarget) : Prop where
  k_le_K : k ≤ K
  work1_length : registers.work1.length = intervalLaneCount k K
  work2_length : registers.work2.length = intervalLaneCount k K
  lengthT_eq_lengthQ : registers.lengthT.length = registers.lengthQ.length
  lengthT_two_le : 2 ≤ registers.lengthT.length
  lengthS_two_le : 2 ≤ registers.lengthS.length
  right_index_capacity :
    DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset ≤
      registers.lengthS.length
  left_index_capacity :
    DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset ≤
      registers.lengthQ.length
  right_top_capacity : intervalHasTopSpecial k K = true →
    intervalTopBit k K < registers.lengthS.length
  left_top_capacity : intervalHasTopSpecial k K = true →
    intervalTopBit k K < registers.lengthQ.length
  scratch_length : registers.scratch.length = intervalScratchBase registers k K + 3
  physical : registers.allWires.Nodup
  endpoints : IntervalEndpointLayout registers.lengthT registers.lengthQ registers.lengthS
    registers.endpointScratch (registers.carry k K)
  traversal : IntervalTraversalLayout (intervalTree registers k K)
    registers.control registers.control (registers.rightPaths k K) (registers.leftPaths k K)
    (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
    (registers.carry k K) (registers.cellScratch k K)
    (registers.targetAt target) (registers.addendAt target)
  topSpecial : intervalHasTopSpecial k K = true →
    TopSpecialLeafLayout registers.control registers.control registers.lengthS
      registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)

/-- All shared scratch roles start clean. -/
def IntervalReady (registers : IntervalRegisters) (state : BasisState) : Prop :=
  Clean registers.scratch state

private theorem intervalEndpointWidth_le_scratch
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    intervalEndpointWidth registers ≤ registers.scratch.length := by
  calc
    intervalEndpointWidth registers ≤ intervalScratchBase registers k K := by
      exact Nat.le_max_right _ _
    _ ≤ intervalScratchBase registers k K + 3 := by omega
    _ = registers.scratch.length := hlayout.scratch_length.symm

private theorem intervalEndpointScratch_length
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.endpointScratch.length = intervalEndpointWidth registers := by
  simp [IntervalRegisters.endpointScratch, List.length_take,
    Nat.min_eq_left (intervalEndpointWidth_le_scratch registers k K target hlayout)]

private theorem intervalLengthQ_le_endpointScratch
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.lengthQ.length ≤ registers.endpointScratch.length := by
  rw [intervalEndpointScratch_length registers k K target hlayout]
  exact Nat.le_max_left _ _

private theorem intervalLengthS_le_endpointScratch
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.lengthS.length ≤ registers.endpointScratch.length := by
  rw [intervalEndpointScratch_length registers k K target hlayout]
  exact Nat.le_max_right _ _

private theorem intervalLengthS_positive
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    0 < registers.lengthS.length := by
  have htwo := hlayout.lengthS_two_le
  omega

private theorem intervalEqualityScratch_length
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    (registers.equalityScratch k K).length = intervalScratchBase registers k K := by
  have hbase : intervalScratchBase registers k K ≤ registers.scratch.length := by
    rw [hlayout.scratch_length]
    omega
  simp [IntervalRegisters.equalityScratch, List.length_take, Nat.min_eq_left hbase]

private theorem intervalLengthQ_sub_two_le_equalityScratch
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.lengthQ.length - 2 ≤ (registers.equalityScratch k K).length := by
  rw [intervalEqualityScratch_length registers k K target hlayout]
  exact le_trans (Nat.sub_le _ _) (le_trans (Nat.le_max_left _ _)
    (Nat.le_max_right _ _))

private theorem intervalLengthS_sub_two_le_equalityScratch
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.lengthS.length - 2 ≤ (registers.equalityScratch k K).length := by
  rw [intervalEqualityScratch_length registers k K target hlayout]
  exact le_trans (Nat.sub_le _ _) (le_trans (Nat.le_max_right _ _)
    (Nat.le_max_right _ _))

private theorem intervalCarry_mem_scratch
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.carry k K ∈ registers.scratch := by
  have hbound : intervalScratchBase registers k K < registers.scratch.length := by
    rw [hlayout.scratch_length]
    omega
  rw [IntervalRegisters.carry, List.getD_eq_getElem registers.scratch 0 hbound]
  exact List.getElem_mem hbound

private theorem list_getD_mem
    (list : List α) (index : Nat) (fallback : α)
    (hindex : index < list.length) :
    list.getD index fallback ∈ list := by
  rw [List.getD_eq_getElem list fallback hindex]
  exact List.getElem_mem hindex

private theorem intervalTopRelative_lt_laneCount
    (k K : Nat) (hkK : k ≤ K) :
    intervalTopRelative k K < intervalLaneCount k K := by
  simp only [intervalTopRelative, intervalLaneCount]
  omega

private theorem intervalTargetAt_mem_allWires
    (registers : IntervalRegisters) (k K label : Nat)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target)
    (hlabel : label < intervalLaneCount k K) :
    registers.targetAt target label ∈ registers.allWires := by
  cases target with
  | work1 =>
      have hbound : label < registers.work1.length := by
        rw [hlayout.work1_length]
        exact hlabel
      have hmem := list_getD_mem registers.work1 label 0 hbound
      change registers.work1.getD label 0 ∈ registers.allWires
      rw [IntervalRegisters.allWires]
      exact List.mem_append_right _ (List.mem_append_left _ hmem)
  | work2 =>
      have hbound : label < registers.work2.length := by
        rw [hlayout.work2_length]
        exact hlabel
      have hmem := list_getD_mem registers.work2 label 0 hbound
      change registers.work2.getD label 0 ∈ registers.allWires
      rw [IntervalRegisters.allWires]
      exact List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ hmem))

private theorem intervalAddendAt_mem_allWires
    (registers : IntervalRegisters) (k K label : Nat)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target)
    (hlabel : label < intervalLaneCount k K) :
    registers.addendAt target label ∈ registers.allWires := by
  cases target with
  | work1 =>
      have hbound : label < registers.work2.length := by
        rw [hlayout.work2_length]
        exact hlabel
      have hmem := list_getD_mem registers.work2 label 0 hbound
      change registers.work2.getD label 0 ∈ registers.allWires
      rw [IntervalRegisters.allWires]
      exact List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ hmem))
  | work2 =>
      have hbound : label < registers.work1.length := by
        rw [hlayout.work1_length]
        exact hlabel
      have hmem := list_getD_mem registers.work1 label 0 hbound
      change registers.work1.getD label 0 ∈ registers.allWires
      rw [IntervalRegisters.allWires]
      exact List.mem_append_right _ (List.mem_append_left _ hmem)

private theorem intervalDecoder_mem_allWires
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    ∀ wire,
      wire ∈ (intervalTree registers k K).decoderWires registers.control
          registers.control (registers.rightPaths k K) (registers.leftPaths k K) →
        wire ∈ registers.allWires := by
  intro wire hwire
  simp only [DualUnaryActionTree.decoderWires, List.mem_append,
    List.mem_dedup, List.mem_cons, List.not_mem_nil, or_false] at hwire
  rcases hwire with hcontrol | hindexA | hindexB | hrightPath | hleftPath
  · rcases hcontrol with rfl | rfl <;> simp [IntervalRegisters.allWires]
  · obtain ⟨bit, hbit, rfl⟩ := DualUnaryActionTree.build_indexAWires
      registers.rightIndex registers.leftIndex
      (DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset)
      (intervalMainLabels k K).toFinset (intervalTree registers k K) (by
        simpa [DualUnaryActionTree.buildSourceFromList,
          DualUnaryActionTree.buildSource] using intervalTree_built registers k K)
      (by simpa using hindexA)
    have hbound : bit < registers.lengthS.length :=
      lt_of_lt_of_le hbit hlayout.right_index_capacity
    have hmem := list_getD_mem registers.lengthS bit 0 hbound
    change registers.lengthS.getD bit 0 ∈ registers.allWires
    rw [IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ hmem)))))
  · obtain ⟨bit, hbit, rfl⟩ := DualUnaryActionTree.build_indexBWires
      registers.rightIndex registers.leftIndex
      (DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset)
      (intervalMainLabels k K).toFinset (intervalTree registers k K) (by
        simpa [DualUnaryActionTree.buildSourceFromList,
          DualUnaryActionTree.buildSource] using intervalTree_built registers k K)
      (by simpa using hindexB)
    have hbound : bit < registers.lengthQ.length :=
      lt_of_lt_of_le hbit hlayout.left_index_capacity
    have hmem := list_getD_mem registers.lengthQ bit 0 hbound
    change registers.lengthQ.getD bit 0 ∈ registers.allWires
    rw [IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ hmem))))
  · have hscratch : wire ∈ registers.scratch :=
      List.mem_of_mem_take hrightPath
    simp [IntervalRegisters.allWires, hscratch]
  · have hscratch : wire ∈ registers.scratch :=
      List.mem_of_mem_drop (List.mem_of_mem_take hleftPath)
    simp [IntervalRegisters.allWires, hscratch]

private theorem intervalScratch_mem_allWires
    (registers : IntervalRegisters) {wire : Wire}
    (hwire : wire ∈ registers.scratch) :
    wire ∈ registers.allWires := by
  rw [IntervalRegisters.allWires]
  exact List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _ hwire)))))

private theorem intervalScratch_not_mem_lengthQ
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target)
    {wire : Wire} (hscratch : wire ∈ registers.scratch) :
    wire ∉ registers.lengthQ := by
  have hphysical := hlayout.physical
  rw [IntervalRegisters.allWires] at hphysical
  have hrest0 := (List.nodup_append.mp hphysical).2.1
  have hrest1 := (List.nodup_append.mp hrest0).2.1
  have hrest2 := (List.nodup_append.mp hrest1).2.1
  have hrest3 := (List.nodup_append.mp hrest2).2.1
  have hcross := (List.nodup_append.mp hrest3).2.2
  intro hq
  exact hcross wire hq wire (by simp [hscratch]) rfl

private theorem intervalScratch_not_mem_work1
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target)
    {wire : Wire} (hscratch : wire ∈ registers.scratch) :
    wire ∉ registers.work1 := by
  have hphysical := hlayout.physical
  rw [IntervalRegisters.allWires] at hphysical
  have hrest0 := (List.nodup_append.mp hphysical).2.1
  have hcross := (List.nodup_append.mp hrest0).2.2
  intro hwork
  exact hcross wire hwork wire (by simp [hscratch]) rfl

private theorem intervalScratch_not_mem_work2
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target)
    {wire : Wire} (hscratch : wire ∈ registers.scratch) :
    wire ∉ registers.work2 := by
  have hphysical := hlayout.physical
  rw [IntervalRegisters.allWires] at hphysical
  have hrest0 := (List.nodup_append.mp hphysical).2.1
  have hrest1 := (List.nodup_append.mp hrest0).2.1
  have hcross := (List.nodup_append.mp hrest1).2.2
  intro hwork
  exact hcross wire hwork wire (by simp [hscratch]) rfl

private theorem intervalScratch_not_mem_lengthS
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target)
    {wire : Wire} (hscratch : wire ∈ registers.scratch) :
    wire ∉ registers.lengthS := by
  have hphysical := hlayout.physical
  rw [IntervalRegisters.allWires] at hphysical
  have hrest0 := (List.nodup_append.mp hphysical).2.1
  have hrest1 := (List.nodup_append.mp hrest0).2.1
  have hrest2 := (List.nodup_append.mp hrest1).2.1
  have hrest3 := (List.nodup_append.mp hrest2).2.1
  have hrest4 := (List.nodup_append.mp hrest3).2.1
  have hcross := (List.nodup_append.mp hrest4).2.2
  intro hs
  exact hcross wire hs wire hscratch rfl

private theorem intervalScratch_ne_sign
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target)
    {wire : Wire} (hscratch : wire ∈ registers.scratch) :
    wire ≠ registers.sign := by
  have hphysical := hlayout.physical
  rw [IntervalRegisters.allWires] at hphysical
  have hcross := (List.nodup_append.mp hphysical).2.2
  intro equality
  exact hcross registers.sign (by simp) wire (by
    simp [hscratch]) equality.symm

private theorem intervalAccumulator_mem_scratch
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.accumulator k K ∈ registers.scratch := by
  have hbound : intervalScratchBase registers k K + 1 < registers.scratch.length := by
    rw [hlayout.scratch_length]
    omega
  exact list_getD_mem registers.scratch _ 0 hbound

private theorem intervalCellScratch_mem_scratch
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.cellScratch k K ∈ registers.scratch := by
  have hbound : intervalScratchBase registers k K + 2 < registers.scratch.length := by
    rw [hlayout.scratch_length]
    omega
  exact list_getD_mem registers.scratch _ 0 hbound

private theorem intervalRightTop_mem_allWires
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.rightTop k K ∈ registers.allWires := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · have hmem := list_getD_mem registers.lengthS (intervalTopBit k K) 0
      (hlayout.right_top_capacity hspecial)
    rw [IntervalRegisters.rightTop, if_pos hspecial, IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ hmem)))))
  · have hbound : 0 < registers.lengthT.length := by
      have := hlayout.lengthT_two_le
      omega
    have hmem := list_getD_mem registers.lengthT 0 0 hbound
    rw [IntervalRegisters.rightTop, if_neg hspecial, IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ hmem)))

private theorem intervalLeftTop_mem_allWires
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.leftTop k K ∈ registers.allWires := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · have hmem := list_getD_mem registers.lengthQ (intervalTopBit k K) 0
      (hlayout.left_top_capacity hspecial)
    rw [IntervalRegisters.leftTop, if_pos hspecial, IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ hmem))))
  · have hbound : 1 < registers.lengthT.length := by
      have := hlayout.lengthT_two_le
      omega
    have hmem := list_getD_mem registers.lengthT 1 0 hbound
    rw [IntervalRegisters.leftTop, if_neg hspecial, IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ hmem)))

private theorem intervalEndpointSupport_mem_allWires
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    ∀ wire,
      wire ∈ intervalEndpointSupport registers.lengthT registers.lengthQ
          registers.lengthS registers.endpointScratch (registers.carry k K) →
        wire ∈ registers.allWires := by
  intro wire hwire
  simp only [intervalEndpointSupport, List.mem_append, List.mem_singleton] at hwire
  rcases hwire with ((((hscratch | hcarry) | ht) | hq) | hs)
  · exact intervalScratch_mem_allWires registers
      (List.mem_of_mem_take hscratch)
  · subst wire
    exact intervalScratch_mem_allWires registers
      (intervalCarry_mem_scratch registers k K target hlayout)
  · simp [IntervalRegisters.allWires, ht]
  · simp [IntervalRegisters.allWires, hq]
  · simp [IntervalRegisters.allWires, hs]

private theorem intervalCarry_ne_sign
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.carry k K ≠ registers.sign := by
  obtain ⟨hhead, htail, hcross⟩ := List.nodup_append.mp hlayout.physical
  exact fun equality ↦ hcross registers.sign (by simp)
    (registers.carry k K) (by
      simp [intervalCarry_mem_scratch registers k K target hlayout]) equality.symm

private def intervalTopFirst
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) : Circuit :=
  if intervalHasTopSpecial k K then
    topSpecialFirstLeaf mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control
  else []

private def intervalTopSecond
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) : Circuit :=
  if intervalHasTopSpecial k K then
    topSpecialSecondLeaf mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control
  else []

/-- Global measurement-uncompute realization of the separately handled first top lane. -/
private def intervalTopFirstAdaptive
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) : Quantum.AdaptiveCircuit :=
  if intervalHasTopSpecial k K then
    topSpecialFirstLeafAdaptive mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control
  else .unitary [] .done

/-- Global measurement-uncompute realization of the separately handled second top lane. -/
private def intervalTopSecondAdaptive
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) : Quantum.AdaptiveCircuit :=
  if intervalHasTopSpecial k K then
    topSpecialSecondLeafAdaptive mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control
  else .unitary [] .done

private def intervalSignUpdate
    (registers : IntervalRegisters) (k K : Nat) (signUpdate : Bool) : Circuit :=
  if signUpdate then [.CX (registers.carry k K) registers.sign] else []

private theorem intervalTopSpecialSupport_mem_allWires
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    ∀ wire,
      wire ∈ topSpecialLeafSupport registers.control registers.control
          registers.lengthS registers.lengthQ (registers.accumulator k K)
          (registers.targetAt target (intervalTopRelative k K))
          (registers.addendAt target (intervalTopRelative k K))
          (registers.carry k K) (registers.cellScratch k K)
          (registers.cellScratch k K) (registers.equalityScratch k K) →
        wire ∈ registers.allWires := by
  intro wire hwire
  simp only [topSpecialLeafSupport, List.mem_append, List.mem_dedup,
    List.mem_cons, List.not_mem_nil, or_false] at hwire
  have hlabel := intervalTopRelative_lt_laneCount k K hlayout.k_le_K
  have htarget := intervalTargetAt_mem_allWires registers k K
    (intervalTopRelative k K) target hlayout hlabel
  have haddend := intervalAddendAt_mem_allWires registers k K
    (intervalTopRelative k K) target hlayout hlabel
  have hacc := intervalScratch_mem_allWires registers
    (intervalAccumulator_mem_scratch registers k K target hlayout)
  have hcarry := intervalScratch_mem_allWires registers
    (intervalCarry_mem_scratch registers k K target hlayout)
  have hcell := intervalScratch_mem_allWires registers
    (intervalCellScratch_mem_scratch registers k K target hlayout)
  rcases hwire with ((((hroot | hs) | hq) | hroles) | heq)
  · rcases hroot with rfl | rfl <;> simp [IntervalRegisters.allWires]
  · simp [IntervalRegisters.allWires, hs]
  · simp [IntervalRegisters.allWires, hq]
  · rcases hroles with rfl | rfl | rfl | rfl | rfl | rfl <;>
      assumption
  · exact intervalScratch_mem_allWires registers
      (List.mem_of_mem_take heq)

private theorem intervalEqualityScratch_outsideLeafRoles
    (registers : IntervalRegisters) (k K label : Nat)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target)
    (hspecial : intervalHasTopSpecial k K = true)
    (hlabel : label ∈ (intervalTree registers k K).labels) :
    ∀ wire, wire ∈ registers.equalityScratch k K →
      wire ∉ [registers.rightTop k K, registers.leftTop k K,
        registers.accumulator k K, registers.targetAt target label,
        registers.addendAt target label, registers.carry k K,
        registers.cellScratch k K] := by
  intro wire hwire hrole
  have hscratch : wire ∈ registers.scratch := List.mem_of_mem_take hwire
  have htop := hlayout.topSpecial hspecial
  have hdisjoint := htop.2.2.2.2
  rw [List.disjoint_left] at hdisjoint
  have hlabelBound := intervalTree_label_lt_laneCount registers k K label hlabel
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrole
  rcases hrole with hright | hleft | hacc | htarget | haddend | hcarry | hcell
  · subst wire
    apply intervalScratch_not_mem_lengthS registers k K target hlayout hscratch
    rw [IntervalRegisters.rightTop, if_pos hspecial]
    exact list_getD_mem registers.lengthS (intervalTopBit k K) 0
      (hlayout.right_top_capacity hspecial)
  · subst wire
    apply intervalScratch_not_mem_lengthQ registers k K target hlayout hscratch
    rw [IntervalRegisters.leftTop, if_pos hspecial]
    exact list_getD_mem registers.lengthQ (intervalTopBit k K) 0
      (hlayout.left_top_capacity hspecial)
  · exact hdisjoint hwire (by simp [hacc])
  · subst wire
    cases target with
    | work1 =>
        apply intervalScratch_not_mem_work1 registers k K .work1 hlayout hscratch
        exact list_getD_mem registers.work1 label 0 (by
          rw [hlayout.work1_length]
          exact hlabelBound)
    | work2 =>
        apply intervalScratch_not_mem_work2 registers k K .work2 hlayout hscratch
        exact list_getD_mem registers.work2 label 0 (by
          rw [hlayout.work2_length]
          exact hlabelBound)
  · subst wire
    cases target with
    | work1 =>
        apply intervalScratch_not_mem_work2 registers k K .work1 hlayout hscratch
        exact list_getD_mem registers.work2 label 0 (by
          rw [hlayout.work2_length]
          exact hlabelBound)
    | work2 =>
        apply intervalScratch_not_mem_work1 registers k K .work2 hlayout hscratch
        exact list_getD_mem registers.work1 label 0 (by
          rw [hlayout.work1_length]
          exact hlabelBound)
  · exact hdisjoint hwire (by simp [hcarry])
  · exact hdisjoint hwire (by simp [hcell])

private theorem intervalRightPaths_mem_equalityScratch
    (registers : IntervalRegisters) (k K : Nat) :
    ∀ wire, wire ∈ registers.rightPaths k K →
      wire ∈ registers.equalityScratch k K := by
  intro wire hwire
  rw [IntervalRegisters.rightPaths] at hwire
  rw [IntervalRegisters.equalityScratch]
  apply List.take_subset_take_left registers.scratch
    (show intervalTreeDepth registers k K ≤ intervalScratchBase registers k K by
      have hdouble : intervalTreeDepth registers k K ≤
          2 * intervalTreeDepth registers k K := by omega
      exact hdouble.trans (Nat.le_max_left _ _))
  exact hwire

private theorem intervalLeftPaths_mem_equalityScratch
    (registers : IntervalRegisters) (k K : Nat) :
    ∀ wire, wire ∈ registers.leftPaths k K →
      wire ∈ registers.equalityScratch k K := by
  intro wire hwire
  rw [IntervalRegisters.leftPaths] at hwire
  rw [IntervalRegisters.equalityScratch]
  have htwice : wire ∈ registers.scratch.take
      (intervalTreeDepth registers k K + intervalTreeDepth registers k K) := by
    rw [List.take_add]
    exact List.mem_append_right _ hwire
  apply List.take_subset_take_left registers.scratch
    (show intervalTreeDepth registers k K + intervalTreeDepth registers k K ≤
        intervalScratchBase registers k K by
      unfold intervalScratchBase
      rw [← two_mul]
      exact Nat.le_max_left _ _)
  exact htwice

private theorem intervalTopScratch_mem_scratch
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    ∀ wire, wire ∈ registers.cellScratch k K :: registers.equalityScratch k K →
      wire ∈ registers.scratch := by
  intro wire hwire
  rcases List.mem_cons.mp hwire with rfl | hwire
  · exact intervalCellScratch_mem_scratch registers k K target hlayout
  · exact List.mem_of_mem_take hwire

/-- In the top-special case, either main traversal preserves the complete scratch bank used by
the separately handled top leaf.  Restricting the leaf obligation to the concrete tree labels is
essential: the physical lane maps are total only via an unreachable `getD` fallback. -/
private theorem intervalTraversal_preservesTopScratch
    (second : Bool) (registers : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target)
    (hspecial : intervalHasTopSpecial k K = true) (state : BasisState)
    (hcleanRight : Clean (registers.rightPaths k K) state)
    (hcleanLeft : Clean (registers.leftPaths k K) state) :
    ∀ wire, wire ∈ registers.cellScratch k K :: registers.equalityScratch k K →
      run (if second then
          intervalSecondTraversal mode (intervalHasTopSpecial k K)
            (registers.rightTop k K) (registers.leftTop k K)
            (registers.accumulator k K) (registers.carry k K)
            (registers.cellScratch k K) (registers.targetAt target)
            (registers.addendAt target) (intervalTree registers k K)
            registers.control registers.control (registers.rightPaths k K)
            (registers.leftPaths k K)
        else
          intervalFirstTraversal mode (intervalHasTopSpecial k K)
            (registers.rightTop k K) (registers.leftTop k K)
            (registers.accumulator k K) (registers.carry k K)
            (registers.cellScratch k K) (registers.targetAt target)
            (registers.addendAt target) (intervalTree registers k K)
            registers.control registers.control (registers.rightPaths k K)
            (registers.leftPaths k K)) state wire = state wire := by
  let tree := intervalTree registers k K
  let decoder := tree.decoderWires registers.control registers.control
    (registers.rightPaths k K) (registers.leftPaths k K)
  let topScratch := registers.cellScratch k K :: registers.equalityScratch k K
  let preserved := decoder ++ topScratch
  let leafAction := if second then
      (fun label rightControl leftControl ↦
        intervalSecondLeaf mode (intervalHasTopSpecial k K)
          (registers.rightTop k K) (registers.leftTop k K)
          (registers.accumulator k K) (registers.targetAt target label)
          (registers.addendAt target label) (registers.carry k K)
          (registers.cellScratch k K) label rightControl leftControl)
    else
      (fun label rightControl leftControl ↦
        intervalFirstLeaf mode (intervalHasTopSpecial k K)
          (registers.rightTop k K) (registers.leftTop k K)
          (registers.accumulator k K) (registers.targetAt target label)
          (registers.addendAt target label) (registers.carry k K)
          (registers.cellScratch k K) label rightControl leftControl)
  have hleaf : DualUnaryLeafPreservesOn leafAction tree.labels decoder preserved := by
    intro label hlabel rightControl leftControl hright hleft next wire hwire
    rcases List.mem_append.mp hwire with hdecoder | htopScratch
    · have houtside := (hlayout.traversal.2 label hlabel).2
      rw [DecoderOutsideIntervalRoles, List.disjoint_left] at houtside
      by_cases hsecond : second = true
      · simp only [leafAction, if_pos hsecond]
        exact intervalSecondLeaf_preservesOutside mode (intervalHasTopSpecial k K)
          (registers.rightTop k K) (registers.leftTop k K)
          (registers.accumulator k K) (registers.targetAt target label)
          (registers.addendAt target label) (registers.carry k K)
          (registers.cellScratch k K) label rightControl leftControl next wire
          (houtside hdecoder)
      · simp only [leafAction, if_neg hsecond]
        exact intervalFirstLeaf_preservesOutside mode (intervalHasTopSpecial k K)
          (registers.rightTop k K) (registers.leftTop k K)
          (registers.accumulator k K) (registers.targetAt target label)
          (registers.addendAt target label) (registers.carry k K)
          (registers.cellScratch k K) label rightControl leftControl next wire
          (houtside hdecoder)
    · simp only [topScratch, List.mem_cons] at htopScratch
      rcases htopScratch with hcell | hequality
      · subst wire
        by_cases hsecond : second = true
        · simp only [leafAction, if_pos hsecond]
          exact intervalSecondLeaf_preservesScratch_of_decoder mode
            (intervalHasTopSpecial k K) (registers.rightTop k K)
            (registers.leftTop k K) (registers.accumulator k K)
            (registers.targetAt target label) (registers.addendAt target label)
            (registers.carry k K) (registers.cellScratch k K) label
            rightControl leftControl decoder next (hlayout.traversal.2 label hlabel).1
            (hlayout.traversal.2 label hlabel).2 hright hleft
        · simp only [leafAction, if_neg hsecond]
          exact intervalFirstLeaf_preservesScratch_of_decoder mode
            (intervalHasTopSpecial k K) (registers.rightTop k K)
            (registers.leftTop k K) (registers.accumulator k K)
            (registers.targetAt target label) (registers.addendAt target label)
            (registers.carry k K) (registers.cellScratch k K) label
            rightControl leftControl decoder next (hlayout.traversal.2 label hlabel).1
            (hlayout.traversal.2 label hlabel).2 hright hleft
      · have houtside := intervalEqualityScratch_outsideLeafRoles registers k K label
          target hlayout hspecial hlabel wire hequality
        by_cases hsecond : second = true
        · simp only [leafAction, if_pos hsecond]
          exact intervalSecondLeaf_preservesOutside mode (intervalHasTopSpecial k K)
            (registers.rightTop k K) (registers.leftTop k K)
            (registers.accumulator k K) (registers.targetAt target label)
            (registers.addendAt target label) (registers.carry k K)
            (registers.cellScratch k K) label rightControl leftControl next wire houtside
        · simp only [leafAction, if_neg hsecond]
          exact intervalFirstLeaf_preservesOutside mode (intervalHasTopSpecial k K)
            (registers.rightTop k K) (registers.leftTop k K)
            (registers.accumulator k K) (registers.targetAt target label)
            (registers.addendAt target label) (registers.carry k K)
            (registers.cellScratch k K) label rightControl leftControl next wire houtside
  have hpreserves := dualUnaryActionUnitary_preservesOn
    (if second then .inc else .dec) leafAction tree registers.control registers.control
    (registers.rightPaths k K) (registers.leftPaths k K) decoder preserved state
    hlayout.traversal.1 hleaf (fun _ hwire ↦ hwire)
    (fun _ hwire ↦ List.mem_append_left topScratch hwire)
    hcleanRight hcleanLeft
  intro wire hwire
  have hw := hpreserves wire (List.mem_append_right decoder hwire)
  cases second <;>
    simpa [leafAction, tree, intervalFirstTraversal, intervalSecondTraversal] using hw

private theorem intervalTopFirst_usesOnly
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target) :
    PaperCircuitUsesOnly registers.allWires
      (intervalTopFirst registers k K mode target) := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopFirst, if_pos hspecial]
    apply (topSpecialFirstLeaf_usesOnly mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control).mono
    exact intervalTopSpecialSupport_mem_allWires registers k K target hlayout
  · simp [intervalTopFirst, hspecial, PaperCircuitUsesOnly]

private theorem intervalTopSecond_usesOnly
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target) :
    PaperCircuitUsesOnly registers.allWires
      (intervalTopSecond registers k K mode target) := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopSecond, if_pos hspecial]
    apply (topSpecialSecondLeaf_usesOnly mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control).mono
    exact intervalTopSpecialSupport_mem_allWires registers k K target hlayout
  · simp [intervalTopSecond, hspecial, PaperCircuitUsesOnly]

private theorem intervalTraversal_usesOnly
    (second : Bool) (registers : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    PaperCircuitUsesOnly registers.allWires
      (if second then
        intervalSecondTraversal mode (intervalHasTopSpecial k K)
          (registers.rightTop k K) (registers.leftTop k K)
          (registers.accumulator k K) (registers.carry k K)
          (registers.cellScratch k K) (registers.targetAt target)
          (registers.addendAt target) (intervalTree registers k K)
          registers.control registers.control (registers.rightPaths k K)
          (registers.leftPaths k K)
      else
        intervalFirstTraversal mode (intervalHasTopSpecial k K)
          (registers.rightTop k K) (registers.leftTop k K)
          (registers.accumulator k K) (registers.carry k K)
          (registers.cellScratch k K) (registers.targetAt target)
          (registers.addendAt target) (intervalTree registers k K)
          registers.control registers.control (registers.rightPaths k K)
          (registers.leftPaths k K)) := by
  let leafAction := if second then
      (fun label rightControl leftControl ↦
        intervalSecondLeaf mode (intervalHasTopSpecial k K)
          (registers.rightTop k K) (registers.leftTop k K)
          (registers.accumulator k K) (registers.targetAt target label)
          (registers.addendAt target label) (registers.carry k K)
          (registers.cellScratch k K) label rightControl leftControl)
    else
      (fun label rightControl leftControl ↦
        intervalFirstLeaf mode (intervalHasTopSpecial k K)
          (registers.rightTop k K) (registers.leftTop k K)
          (registers.accumulator k K) (registers.targetAt target label)
          (registers.addendAt target label) (registers.carry k K)
          (registers.cellScratch k K) label rightControl leftControl)
  have hleaf : DualUnaryLeafUsesOnly leafAction
      (intervalTree registers k K).labels registers.allWires := by
    intro label hlabel rightControl leftControl hright hleft
    have hlabelBound := intervalTree_label_lt_laneCount registers k K label hlabel
    have htarget := intervalTargetAt_mem_allWires registers k K label target
      hlayout hlabelBound
    have haddend := intervalAddendAt_mem_allWires registers k K label target
      hlayout hlabelBound
    have hrightTop := intervalRightTop_mem_allWires registers k K target hlayout
    have hleftTop := intervalLeftTop_mem_allWires registers k K target hlayout
    have hacc := intervalScratch_mem_allWires registers
      (intervalAccumulator_mem_scratch registers k K target hlayout)
    have hcarry := intervalScratch_mem_allWires registers
      (intervalCarry_mem_scratch registers k K target hlayout)
    have hcell := intervalScratch_mem_allWires registers
      (intervalCellScratch_mem_scratch registers k K target hlayout)
    by_cases hsecond : second = true
    · simp only [leafAction, if_pos hsecond]
      apply (intervalSecondLeaf_usesOnly mode (intervalHasTopSpecial k K)
        (registers.rightTop k K) (registers.leftTop k K)
        (registers.accumulator k K) (registers.targetAt target label)
        (registers.addendAt target label) (registers.carry k K)
        (registers.cellScratch k K) label rightControl leftControl).mono
      intro wire hwire
      simp only [intervalLeafSupport, List.mem_append, List.mem_dedup,
        List.mem_cons, List.not_mem_nil, or_false] at hwire
      rcases hwire with hcontrols | hroles
      · rcases hcontrols with rfl | rfl <;> assumption
      · rcases hroles with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          assumption
    · simp only [leafAction, if_neg hsecond]
      apply (intervalFirstLeaf_usesOnly mode (intervalHasTopSpecial k K)
        (registers.rightTop k K) (registers.leftTop k K)
        (registers.accumulator k K) (registers.targetAt target label)
        (registers.addendAt target label) (registers.carry k K)
        (registers.cellScratch k K) label rightControl leftControl).mono
      intro wire hwire
      simp only [intervalLeafSupport, List.mem_append, List.mem_dedup,
        List.mem_cons, List.not_mem_nil, or_false] at hwire
      rcases hwire with hcontrols | hroles
      · rcases hcontrols with rfl | rfl <;> assumption
      · rcases hroles with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          assumption
  have huses := dualUnaryActionUnitary_usesOnly
    (if second then .inc else .dec) leafAction (intervalTree registers k K)
    registers.control registers.control (registers.rightPaths k K)
    (registers.leftPaths k K) registers.allWires
    (intervalDecoder_mem_allWires registers k K target hlayout) hleaf
  cases second <;>
    simpa [leafAction, intervalFirstTraversal, intervalSecondTraversal] using huses

private theorem intervalSignUpdate_usesOnly
    (registers : IntervalRegisters) (k K : Nat) (signUpdate : Bool)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target) :
    PaperCircuitUsesOnly registers.allWires
      (intervalSignUpdate registers k K signUpdate) := by
  by_cases hsign : signUpdate = true
  · rw [intervalSignUpdate, if_pos hsign]
    intro gate hgate
    simp only [List.mem_singleton] at hgate
    subst gate
    intro wire hwire
    simp [gateWires] at hwire
    rcases hwire with rfl | rfl
    · exact intervalScratch_mem_allWires registers
        (intervalCarry_mem_scratch registers k K target hlayout)
    · simp [IntervalRegisters.allWires]
  · simp [intervalSignUpdate, hsign, PaperCircuitUsesOnly]

/-- Coherent reference for the complete forward interval block. -/
def intervalAddSubUnitary
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) : Circuit :=
  prepareIntervalEndpoints registers.lengthT registers.lengthQ registers.lengthS
      registers.endpointScratch (registers.carry k K) n k ++
    intervalTopFirst registers k K mode target ++
    intervalFirstTraversal mode (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K)
      (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K) ++
    intervalSignUpdate registers k K signUpdate ++
    intervalSecondTraversal mode (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K)
      (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K) ++
    intervalTopSecond registers k K mode target ++
    restoreIntervalEndpoints registers.lengthT registers.lengthQ registers.lengthS
      registers.endpointScratch (registers.carry k K) n k

/-- The complete source-shaped coherent interval stays inside its physical register record. -/
theorem intervalAddSubUnitary_usesOnly
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    PaperCircuitUsesOnly registers.allWires
      (intervalAddSubUnitary registers n k K mode signUpdate target) := by
  have hprepare := (prepareIntervalEndpoints_usesOnly registers.lengthT
    registers.lengthQ registers.lengthS registers.endpointScratch
    (registers.carry k K) n k).mono
      (intervalEndpointSupport_mem_allWires registers k K target hlayout)
  have hrestore := (restoreIntervalEndpoints_usesOnly registers.lengthT
    registers.lengthQ registers.lengthS registers.endpointScratch
    (registers.carry k K) n k).mono
      (intervalEndpointSupport_mem_allWires registers k K target hlayout)
  have htopFirst := intervalTopFirst_usesOnly registers k K mode target hlayout
  have hfirst := intervalTraversal_usesOnly false registers k K mode target hlayout
  have hsign := intervalSignUpdate_usesOnly registers k K signUpdate target hlayout
  have hsecond := intervalTraversal_usesOnly true registers k K mode target hlayout
  have htopSecond := intervalTopSecond_usesOnly registers k K mode target hlayout
  simp only [intervalAddSubUnitary]
  exact PaperCircuitUsesOnly.append
    (PaperCircuitUsesOnly.append
      (PaperCircuitUsesOnly.append
        (PaperCircuitUsesOnly.append
          (PaperCircuitUsesOnly.append
            (PaperCircuitUsesOnly.append hprepare htopFirst) hfirst) hsign)
          hsecond) htopSecond) hrestore

/-- Every basis wire outside the physical interval record is unchanged. -/
theorem intervalAddSubUnitary_preservesOutside
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) (state : BasisState)
    (hlayout : IntervalLayout registers k K target)
    {wire : Wire} (hwire : wire ∉ registers.allWires) :
    run (intervalAddSubUnitary registers n k K mode signUpdate target) state wire =
      state wire :=
  PaperCircuitUsesOnly.preservesOutside
    (intervalAddSubUnitary_usesOnly registers n k K mode signUpdate target hlayout)
    state hwire

/-! ## Direct basis semantics -/

/-- Gate-independent state action of the separately handled first top lane. -/
def intervalTopFirstState
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (state : BasisState) : BasisState :=
  if intervalHasTopSpecial k K then
    topSpecialFirstLeafState mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) registers.control registers.control state
  else state

/-- Gate-independent state action of the separately handled second top lane. -/
def intervalTopSecondState
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (state : BasisState) : BasisState :=
  if intervalHasTopSpecial k K then
    topSpecialSecondLeafState mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) registers.control registers.control state
  else state

/-- Direct state action of the optional sign update between the two traversals. -/
def intervalSignUpdateState
    (registers : IntervalRegisters) (k K : Nat) (signUpdate : Bool)
    (state : BasisState) : BasisState :=
  if signUpdate then
    state[registers.sign ↦ Bool.xor (state registers.sign) (state (registers.carry k K))]
  else state

private theorem intervalPrepare_cleanScratch
    (registers : IntervalRegisters) (n k K : Nat) (target : IntervalTarget)
    (state : BasisState) (hlayout : IntervalLayout registers k K target)
    (hready : IntervalReady registers state) :
    Clean registers.scratch
      (run (prepareIntervalEndpoints registers.lengthT registers.lengthQ registers.lengthS
        registers.endpointScratch (registers.carry k K) n k) state) := by
  have hcleanEndpoint : Clean
      (registers.endpointScratch ++ [registers.carry k K]) state := by
    intro wire hwire
    apply hready wire
    rcases List.mem_append.mp hwire with hscratch | hcarry
    · exact List.mem_of_mem_take hscratch
    · simp only [List.mem_singleton] at hcarry
      subst wire
      exact intervalCarry_mem_scratch registers k K target hlayout
  have hcorrect := prepareIntervalEndpoints_correct registers.lengthT registers.lengthQ
    registers.lengthS registers.endpointScratch (registers.carry k K) n k state
    hlayout.lengthT_eq_lengthQ
    (intervalLengthQ_le_endpointScratch registers k K target hlayout)
    (intervalLengthS_le_endpointScratch registers k K target hlayout)
    (intervalLengthS_positive registers k K target hlayout) hlayout.endpoints hcleanEndpoint
  intro wire hwire
  rw [hcorrect.2.2.2.2 wire
    (intervalScratch_not_mem_lengthQ registers k K target hlayout hwire)
    (intervalScratch_not_mem_lengthS registers k K target hlayout hwire)]
  exact hready wire hwire

private theorem run_intervalTopFirst_state
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (state : BasisState)
    (hlayout : IntervalLayout registers k K target)
    (hclean : Clean
      (registers.cellScratch k K :: registers.equalityScratch k K) state) :
    run (intervalTopFirst registers k K mode target) state =
      intervalTopFirstState registers k K mode target state := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopFirst, if_pos hspecial,
      intervalTopFirstState, if_pos hspecial]
    exact run_topSpecialFirstLeaf mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control state (hlayout.topSpecial hspecial) hclean
  · simp [intervalTopFirst, intervalTopFirstState, hspecial]

private theorem run_intervalTopSecond_state
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (state : BasisState)
    (hlayout : IntervalLayout registers k K target)
    (hclean : intervalHasTopSpecial k K = true → Clean
      (registers.cellScratch k K :: registers.equalityScratch k K) state) :
    run (intervalTopSecond registers k K mode target) state =
      intervalTopSecondState registers k K mode target state := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopSecond, if_pos hspecial,
      intervalTopSecondState, if_pos hspecial]
    exact run_topSpecialSecondLeaf mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control state (hlayout.topSpecial hspecial) (hclean hspecial)
  · simp [intervalTopSecond, intervalTopSecondState, hspecial]

private theorem intervalTopFirst_cleanTopScratch
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (state : BasisState)
    (hlayout : IntervalLayout registers k K target)
    (hclean : Clean
      (registers.cellScratch k K :: registers.equalityScratch k K) state) :
    Clean (registers.cellScratch k K :: registers.equalityScratch k K)
      (run (intervalTopFirst registers k K mode target) state) := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopFirst, if_pos hspecial]
    exact topSpecialFirstLeaf_clean mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control state (hlayout.topSpecial hspecial) hclean
  · simpa [intervalTopFirst, hspecial] using hclean

private theorem run_intervalSignUpdate_state
    (registers : IntervalRegisters) (k K : Nat) (signUpdate : Bool)
    (state : BasisState) :
    run (intervalSignUpdate registers k K signUpdate) state =
      intervalSignUpdateState registers k K signUpdate state := by
  cases signUpdate <;> rfl

private theorem intervalSignUpdate_preservesScratch
    (registers : IntervalRegisters) (k K : Nat) (signUpdate : Bool)
    (target : IntervalTarget) (state : BasisState)
    (hlayout : IntervalLayout registers k K target) :
    ∀ wire, wire ∈ registers.scratch →
      run (intervalSignUpdate registers k K signUpdate) state wire = state wire := by
  intro wire hwire
  have hne := intervalScratch_ne_sign registers k K target hlayout hwire
  cases signUpdate with
  | false => rfl
  | true =>
      simp [intervalSignUpdate, Classical.run, Classical.applyGate,
        upd_other _ _ _ hne]

private theorem intervalPaths_clean_of_topScratch
    (registers : IntervalRegisters) (k K : Nat) (state : BasisState)
    (hclean : Clean
      (registers.cellScratch k K :: registers.equalityScratch k K) state) :
    Clean (registers.rightPaths k K) state ∧ Clean (registers.leftPaths k K) state := by
  constructor
  · intro wire hwire
    exact hclean wire (List.mem_cons_of_mem _
      (intervalRightPaths_mem_equalityScratch registers k K wire hwire))
  · intro wire hwire
    exact hclean wire (List.mem_cons_of_mem _
      (intervalLeftPaths_mem_equalityScratch registers k K wire hwire))

/-- Complete direct state action of the forward source interval.  Endpoint transforms remain
bound to their already-certified circuit actions; the top lane, both ordered tree traversals, and
the intervening sign update are exposed as gate-independent state transformers. -/
def intervalAddSubState
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) (state : BasisState) : BasisState :=
  let prepared := run
    (prepareIntervalEndpoints registers.lengthT registers.lengthQ registers.lengthS
      registers.endpointScratch (registers.carry k K) n k) state
  let afterTopFirst := intervalTopFirstState registers k K mode target prepared
  let afterFirst := intervalFirstTraversalState mode (intervalHasTopSpecial k K)
    (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
    (registers.carry k K) (registers.cellScratch k K)
    (registers.targetAt target) (registers.addendAt target)
    (intervalTree registers k K) registers.control registers.control
    (registers.rightPaths k K) (registers.leftPaths k K) afterTopFirst
  let afterSign := intervalSignUpdateState registers k K signUpdate afterFirst
  let afterSecond := intervalSecondTraversalState mode (intervalHasTopSpecial k K)
    (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
    (registers.carry k K) (registers.cellScratch k K)
    (registers.targetAt target) (registers.addendAt target)
    (intervalTree registers k K) registers.control registers.control
    (registers.rightPaths k K) (registers.leftPaths k K) afterSign
  let afterTopSecond := intervalTopSecondState registers k K mode target afterSecond
  run (restoreIntervalEndpoints registers.lengthT registers.lengthQ registers.lengthS
    registers.endpointScratch (registers.carry k K) n k) afterTopSecond

/-- The literal coherent interval has the direct source-ordered basis semantics above. -/
theorem run_intervalAddSubUnitary_state
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) (state : BasisState)
    (hlayout : IntervalLayout registers k K target)
    (hready : IntervalReady registers state) :
    run (intervalAddSubUnitary registers n k K mode signUpdate target) state =
      intervalAddSubState registers n k K mode signUpdate target state := by
  let prepared := run
    (prepareIntervalEndpoints registers.lengthT registers.lengthQ registers.lengthS
      registers.endpointScratch (registers.carry k K) n k) state
  have hpreparedScratch : Clean registers.scratch prepared := by
    exact intervalPrepare_cleanScratch registers n k K target state hlayout hready
  have hpreparedTop : Clean
      (registers.cellScratch k K :: registers.equalityScratch k K) prepared := by
    intro wire hwire
    exact hpreparedScratch wire
      (intervalTopScratch_mem_scratch registers k K target hlayout wire hwire)
  let afterTopFirst := run (intervalTopFirst registers k K mode target) prepared
  have htopFirstRun : afterTopFirst =
      intervalTopFirstState registers k K mode target prepared := by
    exact run_intervalTopFirst_state registers k K mode target prepared hlayout hpreparedTop
  have htopFirstClean : Clean
      (registers.cellScratch k K :: registers.equalityScratch k K) afterTopFirst := by
    exact intervalTopFirst_cleanTopScratch registers k K mode target prepared hlayout hpreparedTop
  have htopFirstPaths := intervalPaths_clean_of_topScratch registers k K
    afterTopFirst htopFirstClean
  let afterFirst := run
    (intervalFirstTraversal mode (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K)
      (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K)) afterTopFirst
  have hfirstRun : afterFirst =
      intervalFirstTraversalState mode (intervalHasTopSpecial k K)
        (registers.rightTop k K) (registers.leftTop k K)
        (registers.accumulator k K) (registers.carry k K)
        (registers.cellScratch k K) (registers.targetAt target)
        (registers.addendAt target) (intervalTree registers k K)
        registers.control registers.control (registers.rightPaths k K)
        (registers.leftPaths k K) afterTopFirst := by
    exact run_intervalFirstTraversal_state mode (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K)
      (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K) afterTopFirst
      hlayout.traversal htopFirstPaths.1 htopFirstPaths.2
  have hfirstPaths : Clean (registers.rightPaths k K) afterFirst ∧
      Clean (registers.leftPaths k K) afterFirst := by
    exact intervalFirstTraversal_clean mode (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K)
      (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K) afterTopFirst
      hlayout.traversal htopFirstPaths.1 htopFirstPaths.2
  have hfirstTop : intervalHasTopSpecial k K = true → Clean
      (registers.cellScratch k K :: registers.equalityScratch k K) afterFirst := by
    intro hspecial wire hwire
    rw [show afterFirst wire = afterTopFirst wire by
      exact intervalTraversal_preservesTopScratch false registers k K mode target
        hlayout hspecial afterTopFirst htopFirstPaths.1 htopFirstPaths.2 wire hwire]
    exact htopFirstClean wire hwire
  let afterSign := run (intervalSignUpdate registers k K signUpdate) afterFirst
  have hsignRun : afterSign =
      intervalSignUpdateState registers k K signUpdate afterFirst :=
    run_intervalSignUpdate_state registers k K signUpdate afterFirst
  have hsignPaths : Clean (registers.rightPaths k K) afterSign ∧
      Clean (registers.leftPaths k K) afterSign := by
    constructor
    · intro wire hwire
      rw [show afterSign wire = afterFirst wire by
        exact intervalSignUpdate_preservesScratch registers k K signUpdate target
          afterFirst hlayout wire
          (intervalTopScratch_mem_scratch registers k K target hlayout wire
            (List.mem_cons_of_mem _
              (intervalRightPaths_mem_equalityScratch registers k K wire hwire)))]
      exact hfirstPaths.1 wire hwire
    · intro wire hwire
      rw [show afterSign wire = afterFirst wire by
        exact intervalSignUpdate_preservesScratch registers k K signUpdate target
          afterFirst hlayout wire
          (intervalTopScratch_mem_scratch registers k K target hlayout wire
            (List.mem_cons_of_mem _
              (intervalLeftPaths_mem_equalityScratch registers k K wire hwire)))]
      exact hfirstPaths.2 wire hwire
  have hsignTop : intervalHasTopSpecial k K = true → Clean
      (registers.cellScratch k K :: registers.equalityScratch k K) afterSign := by
    intro hspecial wire hwire
    rw [show afterSign wire = afterFirst wire by
      exact intervalSignUpdate_preservesScratch registers k K signUpdate target
        afterFirst hlayout wire
        (intervalTopScratch_mem_scratch registers k K target hlayout wire hwire)]
    exact hfirstTop hspecial wire hwire
  let afterSecond := run
    (intervalSecondTraversal mode (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K)
      (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K)) afterSign
  have hsecondRun : afterSecond =
      intervalSecondTraversalState mode (intervalHasTopSpecial k K)
        (registers.rightTop k K) (registers.leftTop k K)
        (registers.accumulator k K) (registers.carry k K)
        (registers.cellScratch k K) (registers.targetAt target)
        (registers.addendAt target) (intervalTree registers k K)
        registers.control registers.control (registers.rightPaths k K)
        (registers.leftPaths k K) afterSign := by
    exact run_intervalSecondTraversal_state mode (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K)
      (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K) afterSign
      hlayout.traversal hsignPaths.1 hsignPaths.2
  have hsecondTop : intervalHasTopSpecial k K = true → Clean
      (registers.cellScratch k K :: registers.equalityScratch k K) afterSecond := by
    intro hspecial wire hwire
    rw [show afterSecond wire = afterSign wire by
      exact intervalTraversal_preservesTopScratch true registers k K mode target
        hlayout hspecial afterSign hsignPaths.1 hsignPaths.2 wire hwire]
    exact hsignTop hspecial wire hwire
  have htopSecondRun := run_intervalTopSecond_state registers k K mode target
    afterSecond hlayout hsecondTop
  rw [intervalAddSubUnitary]
  simp only [Classical.run_append]
  change run
      (restoreIntervalEndpoints registers.lengthT registers.lengthQ registers.lengthS
        registers.endpointScratch (registers.carry k K) n k)
      (run (intervalTopSecond registers k K mode target) afterSecond) = _
  rw [htopSecondRun, hsecondRun, hsignRun, hfirstRun, htopFirstRun]
  rfl

/-- Measurement-uncomputed realization of `intervalAddSubUnitary`. -/
def intervalAddSub
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) : Quantum.AdaptiveCircuit :=
  (Quantum.AdaptiveCircuit.unitary
      (prepareIntervalEndpoints registers.lengthT registers.lengthQ registers.lengthS
        registers.endpointScratch (registers.carry k K) n k) .done).seq
    ((intervalTopFirstAdaptive registers k K mode target).seq
      ((intervalFirstTraversalAdaptive mode (intervalHasTopSpecial k K)
          (registers.rightTop k K) (registers.leftTop k K)
          (registers.accumulator k K) (registers.carry k K)
          (registers.cellScratch k K) (registers.targetAt target)
          (registers.addendAt target) (intervalTree registers k K)
          registers.control registers.control (registers.rightPaths k K)
          (registers.leftPaths k K)).seq
        ((Quantum.AdaptiveCircuit.unitary
            (intervalSignUpdate registers k K signUpdate) .done).seq
          ((intervalSecondTraversalAdaptive mode (intervalHasTopSpecial k K)
              (registers.rightTop k K) (registers.leftTop k K)
              (registers.accumulator k K) (registers.carry k K)
              (registers.cellScratch k K) (registers.targetAt target)
              (registers.addendAt target) (intervalTree registers k K)
              registers.control registers.control (registers.rightPaths k K)
              (registers.leftPaths k K)).seq
            ((intervalTopSecondAdaptive registers k K mode target).seq
              (Quantum.AdaptiveCircuit.unitary
                (restoreIntervalEndpoints registers.lengthT registers.lengthQ
                  registers.lengthS registers.endpointScratch
                  (registers.carry k K) n k) .done))))))

@[simp]
theorem intervalAddSubUnitary_HPFree
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) :
    HPFree (intervalAddSubUnitary registers n k K mode signUpdate target) := by
  simp only [intervalAddSubUnitary, hpFree_append,
    prepareIntervalEndpoints_HPFree, restoreIntervalEndpoints_HPFree,
    intervalFirstTraversal_HPFree, intervalSecondTraversal_HPFree]
  by_cases hspecial : intervalHasTopSpecial k K = true <;>
    by_cases hsign : signUpdate = true <;>
      simp [intervalTopFirst, intervalTopSecond, intervalSignUpdate,
        hspecial, hsign]

private theorem intervalTopFirst_wellFormed
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target) :
    CircuitWellFormed (intervalTopFirst registers k K mode target) := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopFirst, if_pos hspecial]
    exact topSpecialFirstLeaf_wellFormed mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control (hlayout.topSpecial hspecial)
  · simp [intervalTopFirst, hspecial]

private theorem intervalTopSecond_wellFormed
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target) :
    CircuitWellFormed (intervalTopSecond registers k K mode target) := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopSecond, if_pos hspecial]
    exact topSpecialSecondLeaf_wellFormed mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control (hlayout.topSpecial hspecial)
  · simp [intervalTopSecond, hspecial]

private theorem intervalTopFirstAdaptive_wellFormed
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target) :
    (intervalTopFirstAdaptive registers k K mode target).WellFormed := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopFirstAdaptive, if_pos hspecial]
    exact topSpecialFirstLeafAdaptive_wellFormed mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control (hlayout.topSpecial hspecial)
  · simp [intervalTopFirstAdaptive, hspecial,
      Quantum.AdaptiveCircuit.WellFormed]

private theorem intervalTopSecondAdaptive_wellFormed
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target) :
    (intervalTopSecondAdaptive registers k K mode target).WellFormed := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopSecondAdaptive, if_pos hspecial]
    exact topSpecialSecondLeafAdaptive_wellFormed mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control (hlayout.topSpecial hspecial)
  · simp [intervalTopSecondAdaptive, hspecial,
      Quantum.AdaptiveCircuit.WellFormed]

private theorem intervalSignUpdate_wellFormed
    (registers : IntervalRegisters) (k K : Nat) (signUpdate : Bool)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target) :
    CircuitWellFormed (intervalSignUpdate registers k K signUpdate) := by
  by_cases hsign : signUpdate = true
  · simp [intervalSignUpdate, hsign, Gate.WellFormed,
      intervalCarry_ne_sign registers k K target hlayout]
  · simp [intervalSignUpdate, hsign]

theorem intervalAddSubUnitary_wellFormed
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    CircuitWellFormed
      (intervalAddSubUnitary registers n k K mode signUpdate target) := by
  simp only [intervalAddSubUnitary, circuitWellFormed_append]
  refine ⟨⟨⟨⟨⟨⟨
    prepareIntervalEndpoints_wellFormed registers.lengthT registers.lengthQ
      registers.lengthS registers.endpointScratch (registers.carry k K) n k
      hlayout.lengthT_eq_lengthQ
      (intervalLengthQ_le_endpointScratch registers k K target hlayout)
      (intervalLengthS_le_endpointScratch registers k K target hlayout)
      hlayout.endpoints,
    intervalTopFirst_wellFormed registers k K mode target hlayout⟩,
    intervalFirstTraversal_wellFormed mode (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K)
      (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K) hlayout.traversal⟩,
    intervalSignUpdate_wellFormed registers k K signUpdate target hlayout⟩,
    intervalSecondTraversal_wellFormed mode (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K)
      (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K) hlayout.traversal⟩,
    intervalTopSecond_wellFormed registers k K mode target hlayout⟩,
    restoreIntervalEndpoints_wellFormed registers.lengthT registers.lengthQ
      registers.lengthS registers.endpointScratch (registers.carry k K) n k
      hlayout.lengthT_eq_lengthQ
      (intervalLengthQ_le_endpointScratch registers k K target hlayout)
      (intervalLengthS_le_endpointScratch registers k K target hlayout)
      hlayout.endpoints⟩

theorem intervalAddSub_wellFormed
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    (intervalAddSub registers n k K mode signUpdate target).WellFormed := by
  rw [intervalAddSub]
  apply Quantum.AdaptiveCircuit.WellFormed.seq
  · exact ⟨prepareIntervalEndpoints_wellFormed registers.lengthT registers.lengthQ
        registers.lengthS registers.endpointScratch (registers.carry k K) n k
        hlayout.lengthT_eq_lengthQ
        (intervalLengthQ_le_endpointScratch registers k K target hlayout)
        (intervalLengthS_le_endpointScratch registers k K target hlayout)
        hlayout.endpoints, trivial⟩
  · apply Quantum.AdaptiveCircuit.WellFormed.seq
    · exact intervalTopFirstAdaptive_wellFormed registers k K mode target hlayout
    · apply Quantum.AdaptiveCircuit.WellFormed.seq
      · exact intervalFirstTraversalAdaptive_wellFormed mode
          (intervalHasTopSpecial k K) (registers.rightTop k K)
          (registers.leftTop k K) (registers.accumulator k K)
          (registers.carry k K) (registers.cellScratch k K)
          (registers.targetAt target) (registers.addendAt target)
          (intervalTree registers k K) registers.control registers.control
          (registers.rightPaths k K) (registers.leftPaths k K) hlayout.traversal
      · apply Quantum.AdaptiveCircuit.WellFormed.seq
        · exact ⟨intervalSignUpdate_wellFormed registers k K signUpdate target hlayout,
            trivial⟩
        · apply Quantum.AdaptiveCircuit.WellFormed.seq
          · exact intervalSecondTraversalAdaptive_wellFormed mode
              (intervalHasTopSpecial k K) (registers.rightTop k K)
              (registers.leftTop k K) (registers.accumulator k K)
              (registers.carry k K) (registers.cellScratch k K)
              (registers.targetAt target) (registers.addendAt target)
              (intervalTree registers k K) registers.control registers.control
              (registers.rightPaths k K) (registers.leftPaths k K) hlayout.traversal
          · apply Quantum.AdaptiveCircuit.WellFormed.seq
            · exact intervalTopSecondAdaptive_wellFormed registers k K mode target hlayout
            · exact ⟨restoreIntervalEndpoints_wellFormed registers.lengthT
                  registers.lengthQ registers.lengthS registers.endpointScratch
                  (registers.carry k K) n k hlayout.lengthT_eq_lengthQ
                  (intervalLengthQ_le_endpointScratch registers k K target hlayout)
                  (intervalLengthS_le_endpointScratch registers k K target hlayout)
                  hlayout.endpoints,
                trivial⟩

private theorem interval_coherent_seq_circuits
    {first second : Quantum.AdaptiveCircuit}
    {firstCircuit secondCircuit : Circuit}
    {FirstValid SecondValid : BasisState → Prop}
    (hfirst : CoherentlyImplementsOn first
      (Quantum.run firstCircuit) FirstValid)
    (hsecond : CoherentlyImplementsOn second
      (Quantum.run secondCircuit) SecondValid)
    (hfirstClassical : HPFree firstCircuit)
    (hvalid : ∀ state, FirstValid state →
      SecondValid (run firstCircuit state)) :
    CoherentlyImplementsOn (first.seq second)
      (Quantum.run (firstCircuit ++ secondCircuit)) FirstValid := by
  have hseq := hfirst.seq hsecond (by
    intro state hstate
    rw [run_ket_agrees_classical firstCircuit state hfirstClassical]
    exact supportedOn_ket SecondValid _ (hvalid state hstate))
  apply hseq.congrIdeal
  intro state _
  exact (Quantum.run_append firstCircuit secondCircuit (ket state)).symm

private theorem interval_coherent_strengthen
    {program : Quantum.AdaptiveCircuit} {ideal : State →ₗ[ℂ] State}
    {Valid Stronger : BasisState → Prop}
    (hrefines : CoherentlyImplementsOn program ideal Valid)
    (hsub : ∀ state, Stronger state → Valid state) :
    CoherentlyImplementsOn program ideal Stronger := by
  rcases hrefines with ⟨coefficients, haligned, hmass⟩
  refine ⟨coefficients, ?_, hmass⟩
  exact haligned.imp fun branch coefficient hbranch state hstate ↦
    hbranch state (hsub state hstate)

private theorem intervalTopFirstAdaptive_coherent
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target) :
    CoherentlyImplementsOn
      (intervalTopFirstAdaptive registers k K mode target)
      (Quantum.run (intervalTopFirst registers k K mode target))
      (fun state ↦ intervalHasTopSpecial k K = true →
        Clean (registers.cellScratch k K :: registers.equalityScratch k K) state) := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · simpa [intervalTopFirstAdaptive, intervalTopFirst, hspecial] using
      topSpecialFirstLeafAdaptive_coherent mode (intervalTopRelative k K)
        registers.lengthS registers.lengthQ (registers.accumulator k K)
        (registers.targetAt target (intervalTopRelative k K))
        (registers.addendAt target (intervalTopRelative k K))
        (registers.carry k K) (registers.cellScratch k K)
        (registers.cellScratch k K) (registers.equalityScratch k K)
        registers.control registers.control (hlayout.topSpecial hspecial)
  · simpa [intervalTopFirstAdaptive, intervalTopFirst, hspecial] using
      CoherentlyImplementsOn.unitary ([] : Circuit)
        (fun state ↦ intervalHasTopSpecial k K = true →
          Clean (registers.cellScratch k K :: registers.equalityScratch k K) state)

private theorem intervalTopSecondAdaptive_coherent
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target) :
    CoherentlyImplementsOn
      (intervalTopSecondAdaptive registers k K mode target)
      (Quantum.run (intervalTopSecond registers k K mode target))
      (fun state ↦ intervalHasTopSpecial k K = true →
        Clean (registers.cellScratch k K :: registers.equalityScratch k K) state) := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · simpa [intervalTopSecondAdaptive, intervalTopSecond, hspecial] using
      topSpecialSecondLeafAdaptive_coherent mode (intervalTopRelative k K)
        registers.lengthS registers.lengthQ (registers.accumulator k K)
        (registers.targetAt target (intervalTopRelative k K))
        (registers.addendAt target (intervalTopRelative k K))
        (registers.carry k K) (registers.cellScratch k K)
        (registers.cellScratch k K) (registers.equalityScratch k K)
        registers.control registers.control (hlayout.topSpecial hspecial)
  · simpa [intervalTopSecondAdaptive, intervalTopSecond, hspecial] using
      CoherentlyImplementsOn.unitary ([] : Circuit)
        (fun state ↦ intervalHasTopSpecial k K = true →
          Clean (registers.cellScratch k K :: registers.equalityScratch k K) state)

/-- Replacing the reverse decoder ANDs by X-measure/reset preserves the complete interval's
coherent action on every basis input with clean shared scratch. -/
theorem intervalAddSub_coherent
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    CoherentlyImplementsOn
      (intervalAddSub registers n k K mode signUpdate target)
      (Quantum.run (intervalAddSubUnitary registers n k K mode signUpdate target))
      (IntervalReady registers) := by
  let Valid : BasisState → Prop := fun state ↦
    Clean (registers.rightPaths k K) state ∧
      Clean (registers.leftPaths k K) state ∧
      Clean [registers.cellScratch k K] state ∧
      (intervalHasTopSpecial k K = true →
        Clean (registers.cellScratch k K :: registers.equalityScratch k K) state)
  let prepareCircuit :=
    prepareIntervalEndpoints registers.lengthT registers.lengthQ registers.lengthS
      registers.endpointScratch (registers.carry k K) n k
  let topFirstCircuit := intervalTopFirst registers k K mode target
  let firstCircuit := intervalFirstTraversal mode (intervalHasTopSpecial k K)
    (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
    (registers.carry k K) (registers.cellScratch k K)
    (registers.targetAt target) (registers.addendAt target)
    (intervalTree registers k K) registers.control registers.control
    (registers.rightPaths k K) (registers.leftPaths k K)
  let signCircuit := intervalSignUpdate registers k K signUpdate
  let secondCircuit := intervalSecondTraversal mode (intervalHasTopSpecial k K)
    (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
    (registers.carry k K) (registers.cellScratch k K)
    (registers.targetAt target) (registers.addendAt target)
    (intervalTree registers k K) registers.control registers.control
    (registers.rightPaths k K) (registers.leftPaths k K)
  let topSecondCircuit := intervalTopSecond registers k K mode target
  let restoreCircuit :=
    restoreIntervalEndpoints registers.lengthT registers.lengthQ registers.lengthS
      registers.endpointScratch (registers.carry k K) n k
  have hprepare : CoherentlyImplementsOn
      (.unitary prepareCircuit .done) (Quantum.run prepareCircuit)
      (IntervalReady registers) :=
    CoherentlyImplementsOn.unitary prepareCircuit (IntervalReady registers)
  have htopFirst : CoherentlyImplementsOn
      (intervalTopFirstAdaptive registers k K mode target)
      (Quantum.run topFirstCircuit) Valid := by
    apply interval_coherent_strengthen
      (intervalTopFirstAdaptive_coherent registers k K mode target hlayout)
    intro state hvalid
    exact hvalid.2.2.2
  have hfirst : CoherentlyImplementsOn
      (intervalFirstTraversalAdaptive mode (intervalHasTopSpecial k K)
        (registers.rightTop k K) (registers.leftTop k K)
        (registers.accumulator k K) (registers.carry k K)
        (registers.cellScratch k K) (registers.targetAt target)
        (registers.addendAt target) (intervalTree registers k K)
        registers.control registers.control (registers.rightPaths k K)
        (registers.leftPaths k K)) (Quantum.run firstCircuit) Valid := by
    apply interval_coherent_strengthen
      (intervalFirstTraversal_coherent mode (intervalHasTopSpecial k K)
        (registers.rightTop k K) (registers.leftTop k K)
        (registers.accumulator k K) (registers.carry k K)
        (registers.cellScratch k K) (registers.targetAt target)
        (registers.addendAt target) (intervalTree registers k K)
        registers.control registers.control (registers.rightPaths k K)
        (registers.leftPaths k K) hlayout.traversal)
    intro state hvalid
    exact ⟨hvalid.1, hvalid.2.1, hvalid.2.2.1⟩
  have hsign : CoherentlyImplementsOn
      (.unitary signCircuit .done) (Quantum.run signCircuit) Valid :=
    CoherentlyImplementsOn.unitary signCircuit Valid
  have hsecond : CoherentlyImplementsOn
      (intervalSecondTraversalAdaptive mode (intervalHasTopSpecial k K)
        (registers.rightTop k K) (registers.leftTop k K)
        (registers.accumulator k K) (registers.carry k K)
        (registers.cellScratch k K) (registers.targetAt target)
        (registers.addendAt target) (intervalTree registers k K)
        registers.control registers.control (registers.rightPaths k K)
        (registers.leftPaths k K)) (Quantum.run secondCircuit) Valid := by
    apply interval_coherent_strengthen
      (intervalSecondTraversal_coherent mode (intervalHasTopSpecial k K)
        (registers.rightTop k K) (registers.leftTop k K)
        (registers.accumulator k K) (registers.carry k K)
        (registers.cellScratch k K) (registers.targetAt target)
        (registers.addendAt target) (intervalTree registers k K)
        registers.control registers.control (registers.rightPaths k K)
        (registers.leftPaths k K) hlayout.traversal)
    intro state hvalid
    exact ⟨hvalid.1, hvalid.2.1, hvalid.2.2.1⟩
  have htopSecond : CoherentlyImplementsOn
      (intervalTopSecondAdaptive registers k K mode target)
      (Quantum.run topSecondCircuit) Valid := by
    apply interval_coherent_strengthen
      (intervalTopSecondAdaptive_coherent registers k K mode target hlayout)
    intro state hvalid
    exact hvalid.2.2.2
  have hrestore : CoherentlyImplementsOn
      (.unitary restoreCircuit .done) (Quantum.run restoreCircuit) (fun _ ↦ True) :=
    CoherentlyImplementsOn.unitary restoreCircuit (fun _ ↦ True)
  have hprepareClassical : HPFree prepareCircuit := by simp [prepareCircuit]
  have htopFirstClassical : HPFree topFirstCircuit := by
    by_cases hspecial : intervalHasTopSpecial k K = true <;>
      simp [topFirstCircuit, intervalTopFirst, hspecial]
  have hfirstClassical : HPFree firstCircuit := by
    simp [firstCircuit]
  have hsignClassical : HPFree signCircuit := by
    by_cases hsign : signUpdate = true <;>
      simp [signCircuit, intervalSignUpdate, hsign]
  have hsecondClassical : HPFree secondCircuit := by
    simp [secondCircuit]
  have htopSecondClassical : HPFree topSecondCircuit := by
    by_cases hspecial : intervalHasTopSpecial k K = true <;>
      simp [topSecondCircuit, intervalTopSecond, hspecial]
  have hprepareValid : ∀ state, IntervalReady registers state →
      Valid (run prepareCircuit state) := by
    intro state hready
    have hpreparedScratch : Clean registers.scratch (run prepareCircuit state) := by
      simpa only [prepareCircuit] using
      intervalPrepare_cleanScratch registers n k K target state hlayout hready
    have hpreparedTop : Clean
        (registers.cellScratch k K :: registers.equalityScratch k K)
          (run prepareCircuit state) := by
      intro wire hwire
      exact hpreparedScratch wire
        (intervalTopScratch_mem_scratch registers k K target hlayout wire hwire)
    have hpaths := intervalPaths_clean_of_topScratch registers k K
      (run prepareCircuit state) hpreparedTop
    refine ⟨hpaths.1, hpaths.2, ?_, fun _ ↦ hpreparedTop⟩
    intro wire hwire
    have hwireEq : wire = registers.cellScratch k K := by simpa using hwire
    subst wire
    exact hpreparedTop _ (by simp)
  have htopFirstValid : ∀ state, Valid state →
      Valid (run topFirstCircuit state) := by
    intro state hvalid
    by_cases hspecial : intervalHasTopSpecial k K = true
    · have htopClean := intervalTopFirst_cleanTopScratch registers k K mode target
        state hlayout (hvalid.2.2.2 hspecial)
      have hpaths := intervalPaths_clean_of_topScratch registers k K
        (run topFirstCircuit state) htopClean
      refine ⟨hpaths.1, hpaths.2, ?_, fun _ ↦ htopClean⟩
      intro wire hwire
      have hwireEq : wire = registers.cellScratch k K := by simpa using hwire
      subst wire
      exact htopClean _ (by simp)
    · simpa [topFirstCircuit, intervalTopFirst, hspecial] using hvalid
  have hfirstValid : ∀ state, Valid state → Valid (run firstCircuit state) := by
    intro state hstate
    have hclean := intervalFirstTraversal_cleanWithScratch mode
      (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K)
      (registers.accumulator k K) (registers.carry k K)
      (registers.cellScratch k K) (registers.targetAt target)
      (registers.addendAt target) (intervalTree registers k K)
      registers.control registers.control (registers.rightPaths k K)
      (registers.leftPaths k K) state hlayout.traversal hstate.1 hstate.2.1
      hstate.2.2.1
    refine ⟨hclean.1, hclean.2.1, hclean.2.2, ?_⟩
    intro hspecial wire hwire
    rw [show run firstCircuit state wire = state wire by
      simpa only [firstCircuit] using
        intervalTraversal_preservesTopScratch false registers k K mode target
          hlayout hspecial state hstate.1 hstate.2.1 wire hwire]
    exact hstate.2.2.2 hspecial wire hwire
  have hsignValid : ∀ state, Valid state → Valid (run signCircuit state) := by
    intro state hstate
    have hpreserves : ∀ wire, wire ∈ registers.scratch →
        run signCircuit state wire = state wire := by
      intro wire hwire
      simpa only [signCircuit] using
        intervalSignUpdate_preservesScratch registers k K signUpdate target state
          hlayout wire hwire
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro wire hwire
      rw [hpreserves wire (intervalTopScratch_mem_scratch registers k K target
        hlayout wire (List.mem_cons_of_mem _
          (intervalRightPaths_mem_equalityScratch registers k K wire hwire)))]
      exact hstate.1 wire hwire
    · intro wire hwire
      rw [hpreserves wire (intervalTopScratch_mem_scratch registers k K target
        hlayout wire (List.mem_cons_of_mem _
          (intervalLeftPaths_mem_equalityScratch registers k K wire hwire)))]
      exact hstate.2.1 wire hwire
    · intro wire hwire
      have hwireEq : wire = registers.cellScratch k K := by simpa using hwire
      subst wire
      rw [hpreserves _ (intervalTopScratch_mem_scratch registers k K target
        hlayout _ (by simp))]
      exact hstate.2.2.1 _ (by simp)
    · intro hspecial wire hwire
      rw [hpreserves wire
        (intervalTopScratch_mem_scratch registers k K target hlayout wire hwire)]
      exact hstate.2.2.2 hspecial wire hwire
  have hsecondValid : ∀ state, Valid state → Valid (run secondCircuit state) := by
    intro state hstate
    have hclean := intervalSecondTraversal_cleanWithScratch mode
      (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K)
      (registers.accumulator k K) (registers.carry k K)
      (registers.cellScratch k K) (registers.targetAt target)
      (registers.addendAt target) (intervalTree registers k K)
      registers.control registers.control (registers.rightPaths k K)
      (registers.leftPaths k K) state hlayout.traversal hstate.1 hstate.2.1
      hstate.2.2.1
    refine ⟨hclean.1, hclean.2.1, hclean.2.2, ?_⟩
    intro hspecial wire hwire
    rw [show run secondCircuit state wire = state wire by
      simpa only [secondCircuit] using
        intervalTraversal_preservesTopScratch true registers k K mode target
          hlayout hspecial state hstate.1 hstate.2.1 wire hwire]
    exact hstate.2.2.2 hspecial wire hwire
  have htopSecondTail := interval_coherent_seq_circuits htopSecond hrestore
    htopSecondClassical (fun _ _ ↦ trivial)
  have hsecondTail := interval_coherent_seq_circuits hsecond htopSecondTail
    hsecondClassical hsecondValid
  have hsignTail := interval_coherent_seq_circuits hsign hsecondTail
    hsignClassical hsignValid
  have hfirstTail := interval_coherent_seq_circuits hfirst hsignTail
    hfirstClassical hfirstValid
  have htopFirstTail := interval_coherent_seq_circuits htopFirst hfirstTail
    htopFirstClassical htopFirstValid
  have hall := interval_coherent_seq_circuits hprepare htopFirstTail
    hprepareClassical hprepareValid
  simpa only [intervalAddSub, intervalAddSubUnitary, prepareCircuit, topFirstCircuit,
    firstCircuit, signCircuit, secondCircuit, topSecondCircuit, restoreCircuit,
    List.append_assoc] using hall

/-! ## Constructor-derived resources -/

/-- Exact coherent Toffoli count of one physical interval block. -/
def intervalToffoliFormula
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode) : Nat :=
  let tree := intervalTree registers k K
  2 * intervalEndpointToffoliFormula registers.lengthT.length
      registers.lengthQ.length registers.lengthS.length +
    tree.leafCostSum
        (fun label _ _ ↦ rippleFirstCellToffoliCost mode +
          if maskedZeroLeaf (intervalHasTopSpecial k K) label then 2 else 0)
        registers.control registers.control (registers.rightPaths k K)
          (registers.leftPaths k K) +
    tree.leafCostSum
        (fun label _ _ ↦ rippleSecondCellToffoliCost mode +
          if maskedZeroLeaf (intervalHasTopSpecial k K) label then 2 else 0)
        registers.control registers.control (registers.rightPaths k K)
          (registers.leftPaths k K) +
    8 * tree.internalNodes +
    if intervalHasTopSpecial k K then
      4 * mcxVChainToffoliCost registers.lengthS.length +
        4 * mcxVChainToffoliCost registers.lengthQ.length + 4 +
        rippleFirstCellToffoliCost mode + rippleSecondCellToffoliCost mode
    else 0

/-- Exact coherent CNOT count; the optional carry-to-sign update contributes one CNOT. -/
def intervalCnotFormula
    (registers : IntervalRegisters) (k K : Nat) (signUpdate : Bool) : Nat :=
  let tree := intervalTree registers k K
  2 * intervalEndpointCnotFormula registers.lengthT.length
      registers.lengthQ.length registers.lengthS.length +
    2 * tree.leafCostSum
        (fun label _ _ ↦ 2 +
          if maskedZeroLeaf (intervalHasTopSpecial k K) label then 0 else 2)
        registers.control registers.control (registers.rightPaths k K)
          (registers.leftPaths k K) +
    8 * tree.internalNodes +
    (if signUpdate then 1 else 0) +
    if intervalHasTopSpecial k K then
      4 * mcxVChainCnotCost registers.lengthS.length +
        4 * mcxVChainCnotCost registers.lengthQ.length + 4
    else 0

/-- Exact Framework T count of the coherent reference. -/
def intervalCoherentTFormula
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode) : Nat :=
  7 * intervalToffoliFormula registers k K mode

/-- Exact worst-branch T count of the measurement-uncomputed realization. -/
def intervalAdaptiveTFormula
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode) : Nat :=
  let tree := intervalTree registers k K
  2 * intervalEndpointTFormula registers.lengthT.length
      registers.lengthQ.length registers.lengthS.length +
    tree.leafCostSum
        (fun label _ _ ↦ 7 * (rippleFirstCellToffoliCost mode - 1 +
          if maskedZeroLeaf (intervalHasTopSpecial k K) label then 2 else 0))
        registers.control registers.control (registers.rightPaths k K)
          (registers.leftPaths k K) +
    tree.leafCostSum
        (fun label _ _ ↦ 7 * (rippleSecondCellToffoliCost mode - 1 +
          if maskedZeroLeaf (intervalHasTopSpecial k K) label then 2 else 0))
        registers.control registers.control (registers.rightPaths k K)
          (registers.leftPaths k K) +
    28 * tree.internalNodes +
    if intervalHasTopSpecial k K then
      28 * mcxVChainAdaptiveToffoliCost registers.lengthS.length +
        28 * mcxVChainAdaptiveToffoliCost registers.lengthQ.length + 28 +
        7 * (rippleFirstCellToffoliCost mode - 1) +
        7 * (rippleSecondCellToffoliCost mode - 1)
    else 0

/-- Every decoder path, main ripple cell, and top-special v-chain/ripple cleanup is measured. -/
def intervalMeasurementFormula
    (registers : IntervalRegisters) (k K : Nat) : Nat :=
  let tree := intervalTree registers k K
  2 * tree.leafCostSum (fun _ _ _ ↦ 1)
      registers.control registers.control (registers.rightPaths k K)
        (registers.leftPaths k K) +
    4 * tree.internalNodes +
    if intervalHasTopSpecial k K then
      4 * mcxVChainMeasurementCost registers.lengthS.length +
        4 * mcxVChainMeasurementCost registers.lengthQ.length + 2
    else 0

private theorem intervalTopFirst_toffoliCount
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target) :
    eeaToffoliCount (intervalTopFirst registers k K mode target) =
      if intervalHasTopSpecial k K then
        (2 * mcxVChainToffoliCost registers.lengthS.length + 1) +
          rippleFirstCellToffoliCost mode +
          (2 * mcxVChainToffoliCost registers.lengthQ.length + 1)
      else 0 := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopFirst, if_pos hspecial, if_pos hspecial]
    exact topSpecialFirstLeaf_toffoliCount mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control
      (intervalLengthS_sub_two_le_equalityScratch registers k K target hlayout)
      (intervalLengthQ_sub_two_le_equalityScratch registers k K target hlayout)
  · simp [intervalTopFirst, hspecial, eeaToffoliCount]

private theorem intervalTopSecond_toffoliCount
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target) :
    eeaToffoliCount (intervalTopSecond registers k K mode target) =
      if intervalHasTopSpecial k K then
        (2 * mcxVChainToffoliCost registers.lengthQ.length + 1) +
          rippleSecondCellToffoliCost mode +
          (2 * mcxVChainToffoliCost registers.lengthS.length + 1)
      else 0 := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopSecond, if_pos hspecial, if_pos hspecial]
    exact topSpecialSecondLeaf_toffoliCount mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control
      (intervalLengthS_sub_two_le_equalityScratch registers k K target hlayout)
      (intervalLengthQ_sub_two_le_equalityScratch registers k K target hlayout)
  · simp [intervalTopSecond, hspecial, eeaToffoliCount]

private theorem intervalSignUpdate_toffoliCount
    (registers : IntervalRegisters) (k K : Nat) (signUpdate : Bool) :
    eeaToffoliCount (intervalSignUpdate registers k K signUpdate) = 0 := by
  cases signUpdate <;> rfl

private theorem list_eq_two_cons_of_two_le
    {list : List α} (htwo : 2 ≤ list.length) :
    ∃ first second rest, list = first :: second :: rest := by
  cases list with
  | nil => simp at htwo
  | cons first rest =>
      cases rest with
      | nil => simp at htwo
      | cons second rest => exact ⟨first, second, rest, rfl⟩

private theorem intervalPrepare_cnotCount
    (registers : IntervalRegisters) (n k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    eeaCnotCount
        (prepareIntervalEndpoints registers.lengthT registers.lengthQ registers.lengthS
          registers.endpointScratch (registers.carry k K) n k) =
      intervalEndpointCnotFormula registers.lengthT.length
        registers.lengthQ.length registers.lengthS.length := by
  obtain ⟨sLow, sNext, sRest, hs⟩ :=
    list_eq_two_cons_of_two_le hlayout.lengthS_two_le
  rw [hs]
  exact prepareIntervalEndpoints_cnotCount registers.lengthT registers.lengthQ
    registers.endpointScratch sRest sLow sNext (registers.carry k K) n k
    hlayout.lengthT_eq_lengthQ
    (intervalLengthQ_le_endpointScratch registers k K target hlayout)
    (by simpa only [hs] using
      intervalLengthS_le_endpointScratch registers k K target hlayout)

private theorem intervalRestore_cnotCount
    (registers : IntervalRegisters) (n k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    eeaCnotCount
        (restoreIntervalEndpoints registers.lengthT registers.lengthQ registers.lengthS
          registers.endpointScratch (registers.carry k K) n k) =
      intervalEndpointCnotFormula registers.lengthT.length
        registers.lengthQ.length registers.lengthS.length := by
  obtain ⟨sLow, sNext, sRest, hs⟩ :=
    list_eq_two_cons_of_two_le hlayout.lengthS_two_le
  rw [hs]
  exact restoreIntervalEndpoints_cnotCount registers.lengthT registers.lengthQ
    registers.endpointScratch sRest sLow sNext (registers.carry k K) n k
    hlayout.lengthT_eq_lengthQ
    (intervalLengthQ_le_endpointScratch registers k K target hlayout)
    (by simpa only [hs] using
      intervalLengthS_le_endpointScratch registers k K target hlayout)

private theorem intervalTopFirst_cnotCount
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) :
    eeaCnotCount (intervalTopFirst registers k K mode target) =
      if intervalHasTopSpecial k K then
        2 * mcxVChainCnotCost registers.lengthS.length + 2 +
          2 * mcxVChainCnotCost registers.lengthQ.length
      else 0 := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopFirst, if_pos hspecial, if_pos hspecial]
    exact topSpecialFirstLeaf_cnotCount mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control
  · simp [intervalTopFirst, hspecial, eeaCnotCount]

private theorem intervalTopSecond_cnotCount
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) :
    eeaCnotCount (intervalTopSecond registers k K mode target) =
      if intervalHasTopSpecial k K then
        2 * mcxVChainCnotCost registers.lengthQ.length + 2 +
          2 * mcxVChainCnotCost registers.lengthS.length
      else 0 := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopSecond, if_pos hspecial, if_pos hspecial]
    exact topSpecialSecondLeaf_cnotCount mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control
  · simp [intervalTopSecond, hspecial, eeaCnotCount]

private theorem intervalSignUpdate_cnotCount
    (registers : IntervalRegisters) (k K : Nat) (signUpdate : Bool) :
    eeaCnotCount (intervalSignUpdate registers k K signUpdate) =
      if signUpdate then 1 else 0 := by
  cases signUpdate <;> rfl

theorem intervalAddSubUnitary_toffoliCount
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    eeaToffoliCount
        (intervalAddSubUnitary registers n k K mode signUpdate target) =
      intervalToffoliFormula registers k K mode := by
  simp only [intervalAddSubUnitary, eeaToffoliCount_append]
  rw [prepareIntervalEndpoints_toffoliCount registers.lengthT registers.lengthQ
      registers.lengthS registers.endpointScratch (registers.carry k K) n k
      hlayout.lengthT_eq_lengthQ
      (intervalLengthQ_le_endpointScratch registers k K target hlayout)
      (intervalLengthS_le_endpointScratch registers k K target hlayout)
      (intervalLengthS_positive registers k K target hlayout),
    intervalFirstTraversal_toffoliCount mode (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K)
      (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K) hlayout.traversal.1,
    intervalSecondTraversal_toffoliCount mode (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K)
      (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K) hlayout.traversal.1,
    restoreIntervalEndpoints_toffoliCount registers.lengthT registers.lengthQ
      registers.lengthS registers.endpointScratch (registers.carry k K) n k
      hlayout.lengthT_eq_lengthQ
      (intervalLengthQ_le_endpointScratch registers k K target hlayout)
      (intervalLengthS_le_endpointScratch registers k K target hlayout)
      (intervalLengthS_positive registers k K target hlayout),
    intervalTopFirst_toffoliCount registers k K mode target hlayout,
    intervalTopSecond_toffoliCount registers k K mode target hlayout,
    intervalSignUpdate_toffoliCount registers k K signUpdate]
  simp only [intervalToffoliFormula]
  split <;> omega

theorem intervalAddSubUnitary_cnotCount
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    eeaCnotCount
        (intervalAddSubUnitary registers n k K mode signUpdate target) =
      intervalCnotFormula registers k K signUpdate := by
  simp only [intervalAddSubUnitary, eeaCnotCount_append]
  rw [intervalPrepare_cnotCount registers n k K target hlayout,
    intervalFirstTraversal_cnotCount mode (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K)
      (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K) hlayout.traversal.1,
    intervalSecondTraversal_cnotCount mode (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K)
      (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K) hlayout.traversal.1,
    intervalRestore_cnotCount registers n k K target hlayout,
    intervalTopFirst_cnotCount registers k K mode target,
    intervalTopSecond_cnotCount registers k K mode target,
    intervalSignUpdate_cnotCount registers k K signUpdate]
  simp only [intervalCnotFormula]
  split <;> omega

private theorem tCount_eq_seven_mul_toffoli_of_HPFree
    (circuit : Circuit) (hfree : HPFree circuit) :
    ShorECDLP.tCount circuit = 7 * eeaToffoliCount circuit := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      have hgate : IsClassicalGate gate := hfree gate (by simp)
      have htail : HPFree circuit := by
        intro next hnext
        exact hfree next (by simp [hnext])
      cases gate <;>
        simp_all [ShorECDLP.tCount, ShorECDLP.tCost, eeaToffoliCount]
      omega

theorem intervalAddSubUnitary_tCount
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    ShorECDLP.tCount
        (intervalAddSubUnitary registers n k K mode signUpdate target) =
      intervalCoherentTFormula registers k K mode := by
  rw [tCount_eq_seven_mul_toffoli_of_HPFree
    (intervalAddSubUnitary registers n k K mode signUpdate target)
    (intervalAddSubUnitary_HPFree registers n k K mode signUpdate target),
    intervalAddSubUnitary_toffoliCount registers n k K mode signUpdate target hlayout]
  rfl

private theorem intervalAdaptive_tCount_seq
    (first second : Quantum.AdaptiveCircuit) :
    (first.seq second).tCount = first.tCount + second.tCount := by
  induction first with
  | done => simp [Quantum.AdaptiveCircuit.seq, Quantum.AdaptiveCircuit.tCount]
  | unitary circuit next ih =>
      simp [Quantum.AdaptiveCircuit.seq, Quantum.AdaptiveCircuit.tCount,
        ih, Nat.add_assoc]
  | xMeasureReset wire onFalse onTrue ihFalse ihTrue =>
      simp [Quantum.AdaptiveCircuit.seq, Quantum.AdaptiveCircuit.tCount,
        ihFalse, ihTrue, Nat.add_max_add_right]

private theorem intervalAdaptive_measurementCount_seq
    (first second : Quantum.AdaptiveCircuit) :
    (first.seq second).measurementCount =
      first.measurementCount + second.measurementCount := by
  induction first with
  | done => simp [Quantum.AdaptiveCircuit.seq, Quantum.AdaptiveCircuit.measurementCount]
  | unitary circuit next ih =>
      simp [Quantum.AdaptiveCircuit.seq, Quantum.AdaptiveCircuit.measurementCount,
        ih]
  | xMeasureReset wire onFalse onTrue ihFalse ihTrue =>
      simp [Quantum.AdaptiveCircuit.seq, Quantum.AdaptiveCircuit.measurementCount,
        ihFalse, ihTrue, Nat.add_max_add_right, Nat.add_assoc]

private theorem intervalTopFirstAdaptive_tCount
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target) :
    (intervalTopFirstAdaptive registers k K mode target).tCount =
      if intervalHasTopSpecial k K then
        (14 * mcxVChainAdaptiveToffoliCost registers.lengthS.length + 7) +
          7 * (rippleFirstCellToffoliCost mode - 1) +
          (14 * mcxVChainAdaptiveToffoliCost registers.lengthQ.length + 7)
      else 0 := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopFirstAdaptive, if_pos hspecial, if_pos hspecial]
    exact topSpecialFirstLeafAdaptive_tCount mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control
      (intervalLengthS_sub_two_le_equalityScratch registers k K target hlayout)
      (intervalLengthQ_sub_two_le_equalityScratch registers k K target hlayout)
  · simp [intervalTopFirstAdaptive, hspecial,
      Quantum.AdaptiveCircuit.tCount]

private theorem intervalTopSecondAdaptive_tCount
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target) :
    (intervalTopSecondAdaptive registers k K mode target).tCount =
      if intervalHasTopSpecial k K then
        (14 * mcxVChainAdaptiveToffoliCost registers.lengthQ.length + 7) +
          7 * (rippleSecondCellToffoliCost mode - 1) +
          (14 * mcxVChainAdaptiveToffoliCost registers.lengthS.length + 7)
      else 0 := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopSecondAdaptive, if_pos hspecial, if_pos hspecial]
    exact topSpecialSecondLeafAdaptive_tCount mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control
      (intervalLengthS_sub_two_le_equalityScratch registers k K target hlayout)
      (intervalLengthQ_sub_two_le_equalityScratch registers k K target hlayout)
  · simp [intervalTopSecondAdaptive, hspecial,
      Quantum.AdaptiveCircuit.tCount]

private theorem intervalTopFirstAdaptive_measurementCount
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target) :
    (intervalTopFirstAdaptive registers k K mode target).measurementCount =
      if intervalHasTopSpecial k K then
        2 * mcxVChainMeasurementCost registers.lengthS.length + 1 +
          2 * mcxVChainMeasurementCost registers.lengthQ.length
      else 0 := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopFirstAdaptive, if_pos hspecial, if_pos hspecial]
    exact topSpecialFirstLeafAdaptive_measurementCount mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control
      (intervalLengthS_sub_two_le_equalityScratch registers k K target hlayout)
      (intervalLengthQ_sub_two_le_equalityScratch registers k K target hlayout)
  · simp [intervalTopFirstAdaptive, hspecial,
      Quantum.AdaptiveCircuit.measurementCount]

private theorem intervalTopSecondAdaptive_measurementCount
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target) :
    (intervalTopSecondAdaptive registers k K mode target).measurementCount =
      if intervalHasTopSpecial k K then
        2 * mcxVChainMeasurementCost registers.lengthQ.length + 1 +
          2 * mcxVChainMeasurementCost registers.lengthS.length
      else 0 := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopSecondAdaptive, if_pos hspecial, if_pos hspecial]
    exact topSpecialSecondLeafAdaptive_measurementCount mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control
      (intervalLengthS_sub_two_le_equalityScratch registers k K target hlayout)
      (intervalLengthQ_sub_two_le_equalityScratch registers k K target hlayout)
  · simp [intervalTopSecondAdaptive, hspecial,
      Quantum.AdaptiveCircuit.measurementCount]

private theorem intervalSignUpdate_tCount
    (registers : IntervalRegisters) (k K : Nat) (signUpdate : Bool) :
    ShorECDLP.tCount (intervalSignUpdate registers k K signUpdate) = 0 := by
  cases signUpdate <;> rfl

theorem intervalAddSub_tCount
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
  (intervalAddSub registers n k K mode signUpdate target).tCount =
      intervalAdaptiveTFormula registers k K mode := by
  simp only [intervalAddSub, intervalAdaptive_tCount_seq,
    Quantum.AdaptiveCircuit.tCount]
  rw [prepareIntervalEndpoints_tCount registers.lengthT registers.lengthQ
      registers.lengthS registers.endpointScratch (registers.carry k K) n k
      hlayout.lengthT_eq_lengthQ
      (intervalLengthQ_le_endpointScratch registers k K target hlayout)
      (intervalLengthS_le_endpointScratch registers k K target hlayout)
      (intervalLengthS_positive registers k K target hlayout),
    intervalTopFirstAdaptive_tCount registers k K mode target hlayout,
    intervalFirstTraversalAdaptive_tCount mode (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K)
      (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K) hlayout.traversal.1,
    intervalSecondTraversalAdaptive_tCount mode (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K)
      (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K) hlayout.traversal.1,
    restoreIntervalEndpoints_tCount registers.lengthT registers.lengthQ
      registers.lengthS registers.endpointScratch (registers.carry k K) n k
      hlayout.lengthT_eq_lengthQ
      (intervalLengthQ_le_endpointScratch registers k K target hlayout)
      (intervalLengthS_le_endpointScratch registers k K target hlayout)
      (intervalLengthS_positive registers k K target hlayout),
    intervalTopSecondAdaptive_tCount registers k K mode target hlayout,
    intervalSignUpdate_tCount registers k K signUpdate]
  simp only [intervalAdaptiveTFormula]
  split <;> omega

theorem intervalAddSub_measurementCount
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    (intervalAddSub registers n k K mode signUpdate target).measurementCount =
      intervalMeasurementFormula registers k K := by
  simp only [intervalAddSub, intervalAdaptive_measurementCount_seq,
    Quantum.AdaptiveCircuit.measurementCount]
  rw [intervalTopFirstAdaptive_measurementCount registers k K mode target hlayout,
    intervalFirstTraversalAdaptive_measurementCount mode
      (intervalHasTopSpecial k K) (registers.rightTop k K)
      (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K)
      (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K) hlayout.traversal.1,
    intervalSecondTraversalAdaptive_measurementCount mode
      (intervalHasTopSpecial k K) (registers.rightTop k K)
      (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K)
      (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K) hlayout.traversal.1,
    intervalTopSecondAdaptive_measurementCount registers k K mode target hlayout]
  by_cases hspecial : intervalHasTopSpecial k K = true <;>
    simp [intervalMeasurementFormula, hspecial] <;> omega

/-! ## Closed physical witness and pinned-source resource regressions -/

/-- A nontrivial source-shaped allocation for the five-lane interval `[3,7]`.  Its four-label
main tree has depth two, and label four is handled by the separate top-special block. -/
def intervalSourceComparisonRegisters : IntervalRegisters where
  control := 0
  sign := 1
  work1 := List.range' 2 5
  work2 := List.range' 7 5
  lengthT := List.range' 12 3
  lengthQ := List.range' 15 3
  lengthS := List.range' 18 4
  scratch := List.range' 22 7

private theorem intervalSourceComparison_tree :
    intervalTree intervalSourceComparisonRegisters 3 7 =
      .node 19 16
        (.node 18 15 (.leaf 0) (.leaf 1))
        (.node 18 15 (.leaf 2) (.leaf 3)) := by
  rfl

private theorem intervalSourceComparison_decoderLayout :
    (intervalTree intervalSourceComparisonRegisters 3 7).Layout
      intervalSourceComparisonRegisters.control intervalSourceComparisonRegisters.control
      (intervalSourceComparisonRegisters.rightPaths 3 7)
      (intervalSourceComparisonRegisters.leftPaths 3 7) := by
  change DualUnaryActionTree.Layout
    (.node 19 16
      (.node 18 15 (.leaf 0) (.leaf 1))
      (.node 18 15 (.leaf 2) (.leaf 3))) 0 0
        ([22, 23] : List Wire) ([24, 25] : List Wire)
  apply DualUnaryActionTree.Layout.node
  · norm_num [DualUnaryActionTree.decoderWires, DualUnaryActionTree.indexAWires,
      DualUnaryActionTree.indexBWires]
  · apply DualUnaryActionTree.Layout.node
    · norm_num [DualUnaryActionTree.decoderWires, DualUnaryActionTree.indexAWires,
        DualUnaryActionTree.indexBWires]
    · apply DualUnaryActionTree.Layout.leaf
      norm_num [DualUnaryActionTree.decoderWires, DualUnaryActionTree.indexAWires,
        DualUnaryActionTree.indexBWires]
    · apply DualUnaryActionTree.Layout.leaf
      norm_num [DualUnaryActionTree.decoderWires, DualUnaryActionTree.indexAWires,
        DualUnaryActionTree.indexBWires]
  · apply DualUnaryActionTree.Layout.node
    · norm_num [DualUnaryActionTree.decoderWires, DualUnaryActionTree.indexAWires,
        DualUnaryActionTree.indexBWires]
    · apply DualUnaryActionTree.Layout.leaf
      norm_num [DualUnaryActionTree.decoderWires, DualUnaryActionTree.indexAWires,
        DualUnaryActionTree.indexBWires]
    · apply DualUnaryActionTree.Layout.leaf
      norm_num [DualUnaryActionTree.decoderWires, DualUnaryActionTree.indexAWires,
        DualUnaryActionTree.indexBWires]

/-- The wrapper layout is genuinely inhabited; in particular, its public contracts are not
vacuous after restricting finite-bank leaf obligations to the labels present in the tree. -/
theorem intervalSourceComparisonLayout :
    IntervalLayout intervalSourceComparisonRegisters 3 7 .work1 := by
  refine {
    k_le_K := by norm_num
    work1_length := by norm_num [intervalSourceComparisonRegisters, intervalLaneCount]
    work2_length := by norm_num [intervalSourceComparisonRegisters, intervalLaneCount]
    lengthT_eq_lengthQ := by norm_num [intervalSourceComparisonRegisters]
    lengthT_two_le := by norm_num [intervalSourceComparisonRegisters]
    lengthS_two_le := by norm_num [intervalSourceComparisonRegisters]
    right_index_capacity := by
      change 2 ≤ 4
      norm_num
    left_index_capacity := by
      change 2 ≤ 3
      norm_num
    right_top_capacity := by
      change true = true → 2 < 4
      norm_num
    left_top_capacity := by
      change true = true → 2 < 3
      norm_num
    scratch_length := by
      change 7 = 4 + 3
      norm_num
    physical := by
      change ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13,
        14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28] :
          List Wire).Nodup
      decide
    endpoints := by
      change IntervalEndpointLayout ([12, 13, 14] : List Wire)
        ([15, 16, 17] : List Wire) ([18, 19, 20, 21] : List Wire)
        ([22, 23, 24, 25] : List Wire) 26
      norm_num [IntervalEndpointLayout]
    traversal := ?_
    topSpecial := ?_
  }
  · rw [IntervalTraversalLayout]
    refine ⟨intervalSourceComparison_decoderLayout, ?_⟩
    intro label hlabel
    rw [intervalSourceComparison_tree] at hlabel
    simp [DualUnaryActionTree.labels] at hlabel
    rcases hlabel with rfl | rfl | rfl | rfl
    · change ([20, 17, 27, 2, 7, 26, 28] : List Wire).Nodup ∧
        DecoderOutsideIntervalRoles ([0, 19, 18, 16, 15, 22, 23, 24, 25] : List Wire)
          20 17 27 2 7 26 28
      norm_num [DecoderOutsideIntervalRoles]
    · change ([20, 17, 27, 3, 8, 26, 28] : List Wire).Nodup ∧
        DecoderOutsideIntervalRoles ([0, 19, 18, 16, 15, 22, 23, 24, 25] : List Wire)
          20 17 27 3 8 26 28
      norm_num [DecoderOutsideIntervalRoles]
    · change ([20, 17, 27, 4, 9, 26, 28] : List Wire).Nodup ∧
        DecoderOutsideIntervalRoles ([0, 19, 18, 16, 15, 22, 23, 24, 25] : List Wire)
          20 17 27 4 9 26 28
      norm_num [DecoderOutsideIntervalRoles]
    · change ([20, 17, 27, 5, 10, 26, 28] : List Wire).Nodup ∧
        DecoderOutsideIntervalRoles ([0, 19, 18, 16, 15, 22, 23, 24, 25] : List Wire)
          20 17 27 5 10 26 28
      norm_num [DecoderOutsideIntervalRoles]
  · intro _
    change TopSpecialLeafLayout 0 0 ([18, 19, 20, 21] : List Wire)
      ([15, 16, 17] : List Wire) 27 6 11 26 28 28
      ([22, 23, 24, 25] : List Wire)
    norm_num [TopSpecialLeafLayout, EqControlLayout]

/-- Closed comparison against the pinned source for `n=8`, `[k,K]=[3,7]`, addition with the
sign update, and `Work1` as target.  These equalities are about the actual wrapper terms. -/
theorem intervalSourceComparison_resources :
    eeaToffoliCount
        (intervalAddSubUnitary intervalSourceComparisonRegisters 8 3 7 .add true .work1) = 175 ∧
      eeaCnotCount
        (intervalAddSubUnitary intervalSourceComparisonRegisters 8 3 7 .add true .work1) = 203 ∧
      (intervalAddSub intervalSourceComparisonRegisters 8 3 7 .add true .work1).tCount = 987 ∧
      (intervalAddSub intervalSourceComparisonRegisters 8 3 7 .add true .work1).measurementCount =
        34 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [intervalAddSubUnitary_toffoliCount intervalSourceComparisonRegisters 8 3 7
      .add true .work1 intervalSourceComparisonLayout]
    rfl
  · rw [intervalAddSubUnitary_cnotCount intervalSourceComparisonRegisters 8 3 7
      .add true .work1 intervalSourceComparisonLayout]
    rfl
  · rw [intervalAddSub_tCount intervalSourceComparisonRegisters 8 3 7
      .add true .work1 intervalSourceComparisonLayout]
    rfl
  · rw [intervalAddSub_measurementCount intervalSourceComparisonRegisters 8 3 7
      .add true .work1 intervalSourceComparisonLayout]
    rfl

/-- Pinned-source edge regression: one ordinary lane measures its one ripple cleanup per pass. -/
theorem intervalSingleton_sourceResourceRegression :
    let registers : IntervalRegisters := {
      control := 0
      sign := 1
      work1 := List.range' 2 1
      work2 := List.range' 3 1
      lengthT := List.range' 4 2
      lengthQ := List.range' 6 2
      lengthS := List.range' 8 2
      scratch := List.range' 10 5 }
    intervalToffoliFormula registers 4 4 .add = 47 ∧
      intervalCnotFormula registers 4 4 false = 94 ∧
      intervalAdaptiveTFormula registers 4 4 .add = 315 ∧
      intervalMeasurementFormula registers 4 4 = 2 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Pinned-source edge regression: the two-lane top-special case has four ripple erasures and
zero equality-chain erasures at width two. -/
theorem intervalTopSpecialTwoLane_sourceResourceRegression :
    let registers : IntervalRegisters := {
      control := 0
      sign := 1
      work1 := List.range' 2 2
      work2 := List.range' 4 2
      lengthT := List.range' 6 2
      lengthQ := List.range' 8 2
      lengthS := List.range' 10 2
      scratch := List.range' 12 5 }
    intervalToffoliFormula registers 4 5 .add = 70 ∧
      intervalCnotFormula registers 4 5 false = 94 ∧
      intervalAdaptiveTFormula registers 4 5 .add = 462 ∧
      intervalMeasurementFormula registers 4 5 = 4 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/- Production-shaped pinned-source regression for the 257-lane interval and 9/11-bit endpoints. -/
set_option maxRecDepth 10000 in
theorem intervalProduction_sourceResourceRegression :
    let registers : IntervalRegisters := {
      control := 0
      sign := 1
      work1 := List.range' 2 257
      work2 := List.range' 259 257
      lengthT := List.range' 516 9
      lengthQ := List.range' 525 9
      lengthS := List.range' 534 11
      scratch := List.range' 545 19 }
    intervalAdaptiveTFormula registers 1 257 .add = 18319 ∧
      intervalMeasurementFormula registers 1 257 = 1598 := by
  exact ⟨rfl, rfl⟩

end

end ShorECDLP.Paper2607_13816
