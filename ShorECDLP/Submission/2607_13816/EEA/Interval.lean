import ShorECDLP.Submission.«2607_13816».EEA.Endpoint
import ShorECDLP.Submission.«2607_13816».EEA.IntervalCleanup
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
source inverse aggregate is the same block with the opposite ripple mode; its whole-state round
trip is certified at the clean boundary needed by the later four-phase indexed EEA step.
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

private theorem intervalTree_label_ne_topRelative
    (registers : IntervalRegisters) (k K label : Nat)
    (hspecial : intervalHasTopSpecial k K = true)
    (hlabel : label ∈ (intervalTree registers k K).labels) :
    label ≠ intervalTopRelative k K := by
  rw [intervalTree_labels] at hlabel
  have hmain : label ∈ intervalMainLabels k K := by
    simpa using hlabel
  have hlt : label < intervalLaneCount k K - 1 := by
    simpa [intervalMainLabels, hspecial] using hmain
  exact Nat.ne_of_lt (by simpa [intervalTopRelative] using hlt)

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

private def intervalNonSignTail (registers : IntervalRegisters) : List Wire :=
  registers.work1 ++ (registers.work2 ++
    (registers.lengthT ++ (registers.lengthQ ++
      (registers.lengthS ++ registers.scratch))))

private def intervalFixedWires (registers : IntervalRegisters) : List Wire :=
  [registers.control, registers.sign] ++
    (registers.lengthT ++ (registers.lengthQ ++
      (registers.lengthS ++ registers.scratch)))

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

private theorem intervalControl_ne_sign
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.control ≠ registers.sign := by
  have hphysical := hlayout.physical
  rw [IntervalRegisters.allWires] at hphysical
  have hnot := (List.nodup_cons.mp (List.nodup_append.mp hphysical).1).1
  intro equality
  exact hnot (by simp [equality])

private theorem intervalNonSignTail_ne_sign
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target)
    {wire : Wire} (hwire : wire ∈ intervalNonSignTail registers) :
    wire ≠ registers.sign := by
  have hphysical := hlayout.physical
  rw [IntervalRegisters.allWires] at hphysical
  have hcross := (List.nodup_append.mp hphysical).2.2
  intro equality
  exact (hcross registers.sign (by simp) wire hwire) equality.symm

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

private theorem intervalWork1_nodup
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.work1.Nodup := by
  have hphysical := hlayout.physical
  rw [IntervalRegisters.allWires] at hphysical
  exact (List.nodup_append.mp
    (List.nodup_append.mp hphysical).2.1).1

private theorem intervalWork2_nodup
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.work2.Nodup := by
  have hphysical := hlayout.physical
  rw [IntervalRegisters.allWires] at hphysical
  have hafterControls := (List.nodup_append.mp hphysical).2.1
  have hafterWork1 := (List.nodup_append.mp hafterControls).2.1
  exact (List.nodup_append.mp hafterWork1).1

private theorem intervalWork1_disjoint_work2
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    List.Disjoint registers.work1 registers.work2 := by
  have hphysical := hlayout.physical
  rw [IntervalRegisters.allWires] at hphysical
  have hafterControls := (List.nodup_append.mp hphysical).2.1
  have hcross := (List.nodup_append.mp hafterControls).2.2
  intro wire hwork1 hwork2
  exact (hcross wire hwork1 wire (List.mem_append_left _ hwork2)) rfl

private theorem intervalTargetAt_injective
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target)
    {first second : Nat}
    (hfirst : first < intervalLaneCount k K)
    (hsecond : second < intervalLaneCount k K) :
    registers.targetAt target first = registers.targetAt target second →
      first = second := by
  intro equality
  cases target with
  | work1 =>
      have hfirstBound : first < registers.work1.length := by
        simpa [hlayout.work1_length] using hfirst
      have hsecondBound : second < registers.work1.length := by
        simpa [hlayout.work1_length] using hsecond
      simp only [IntervalRegisters.targetAt] at equality
      rw [List.getD_eq_getElem registers.work1 0 hfirstBound,
        List.getD_eq_getElem registers.work1 0 hsecondBound] at equality
      exact (intervalWork1_nodup registers k K .work1 hlayout).getElem_inj_iff.mp equality
  | work2 =>
      have hfirstBound : first < registers.work2.length := by
        simpa [hlayout.work2_length] using hfirst
      have hsecondBound : second < registers.work2.length := by
        simpa [hlayout.work2_length] using hsecond
      simp only [IntervalRegisters.targetAt] at equality
      rw [List.getD_eq_getElem registers.work2 0 hfirstBound,
        List.getD_eq_getElem registers.work2 0 hsecondBound] at equality
      exact (intervalWork2_nodup registers k K .work2 hlayout).getElem_inj_iff.mp equality

private theorem intervalTargetAt_ne_addendAt
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target)
    {targetLabel addendLabel : Nat}
    (htarget : targetLabel < intervalLaneCount k K)
    (haddend : addendLabel < intervalLaneCount k K) :
    registers.targetAt target targetLabel ≠
      registers.addendAt target addendLabel := by
  have hdisjoint := intervalWork1_disjoint_work2 registers k K target hlayout
  cases target with
  | work1 =>
      have htargetBound : targetLabel < registers.work1.length := by
        simpa [hlayout.work1_length] using htarget
      have haddendBound : addendLabel < registers.work2.length := by
        simpa [hlayout.work2_length] using haddend
      have htargetMem := list_getD_mem registers.work1 targetLabel 0 htargetBound
      have haddendMem := list_getD_mem registers.work2 addendLabel 0 haddendBound
      exact fun equality ↦ by
        change registers.work1.getD targetLabel 0 =
          registers.work2.getD addendLabel 0 at equality
        exact hdisjoint htargetMem (equality.symm ▸ haddendMem)
  | work2 =>
      have htargetBound : targetLabel < registers.work2.length := by
        simpa [hlayout.work2_length] using htarget
      have haddendBound : addendLabel < registers.work1.length := by
        simpa [hlayout.work1_length] using haddend
      have htargetMem := list_getD_mem registers.work2 targetLabel 0 htargetBound
      have haddendMem := list_getD_mem registers.work1 addendLabel 0 haddendBound
      exact fun equality ↦ by
        change registers.work2.getD targetLabel 0 =
          registers.work1.getD addendLabel 0 at equality
        exact hdisjoint haddendMem (equality ▸ htargetMem)

private theorem intervalTargetAt_not_mem_fixed
    (registers : IntervalRegisters) (k K label : Nat)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target)
    (hlabel : label < intervalLaneCount k K) :
    registers.targetAt target label ∉ intervalFixedWires registers := by
  have hphysical := hlayout.physical
  rw [IntervalRegisters.allWires] at hphysical
  obtain ⟨hcontrols, htail, hcontrolsTail⟩ := List.nodup_append.mp hphysical
  cases target with
  | work1 =>
      have hbound : label < registers.work1.length := by
        simpa [hlayout.work1_length] using hlabel
      have htarget := list_getD_mem registers.work1 label 0 hbound
      obtain ⟨hwork1, hafterWork1, hwork1Tail⟩ := List.nodup_append.mp htail
      change registers.work1.getD label 0 ∉ intervalFixedWires registers
      intro hfixed
      rw [intervalFixedWires] at hfixed
      rcases List.mem_append.mp hfixed with hcontrol | hrest
      · exact hcontrolsTail _ hcontrol _
          (List.mem_append_left _ htarget) rfl
      · exact hwork1Tail _ htarget _
          (List.mem_append_right registers.work2 hrest) rfl
  | work2 =>
      have hbound : label < registers.work2.length := by
        simpa [hlayout.work2_length] using hlabel
      have htarget := list_getD_mem registers.work2 label 0 hbound
      obtain ⟨hwork1, hafterWork1, hwork1Tail⟩ := List.nodup_append.mp htail
      obtain ⟨hwork2, hafterWork2, hwork2Tail⟩ :=
        List.nodup_append.mp hafterWork1
      change registers.work2.getD label 0 ∉ intervalFixedWires registers
      intro hfixed
      rw [intervalFixedWires] at hfixed
      rcases List.mem_append.mp hfixed with hcontrol | hrest
      · exact hcontrolsTail _ hcontrol _
          (List.mem_append_right registers.work1
            (List.mem_append_left _ htarget)) rfl
      · exact hwork2Tail _ htarget _ hrest rfl

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

private theorem intervalDecoder_ne_sign
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target)
    {wire : Wire}
    (hwire : wire ∈ (intervalTree registers k K).decoderWires registers.control
      registers.control (registers.rightPaths k K) (registers.leftPaths k K)) :
    wire ≠ registers.sign := by
  simp only [DualUnaryActionTree.decoderWires, List.mem_append,
    List.mem_dedup, List.mem_cons, List.not_mem_nil, or_false] at hwire
  rcases hwire with hcontrol | hindexA | hindexB | hrightPath | hleftPath
  · rcases hcontrol with rfl | rfl <;>
      exact intervalControl_ne_sign registers k K target hlayout
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
    apply intervalNonSignTail_ne_sign registers k K target hlayout
    change registers.lengthS.getD bit 0 ∈ intervalNonSignTail registers
    exact List.mem_append_right registers.work1
      (List.mem_append_right registers.work2
        (List.mem_append_right registers.lengthT
          (List.mem_append_right registers.lengthQ
            (List.mem_append_left registers.scratch hmem))))
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
    apply intervalNonSignTail_ne_sign registers k K target hlayout
    change registers.lengthQ.getD bit 0 ∈ intervalNonSignTail registers
    exact List.mem_append_right registers.work1
      (List.mem_append_right registers.work2
        (List.mem_append_right registers.lengthT
          (List.mem_append_left (registers.lengthS ++ registers.scratch) hmem)))
  · have hscratch : wire ∈ registers.scratch :=
      List.mem_of_mem_take hrightPath
    apply intervalNonSignTail_ne_sign registers k K target hlayout
    exact List.mem_append_right registers.work1
      (List.mem_append_right registers.work2
        (List.mem_append_right registers.lengthT
          (List.mem_append_right registers.lengthQ
            (List.mem_append_right registers.lengthS hscratch))))
  · have hscratch : wire ∈ registers.scratch :=
      List.mem_of_mem_drop (List.mem_of_mem_take hleftPath)
    apply intervalNonSignTail_ne_sign registers k K target hlayout
    exact List.mem_append_right registers.work1
      (List.mem_append_right registers.work2
        (List.mem_append_right registers.lengthT
          (List.mem_append_right registers.lengthQ
            (List.mem_append_right registers.lengthS hscratch))))

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

private theorem intervalTargetAt_ne_sign
    (registers : IntervalRegisters) (k K label : Nat)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target)
    (hlabel : label < intervalLaneCount k K) :
    registers.targetAt target label ≠ registers.sign := by
  cases target with
  | work1 =>
      have hbound : label < registers.work1.length := by
        simpa [hlayout.work1_length] using hlabel
      have hmem := list_getD_mem registers.work1 label 0 hbound
      apply intervalNonSignTail_ne_sign registers k K .work1 hlayout
      exact List.mem_append_left _ hmem
  | work2 =>
      have hbound : label < registers.work2.length := by
        simpa [hlayout.work2_length] using hlabel
      have hmem := list_getD_mem registers.work2 label 0 hbound
      apply intervalNonSignTail_ne_sign registers k K .work2 hlayout
      exact List.mem_append_right registers.work1 (List.mem_append_left _ hmem)

private theorem intervalAddendAt_ne_sign
    (registers : IntervalRegisters) (k K label : Nat)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target)
    (hlabel : label < intervalLaneCount k K) :
    registers.addendAt target label ≠ registers.sign := by
  cases target with
  | work1 =>
      have hbound : label < registers.work2.length := by
        simpa [hlayout.work2_length] using hlabel
      have hmem := list_getD_mem registers.work2 label 0 hbound
      apply intervalNonSignTail_ne_sign registers k K .work1 hlayout
      exact List.mem_append_right registers.work1 (List.mem_append_left _ hmem)
  | work2 =>
      have hbound : label < registers.work1.length := by
        simpa [hlayout.work1_length] using hlabel
      have hmem := list_getD_mem registers.work1 label 0 hbound
      apply intervalNonSignTail_ne_sign registers k K .work2 hlayout
      exact List.mem_append_left _ hmem

private theorem intervalRightTop_ne_sign
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.rightTop k K ≠ registers.sign := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · have hmem := list_getD_mem registers.lengthS (intervalTopBit k K) 0
      (hlayout.right_top_capacity hspecial)
    rw [IntervalRegisters.rightTop, if_pos hspecial]
    apply intervalNonSignTail_ne_sign registers k K target hlayout
    exact List.mem_append_right registers.work1
      (List.mem_append_right registers.work2
        (List.mem_append_right registers.lengthT
          (List.mem_append_right registers.lengthQ
            (List.mem_append_left registers.scratch hmem))))
  · have hbound : 0 < registers.lengthT.length :=
      lt_of_lt_of_le (by decide) hlayout.lengthT_two_le
    have hmem := list_getD_mem registers.lengthT 0 0 hbound
    rw [IntervalRegisters.rightTop, if_neg hspecial]
    apply intervalNonSignTail_ne_sign registers k K target hlayout
    exact List.mem_append_right registers.work1
      (List.mem_append_right registers.work2
        (List.mem_append_left _ hmem))

private theorem intervalLeftTop_ne_sign
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.leftTop k K ≠ registers.sign := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · have hmem := list_getD_mem registers.lengthQ (intervalTopBit k K) 0
      (hlayout.left_top_capacity hspecial)
    rw [IntervalRegisters.leftTop, if_pos hspecial]
    apply intervalNonSignTail_ne_sign registers k K target hlayout
    exact List.mem_append_right registers.work1
      (List.mem_append_right registers.work2
        (List.mem_append_right registers.lengthT
          (List.mem_append_left _ hmem)))
  · have hbound : 1 < registers.lengthT.length := hlayout.lengthT_two_le
    have hmem := list_getD_mem registers.lengthT 1 0 hbound
    rw [IntervalRegisters.leftTop, if_neg hspecial]
    apply intervalNonSignTail_ne_sign registers k K target hlayout
    exact List.mem_append_right registers.work1
      (List.mem_append_right registers.work2
        (List.mem_append_left _ hmem))

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

private theorem intervalSign_not_mem_topSpecialSupport
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.sign ∉
      topSpecialLeafSupport registers.control registers.control
        registers.lengthS registers.lengthQ (registers.accumulator k K)
        (registers.targetAt target (intervalTopRelative k K))
        (registers.addendAt target (intervalTopRelative k K))
        (registers.carry k K) (registers.cellScratch k K)
        (registers.cellScratch k K) (registers.equalityScratch k K) := by
  intro hwire
  simp only [topSpecialLeafSupport, List.mem_append, List.mem_dedup,
    List.mem_cons, List.not_mem_nil, or_false] at hwire
  have hlabel := intervalTopRelative_lt_laneCount k K hlayout.k_le_K
  rcases hwire with ((((hroot | hs) | hq) | hroles) | heq)
  · rcases hroot with hroot | hroot <;>
      exact (intervalControl_ne_sign registers k K target hlayout) hroot.symm
  · exact (intervalNonSignTail_ne_sign registers k K target hlayout
      (List.mem_append_right registers.work1
        (List.mem_append_right registers.work2
          (List.mem_append_right registers.lengthT
            (List.mem_append_right registers.lengthQ
              (List.mem_append_left registers.scratch hs)))))) rfl
  · exact (intervalNonSignTail_ne_sign registers k K target hlayout
      (List.mem_append_right registers.work1
        (List.mem_append_right registers.work2
          (List.mem_append_right registers.lengthT
            (List.mem_append_left (registers.lengthS ++ registers.scratch) hq))))) rfl
  · rcases hroles with haccumulator | htarget | haddend | hcarry | hcell | heqFlag
    · exact (intervalScratch_ne_sign registers k K target hlayout
        (haccumulator ▸ intervalAccumulator_mem_scratch registers k K target hlayout))
        haccumulator.symm
    · exact (intervalTargetAt_ne_sign registers k K (intervalTopRelative k K)
        target hlayout hlabel) htarget.symm
    · exact (intervalAddendAt_ne_sign registers k K (intervalTopRelative k K)
        target hlayout hlabel) haddend.symm
    · exact (intervalScratch_ne_sign registers k K target hlayout
        (hcarry ▸ intervalCarry_mem_scratch registers k K target hlayout)) hcarry.symm
    · exact (intervalScratch_ne_sign registers k K target hlayout
        (hcell ▸ intervalCellScratch_mem_scratch registers k K target hlayout)) hcell.symm
    · exact (intervalScratch_ne_sign registers k K target hlayout
        (heqFlag ▸ intervalCellScratch_mem_scratch registers k K target hlayout))
        heqFlag.symm
  · have hscratch : registers.sign ∈ registers.scratch := List.mem_of_mem_take heq
    exact (intervalScratch_ne_sign registers k K target hlayout hscratch) rfl

private theorem intervalMainTarget_not_mem_topSpecialSupport
    (registers : IntervalRegisters) (k K label : Nat)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target)
    (hspecial : intervalHasTopSpecial k K = true)
    (hlabel : label ∈ (intervalTree registers k K).labels) :
    registers.targetAt target label ∉
      topSpecialLeafSupport registers.control registers.control
        registers.lengthS registers.lengthQ (registers.accumulator k K)
        (registers.targetAt target (intervalTopRelative k K))
        (registers.addendAt target (intervalTopRelative k K))
        (registers.carry k K) (registers.cellScratch k K)
        (registers.cellScratch k K) (registers.equalityScratch k K) := by
  have hlabelBound := intervalTree_label_lt_laneCount registers k K label hlabel
  have htopBound := intervalTopRelative_lt_laneCount k K hlayout.k_le_K
  have hfixed := intervalTargetAt_not_mem_fixed registers k K label target hlayout hlabelBound
  have hneTop := intervalTree_label_ne_topRelative registers k K label hspecial hlabel
  have hneTarget : registers.targetAt target label ≠
      registers.targetAt target (intervalTopRelative k K) := by
    intro equality
    exact hneTop (intervalTargetAt_injective registers k K target hlayout
      hlabelBound htopBound equality)
  have hneAddend : registers.targetAt target label ≠
      registers.addendAt target (intervalTopRelative k K) :=
    intervalTargetAt_ne_addendAt registers k K target hlayout hlabelBound htopBound
  intro hwire
  simp only [topSpecialLeafSupport, List.mem_append, List.mem_dedup,
    List.mem_cons, List.not_mem_nil, or_false] at hwire
  rcases hwire with ((((hroot | hs) | hq) | hroles) | heq)
  · apply hfixed
    rcases hroot with hroot | hroot <;> rw [hroot] <;>
      simp [intervalFixedWires]
  · exact hfixed (by simp [intervalFixedWires, hs])
  · exact hfixed (by simp [intervalFixedWires, hq])
  · rcases hroles with haccumulator | htarget | haddend | hcarry | hcell | heqFlag
    · apply hfixed
      rw [haccumulator]
      simp [intervalFixedWires,
        intervalAccumulator_mem_scratch registers k K target hlayout]
    · exact hneTarget htarget
    · exact hneAddend haddend
    · apply hfixed
      rw [hcarry]
      simp [intervalFixedWires,
        intervalCarry_mem_scratch registers k K target hlayout]
    · apply hfixed
      rw [hcell]
      simp [intervalFixedWires,
        intervalCellScratch_mem_scratch registers k K target hlayout]
    · apply hfixed
      rw [heqFlag]
      simp [intervalFixedWires,
        intervalCellScratch_mem_scratch registers k K target hlayout]
  · apply hfixed
    have hscratch : registers.targetAt target label ∈ registers.scratch :=
      List.mem_of_mem_take heq
    simp [intervalFixedWires, hscratch]

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

private theorem intervalTopSecond_avoidsSignAndMainTargets
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target) :
    PaperCircuitAvoids
      (registers.sign ::
        (intervalTree registers k K).labels.map (registers.targetAt target))
      (intervalTopSecond registers k K mode target) := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopSecond, if_pos hspecial]
    apply PaperCircuitAvoids.ofUsesOnly
      (topSpecialSecondLeaf_usesOnly mode (intervalTopRelative k K)
        registers.lengthS registers.lengthQ (registers.accumulator k K)
        (registers.targetAt target (intervalTopRelative k K))
        (registers.addendAt target (intervalTopRelative k K))
        (registers.carry k K) (registers.cellScratch k K)
        (registers.cellScratch k K) (registers.equalityScratch k K)
        registers.control registers.control)
    rw [List.disjoint_left]
    intro wire hprotected hsupport
    rcases List.mem_cons.mp hprotected with hsign | htarget
    · subst wire
      exact intervalSign_not_mem_topSpecialSupport registers k K target hlayout hsupport
    · obtain ⟨label, hlabel, rfl⟩ := List.mem_map.mp htarget
      exact intervalMainTarget_not_mem_topSpecialSupport registers k K label target
        hlayout hspecial hlabel hsupport
  · simp [intervalTopSecond, hspecial, PaperCircuitAvoids]

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

private theorem intervalTraversal_avoidsSign
    (second : Bool) (registers : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    PaperCircuitAvoids [registers.sign]
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
  let tree := intervalTree registers k K
  let decoder := tree.decoderWires registers.control registers.control
    (registers.rightPaths k K) (registers.leftPaths k K)
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
  have hdecoder : ∀ wire, wire ∈ decoder → wire ∉ [registers.sign] := by
    intro wire hwire hsign
    simp only [List.mem_singleton] at hsign
    subst wire
    exact (intervalDecoder_ne_sign registers k K target hlayout
      (by simpa [tree, decoder] using hwire)) rfl
  have hleaf : ∀ label, label ∈ tree.labels →
      ∀ rightControl, rightControl ∈ decoder →
      ∀ leftControl, leftControl ∈ decoder →
        PaperCircuitAvoids [registers.sign]
          (leafAction label rightControl leftControl) := by
    intro label hlabel rightControl hright leftControl hleft
    have hlabelBound := intervalTree_label_lt_laneCount registers k K label
      (by simpa [tree] using hlabel)
    have hdisjoint : List.Disjoint [registers.sign]
        (intervalLeafSupport rightControl leftControl
          (registers.rightTop k K) (registers.leftTop k K)
          (registers.accumulator k K) (registers.targetAt target label)
          (registers.addendAt target label) (registers.carry k K)
          (registers.cellScratch k K)) := by
      intro wire hsign hsupport
      simp only [List.mem_singleton] at hsign
      subst wire
      simp only [intervalLeafSupport, List.mem_append, List.mem_dedup,
        List.mem_cons, List.not_mem_nil, or_false] at hsupport
      rcases hsupport with hcontrol | hrole
      · rcases hcontrol with hcontrol | hcontrol
        · exact (intervalDecoder_ne_sign registers k K target hlayout
            (by simpa [tree, decoder] using hright)) hcontrol.symm
        · exact (intervalDecoder_ne_sign registers k K target hlayout
            (by simpa [tree, decoder] using hleft)) hcontrol.symm
      · rcases hrole with hrightTop | hleftTop | haccumulator | htarget |
          haddend | hcarry | hscratch
        · exact (intervalRightTop_ne_sign registers k K target hlayout) hrightTop.symm
        · exact (intervalLeftTop_ne_sign registers k K target hlayout) hleftTop.symm
        · exact (intervalScratch_ne_sign registers k K target hlayout
            (intervalAccumulator_mem_scratch registers k K target hlayout))
            haccumulator.symm
        · exact (intervalTargetAt_ne_sign registers k K label target hlayout hlabelBound)
            htarget.symm
        · exact (intervalAddendAt_ne_sign registers k K label target hlayout hlabelBound)
            haddend.symm
        · exact (intervalScratch_ne_sign registers k K target hlayout
            (intervalCarry_mem_scratch registers k K target hlayout)) hcarry.symm
        · exact (intervalScratch_ne_sign registers k K target hlayout
            (intervalCellScratch_mem_scratch registers k K target hlayout)) hscratch.symm
    by_cases hsecond : second = true
    · simp only [leafAction, if_pos hsecond]
      exact PaperCircuitAvoids.ofUsesOnly
        (intervalSecondLeaf_usesOnly mode (intervalHasTopSpecial k K)
          (registers.rightTop k K) (registers.leftTop k K)
          (registers.accumulator k K) (registers.targetAt target label)
          (registers.addendAt target label) (registers.carry k K)
          (registers.cellScratch k K) label rightControl leftControl) hdisjoint
    · simp only [leafAction, if_neg hsecond]
      exact PaperCircuitAvoids.ofUsesOnly
        (intervalFirstLeaf_usesOnly mode (intervalHasTopSpecial k K)
          (registers.rightTop k K) (registers.leftTop k K)
          (registers.accumulator k K) (registers.targetAt target label)
          (registers.addendAt target label) (registers.carry k K)
          (registers.cellScratch k K) label rightControl leftControl) hdisjoint
  have havoid := dualUnaryActionUnitary_avoids
    (if second then .inc else .dec) leafAction tree registers.control registers.control
    (registers.rightPaths k K) (registers.leftPaths k K)
    (protectedWires := [registers.sign]) hlayout.traversal.1 hdecoder hleaf
  cases second <;>
    simpa [tree, leafAction, intervalFirstTraversal, intervalSecondTraversal] using havoid

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

private theorem intervalSignUpdate_agreesOutsideSign
    (registers : IntervalRegisters) (k K : Nat) (signUpdate : Bool)
    (state : BasisState) :
    AgreesOutside [registers.sign]
      (run (intervalSignUpdate registers k K signUpdate) state) state := by
  intro wire hwire
  simp only [List.mem_singleton] at hwire
  cases signUpdate with
  | false => rfl
  | true =>
      simp [intervalSignUpdate, Classical.run, Classical.applyGate, upd, hwire]

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

private theorem intervalMainTraversals_pair_preservesOutsideTargets
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (state : BasisState)
    (hlayout : IntervalLayout registers k K target) :
    AgreesOutside
      ((intervalTree registers k K).labels.map (registers.targetAt target))
      (run
        (intervalFirstTraversal mode (intervalHasTopSpecial k K)
            (registers.rightTop k K) (registers.leftTop k K)
            (registers.accumulator k K) (registers.carry k K)
            (registers.cellScratch k K) (registers.targetAt target)
            (registers.addendAt target) (intervalTree registers k K)
            registers.control registers.control (registers.rightPaths k K)
            (registers.leftPaths k K) ++
          intervalSecondTraversal mode (intervalHasTopSpecial k K)
            (registers.rightTop k K) (registers.leftTop k K)
            (registers.accumulator k K) (registers.carry k K)
            (registers.cellScratch k K) (registers.targetAt target)
            (registers.addendAt target) (intervalTree registers k K)
            registers.control registers.control (registers.rightPaths k K)
            (registers.leftPaths k K)) state)
      state := by
  apply intervalTraversals_pair_preservesOutsideTargets mode
    (intervalHasTopSpecial k K) (registers.rightTop k K)
    (registers.leftTop k K) (registers.accumulator k K)
    (registers.carry k K) (registers.cellScratch k K)
    (registers.targetAt target) (registers.addendAt target)
    (intervalTree registers k K) registers.control registers.control
    (registers.rightPaths k K) (registers.leftPaths k K) state hlayout.traversal
  · rw [intervalTree_labels]
    exact Finset.sort_nodup _ _
  · intro label hlabel other hother hne
    have hlabelBound := intervalTree_label_lt_laneCount registers k K label hlabel
    have hotherBound := intervalTree_label_lt_laneCount registers k K other hother
    have htargetNe : registers.targetAt target other ≠
        registers.targetAt target label := by
      intro equality
      exact hne (intervalTargetAt_injective registers k K target hlayout
        hotherBound hlabelBound equality)
    have haddendNe : registers.targetAt target other ≠
        registers.addendAt target label :=
      intervalTargetAt_ne_addendAt registers k K target hlayout
        hotherBound hlabelBound
    have hroles := (hlayout.traversal.2 other hother).1
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at hroles
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    aesop

private theorem intervalTop_pair_preservesOutsideTarget
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (state : BasisState)
    (hlayout : IntervalLayout registers k K target)
    (hclean : Clean
      (registers.cellScratch k K :: registers.equalityScratch k K) state) :
    AgreesOutside [registers.targetAt target (intervalTopRelative k K)]
      (run (intervalTopFirst registers k K mode target ++
        intervalTopSecond registers k K mode target) state)
      state := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopFirst, if_pos hspecial, intervalTopSecond, if_pos hspecial]
    apply topSpecialLeaf_pair_preservesOutsideTarget mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control state (hlayout.topSpecial hspecial) hclean
    have hlabel := intervalTopRelative_lt_laneCount k K hlayout.k_le_K
    have htargetFixed := intervalTargetAt_not_mem_fixed registers k K
      (intervalTopRelative k K) target hlayout hlabel
    intro hsupport
    apply htargetFixed
    simp only [List.mem_cons, List.mem_append] at hsupport
    rcases hsupport with (hcontrol | haccumulator | hregister) | hcell | hequality
    · rw [hcontrol]
      simp [intervalFixedWires]
    · rw [haccumulator]
      simp [intervalFixedWires,
        intervalAccumulator_mem_scratch registers k K target hlayout]
    · simp [intervalFixedWires, hregister]
    · rw [hcell]
      simp [intervalFixedWires,
        intervalCellScratch_mem_scratch registers k K target hlayout]
    · have hscratch : registers.targetAt target (intervalTopRelative k K) ∈
          registers.scratch := List.mem_of_mem_take hequality
      simp [intervalFixedWires, hscratch]
  · simp [intervalTopFirst, intervalTopSecond, hspecial, AgreesOutside]

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

/-! ## Source inverse aggregate -/

/-- The source's `inverse=True` branch switches each ripple pass to the opposite arithmetic mode. -/
def RippleMode.inverse : RippleMode → RippleMode
  | .add => .sub
  | .sub => .add

@[simp]
theorem RippleMode.inverse_inverse (mode : RippleMode) :
    mode.inverse.inverse = mode := by
  cases mode <;> rfl

theorem rippleFirstCell_inverse_eq
    (mode : RippleMode) (control target addend carry scratch : Wire) :
    rippleFirstCell mode.inverse control target addend carry scratch =
      (rippleSecondCell mode control target addend carry scratch).adjoint := by
  cases mode <;>
    simp [RippleMode.inverse, rippleFirstCell, rippleSecondCell,
      controlledMaj, controlledUma, controlledMajInv, controlledUmaInv,
      cleanC3X, Circuit.adjoint]

theorem rippleSecondCell_inverse_eq
    (mode : RippleMode) (control target addend carry scratch : Wire) :
    rippleSecondCell mode.inverse control target addend carry scratch =
      (rippleFirstCell mode control target addend carry scratch).adjoint := by
  cases mode <;>
    simp [RippleMode.inverse, rippleFirstCell, rippleSecondCell,
      controlledMaj, controlledUma, controlledMajInv, controlledUmaInv,
      cleanC3X, Circuit.adjoint]

/-- Reversing a unary traversal exchanges its increasing and decreasing source orders. -/
def UnaryOrder.reverse : UnaryOrder → UnaryOrder
  | .inc => .dec
  | .dec => .inc

@[simp]
theorem UnaryOrder.reverse_reverse (order : UnaryOrder) :
    order.reverse.reverse = order := by
  cases order <;> rfl

@[simp]
private theorem computeZeroAnd_adjoint
    (control indexBit target : Wire) :
    (computeZeroAnd control indexBit target).adjoint =
      computeZeroAnd control indexBit target := by
  simp [computeZeroAnd, Circuit.adjoint]

theorem dualUnaryActionUnitary_reverse_eq_adjoint
    (order : UnaryOrder)
    (leafAction inverseLeafAction : Nat → Wire → Wire → Circuit)
    (hleaf : ∀ label controlA controlB,
      inverseLeafAction label controlA controlB =
        (leafAction label controlA controlB).adjoint)
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (ancillasA ancillasB : List Wire) :
    dualUnaryActionUnitary order.reverse inverseLeafAction tree controlA controlB
        ancillasA ancillasB =
      (dualUnaryActionUnitary order leafAction tree controlA controlB
        ancillasA ancillasB).adjoint := by
  induction tree generalizing controlA controlB ancillasA ancillasB with
  | leaf label =>
      exact hleaf label controlA controlB
  | node indexBitA indexBitB zero one ihZero ihOne =>
      cases ancillasA with
      | nil => simp [dualUnaryActionUnitary]
      | cons pathA restA =>
          cases ancillasB with
          | nil => simp [dualUnaryActionUnitary]
          | cons pathB restB =>
              cases order <;>
                simp only [UnaryOrder.reverse] at ihZero ihOne ⊢ <;>
                simp [dualUnaryActionUnitary, circuit_adjoint_append,
                  ihZero, ihOne]

@[simp]
private theorem endpointLeafToggle_adjoint
    (topSpecial : Bool) (label : Nat)
    (endpointTop control accumulator : Wire) :
    (endpointLeafToggle topSpecial label endpointTop control accumulator).adjoint =
      endpointLeafToggle topSpecial label endpointTop control accumulator := by
  unfold endpointLeafToggle
  split <;> simp [Circuit.adjoint]

theorem intervalFirstLeaf_inverse_eq_adjoint_second
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    intervalFirstLeaf mode.inverse topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl =
      (intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl).adjoint := by
  simp [intervalFirstLeaf, intervalSecondLeaf, circuit_adjoint_append,
    rippleFirstCell_inverse_eq]

theorem intervalSecondLeaf_inverse_eq_adjoint_first
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    intervalSecondLeaf mode.inverse topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl =
      (intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl).adjoint := by
  simp [intervalFirstLeaf, intervalSecondLeaf, circuit_adjoint_append,
    rippleSecondCell_inverse_eq]

theorem intervalFirstTraversal_inverse_eq_adjoint_second
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) :
    intervalFirstTraversal mode.inverse topSpecial rightTop leftTop accumulator
        carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths =
      (intervalSecondTraversal mode topSpecial rightTop leftTop accumulator
        carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).adjoint := by
  apply dualUnaryActionUnitary_reverse_eq_adjoint .inc
  intro label controlA controlB
  exact intervalFirstLeaf_inverse_eq_adjoint_second mode topSpecial
    rightTop leftTop accumulator (targetAt label) (addendAt label)
    carry scratch label controlA controlB

theorem intervalSecondTraversal_inverse_eq_adjoint_first
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) :
    intervalSecondTraversal mode.inverse topSpecial rightTop leftTop accumulator
        carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths =
      (intervalFirstTraversal mode topSpecial rightTop leftTop accumulator
        carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).adjoint := by
  apply dualUnaryActionUnitary_reverse_eq_adjoint .dec
  intro label controlA controlB
  exact intervalSecondLeaf_inverse_eq_adjoint_first mode topSpecial
    rightTop leftTop accumulator (targetAt label) (addendAt label)
    carry scratch label controlA controlB

private theorem run_toggleEqConstUnderControl_twice
    (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire)
    (state : BasisState)
    (hlayout : EqControlLayout root register accumulator flag scratches)
    (hclean : Clean (flag :: scratches) state) :
    run (toggleEqConstUnderControl root register value accumulator flag scratches)
        (run (toggleEqConstUnderControl root register value accumulator flag scratches)
          state) = state := by
  let circuit := toggleEqConstUnderControl root register value accumulator flag scratches
  let after := run circuit state
  have hfirst : after =
      state[accumulator ↦ Bool.xor (state accumulator)
        (state root && registerMatches register value state)] := by
    exact run_toggleEqConstUnderControl root register value accumulator flag scratches
      state hlayout hclean
  have hcleanAfter : Clean (flag :: scratches) after := by
    exact toggleEqConstUnderControl_clean root register value accumulator flag scratches
      state hlayout hclean
  have hsecond := run_toggleEqConstUnderControl root register value accumulator flag scratches
    after hlayout hcleanAfter
  change run circuit after = state
  rw [hsecond, hfirst]
  have haccRoot : accumulator ≠ root := by
    intro h
    subst root
    simpa using (List.nodup_cons.mp hlayout.2).1
  have haccRegister : accumulator ∉ register := by
    intro h
    exact (List.nodup_cons.mp (List.nodup_cons.mp hlayout.2).2).1 (by simp [h])
  have hmatch :
      registerMatches register value
          state[accumulator ↦ Bool.xor (state accumulator)
            (state root && registerMatches register value state)] =
        registerMatches register value state := by
    exact registerMatchesFrom_upd_not_mem register value 0 state accumulator _
      haccRegister
  funext wire
  by_cases hwire : wire = accumulator
  · subst wire
    simp [upd, Ne.symm haccRoot, hmatch]
  · simp [upd, hwire]

private theorem run_toggleEqConstUnderControl_eq_adjoint
    (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire)
    (state : BasisState)
    (hlayout : EqControlLayout root register accumulator flag scratches)
    (hclean : Clean (flag :: scratches) state) :
    run (toggleEqConstUnderControl root register value accumulator flag scratches)
        state =
      run (toggleEqConstUnderControl root register value accumulator flag scratches).adjoint
        state := by
  let circuit := toggleEqConstUnderControl root register value accumulator flag scratches
  have htwice := run_toggleEqConstUnderControl_twice root register value accumulator
    flag scratches state hlayout hclean
  have hadjoint := run_adjoint_run_classical circuit
    (toggleEqConstUnderControl_wellFormed root register value accumulator flag scratches
      hlayout) (run circuit state)
  change run circuit state = run circuit.adjoint state
  rw [htwice] at hadjoint
  exact hadjoint.symm

private theorem run_topSpecialFirstLeaf_inverse_eq_adjoint_second
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (state : BasisState)
    (hlayout : TopSpecialLeafLayout rightRoot leftRoot rightRegister leftRegister
      accumulator target addend carry rippleScratch eqFlag eqScratches)
    (hclean : Clean (eqFlag :: eqScratches) state) :
    run (topSpecialFirstLeaf mode.inverse topValue rightRegister leftRegister
        accumulator target addend carry rippleScratch eqFlag eqScratches
        rightRoot leftRoot) state =
      run (topSpecialSecondLeaf mode topValue rightRegister leftRegister
        accumulator target addend carry rippleScratch eqFlag eqScratches
        rightRoot leftRoot).adjoint state := by
  have heq : eqFlag = rippleScratch := hlayout.2.2.2.1
  subst eqFlag
  let rightCircuit := toggleEqConstUnderControl rightRoot rightRegister topValue
    accumulator rippleScratch eqScratches
  let cellCircuit := rippleFirstCell mode.inverse accumulator target addend carry
    rippleScratch
  let afterRight := run rightCircuit state
  let afterCell := run cellCircuit afterRight
  have hrightClean : Clean (rippleScratch :: eqScratches) afterRight := by
    exact toggleEqConstUnderControl_clean rightRoot rightRegister topValue
      accumulator rippleScratch eqScratches state hlayout.1 hclean
  have hcellClean : Clean (rippleScratch :: eqScratches) afterCell := by
    intro wire hwire
    rcases List.mem_cons.mp hwire with hhead | hwire
    · subst wire
      change run cellCircuit afterRight rippleScratch = false
      rw [show run cellCircuit afterRight rippleScratch = afterRight rippleScratch by
        exact rippleFirstCell_preservesScratch mode.inverse accumulator target addend carry
          rippleScratch afterRight hlayout.2.2.1]
      exact hrightClean rippleScratch (by simp)
    · change run cellCircuit afterRight wire = false
      rw [(rippleFirstCell_usesOnly mode.inverse accumulator target addend carry
        rippleScratch).preservesOutside afterRight (by
          have hdisjoint := hlayout.2.2.2.2
          rw [List.disjoint_left] at hdisjoint
          exact hdisjoint hwire)]
      exact hrightClean wire (by simp [hwire])
  rw [topSpecialFirstLeaf, topSpecialSecondLeaf,
    circuit_adjoint_append, circuit_adjoint_append]
  simp only [Classical.run_append]
  rw [← run_toggleEqConstUnderControl_eq_adjoint rightRoot rightRegister topValue
    accumulator rippleScratch eqScratches state hlayout.1 hclean]
  rw [rippleFirstCell_inverse_eq]
  simpa [afterCell, cellCircuit, afterRight, rightCircuit,
    rippleFirstCell_inverse_eq] using
    (run_toggleEqConstUnderControl_eq_adjoint leftRoot leftRegister topValue
      accumulator rippleScratch eqScratches afterCell hlayout.2.1 hcellClean)

private theorem run_topSpecialSecondLeaf_inverse_eq_adjoint_first
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (state : BasisState)
    (hlayout : TopSpecialLeafLayout rightRoot leftRoot rightRegister leftRegister
      accumulator target addend carry rippleScratch eqFlag eqScratches)
    (hclean : Clean (eqFlag :: eqScratches) state) :
    run (topSpecialSecondLeaf mode.inverse topValue rightRegister leftRegister
        accumulator target addend carry rippleScratch eqFlag eqScratches
        rightRoot leftRoot) state =
      run (topSpecialFirstLeaf mode topValue rightRegister leftRegister
        accumulator target addend carry rippleScratch eqFlag eqScratches
        rightRoot leftRoot).adjoint state := by
  have heq : eqFlag = rippleScratch := hlayout.2.2.2.1
  subst eqFlag
  let leftCircuit := toggleEqConstUnderControl leftRoot leftRegister topValue
    accumulator rippleScratch eqScratches
  let cellCircuit := rippleSecondCell mode.inverse accumulator target addend carry
    rippleScratch
  let afterLeft := run leftCircuit state
  let afterCell := run cellCircuit afterLeft
  have hleftClean : Clean (rippleScratch :: eqScratches) afterLeft := by
    exact toggleEqConstUnderControl_clean leftRoot leftRegister topValue
      accumulator rippleScratch eqScratches state hlayout.2.1 hclean
  have hcellClean : Clean (rippleScratch :: eqScratches) afterCell := by
    intro wire hwire
    rcases List.mem_cons.mp hwire with hhead | hwire
    · subst wire
      change run cellCircuit afterLeft rippleScratch = false
      rw [show run cellCircuit afterLeft rippleScratch = afterLeft rippleScratch by
        exact rippleSecondCell_preservesScratch mode.inverse accumulator target addend carry
          rippleScratch afterLeft hlayout.2.2.1]
      exact hleftClean rippleScratch (by simp)
    · change run cellCircuit afterLeft wire = false
      rw [(rippleSecondCell_usesOnly mode.inverse accumulator target addend carry
        rippleScratch).preservesOutside afterLeft (by
          have hdisjoint := hlayout.2.2.2.2
          rw [List.disjoint_left] at hdisjoint
          exact hdisjoint hwire)]
      exact hleftClean wire (by simp [hwire])
  rw [topSpecialSecondLeaf, topSpecialFirstLeaf,
    circuit_adjoint_append, circuit_adjoint_append]
  simp only [Classical.run_append]
  rw [← run_toggleEqConstUnderControl_eq_adjoint leftRoot leftRegister topValue
    accumulator rippleScratch eqScratches state hlayout.2.1 hclean]
  rw [rippleSecondCell_inverse_eq]
  simpa [afterCell, cellCircuit, afterLeft, leftCircuit,
    rippleSecondCell_inverse_eq] using
    (run_toggleEqConstUnderControl_eq_adjoint rightRoot rightRegister topValue
      accumulator rippleScratch eqScratches afterCell hlayout.1 hcellClean)

private theorem run_intervalTopFirst_inverse_eq_adjoint_second
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (state : BasisState)
    (hlayout : IntervalLayout registers k K target)
    (hclean : Clean
      (registers.cellScratch k K :: registers.equalityScratch k K) state) :
    run (intervalTopFirst registers k K mode.inverse target) state =
      run (intervalTopSecond registers k K mode target).adjoint state := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopFirst, if_pos hspecial, intervalTopSecond, if_pos hspecial]
    exact run_topSpecialFirstLeaf_inverse_eq_adjoint_second mode
      (intervalTopRelative k K) registers.lengthS registers.lengthQ
      (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control state (hlayout.topSpecial hspecial) hclean
  · simp [intervalTopFirst, intervalTopSecond, hspecial]

private theorem run_intervalTopSecond_inverse_eq_adjoint_first
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (state : BasisState)
    (hlayout : IntervalLayout registers k K target)
    (hclean : Clean
      (registers.cellScratch k K :: registers.equalityScratch k K) state) :
    run (intervalTopSecond registers k K mode.inverse target) state =
      run (intervalTopFirst registers k K mode target).adjoint state := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [intervalTopSecond, if_pos hspecial, intervalTopFirst, if_pos hspecial]
    exact run_topSpecialSecondLeaf_inverse_eq_adjoint_first mode
      (intervalTopRelative k K) registers.lengthS registers.lengthQ
      (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control state (hlayout.topSpecial hspecial) hclean
  · simp [intervalTopFirst, intervalTopSecond, hspecial]

@[simp]
private theorem intervalSignUpdate_adjoint
    (registers : IntervalRegisters) (k K : Nat) (signUpdate : Bool) :
    (intervalSignUpdate registers k K signUpdate).adjoint =
      intervalSignUpdate registers k K signUpdate := by
  cases signUpdate <;> simp [intervalSignUpdate, Circuit.adjoint]

private def intervalAddSubBodyUnitary
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) : Circuit :=
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
    intervalTopSecond registers k K mode target

private theorem intervalAddSubBodyUnitary_wellFormed
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    CircuitWellFormed
      (intervalAddSubBodyUnitary registers k K mode signUpdate target) := by
  simp only [intervalAddSubBodyUnitary, circuitWellFormed_append]
  exact ⟨⟨⟨⟨
    intervalTopFirst_wellFormed registers k K mode target hlayout,
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
    intervalTopSecond_wellFormed registers k K mode target hlayout⟩

private theorem intervalAddSubBodyUnitary_preservesOutsideChanges
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) (state : BasisState)
    (hlayout : IntervalLayout registers k K target)
    (hclean : Clean
      (registers.cellScratch k K :: registers.equalityScratch k K) state) :
    AgreesOutside
      ((registers.sign ::
          (intervalTree registers k K).labels.map (registers.targetAt target)) ++
        [registers.targetAt target (intervalTopRelative k K)])
      (run (intervalAddSubBodyUnitary registers k K mode signUpdate target) state)
      state := by
  let topFirst := intervalTopFirst registers k K mode target
  let first := intervalFirstTraversal mode (intervalHasTopSpecial k K)
    (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
    (registers.carry k K) (registers.cellScratch k K)
    (registers.targetAt target) (registers.addendAt target)
    (intervalTree registers k K) registers.control registers.control
    (registers.rightPaths k K) (registers.leftPaths k K)
  let sign := intervalSignUpdate registers k K signUpdate
  let second := intervalSecondTraversal mode (intervalHasTopSpecial k K)
    (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
    (registers.carry k K) (registers.cellScratch k K)
    (registers.targetAt target) (registers.addendAt target)
    (intervalTree registers k K) registers.control registers.control
    (registers.rightPaths k K) (registers.leftPaths k K)
  let topSecond := intervalTopSecond registers k K mode target
  let afterTop := run topFirst state
  let afterFirst := run first afterTop
  let afterSign := run sign afterFirst
  let afterSecond := run second afterSign
  have hsign : AgreesOutside [registers.sign] afterSign afterFirst := by
    simpa only [afterSign, sign] using
      intervalSignUpdate_agreesOutsideSign registers k K signUpdate afterFirst
  have hsecondSign : AgreesOutside [registers.sign]
      afterSecond (run second afterFirst) := by
    change AgreesOutside [registers.sign]
      (run second afterSign) (run second afterFirst)
    have havoid := intervalTraversal_avoidsSign true registers k K mode target hlayout
    simpa only [second] using havoid.run_agreesOutside hsign
  have hmain : AgreesOutside
      ((intervalTree registers k K).labels.map (registers.targetAt target))
      (run second (run first afterTop)) afterTop := by
    simpa only [first, second, Classical.run_append] using
      intervalMainTraversals_pair_preservesOutsideTargets registers k K mode target
        afterTop hlayout
  have hthroughMain : AgreesOutside
      (registers.sign ::
        (intervalTree registers k K).labels.map (registers.targetAt target))
      afterSecond afterTop := by
    intro wire hwire
    simp only [List.mem_cons, not_or] at hwire
    rw [hsecondSign wire (by simpa using hwire.1)]
    exact hmain wire hwire.2
  have htopTransport : AgreesOutside
      (registers.sign ::
        (intervalTree registers k K).labels.map (registers.targetAt target))
      (run topSecond afterSecond) (run topSecond afterTop) := by
    have havoid := intervalTopSecond_avoidsSignAndMainTargets registers k K mode target
      hlayout
    simpa only [topSecond] using havoid.run_agreesOutside hthroughMain
  have htopPair : AgreesOutside
      [registers.targetAt target (intervalTopRelative k K)]
      (run topSecond afterTop) state := by
    simpa only [topFirst, topSecond, afterTop, Classical.run_append] using
      intervalTop_pair_preservesOutsideTarget registers k K mode target state hlayout hclean
  have hcombined : AgreesOutside
      ((registers.sign ::
          (intervalTree registers k K).labels.map (registers.targetAt target)) ++
        [registers.targetAt target (intervalTopRelative k K)])
      (run topSecond afterSecond) state := by
    intro wire hwire
    simp only [List.mem_append, not_or] at hwire
    rw [htopTransport wire hwire.1]
    exact htopPair wire hwire.2
  simpa only [intervalAddSubBodyUnitary, topFirst, first, sign, second, topSecond,
    afterTop, afterFirst, afterSign, afterSecond, Classical.run_append] using hcombined

private theorem intervalScratch_not_mem_bodyChanges
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target)
    {wire : Wire} (hscratch : wire ∈ registers.scratch) :
    wire ∉
      ((registers.sign ::
          (intervalTree registers k K).labels.map (registers.targetAt target)) ++
        [registers.targetAt target (intervalTopRelative k K)]) := by
  intro hchanged
  rcases List.mem_append.mp hchanged with hmain | htop
  · rcases List.mem_cons.mp hmain with hsign | htargets
    · exact (intervalScratch_ne_sign registers k K target hlayout hscratch) hsign
    obtain ⟨label, hlabel, equality⟩ := List.mem_map.mp htargets
    have hbound := intervalTree_label_lt_laneCount registers k K label hlabel
    cases target with
    | work1 =>
        apply intervalScratch_not_mem_work1 registers k K .work1 hlayout hscratch
        exact equality ▸ list_getD_mem registers.work1 label 0 (by
          rw [hlayout.work1_length]
          exact hbound)
    | work2 =>
        apply intervalScratch_not_mem_work2 registers k K .work2 hlayout hscratch
        exact equality ▸ list_getD_mem registers.work2 label 0 (by
          rw [hlayout.work2_length]
          exact hbound)
  · simp only [List.mem_singleton] at htop
    have hbound := intervalTopRelative_lt_laneCount k K hlayout.k_le_K
    cases target with
    | work1 =>
        apply intervalScratch_not_mem_work1 registers k K .work1 hlayout hscratch
        exact htop.symm ▸ list_getD_mem registers.work1 (intervalTopRelative k K) 0
          (by rw [hlayout.work1_length]; exact hbound)
    | work2 =>
        apply intervalScratch_not_mem_work2 registers k K .work2 hlayout hscratch
        exact htop.symm ▸ list_getD_mem registers.work2 (intervalTopRelative k K) 0
          (by rw [hlayout.work2_length]; exact hbound)

private theorem intervalAddSubBodyUnitary_cleanScratch
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) (state : BasisState)
    (hlayout : IntervalLayout registers k K target)
    (hready : IntervalReady registers state) :
    Clean registers.scratch
      (run (intervalAddSubBodyUnitary registers k K mode signUpdate target) state) := by
  have htop : Clean
      (registers.cellScratch k K :: registers.equalityScratch k K) state := by
    intro wire hwire
    exact hready wire
      (intervalTopScratch_mem_scratch registers k K target hlayout wire hwire)
  have hbody := intervalAddSubBodyUnitary_preservesOutsideChanges registers k K mode
    signUpdate target state hlayout htop
  intro wire hwire
  rw [hbody wire
    (intervalScratch_not_mem_bodyChanges registers k K target hlayout hwire)]
  exact hready wire hwire

/-- The complete forward interval restores its entire shared scratch bank from the sole input
`IntervalReady` premise. -/
theorem intervalAddSubUnitary_ready
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) (state : BasisState)
    (hlayout : IntervalLayout registers k K target)
    (hready : IntervalReady registers state) :
    IntervalReady registers
      (run (intervalAddSubUnitary registers n k K mode signUpdate target) state) := by
  let prepare := prepareIntervalEndpoints registers.lengthT registers.lengthQ
    registers.lengthS registers.endpointScratch (registers.carry k K) n k
  let body := intervalAddSubBodyUnitary registers k K mode signUpdate target
  let restore := restoreIntervalEndpoints registers.lengthT registers.lengthQ
    registers.lengthS registers.endpointScratch (registers.carry k K) n k
  let prepared := run prepare state
  let afterBody := run body prepared
  have hprepared : IntervalReady registers prepared := by
    simpa only [IntervalReady, prepare, prepared] using
      intervalPrepare_cleanScratch registers n k K target state hlayout hready
  have hafterBody : Clean registers.scratch afterBody := by
    simpa only [body, afterBody] using
      intervalAddSubBodyUnitary_cleanScratch registers k K mode signUpdate target
        prepared hlayout hprepared
  have hendpoint : Clean
      (registers.endpointScratch ++ [registers.carry k K]) afterBody := by
    intro wire hwire
    apply hafterBody wire
    rcases List.mem_append.mp hwire with hscratch | hcarry
    · exact List.mem_of_mem_take hscratch
    · simp only [List.mem_singleton] at hcarry
      subst wire
      exact intervalCarry_mem_scratch registers k K target hlayout
  have hrestore := restoreIntervalEndpoints_correct registers.lengthT registers.lengthQ
    registers.lengthS registers.endpointScratch (registers.carry k K) n k afterBody
    hlayout.lengthT_eq_lengthQ
    (intervalLengthQ_le_endpointScratch registers k K target hlayout)
    (intervalLengthS_le_endpointScratch registers k K target hlayout)
    (intervalLengthS_positive registers k K target hlayout) hlayout.endpoints hendpoint
  have hshape :
      run (intervalAddSubUnitary registers n k K mode signUpdate target) state =
        run restore afterBody := by
    simp only [intervalAddSubUnitary, intervalAddSubBodyUnitary, prepare, body, restore,
      prepared, afterBody, Classical.run_append]
  intro wire hwire
  rw [hshape, hrestore.2.2.2.2 wire
    (intervalScratch_not_mem_lengthQ registers k K target hlayout hwire)
    (intervalScratch_not_mem_lengthS registers k K target hlayout hwire)]
  exact hafterBody wire hwire

private theorem run_intervalAddSubBodyUnitary_inverse_eq_adjoint
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) (state : BasisState)
    (hlayout : IntervalLayout registers k K target)
    (hclean : Clean
      (registers.cellScratch k K :: registers.equalityScratch k K) state) :
    run (intervalAddSubBodyUnitary registers k K mode.inverse signUpdate target) state =
      run (intervalAddSubBodyUnitary registers k K mode signUpdate target).adjoint state := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · let topFirstInv := intervalTopFirst registers k K mode.inverse target
    let firstInv := intervalFirstTraversal mode.inverse (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K)
      (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K)
    let sign := intervalSignUpdate registers k K signUpdate
    let secondInv := intervalSecondTraversal mode.inverse (intervalHasTopSpecial k K)
      (registers.rightTop k K) (registers.leftTop k K) (registers.accumulator k K)
      (registers.carry k K) (registers.cellScratch k K)
      (registers.targetAt target) (registers.addendAt target)
      (intervalTree registers k K) registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K)
    let afterTop := run topFirstInv state
    let afterFirst := run firstInv afterTop
    let afterSign := run sign afterFirst
    let afterSecond := run secondInv afterSign
    have hcleanTop : Clean
        (registers.cellScratch k K :: registers.equalityScratch k K) afterTop := by
      exact intervalTopFirst_cleanTopScratch registers k K mode.inverse target state
        hlayout hclean
    have hpathsTop := intervalPaths_clean_of_topScratch registers k K afterTop hcleanTop
    have hcleanFirst : Clean
        (registers.cellScratch k K :: registers.equalityScratch k K) afterFirst := by
      intro wire hwire
      change run firstInv afterTop wire = false
      rw [show run firstInv afterTop wire = afterTop wire by
        simpa only [firstInv] using
          intervalTraversal_preservesTopScratch false registers k K mode.inverse target
            hlayout hspecial afterTop hpathsTop.1 hpathsTop.2 wire hwire]
      exact hcleanTop wire hwire
    have hcleanSign : Clean
        (registers.cellScratch k K :: registers.equalityScratch k K) afterSign := by
      intro wire hwire
      change run sign afterFirst wire = false
      rw [show run sign afterFirst wire = afterFirst wire by
        simpa only [sign] using
          intervalSignUpdate_preservesScratch registers k K signUpdate target afterFirst
            hlayout wire
              (intervalTopScratch_mem_scratch registers k K target hlayout wire hwire)]
      exact hcleanFirst wire hwire
    have hpathsSign := intervalPaths_clean_of_topScratch registers k K afterSign hcleanSign
    have hcleanSecond : Clean
        (registers.cellScratch k K :: registers.equalityScratch k K) afterSecond := by
      intro wire hwire
      change run secondInv afterSign wire = false
      rw [show run secondInv afterSign wire = afterSign wire by
        simpa only [secondInv] using
          intervalTraversal_preservesTopScratch true registers k K mode.inverse target
            hlayout hspecial afterSign hpathsSign.1 hpathsSign.2 wire hwire]
      exact hcleanSign wire hwire
    have hafterSecond : afterSecond =
        run (intervalFirstTraversal mode (intervalHasTopSpecial k K)
          (registers.rightTop k K) (registers.leftTop k K)
          (registers.accumulator k K) (registers.carry k K)
          (registers.cellScratch k K) (registers.targetAt target)
          (registers.addendAt target) (intervalTree registers k K)
          registers.control registers.control (registers.rightPaths k K)
          (registers.leftPaths k K)).adjoint
          (run (intervalSignUpdate registers k K signUpdate)
            (run (intervalSecondTraversal mode (intervalHasTopSpecial k K)
              (registers.rightTop k K) (registers.leftTop k K)
              (registers.accumulator k K) (registers.carry k K)
              (registers.cellScratch k K) (registers.targetAt target)
              (registers.addendAt target) (intervalTree registers k K)
              registers.control registers.control (registers.rightPaths k K)
              (registers.leftPaths k K)).adjoint
              (run (intervalTopSecond registers k K mode target).adjoint state))) := by
      simp only [afterSecond, afterSign, afterFirst, afterTop, secondInv, sign,
        firstInv, topFirstInv]
      rw [run_intervalTopFirst_inverse_eq_adjoint_second registers k K mode target
        state hlayout hclean]
      rw [intervalFirstTraversal_inverse_eq_adjoint_second]
      rw [intervalSecondTraversal_inverse_eq_adjoint_first]
    rw [intervalAddSubBodyUnitary, intervalAddSubBodyUnitary,
      circuit_adjoint_append, circuit_adjoint_append,
      circuit_adjoint_append, circuit_adjoint_append]
    simp only [Classical.run_append]
    rw [run_intervalTopFirst_inverse_eq_adjoint_second registers k K mode target state
      hlayout hclean]
    rw [intervalFirstTraversal_inverse_eq_adjoint_second]
    rw [intervalSignUpdate_adjoint]
    rw [intervalSecondTraversal_inverse_eq_adjoint_first]
    rw [← hafterSecond]
    exact run_intervalTopSecond_inverse_eq_adjoint_first registers k K mode target
      afterSecond hlayout hcleanSecond
  · simp [intervalAddSubBodyUnitary, intervalTopFirst, intervalTopSecond,
      hspecial, circuit_adjoint_append,
      intervalFirstTraversal_inverse_eq_adjoint_second,
      intervalSecondTraversal_inverse_eq_adjoint_first]

/-- Coherent source inverse: the pinned generator reuses the same interval wrapper with the
opposite ripple mode. -/
def intervalAddSubInverseUnitary
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) : Circuit :=
  intervalAddSubUnitary registers n k K mode.inverse signUpdate target

/-- Measurement-uncomputed source inverse, using the same inverse-mode specialization. -/
def intervalAddSubInverse
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) : Quantum.AdaptiveCircuit :=
  intervalAddSub registers n k K mode.inverse signUpdate target

@[simp]
theorem intervalAddSubInverseUnitary_HPFree
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) :
    HPFree (intervalAddSubInverseUnitary registers n k K mode signUpdate target) := by
  simp [intervalAddSubInverseUnitary]

theorem intervalAddSubInverseUnitary_usesOnly
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    PaperCircuitUsesOnly registers.allWires
      (intervalAddSubInverseUnitary registers n k K mode signUpdate target) := by
  simpa [intervalAddSubInverseUnitary] using
    intervalAddSubUnitary_usesOnly registers n k K mode.inverse signUpdate target hlayout

theorem intervalAddSubInverseUnitary_preservesOutside
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) (state : BasisState)
    (hlayout : IntervalLayout registers k K target)
    {wire : Wire} (hwire : wire ∉ registers.allWires) :
    run (intervalAddSubInverseUnitary registers n k K mode signUpdate target) state wire =
      state wire := by
  exact PaperCircuitUsesOnly.preservesOutside
    (intervalAddSubInverseUnitary_usesOnly registers n k K mode signUpdate target hlayout)
    state hwire

theorem intervalAddSubInverseUnitary_wellFormed
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    CircuitWellFormed
      (intervalAddSubInverseUnitary registers n k K mode signUpdate target) := by
  simpa [intervalAddSubInverseUnitary] using
    intervalAddSubUnitary_wellFormed registers n k K mode.inverse signUpdate target hlayout

theorem intervalAddSubInverse_wellFormed
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    (intervalAddSubInverse registers n k K mode signUpdate target).WellFormed := by
  simpa [intervalAddSubInverse] using
    intervalAddSub_wellFormed registers n k K mode.inverse signUpdate target hlayout

theorem run_intervalAddSubInverseUnitary_state
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) (state : BasisState)
    (hlayout : IntervalLayout registers k K target)
    (hready : IntervalReady registers state) :
    run (intervalAddSubInverseUnitary registers n k K mode signUpdate target) state =
      intervalAddSubState registers n k K mode.inverse signUpdate target state := by
  exact run_intervalAddSubUnitary_state registers n k K mode.inverse signUpdate target
    state hlayout hready

/-- The inverse-mode specialization restores the same complete shared scratch bank. -/
theorem intervalAddSubInverseUnitary_ready
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) (state : BasisState)
    (hlayout : IntervalLayout registers k K target)
    (hready : IntervalReady registers state) :
    IntervalReady registers
      (run (intervalAddSubInverseUnitary registers n k K mode signUpdate target) state) := by
  simpa [intervalAddSubInverseUnitary] using
    intervalAddSubUnitary_ready registers n k K mode.inverse signUpdate target state
      hlayout hready

theorem intervalAddSubInverse_coherent
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    CoherentlyImplementsOn
      (intervalAddSubInverse registers n k K mode signUpdate target)
      (Quantum.run
        (intervalAddSubInverseUnitary registers n k K mode signUpdate target))
      (IntervalReady registers) := by
  simpa [intervalAddSubInverse, intervalAddSubInverseUnitary] using
    intervalAddSub_coherent registers n k K mode.inverse signUpdate target hlayout

@[simp]
theorem intervalToffoliFormula_inverse
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode) :
    intervalToffoliFormula registers k K mode.inverse =
      intervalToffoliFormula registers k K mode := by
  cases mode <;>
    simp [RippleMode.inverse, intervalToffoliFormula,
      rippleFirstCellToffoliCost, rippleSecondCellToffoliCost,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

@[simp]
theorem intervalCoherentTFormula_inverse
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode) :
    intervalCoherentTFormula registers k K mode.inverse =
      intervalCoherentTFormula registers k K mode := by
  simp [intervalCoherentTFormula]

@[simp]
theorem intervalAdaptiveTFormula_inverse
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode) :
    intervalAdaptiveTFormula registers k K mode.inverse =
      intervalAdaptiveTFormula registers k K mode := by
  cases mode <;>
    simp [RippleMode.inverse, intervalAdaptiveTFormula,
      rippleFirstCellToffoliCost, rippleSecondCellToffoliCost,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem intervalAddSubInverseUnitary_toffoliCount
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    eeaToffoliCount
        (intervalAddSubInverseUnitary registers n k K mode signUpdate target) =
      intervalToffoliFormula registers k K mode := by
  rw [intervalAddSubInverseUnitary,
    intervalAddSubUnitary_toffoliCount registers n k K mode.inverse signUpdate target
      hlayout, intervalToffoliFormula_inverse]

theorem intervalAddSubInverseUnitary_cnotCount
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    eeaCnotCount
        (intervalAddSubInverseUnitary registers n k K mode signUpdate target) =
      intervalCnotFormula registers k K signUpdate := by
  exact intervalAddSubUnitary_cnotCount registers n k K mode.inverse signUpdate target hlayout

theorem intervalAddSubInverse_tCount
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    (intervalAddSubInverse registers n k K mode signUpdate target).tCount =
      intervalAdaptiveTFormula registers k K mode := by
  rw [intervalAddSubInverse,
    intervalAddSub_tCount registers n k K mode.inverse signUpdate target hlayout,
    intervalAdaptiveTFormula_inverse]

theorem intervalAddSubInverseUnitary_tCount
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    ShorECDLP.tCount
        (intervalAddSubInverseUnitary registers n k K mode signUpdate target) =
      intervalCoherentTFormula registers k K mode := by
  rw [intervalAddSubInverseUnitary,
    intervalAddSubUnitary_tCount registers n k K mode.inverse signUpdate target hlayout,
    intervalCoherentTFormula_inverse]

theorem intervalAddSubInverse_measurementCount
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    (intervalAddSubInverse registers n k K mode signUpdate target).measurementCount =
      intervalMeasurementFormula registers k K := by
  exact intervalAddSub_measurementCount registers n k K mode.inverse signUpdate target hlayout

private theorem intervalReady_endpointClean
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (state : BasisState) (hlayout : IntervalLayout registers k K target)
    (hready : IntervalReady registers state) :
    Clean (registers.endpointScratch ++ [registers.carry k K]) state := by
  intro wire hwire
  apply hready wire
  rcases List.mem_append.mp hwire with hscratch | hcarry
  · exact List.mem_of_mem_take hscratch
  · simp only [List.mem_singleton] at hcarry
    subst wire
    exact intervalCarry_mem_scratch registers k K target hlayout

/-- The source inverse restores the complete basis state after the forward block from the sole
input `IntervalReady` premise. -/
theorem run_intervalAddSubInverseUnitary_after_forward
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) (state : BasisState)
    (hlayout : IntervalLayout registers k K target)
    (hready : IntervalReady registers state) :
    run (intervalAddSubInverseUnitary registers n k K mode signUpdate target)
        (run (intervalAddSubUnitary registers n k K mode signUpdate target) state) =
      state := by
  let prepare := prepareIntervalEndpoints registers.lengthT registers.lengthQ
    registers.lengthS registers.endpointScratch (registers.carry k K) n k
  let body := intervalAddSubBodyUnitary registers k K mode signUpdate target
  let bodyInverse :=
    intervalAddSubBodyUnitary registers k K mode.inverse signUpdate target
  let restore := restoreIntervalEndpoints registers.lengthT registers.lengthQ
    registers.lengthS registers.endpointScratch (registers.carry k K) n k
  let prepared := run prepare state
  let afterBody := run body prepared
  let output := run restore afterBody
  have hforward :
      run (intervalAddSubUnitary registers n k K mode signUpdate target) state =
        output := by
    rw [intervalAddSubUnitary]
    simp only [Classical.run_append]
    simp only [output, afterBody, body, intervalAddSubBodyUnitary, prepared,
      prepare, restore, Classical.run_append]
  have hinverse : ∀ input : BasisState,
      Classical.run
          (intervalAddSubInverseUnitary registers n k K mode signUpdate target) input =
        run restore (run bodyInverse (run prepare input)) := by
    intro input
    change run (intervalAddSubUnitary registers n k K mode.inverse signUpdate target)
      input = _
    rw [intervalAddSubUnitary]
    simp only [Classical.run_append]
    simp only [bodyInverse, intervalAddSubBodyUnitary, prepare, restore,
      Classical.run_append]
  have hreadyOutput : IntervalReady registers output := by
    rw [← hforward]
    exact intervalAddSubUnitary_ready registers n k K mode signUpdate target state
      hlayout hready
  have houtputEndpoint :
      Clean (registers.endpointScratch ++ [registers.carry k K]) output :=
    intervalReady_endpointClean registers k K target output hlayout hreadyOutput
  have hinner : run prepare output = afterBody := by
    simpa [prepare, restore, output] using
      (run_prepareIntervalEndpoints_after_restore registers.lengthT registers.lengthQ
        registers.lengthS registers.endpointScratch (registers.carry k K) n k afterBody
        hlayout.lengthT_eq_lengthQ
        (intervalLengthQ_le_endpointScratch registers k K target hlayout)
        (intervalLengthS_le_endpointScratch registers k K target hlayout)
        (intervalLengthS_positive registers k K target hlayout) hlayout.endpoints
        houtputEndpoint)
  have hafterBodyScratch : Clean registers.scratch afterBody := by
    have hclean := intervalPrepare_cleanScratch registers n k K target output hlayout
      hreadyOutput
    simpa only [prepare, hinner] using hclean
  have hafterBodyTop : Clean
      (registers.cellScratch k K :: registers.equalityScratch k K) afterBody := by
    intro wire hwire
    exact hafterBodyScratch wire
      (intervalTopScratch_mem_scratch registers k K target hlayout wire hwire)
  have hbodyInverse : run bodyInverse afterBody = prepared := by
    have heq := run_intervalAddSubBodyUnitary_inverse_eq_adjoint registers k K mode
      signUpdate target afterBody hlayout hafterBodyTop
    rw [show run bodyInverse afterBody = run body.adjoint afterBody by
      simpa only [bodyInverse, body] using heq]
    simpa only [afterBody, body] using
      (run_adjoint_run_classical body
        (intervalAddSubBodyUnitary_wellFormed registers k K mode signUpdate target hlayout)
        prepared)
  have hinputEndpoint :
      Clean (registers.endpointScratch ++ [registers.carry k K]) state :=
    intervalReady_endpointClean registers k K target state hlayout hready
  have houter : run restore prepared = state := by
    simpa only [restore, prepare, prepared] using
      (run_restoreIntervalEndpoints_after_prepare registers.lengthT registers.lengthQ
        registers.lengthS registers.endpointScratch (registers.carry k K) n k state
        hlayout.lengthT_eq_lengthQ
        (intervalLengthQ_le_endpointScratch registers k K target hlayout)
        (intervalLengthS_le_endpointScratch registers k K target hlayout)
        (intervalLengthS_positive registers k K target hlayout) hlayout.endpoints
        hinputEndpoint)
  rw [hforward, hinverse, hinner, hbodyInverse, houter]

/-- Symmetrically, the forward source block restores the complete basis state after its inverse
at the same clean wrapper boundary. -/
theorem run_intervalAddSubUnitary_after_inverse
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) (state : BasisState)
    (hlayout : IntervalLayout registers k K target)
    (hready : IntervalReady registers state) :
    run (intervalAddSubUnitary registers n k K mode signUpdate target)
        (run (intervalAddSubInverseUnitary registers n k K mode signUpdate target) state) =
      state := by
  simpa [intervalAddSubInverseUnitary] using
    (run_intervalAddSubInverseUnitary_after_forward registers n k K mode.inverse
      signUpdate target state hlayout hready)

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

/-- The pinned inverse branch has the same closed resources while using the opposite ripple
specialization inside the exact source wrapper. -/
theorem intervalSourceComparison_inverseResources :
    eeaToffoliCount
        (intervalAddSubInverseUnitary intervalSourceComparisonRegisters 8 3 7
          .add true .work1) = 175 ∧
      eeaCnotCount
        (intervalAddSubInverseUnitary intervalSourceComparisonRegisters 8 3 7
          .add true .work1) = 203 ∧
      (intervalAddSubInverse intervalSourceComparisonRegisters 8 3 7
          .add true .work1).tCount = 987 ∧
      (intervalAddSubInverse intervalSourceComparisonRegisters 8 3 7
          .add true .work1).measurementCount = 34 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [intervalAddSubInverseUnitary_toffoliCount intervalSourceComparisonRegisters
      8 3 7 .add true .work1 intervalSourceComparisonLayout]
    rfl
  · rw [intervalAddSubInverseUnitary_cnotCount intervalSourceComparisonRegisters
      8 3 7 .add true .work1 intervalSourceComparisonLayout]
    rfl
  · rw [intervalAddSubInverse_tCount intervalSourceComparisonRegisters
      8 3 7 .add true .work1 intervalSourceComparisonLayout]
    rfl
  · rw [intervalAddSubInverse_measurementCount intervalSourceComparisonRegisters
      8 3 7 .add true .work1 intervalSourceComparisonLayout]
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
