import ShorECDLP.Submission.«2607_13816».EEA.QuotientSwap
import ShorECDLP.Submission.«2607_13816».EEA.IntervalCleanup

/-!
# Prepared-boundary coefficient-prefix arithmetic

This module implements the forward branch of the pinned supplement's
`lc_prefix_addsub_prepared_boundary_gate`.  The caller has already prepared the absolute endpoint
in `boundary`.  The block seeds one shared prefix accumulator from `control`, visits labels
`k, ..., K` in increasing source-tree order with the first Figure-11 ripple cell, optionally
updates `sign` from the carry, and visits the same labels in decreasing order with the second
cell before clearing the accumulator.

Both the literal coherent stream and the measurement-uncomputed stream use the same source-built
tree and leaf order.  Phase-dependent boundary preparation/restoration and the explicit inverse
are provided by the adjacent `TBoundary` and `CoefficientPrefixInverse` modules; their indexed-step
composition remains a later boundary.
-/

namespace ShorECDLP.Paper2607_13816

open Classical Quantum

noncomputable section

/-- Which coefficient work bank receives the prefix update. -/
inductive CoefficientTarget where
  | work1
  | work2
deriving DecidableEq, Repr

/-- Physical registers of one prepared-boundary prefix block. -/
structure CoefficientPrefixRegisters where
  control : Wire
  sign : Wire
  work1 : List Wire
  work2 : List Wire
  boundary : List Wire
  scratch : List Wire
deriving Repr

def CoefficientPrefixRegisters.scratchBase
    (registers : CoefficientPrefixRegisters) (k K : Nat) : Nat :=
  max (quotientSwapUnaryDepth k K) registers.boundary.length

/-- Tree-routing view of the prepared boundary.  The quotient selector's `lengthT` arithmetic
register is deliberately empty here: coefficient routing depends only on the boundary word. -/
def CoefficientPrefixRegisters.routing
    (registers : CoefficientPrefixRegisters) (_k _K : Nat) : QuotientSwapRegisters where
  control := registers.control
  sign := registers.sign
  work1 := registers.work1
  lengthT := []
  lengthQ := registers.boundary
  scratch := registers.scratch

def coefficientPrefixTree
    (registers : CoefficientPrefixRegisters) (k K : Nat) : UnaryActionTree :=
  quotientSwapTree (registers.routing k K) k K

def CoefficientPrefixRegisters.path
    (registers : CoefficientPrefixRegisters) (k K : Nat) : List Wire :=
  (registers.routing k K).path k K

def CoefficientPrefixRegisters.carry
    (registers : CoefficientPrefixRegisters) (k K : Nat) : Wire :=
  registers.scratch.getD (registers.scratchBase k K) 0

def CoefficientPrefixRegisters.accumulator
    (registers : CoefficientPrefixRegisters) (k K : Nat) : Wire :=
  registers.scratch.getD (registers.scratchBase k K + 1) 0

def CoefficientPrefixRegisters.cellScratch
    (registers : CoefficientPrefixRegisters) (k K : Nat) : Wire :=
  registers.scratch.getD (registers.scratchBase k K + 2) 0

def CoefficientPrefixRegisters.laneAt
    (_registers : CoefficientPrefixRegisters) (k label : Nat) : Nat :=
  label - k

def CoefficientPrefixRegisters.work1At
    (registers : CoefficientPrefixRegisters) (k label : Nat) : Wire :=
  registers.work1.getD (registers.laneAt k label)
    (registers.work1.getD 0 0)

def CoefficientPrefixRegisters.work2At
    (registers : CoefficientPrefixRegisters) (k label : Nat) : Wire :=
  registers.work2.getD (registers.laneAt k label)
    (registers.work2.getD 0 0)

def CoefficientPrefixRegisters.targetAt
    (registers : CoefficientPrefixRegisters) (target : CoefficientTarget)
    (k label : Nat) : Wire :=
  match target with
  | .work1 => registers.work1At k label
  | .work2 => registers.work2At k label

def CoefficientPrefixRegisters.addendAt
    (registers : CoefficientPrefixRegisters) (target : CoefficientTarget)
    (k label : Nat) : Wire :=
  match target with
  | .work1 => registers.work2At k label
  | .work2 => registers.work1At k label

def CoefficientPrefixRegisters.allWires
    (registers : CoefficientPrefixRegisters) : List Wire :=
  [registers.control, registers.sign] ++
    (registers.work1 ++
      (registers.work2 ++ (registers.boundary ++ registers.scratch)))

/-- Source-level register contract.  The coefficient block needs only the source-tree's
nonempty-label, boundary-width, and path-layout obligations; it does not inherit the quotient
selector's unrelated equal-width arithmetic-register premise. -/
structure CoefficientPrefixLayout
    (registers : CoefficientPrefixRegisters) (k K : Nat) : Prop where
  k_le_K : k ≤ K
  work1_length : registers.work1.length = K - k + 1
  work2_length : registers.work2.length = K - k + 1
  index_width : DualUnaryActionTree.sourceWidth
    (quotientSwapLabels k K).toFinset ≤ registers.boundary.length
  scratch_length : registers.scratch.length = registers.scratchBase k K + 3
  physical : registers.allWires.Nodup
  tree : (coefficientPrefixTree registers k K).Layout registers.control
    (registers.path k K)

/-- All shared source scratch is clean at the prepared-boundary block boundary. -/
def CoefficientPrefixReady
    (registers : CoefficientPrefixRegisters) (state : BasisState) : Prop :=
  Clean registers.scratch state

theorem coefficientPrefixTree_labels
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K) :
    (coefficientPrefixTree registers k K).labels =
      (quotientSwapLabels k K).toFinset.sort (· ≤ ·) := by
  exact quotientSwapTree_labels (registers.routing k K) hlayout.k_le_K

/-- A prepared in-range boundary routes to its exact absolute label. -/
theorem coefficientPrefixTree_routeLabel_eq
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K)
    (hvalue : boolWordToNat (wireValues registers.boundary state) ∈
      quotientSwapLabels k K) :
    (coefficientPrefixTree registers k K).routeLabel state =
      boolWordToNat (wireValues registers.boundary state) := by
  exact quotientSwapTree_routeLabel_eq_of_width (registers.routing k K) state
    hlayout.k_le_K (by simpa [CoefficientPrefixRegisters.routing] using hlayout.index_width)
    (by simpa [CoefficientPrefixRegisters.routing] using hvalue)

private theorem coefficientPrefix_getD_mem
    (list : List α) (index : Nat) (fallback : α)
    (hindex : index < list.length) :
    list.getD index fallback ∈ list := by
  rw [List.getD_eq_getElem list fallback hindex]
  exact List.getElem_mem hindex

private theorem coefficientPrefix_label_bounds
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (hlayout : CoefficientPrefixLayout registers k K)
    (hlabel : label ∈ (coefficientPrefixTree registers k K).labels) :
    k ≤ label ∧ label ≤ K := by
  rw [coefficientPrefixTree_labels registers hlayout] at hlabel
  have : label ∈ quotientSwapLabels k K := by simpa using hlabel
  simp only [quotientSwapLabels, List.mem_range'] at this
  omega

private theorem coefficientPrefix_firstWork1_mem
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K) :
    registers.work1.getD 0 0 ∈ registers.work1 := by
  have hlength : registers.work1.length = K - k + 1 := hlayout.work1_length
  exact coefficientPrefix_getD_mem registers.work1 0 0 (by rw [hlength]; omega)

private theorem coefficientPrefix_firstWork2_mem
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K) :
    registers.work2.getD 0 0 ∈ registers.work2 := by
  exact coefficientPrefix_getD_mem registers.work2 0 0 (by
    rw [hlayout.work2_length]
    omega)

private theorem coefficientPrefix_work1At_mem_any
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K) (label : Nat) :
    registers.work1At k label ∈ registers.work1 := by
  by_cases hindex : registers.laneAt k label < registers.work1.length
  · exact coefficientPrefix_getD_mem registers.work1 (registers.laneAt k label)
      (registers.work1.getD 0 0) hindex
  · rw [CoefficientPrefixRegisters.work1At,
      List.getD_eq_default registers.work1 (registers.work1.getD 0 0)
        (Nat.le_of_not_gt hindex)]
    exact coefficientPrefix_firstWork1_mem registers hlayout

private theorem coefficientPrefix_work2At_mem_any
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K) (label : Nat) :
    registers.work2At k label ∈ registers.work2 := by
  by_cases hindex : registers.laneAt k label < registers.work2.length
  · exact coefficientPrefix_getD_mem registers.work2 (registers.laneAt k label)
      (registers.work2.getD 0 0) hindex
  · rw [CoefficientPrefixRegisters.work2At,
      List.getD_eq_default registers.work2 (registers.work2.getD 0 0)
        (Nat.le_of_not_gt hindex)]
    exact coefficientPrefix_firstWork2_mem registers hlayout

private theorem coefficientPrefix_physical_parts
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K) :
    [registers.control, registers.sign].Nodup ∧
      registers.work1.Nodup ∧ registers.work2.Nodup ∧
      registers.boundary.Nodup ∧ registers.scratch.Nodup ∧
      (∀ fixed ∈ [registers.control, registers.sign],
        ∀ wire ∈ registers.work1 ++
          (registers.work2 ++ (registers.boundary ++ registers.scratch)),
          fixed ≠ wire) ∧
      (∀ first ∈ registers.work1,
        ∀ wire ∈ registers.work2 ++ (registers.boundary ++ registers.scratch),
          first ≠ wire) ∧
      (∀ second ∈ registers.work2,
        ∀ wire ∈ registers.boundary ++ registers.scratch,
          second ≠ wire) ∧
      (∀ boundary ∈ registers.boundary,
        ∀ scratch ∈ registers.scratch, boundary ≠ scratch) := by
  have hphysical := hlayout.physical
  rw [CoefficientPrefixRegisters.allWires] at hphysical
  obtain ⟨hfixed, hrest, hfixedCross⟩ := List.nodup_append.mp hphysical
  obtain ⟨hwork1, hrest, hwork1Cross⟩ := List.nodup_append.mp hrest
  obtain ⟨hwork2, hrest, hwork2Cross⟩ := List.nodup_append.mp hrest
  obtain ⟨hboundary, hscratch, hboundaryScratch⟩ :=
    List.nodup_append.mp hrest
  exact ⟨hfixed, hwork1, hwork2, hboundary, hscratch,
    hfixedCross, hwork1Cross, hwork2Cross, hboundaryScratch⟩

private theorem coefficientPrefix_scratchAt_mem
    (registers : CoefficientPrefixRegisters) {k K index : Nat}
    (hlayout : CoefficientPrefixLayout registers k K)
    (hindex : index < registers.scratchBase k K + 3) :
    registers.scratch.getD index 0 ∈ registers.scratch := by
  apply coefficientPrefix_getD_mem
  rw [hlayout.scratch_length]
  exact hindex

private theorem coefficientPrefix_scratchAt_ne
    (registers : CoefficientPrefixRegisters) {k K first second : Nat}
    (hlayout : CoefficientPrefixLayout registers k K)
    (hfirst : first < registers.scratchBase k K + 3)
    (hsecond : second < registers.scratchBase k K + 3)
    (hne : first ≠ second) :
    registers.scratch.getD first 0 ≠ registers.scratch.getD second 0 := by
  have hfirstLength : first < registers.scratch.length := by
    rw [hlayout.scratch_length]
    exact hfirst
  have hsecondLength : second < registers.scratch.length := by
    rw [hlayout.scratch_length]
    exact hsecond
  rw [List.getD_eq_getElem registers.scratch 0 hfirstLength,
    List.getD_eq_getElem registers.scratch 0 hsecondLength]
  intro heq
  exact hne ((coefficientPrefix_physical_parts registers hlayout).2.2.2.2.1
    |>.getElem_inj_iff.mp heq)

private theorem coefficientPrefix_scratch_roles_nodup
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K) :
    [registers.carry k K, registers.accumulator k K,
      registers.cellScratch k K].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or]
  exact ⟨⟨coefficientPrefix_scratchAt_ne registers hlayout (by omega) (by omega)
      (by omega),
    coefficientPrefix_scratchAt_ne registers hlayout (by omega) (by omega) (by omega)⟩,
    ⟨coefficientPrefix_scratchAt_ne registers hlayout (by omega) (by omega) (by omega),
      (by simp)⟩⟩

private theorem coefficientPrefix_path_eq_take
    (registers : CoefficientPrefixRegisters) (k K : Nat) :
    registers.path k K = registers.scratch.take (quotientSwapUnaryDepth k K) := by
  rfl

private theorem coefficientPrefix_path_not_scratchAt
    (registers : CoefficientPrefixRegisters) {k K index : Nat}
    (hlayout : CoefficientPrefixLayout registers k K)
    (hindexLength : index < registers.scratchBase k K + 3)
    (hdepthIndex : quotientSwapUnaryDepth k K ≤ index) :
    registers.scratch.getD index 0 ∉ registers.path k K := by
  have hscratch := (coefficientPrefix_physical_parts registers hlayout).2.2.2.2.1
  have hlength : index < registers.scratch.length := by
    rw [hlayout.scratch_length]
    exact hindexLength
  intro hmem
  rw [coefficientPrefix_path_eq_take registers k K,
    List.mem_take_iff_getElem] at hmem
  obtain ⟨pathIndex, hpathIndex, heq⟩ := hmem
  have hpathDepth : pathIndex < quotientSwapUnaryDepth k K :=
    lt_of_lt_of_le hpathIndex (Nat.min_le_left _ _)
  rw [List.getD_eq_getElem registers.scratch 0 hlength] at heq
  have : pathIndex = index := hscratch.getElem_inj_iff.mp heq
  omega

private theorem coefficientPrefix_path_not_carry
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K) :
    registers.carry k K ∉ registers.path k K := by
  apply coefficientPrefix_path_not_scratchAt registers
    (k := k) (K := K) (index := registers.scratchBase k K) hlayout (by omega)
  exact Nat.le_max_left _ _

private theorem coefficientPrefix_path_not_accumulator
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K) :
    registers.accumulator k K ∉ registers.path k K := by
  apply coefficientPrefix_path_not_scratchAt registers
    (k := k) (K := K) (index := registers.scratchBase k K + 1) hlayout (by omega)
  exact le_trans (Nat.le_max_left _ _) (Nat.le_succ _)

private theorem coefficientPrefix_path_not_cellScratch
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K) :
    registers.cellScratch k K ∉ registers.path k K := by
  apply coefficientPrefix_path_not_scratchAt registers
    (k := k) (K := K) (index := registers.scratchBase k K + 2) hlayout (by omega)
  rw [CoefficientPrefixRegisters.scratchBase]
  exact le_trans
    (Nat.le_max_left (quotientSwapUnaryDepth k K) registers.boundary.length)
    (by omega)

private theorem coefficientPrefix_path_mem_scratch
    (registers : CoefficientPrefixRegisters) (k K : Nat) :
    ∀ wire, wire ∈ registers.path k K → wire ∈ registers.scratch := by
  intro wire hwire
  rw [coefficientPrefix_path_eq_take registers k K] at hwire
  exact List.mem_of_mem_take hwire

private theorem coefficientPrefix_decoder_classify
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K) :
    ∀ wire,
      wire ∈ registers.control ::
          (coefficientPrefixTree registers k K).indexWires.dedup ++
            registers.path k K →
      wire = registers.control ∨ wire ∈ registers.boundary ∨
        wire ∈ registers.path k K := by
  intro wire hwire
  simp only [List.mem_cons, List.mem_append] at hwire
  rcases hwire with (rfl | hindex) | hpath
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (by
      have hmem := quotientSwapTree_indexWires_mem_lengthQ
        (registers.routing k K) hlayout.k_le_K
          (by simpa [CoefficientPrefixRegisters.routing] using hlayout.index_width)
          wire (by simpa using hindex)
      simpa [CoefficientPrefixRegisters.routing] using hmem))
  · exact Or.inr (Or.inr hpath)

private theorem coefficientPrefix_decoder_ne_work1
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K)
    {decoder work : Wire}
    (hdecoder : decoder ∈ registers.control ::
      (coefficientPrefixTree registers k K).indexWires.dedup ++ registers.path k K)
    (hwork : work ∈ registers.work1) :
    decoder ≠ work := by
  obtain ⟨_, _, _, _, _, hfixedCross, hwork1Cross, _, _⟩ :=
    coefficientPrefix_physical_parts registers hlayout
  rcases coefficientPrefix_decoder_classify registers hlayout decoder hdecoder with
    rfl | hboundary | hpath
  · exact hfixedCross registers.control (by simp) work (by simp [hwork])
  · exact (hwork1Cross work hwork decoder
      (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hboundary))))).symm
  · exact (hwork1Cross work hwork decoder
      (List.mem_append.mpr (Or.inr (List.mem_append.mpr
        (Or.inr (coefficientPrefix_path_mem_scratch registers k K decoder hpath)))))).symm

private theorem coefficientPrefix_decoder_ne_work2
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K)
    {decoder work : Wire}
    (hdecoder : decoder ∈ registers.control ::
      (coefficientPrefixTree registers k K).indexWires.dedup ++ registers.path k K)
    (hwork : work ∈ registers.work2) :
    decoder ≠ work := by
  obtain ⟨_, _, _, _, _, hfixedCross, _, hwork2Cross, _⟩ :=
    coefficientPrefix_physical_parts registers hlayout
  rcases coefficientPrefix_decoder_classify registers hlayout decoder hdecoder with
    rfl | hboundary | hpath
  · exact hfixedCross registers.control (by simp) work (by simp [hwork])
  · exact (hwork2Cross work hwork decoder
      (List.mem_append.mpr (Or.inl hboundary))).symm
  · exact (hwork2Cross work hwork decoder
      (List.mem_append.mpr (Or.inr
        (coefficientPrefix_path_mem_scratch registers k K decoder hpath)))).symm

private theorem coefficientPrefix_decoder_ne_scratchAt
    (registers : CoefficientPrefixRegisters) {k K index : Nat}
    (hlayout : CoefficientPrefixLayout registers k K)
    {decoder : Wire}
    (hdecoder : decoder ∈ registers.control ::
      (coefficientPrefixTree registers k K).indexWires.dedup ++ registers.path k K)
    (hindex : index < registers.scratchBase k K + 3)
    (hnotPath : registers.scratch.getD index 0 ∉ registers.path k K) :
    decoder ≠ registers.scratch.getD index 0 := by
  obtain ⟨_, _, _, _, _, hfixedCross, _, _, hboundaryScratch⟩ :=
    coefficientPrefix_physical_parts registers hlayout
  have hscratch := coefficientPrefix_scratchAt_mem registers hlayout hindex
  rcases coefficientPrefix_decoder_classify registers hlayout decoder hdecoder with
    rfl | hboundary | hpath
  · exact hfixedCross registers.control (by simp)
      (registers.scratch.getD index 0)
      (List.mem_append.mpr (Or.inr (List.mem_append.mpr
        (Or.inr (List.mem_append.mpr (Or.inr hscratch))))))
  · exact hboundaryScratch decoder hboundary
      (registers.scratch.getD index 0) hscratch
  · intro equality
    apply hnotPath
    rwa [← equality]

private theorem coefficientPrefix_decoder_disjoint_leafRoles
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    List.Disjoint
      (registers.control ::
        (coefficientPrefixTree registers k K).indexWires.dedup ++ registers.path k K)
      (registers.accumulator k K :: registers.targetAt target k label ::
        registers.addendAt target k label :: registers.carry k K ::
        registers.cellScratch k K :: []) := by
  rw [List.disjoint_left]
  intro decoder hdecoder hrole
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrole
  rcases hrole with haccumulator | htarget | haddend | hcarry | hcell
  · exact (coefficientPrefix_decoder_ne_scratchAt registers hlayout hdecoder
      (by omega) (coefficientPrefix_path_not_accumulator registers hlayout))
      (by simpa [CoefficientPrefixRegisters.accumulator] using haccumulator)
  · cases target with
    | work1 =>
        exact (coefficientPrefix_decoder_ne_work1 registers hlayout hdecoder
          (coefficientPrefix_work1At_mem_any registers hlayout label))
          (by simpa [CoefficientPrefixRegisters.targetAt] using htarget)
    | work2 =>
        exact (coefficientPrefix_decoder_ne_work2 registers hlayout hdecoder
          (coefficientPrefix_work2At_mem_any registers hlayout label))
          (by simpa [CoefficientPrefixRegisters.targetAt] using htarget)
  · cases target with
    | work1 =>
        exact (coefficientPrefix_decoder_ne_work2 registers hlayout hdecoder
          (coefficientPrefix_work2At_mem_any registers hlayout label))
          (by simpa [CoefficientPrefixRegisters.addendAt] using haddend)
    | work2 =>
        exact (coefficientPrefix_decoder_ne_work1 registers hlayout hdecoder
          (coefficientPrefix_work1At_mem_any registers hlayout label))
          (by simpa [CoefficientPrefixRegisters.addendAt] using haddend)
  · exact (coefficientPrefix_decoder_ne_scratchAt registers hlayout hdecoder
      (by omega) (coefficientPrefix_path_not_carry registers hlayout))
      (by simpa [CoefficientPrefixRegisters.carry] using hcarry)
  · exact (coefficientPrefix_decoder_ne_scratchAt registers hlayout hdecoder
      (by omega) (coefficientPrefix_path_not_cellScratch registers hlayout))
      (by simpa [CoefficientPrefixRegisters.cellScratch] using hcell)

private theorem coefficientPrefix_cellLayout
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    [registers.accumulator k K, registers.targetAt target k label,
      registers.addendAt target k label, registers.carry k K,
      registers.cellScratch k K].Nodup := by
  obtain ⟨_, _, _, _, _, _, hwork1Cross, hwork2Cross, _⟩ :=
    coefficientPrefix_physical_parts registers hlayout
  have hwork1 := coefficientPrefix_work1At_mem_any registers hlayout label
  have hwork2 := coefficientPrefix_work2At_mem_any registers hlayout label
  have hcarry := coefficientPrefix_scratchAt_mem registers hlayout (by omega :
    registers.scratchBase k K < registers.scratchBase k K + 3)
  have haccumulator := coefficientPrefix_scratchAt_mem registers hlayout (by omega :
    registers.scratchBase k K + 1 < registers.scratchBase k K + 3)
  have hcell := coefficientPrefix_scratchAt_mem registers hlayout (by omega :
    registers.scratchBase k K + 2 < registers.scratchBase k K + 3)
  have hwork2InWork1Tail : registers.work2At k label ∈
      registers.work2 ++ (registers.boundary ++ registers.scratch) :=
    List.mem_append.mpr (Or.inl hwork2)
  have haccInWork1Tail : registers.accumulator k K ∈
      registers.work2 ++ (registers.boundary ++ registers.scratch) :=
    List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr haccumulator)))
  have hcarryInWork1Tail : registers.carry k K ∈
      registers.work2 ++ (registers.boundary ++ registers.scratch) :=
    List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hcarry)))
  have hcellInWork1Tail : registers.cellScratch k K ∈
      registers.work2 ++ (registers.boundary ++ registers.scratch) :=
    List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hcell)))
  have haccInWork2Tail : registers.accumulator k K ∈
      registers.boundary ++ registers.scratch :=
    List.mem_append.mpr (Or.inr haccumulator)
  have hcarryInWork2Tail : registers.carry k K ∈
      registers.boundary ++ registers.scratch :=
    List.mem_append.mpr (Or.inr hcarry)
  have hcellInWork2Tail : registers.cellScratch k K ∈
      registers.boundary ++ registers.scratch :=
    List.mem_append.mpr (Or.inr hcell)
  have hscratchRoles := coefficientPrefix_scratch_roles_nodup registers hlayout
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hscratchRoles
  rcases hscratchRoles with ⟨⟨hcarryAcc, hcarryCell⟩,
    ⟨haccCell, _⟩⟩
  cases target with
  | work1 =>
      simp only [CoefficientPrefixRegisters.targetAt,
        CoefficientPrefixRegisters.addendAt, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, not_or]
      exact ⟨⟨
          (hwork1Cross _ hwork1 _ haccInWork1Tail).symm,
          (hwork2Cross _ hwork2 _ haccInWork2Tail).symm,
          Ne.symm hcarryAcc, haccCell⟩,
        ⟨⟨hwork1Cross _ hwork1 _ hwork2InWork1Tail,
            hwork1Cross _ hwork1 _ hcarryInWork1Tail,
            hwork1Cross _ hwork1 _ hcellInWork1Tail⟩,
          ⟨⟨hwork2Cross _ hwork2 _ hcarryInWork2Tail,
              hwork2Cross _ hwork2 _ hcellInWork2Tail⟩,
            ⟨hcarryCell, by simp⟩⟩⟩⟩
  | work2 =>
      simp only [CoefficientPrefixRegisters.targetAt,
        CoefficientPrefixRegisters.addendAt, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, not_or]
      exact ⟨⟨
          (hwork2Cross _ hwork2 _ haccInWork2Tail).symm,
          (hwork1Cross _ hwork1 _ haccInWork1Tail).symm,
          Ne.symm hcarryAcc, haccCell⟩,
        ⟨⟨(hwork1Cross _ hwork1 _ hwork2InWork1Tail).symm,
            hwork2Cross _ hwork2 _ hcarryInWork2Tail,
            hwork2Cross _ hwork2 _ hcellInWork2Tail⟩,
          ⟨⟨hwork1Cross _ hwork1 _ hcarryInWork1Tail,
              hwork1Cross _ hwork1 _ hcellInWork1Tail⟩,
            ⟨hcarryCell, by simp⟩⟩⟩⟩

/-! ## Literal source leaves -/

/-- First-pass source leaf: apply the selected Figure-11 cell, then switch the prefix accumulator
at this equality pulse. -/
def coefficientPrefixFirstLeaf
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) : Circuit :=
  rippleFirstCell mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K) ++
    [.CX equalityControl (registers.accumulator k K)]

/-- Second-pass source leaf: switch the accumulator first, then apply the second cell. -/
def coefficientPrefixSecondLeaf
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) : Circuit :=
  [.CX equalityControl (registers.accumulator k K)] ++
    rippleSecondCell mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K)

def coefficientPrefixFirstLeafAdaptive
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) : AdaptiveCircuit :=
  (rippleFirstCellAdaptive mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K)).seq
    (.unitary [.CX equalityControl (registers.accumulator k K)] .done)

def coefficientPrefixSecondLeafAdaptive
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) : AdaptiveCircuit :=
  .unitary [.CX equalityControl (registers.accumulator k K)]
    (rippleSecondCellAdaptive mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K))

/-- Optional carry-to-sign update at the exact position between the two traversals. -/
def coefficientPrefixSignCircuit
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (signUpdate : Bool) : Circuit :=
  if signUpdate then [.CX (registers.carry k K) registers.sign] else []

/-- Literal coherent forward stream of `lc_prefix_addsub_prepared_boundary_gate`. -/
def coefficientPrefixUnitary
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) : Circuit :=
  [.CX registers.control (registers.accumulator k K)] ++
    unaryActionUnitary .inc (coefficientPrefixFirstLeaf registers k K mode target)
      (coefficientPrefixTree registers k K) registers.control (registers.path k K) ++
    coefficientPrefixSignCircuit registers k K signUpdate ++
    unaryActionUnitary .dec (coefficientPrefixSecondLeaf registers k K mode target)
      (coefficientPrefixTree registers k K) registers.control (registers.path k K) ++
    [.CX registers.control (registers.accumulator k K)]

/-- Measurement-uncomputed forward stream with the same source-tree and block order. -/
def coefficientPrefixAdaptive
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) :
    AdaptiveCircuit :=
  .unitary [.CX registers.control (registers.accumulator k K)]
    ((unaryAdaptiveAction .inc
      (coefficientPrefixFirstLeafAdaptive registers k K mode target)
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K)).seq
      (.unitary (coefficientPrefixSignCircuit registers k K signUpdate)
        ((unaryAdaptiveAction .dec
          (coefficientPrefixSecondLeafAdaptive registers k K mode target)
          (coefficientPrefixTree registers k K) registers.control
          (registers.path k K)).seq
          (.unitary [.CX registers.control (registers.accumulator k K)] .done))))

/-! ## Gate-independent basis-state semantics -/

def coefficientPrefixFirstLeafState
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (active : Bool) (state : BasisState) : BasisState :=
  let afterCell := writeRippleCell
    (registers.targetAt target k label) (registers.addendAt target k label)
    (registers.carry k K)
    (rippleFirstBits mode (state (registers.accumulator k K))
      (readRippleCell (registers.targetAt target k label)
        (registers.addendAt target k label) (registers.carry k K) state)) state
  afterCell[registers.accumulator k K ↦
    Bool.xor (afterCell (registers.accumulator k K)) active]

def coefficientPrefixSecondLeafState
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (active : Bool) (state : BasisState) : BasisState :=
  let switched := state[registers.accumulator k K ↦
    Bool.xor (state (registers.accumulator k K)) active]
  writeRippleCell
    (registers.targetAt target k label) (registers.addendAt target k label)
    (registers.carry k K)
    (rippleSecondBits mode (switched (registers.accumulator k K))
      (readRippleCell (registers.targetAt target k label)
        (registers.addendAt target k label) (registers.carry k K) switched)) switched

/-- Total circuit-level trace for one first-pass leaf, with the dynamic decoder wire erased to its
Boolean pulse.  This remains private proof infrastructure; the public recurrence below uses only
`coefficientPrefixFirstLeafState`. -/
private def coefficientPrefixFirstLeafTraceState
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (active : Bool) (state : BasisState) : BasisState :=
  let afterCell := Classical.run
    (rippleFirstCell mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K)) state
  afterCell[registers.accumulator k K ↦
    Bool.xor (afterCell (registers.accumulator k K)) active]

/-- Total circuit-level trace for one second-pass leaf. -/
private def coefficientPrefixSecondLeafTraceState
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (active : Bool) (state : BasisState) : BasisState :=
  let switched := state[registers.accumulator k K ↦
    Bool.xor (state (registers.accumulator k K)) active]
  Classical.run
    (rippleSecondCell mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K)) switched

theorem run_coefficientPrefixFirstLeaf_state
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (equalityControl : Wire)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K)
    (hcontrol : equalityControl ∈ registers.control ::
      (coefficientPrefixTree registers k K).indexWires.dedup ++ registers.path k K)
    (hclean : state (registers.cellScratch k K) = false) :
    Classical.run
        (coefficientPrefixFirstLeaf registers k K mode target label equalityControl) state =
      coefficientPrefixFirstLeafState registers k K mode target label
        (state equalityControl) state := by
  let cell := rippleFirstCell mode (registers.accumulator k K)
    (registers.targetAt target k label) (registers.addendAt target k label)
    (registers.carry k K) (registers.cellScratch k K)
  let afterCell := Classical.run cell state
  have hcell : afterCell = writeRippleCell
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K)
      (rippleFirstBits mode (state (registers.accumulator k K))
        (readRippleCell (registers.targetAt target k label)
          (registers.addendAt target k label) (registers.carry k K) state)) state := by
    exact run_rippleFirstCell_state mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K) state
      (coefficientPrefix_cellLayout (label := label) registers target hlayout) hclean
  have houtside := coefficientPrefix_decoder_disjoint_leafRoles
    (label := label) registers target hlayout
  rw [List.disjoint_left] at houtside
  have hequalityOutside : equalityControl ∉
      [registers.accumulator k K, registers.targetAt target k label,
        registers.addendAt target k label, registers.carry k K,
        registers.cellScratch k K] := houtside hcontrol
  have hequality : afterCell equalityControl = state equalityControl := by
    rw [show afterCell = Classical.run cell state by rfl]
    exact (rippleFirstCell_usesOnly mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K)).preservesOutside
        state hequalityOutside
  rw [coefficientPrefixFirstLeaf, Classical.run_append]
  change Classical.run ([.CX equalityControl (registers.accumulator k K)] : Circuit)
      afterCell = _
  simp only [Classical.run_cons, Classical.run_nil, Classical.applyGate]
  rw [hequality, hcell]
  rfl

theorem run_coefficientPrefixSecondLeaf_state
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (equalityControl : Wire)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K)
    (hcontrol : equalityControl ∈ registers.control ::
      (coefficientPrefixTree registers k K).indexWires.dedup ++ registers.path k K)
    (hclean : state (registers.cellScratch k K) = false) :
    Classical.run
        (coefficientPrefixSecondLeaf registers k K mode target label equalityControl) state =
      coefficientPrefixSecondLeafState registers k K mode target label
        (state equalityControl) state := by
  let switched := Classical.run
    ([.CX equalityControl (registers.accumulator k K)] : Circuit) state
  have houtside := coefficientPrefix_decoder_disjoint_leafRoles
    (label := label) registers target hlayout
  rw [List.disjoint_left] at houtside
  have hequalityOutside : equalityControl ∉
      [registers.accumulator k K, registers.targetAt target k label,
        registers.addendAt target k label, registers.carry k K,
        registers.cellScratch k K] := houtside hcontrol
  have hcellLayout := coefficientPrefix_cellLayout (label := label) registers target hlayout
  have haccScratch : registers.accumulator k K ≠ registers.cellScratch k K := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at hcellLayout
    exact hcellLayout.1.2.2.2
  have hswitched : switched =
      state[registers.accumulator k K ↦ Bool.xor
        (state (registers.accumulator k K)) (state equalityControl)] := by
    rfl
  have hcleanSwitched : switched (registers.cellScratch k K) = false := by
    rw [hswitched, upd_other state (registers.accumulator k K) _
      (Ne.symm haccScratch)]
    exact hclean
  rw [coefficientPrefixSecondLeaf, Classical.run_append]
  change Classical.run
      (rippleSecondCell mode (registers.accumulator k K)
        (registers.targetAt target k label) (registers.addendAt target k label)
        (registers.carry k K) (registers.cellScratch k K)) switched = _
  rw [run_rippleSecondCell_state mode (registers.accumulator k K)
    (registers.targetAt target k label) (registers.addendAt target k label)
    (registers.carry k K) (registers.cellScratch k K) switched
    (coefficientPrefix_cellLayout (label := label) registers target hlayout) hcleanSwitched,
    hswitched]
  rfl

private theorem coefficientPrefixFirstLeaf_preservesDecoder
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (mode : RippleMode) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    ∀ equalityControl state wire,
        wire ∈ registers.control ::
          (coefficientPrefixTree registers k K).indexWires.dedup ++ registers.path k K →
        Classical.run
            (coefficientPrefixFirstLeaf registers k K mode target label equalityControl)
            state wire = state wire := by
  intro equalityControl state wire hwire
  have houtside := coefficientPrefix_decoder_disjoint_leafRoles
    (label := label) registers target hlayout
  rw [List.disjoint_left] at houtside
  have hnot := houtside hwire
  have hripple := (rippleFirstCell_usesOnly mode (registers.accumulator k K)
    (registers.targetAt target k label) (registers.addendAt target k label)
    (registers.carry k K) (registers.cellScratch k K)).preservesOutside state hnot
  have hwireAcc : wire ≠ registers.accumulator k K := by
    intro equality
    exact hnot (by simp [equality])
  rw [coefficientPrefixFirstLeaf, Classical.run_append]
  simp only [Classical.run_cons, Classical.run_nil, Classical.applyGate]
  rw [upd_other _ _ _ hwireAcc, hripple]

private theorem coefficientPrefixSecondLeaf_preservesDecoder
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (mode : RippleMode) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    ∀ equalityControl state wire,
        wire ∈ registers.control ::
          (coefficientPrefixTree registers k K).indexWires.dedup ++ registers.path k K →
        Classical.run
            (coefficientPrefixSecondLeaf registers k K mode target label equalityControl)
            state wire = state wire := by
  intro equalityControl state wire hwire
  have houtside := coefficientPrefix_decoder_disjoint_leafRoles
    (label := label) registers target hlayout
  rw [List.disjoint_left] at houtside
  have hnot := houtside hwire
  have hwireAcc : wire ≠ registers.accumulator k K := by
    intro equality
    exact hnot (by simp [equality])
  let switched := Classical.run
    ([.CX equalityControl (registers.accumulator k K)] : Circuit) state
  have hswitchedWire : switched wire = state wire := by
    simp [switched, Classical.run, Classical.applyGate, upd, hwireAcc]
  rw [coefficientPrefixSecondLeaf, Classical.run_append]
  change Classical.run
      (rippleSecondCell mode (registers.accumulator k K)
        (registers.targetAt target k label) (registers.addendAt target k label)
        (registers.carry k K) (registers.cellScratch k K)) switched wire = state wire
  rw [(rippleSecondCell_usesOnly mode (registers.accumulator k K)
    (registers.targetAt target k label) (registers.addendAt target k label)
    (registers.carry k K) (registers.cellScratch k K)).preservesOutside switched hnot,
    hswitchedWire]

private theorem coefficientPrefixFirstLeaf_preservesCellScratch
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (equalityControl : Wire)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K) :
    Classical.run
        (coefficientPrefixFirstLeaf registers k K mode target label equalityControl)
        state (registers.cellScratch k K) = state (registers.cellScratch k K) := by
  have hcell := coefficientPrefix_cellLayout (label := label) registers target hlayout
  have haccScratch : registers.cellScratch k K ≠ registers.accumulator k K := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at hcell
    exact Ne.symm hcell.1.2.2.2
  rw [coefficientPrefixFirstLeaf, Classical.run_append]
  simp only [Classical.run_cons, Classical.run_nil, Classical.applyGate]
  rw [upd_other _ _ _ haccScratch,
    rippleFirstCell_preservesScratch mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K) state hcell]

private theorem coefficientPrefixSecondLeaf_preservesCellScratch
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (equalityControl : Wire)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K) :
    Classical.run
        (coefficientPrefixSecondLeaf registers k K mode target label equalityControl)
        state (registers.cellScratch k K) = state (registers.cellScratch k K) := by
  have hcell := coefficientPrefix_cellLayout (label := label) registers target hlayout
  have haccScratch : registers.cellScratch k K ≠ registers.accumulator k K := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at hcell
    exact Ne.symm hcell.1.2.2.2
  let switched := Classical.run
    ([.CX equalityControl (registers.accumulator k K)] : Circuit) state
  have hswitched : switched (registers.cellScratch k K) =
      state (registers.cellScratch k K) := by
    simp [switched, Classical.run, Classical.applyGate, upd, haccScratch]
  rw [coefficientPrefixSecondLeaf, Classical.run_append]
  change Classical.run
      (rippleSecondCell mode (registers.accumulator k K)
        (registers.targetAt target k label) (registers.addendAt target k label)
        (registers.carry k K) (registers.cellScratch k K)) switched
        (registers.cellScratch k K) = state (registers.cellScratch k K)
  rw [rippleSecondCell_preservesScratch mode (registers.accumulator k K)
    (registers.targetAt target k label) (registers.addendAt target k label)
    (registers.carry k K) (registers.cellScratch k K) switched hcell, hswitched]

private theorem coefficientPrefix_runFirstLeaf_trace
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (equalityControl : Wire)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K)
    (hcontrol : equalityControl ∈ registers.control ::
      (coefficientPrefixTree registers k K).indexWires.dedup ++ registers.path k K) :
    Classical.run
        (coefficientPrefixFirstLeaf registers k K mode target label equalityControl) state =
      coefficientPrefixFirstLeafTraceState registers k K mode target label
        (state equalityControl) state := by
  let cell := rippleFirstCell mode (registers.accumulator k K)
    (registers.targetAt target k label) (registers.addendAt target k label)
    (registers.carry k K) (registers.cellScratch k K)
  have houtside := coefficientPrefix_decoder_disjoint_leafRoles
    (label := label) registers target hlayout
  rw [List.disjoint_left] at houtside
  have hequalityOutside : equalityControl ∉
      [registers.accumulator k K, registers.targetAt target k label,
        registers.addendAt target k label, registers.carry k K,
        registers.cellScratch k K] := houtside hcontrol
  have hequality : Classical.run cell state equalityControl = state equalityControl :=
    (rippleFirstCell_usesOnly mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K)).preservesOutside
        state hequalityOutside
  rw [coefficientPrefixFirstLeaf, Classical.run_append]
  change Classical.run ([.CX equalityControl (registers.accumulator k K)] : Circuit)
      (Classical.run cell state) = _
  simp only [coefficientPrefixFirstLeafTraceState, Classical.run_cons,
    Classical.run_nil, Classical.applyGate]
  rw [hequality]

private theorem coefficientPrefix_runSecondLeaf_trace
    (registers : CoefficientPrefixRegisters) (k K label : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (equalityControl : Wire)
    (state : BasisState) :
    Classical.run
        (coefficientPrefixSecondLeaf registers k K mode target label equalityControl) state =
      coefficientPrefixSecondLeafTraceState registers k K mode target label
        (state equalityControl) state := by
  rw [coefficientPrefixSecondLeaf, Classical.run_append]
  rfl

private theorem coefficientPrefix_run_agreesOutside_of_disjoint
    (support protectedWires : List Wire) (circuit : Circuit)
    (left right : BasisState)
    (huses : PaperCircuitUsesOnly support circuit)
    (hdisjoint : List.Disjoint protectedWires support)
    (houtside : AgreesOutside protectedWires left right) :
    AgreesOutside protectedWires
      (Classical.run circuit left) (Classical.run circuit right) := by
  rw [List.disjoint_left] at hdisjoint
  intro wire hwire
  by_cases hsupport : wire ∈ support
  · exact huses.run_congrOn left right (by
      intro used hused
      exact houtside used (fun hprotected => hdisjoint hprotected hused))
        wire hsupport
  · rw [huses.preservesOutside left hsupport,
      huses.preservesOutside right hsupport]
    exact houtside wire hwire

private theorem coefficientPrefix_update_agreesOutside
    (protectedWires : List Wire) (left right : BasisState)
    (target : Wire) (leftValue rightValue : Bool)
    (houtside : AgreesOutside protectedWires left right)
    (hvalue : leftValue = rightValue) :
    AgreesOutside protectedWires
      (left[target ↦ leftValue]) (right[target ↦ rightValue]) := by
  intro wire hwire
  by_cases htarget : wire = target
  · subst wire
    simpa [upd] using hvalue
  · simp [upd, htarget, houtside wire hwire]

private theorem coefficientPrefixFirstLeafTrace_preservesDecoder
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    LogicalLeafPreserves
      (fun nextLabel active next =>
        coefficientPrefixFirstLeafTraceState registers k K mode target
          nextLabel active next)
      (registers.control ::
        (coefficientPrefixTree registers k K).indexWires.dedup ++
          registers.path k K) := by
  intro nextLabel active state wire hwire
  have houtside := coefficientPrefix_decoder_disjoint_leafRoles
    (label := nextLabel) registers target hlayout
  rw [List.disjoint_left] at houtside
  have hnot := houtside hwire
  have hwireAcc : wire ≠ registers.accumulator k K := by
    intro equality
    exact hnot (by simp [equality])
  simp only [coefficientPrefixFirstLeafTraceState]
  rw [upd_other _ _ _ hwireAcc]
  exact (rippleFirstCell_usesOnly mode (registers.accumulator k K)
    (registers.targetAt target k nextLabel) (registers.addendAt target k nextLabel)
    (registers.carry k K) (registers.cellScratch k K)).preservesOutside state hnot

private theorem coefficientPrefixSecondLeafTrace_preservesDecoder
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    LogicalLeafPreserves
      (fun nextLabel active next =>
        coefficientPrefixSecondLeafTraceState registers k K mode target
          nextLabel active next)
      (registers.control ::
        (coefficientPrefixTree registers k K).indexWires.dedup ++
          registers.path k K) := by
  intro nextLabel active state wire hwire
  have houtside := coefficientPrefix_decoder_disjoint_leafRoles
    (label := nextLabel) registers target hlayout
  rw [List.disjoint_left] at houtside
  have hnot := houtside hwire
  have hwireAcc : wire ≠ registers.accumulator k K := by
    intro equality
    exact hnot (by simp [equality])
  let switched := state[registers.accumulator k K ↦
    Bool.xor (state (registers.accumulator k K)) active]
  simp only [coefficientPrefixSecondLeafTraceState]
  change Classical.run
      (rippleSecondCell mode (registers.accumulator k K)
        (registers.targetAt target k nextLabel)
        (registers.addendAt target k nextLabel) (registers.carry k K)
        (registers.cellScratch k K)) switched wire = state wire
  rw [(rippleSecondCell_usesOnly mode (registers.accumulator k K)
    (registers.targetAt target k nextLabel) (registers.addendAt target k nextLabel)
    (registers.carry k K) (registers.cellScratch k K)).preservesOutside switched hnot]
  exact upd_other state (registers.accumulator k K) _ hwireAcc

private theorem coefficientPrefixFirstLeafTrace_respectsOutside
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    LogicalLeafRespectsOutside
      (fun label active state =>
        coefficientPrefixFirstLeafTraceState registers k K mode target
          label active state)
      (registers.control ::
        (coefficientPrefixTree registers k K).indexWires.dedup ++
          registers.path k K) registers.control := by
  intro label active left right houtside _
  let decoder := registers.control ::
    (coefficientPrefixTree registers k K).indexWires.dedup ++ registers.path k K
  let support := [registers.accumulator k K, registers.targetAt target k label,
    registers.addendAt target k label, registers.carry k K,
    registers.cellScratch k K]
  let cell := rippleFirstCell mode (registers.accumulator k K)
    (registers.targetAt target k label) (registers.addendAt target k label)
    (registers.carry k K) (registers.cellScratch k K)
  have hdisjoint : List.Disjoint decoder support := by
    simpa only [decoder, support] using
      coefficientPrefix_decoder_disjoint_leafRoles
        (label := label) registers target hlayout
  have huses : PaperCircuitUsesOnly support cell := by
    dsimp only [support, cell]
    exact rippleFirstCell_usesOnly mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K)
  have hrun : AgreesOutside decoder
      (Classical.run cell left) (Classical.run cell right) :=
    coefficientPrefix_run_agreesOutside_of_disjoint support decoder cell left right
      huses hdisjoint (by simpa only [decoder] using houtside)
  have hacc : registers.accumulator k K ∉ decoder := by
    rw [List.disjoint_left] at hdisjoint
    exact fun hmem => hdisjoint hmem (by simp [support])
  change AgreesOutside decoder
    (coefficientPrefixFirstLeafTraceState registers k K mode target label active left)
    (coefficientPrefixFirstLeafTraceState registers k K mode target label active right)
  simpa [coefficientPrefixFirstLeafTraceState, cell] using
    coefficientPrefix_update_agreesOutside decoder
      (Classical.run cell left) (Classical.run cell right)
      (registers.accumulator k K)
      (Bool.xor (Classical.run cell left (registers.accumulator k K)) active)
      (Bool.xor (Classical.run cell right (registers.accumulator k K)) active)
      hrun (by rw [hrun (registers.accumulator k K) hacc])

private theorem coefficientPrefixSecondLeafTrace_respectsOutside
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    LogicalLeafRespectsOutside
      (fun label active state =>
        coefficientPrefixSecondLeafTraceState registers k K mode target
          label active state)
      (registers.control ::
        (coefficientPrefixTree registers k K).indexWires.dedup ++
          registers.path k K) registers.control := by
  intro label active left right houtside _
  let decoder := registers.control ::
    (coefficientPrefixTree registers k K).indexWires.dedup ++ registers.path k K
  let support := [registers.accumulator k K, registers.targetAt target k label,
    registers.addendAt target k label, registers.carry k K,
    registers.cellScratch k K]
  let cell := rippleSecondCell mode (registers.accumulator k K)
    (registers.targetAt target k label) (registers.addendAt target k label)
    (registers.carry k K) (registers.cellScratch k K)
  have hdisjoint : List.Disjoint decoder support := by
    simpa only [decoder, support] using
      coefficientPrefix_decoder_disjoint_leafRoles
        (label := label) registers target hlayout
  have huses : PaperCircuitUsesOnly support cell := by
    dsimp only [support, cell]
    exact rippleSecondCell_usesOnly mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K)
  have hacc : registers.accumulator k K ∉ decoder := by
    rw [List.disjoint_left] at hdisjoint
    exact fun hmem => hdisjoint hmem (by simp [support])
  let leftSwitched := left[registers.accumulator k K ↦
    Bool.xor (left (registers.accumulator k K)) active]
  let rightSwitched := right[registers.accumulator k K ↦
    Bool.xor (right (registers.accumulator k K)) active]
  have hswitched : AgreesOutside decoder leftSwitched rightSwitched := by
    apply coefficientPrefix_update_agreesOutside decoder left right
      (registers.accumulator k K) _ _ (by simpa only [decoder] using houtside)
    rw [houtside (registers.accumulator k K) (by simpa only [decoder] using hacc)]
  change AgreesOutside decoder
    (coefficientPrefixSecondLeafTraceState registers k K mode target label active left)
    (coefficientPrefixSecondLeafTraceState registers k K mode target label active right)
  simpa [coefficientPrefixSecondLeafTraceState, leftSwitched,
    rightSwitched, cell] using
    coefficientPrefix_run_agreesOutside_of_disjoint support decoder cell
      leftSwitched rightSwitched huses hdisjoint hswitched

private theorem coefficientPrefixFirstLeafTrace_eq_direct
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (active : Bool)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K)
    (hclean : state (registers.cellScratch k K) = false) :
    coefficientPrefixFirstLeafTraceState registers k K mode target label active state =
      coefficientPrefixFirstLeafState registers k K mode target label active state := by
  rw [coefficientPrefixFirstLeafTraceState,
    run_rippleFirstCell_state mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K) state
      (coefficientPrefix_cellLayout (label := label) registers target hlayout) hclean]
  rfl

private theorem coefficientPrefixSecondLeafTrace_eq_direct
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (active : Bool)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K)
    (hclean : state (registers.cellScratch k K) = false) :
    coefficientPrefixSecondLeafTraceState registers k K mode target label active state =
      coefficientPrefixSecondLeafState registers k K mode target label active state := by
  let switched := state[registers.accumulator k K ↦
    Bool.xor (state (registers.accumulator k K)) active]
  have hcellLayout := coefficientPrefix_cellLayout
    (label := label) registers target hlayout
  have haccScratch : registers.accumulator k K ≠ registers.cellScratch k K := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at hcellLayout
    exact hcellLayout.1.2.2.2
  have hcleanSwitched : switched (registers.cellScratch k K) = false := by
    rw [show switched = state[registers.accumulator k K ↦
        Bool.xor (state (registers.accumulator k K)) active] by rfl,
      upd_other state (registers.accumulator k K) _ (Ne.symm haccScratch)]
    exact hclean
  rw [coefficientPrefixSecondLeafTraceState,
    run_rippleSecondCell_state mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K) switched hcellLayout
      hcleanSwitched]
  rfl

private theorem coefficientPrefixFirstLeafTrace_preservesCellScratch
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (active : Bool)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K)
    (hclean : state (registers.cellScratch k K) = false) :
    coefficientPrefixFirstLeafTraceState registers k K mode target label active state
        (registers.cellScratch k K) = false := by
  rw [coefficientPrefixFirstLeafTraceState]
  have hcellLayout := coefficientPrefix_cellLayout
    (label := label) registers target hlayout
  have haccScratch : registers.cellScratch k K ≠ registers.accumulator k K := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at hcellLayout
    exact Ne.symm hcellLayout.1.2.2.2
  rw [upd_other _ _ _ haccScratch,
    rippleFirstCell_preservesScratch mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K) state hcellLayout,
    hclean]

private theorem coefficientPrefixSecondLeafTrace_preservesCellScratch
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (active : Bool)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K)
    (hclean : state (registers.cellScratch k K) = false) :
    coefficientPrefixSecondLeafTraceState registers k K mode target label active state
        (registers.cellScratch k K) = false := by
  let switched := state[registers.accumulator k K ↦
    Bool.xor (state (registers.accumulator k K)) active]
  have hcellLayout := coefficientPrefix_cellLayout
    (label := label) registers target hlayout
  have haccScratch : registers.cellScratch k K ≠ registers.accumulator k K := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at hcellLayout
    exact Ne.symm hcellLayout.1.2.2.2
  have hswitched : switched (registers.cellScratch k K) = false := by
    rw [show switched = state[registers.accumulator k K ↦
        Bool.xor (state (registers.accumulator k K)) active] by rfl,
      upd_other state (registers.accumulator k K) _ haccScratch, hclean]
  rw [coefficientPrefixSecondLeafTraceState,
    rippleSecondCell_preservesScratch mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K) switched hcellLayout,
    hswitched]

@[simp]
private theorem coefficientPrefixFirstLeaf_HPFree
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) :
    HPFree (coefficientPrefixFirstLeaf registers k K mode target label equalityControl) := by
  simp [coefficientPrefixFirstLeaf]

@[simp]
private theorem coefficientPrefixSecondLeaf_HPFree
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) :
    HPFree (coefficientPrefixSecondLeaf registers k K mode target label equalityControl) := by
  simp [coefficientPrefixSecondLeaf]

private theorem coefficientPrefixFirstLeaf_wellFormed
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (equalityControl : Wire)
    (hlayout : CoefficientPrefixLayout registers k K)
    (hcontrol : equalityControl ∈ registers.control ::
      (coefficientPrefixTree registers k K).indexWires.dedup ++ registers.path k K) :
    CircuitWellFormed
      (coefficientPrefixFirstLeaf registers k K mode target label equalityControl) := by
  have houtside := coefficientPrefix_decoder_disjoint_leafRoles
    (label := label) registers target hlayout
  rw [List.disjoint_left] at houtside
  have hcontrolAcc : equalityControl ≠ registers.accumulator k K := by
    intro equality
    exact houtside hcontrol (by simp [equality])
  rw [coefficientPrefixFirstLeaf, circuitWellFormed_append]
  exact ⟨rippleFirstCell_wellFormed mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K)
      (coefficientPrefix_cellLayout (label := label) registers target hlayout),
    by simp [CircuitWellFormed, Gate.WellFormed, hcontrolAcc]⟩

private theorem coefficientPrefixSecondLeaf_wellFormed
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (equalityControl : Wire)
    (hlayout : CoefficientPrefixLayout registers k K)
    (hcontrol : equalityControl ∈ registers.control ::
      (coefficientPrefixTree registers k K).indexWires.dedup ++ registers.path k K) :
    CircuitWellFormed
      (coefficientPrefixSecondLeaf registers k K mode target label equalityControl) := by
  have houtside := coefficientPrefix_decoder_disjoint_leafRoles
    (label := label) registers target hlayout
  rw [List.disjoint_left] at houtside
  have hcontrolAcc : equalityControl ≠ registers.accumulator k K := by
    intro equality
    exact houtside hcontrol (by simp [equality])
  rw [coefficientPrefixSecondLeaf, circuitWellFormed_append]
  exact ⟨by simp [CircuitWellFormed, Gate.WellFormed, hcontrolAcc],
    rippleSecondCell_wellFormed mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K)
      (coefficientPrefix_cellLayout (label := label) registers target hlayout)⟩

private theorem coefficientPrefix_coherent_seq_circuits
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
  exact (Quantum.run_append firstCircuit secondCircuit (Quantum.ket state)).symm

private theorem coefficientPrefixFirstLeafAdaptive_coherent
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (equalityControl : Wire)
    (hlayout : CoefficientPrefixLayout registers k K) :
    CoherentlyImplementsOn
      (coefficientPrefixFirstLeafAdaptive registers k K mode target label equalityControl)
      (Quantum.run
        (coefficientPrefixFirstLeaf registers k K mode target label equalityControl))
      (fun state ↦ Clean [registers.cellScratch k K] state) := by
  have hcell := coefficientPrefix_cellLayout (label := label) registers target hlayout
  have hseq := coefficientPrefix_coherent_seq_circuits
    (rippleFirstCellAdaptive_coherent mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K) hcell)
    (CoherentlyImplementsOn.unitary
      ([.CX equalityControl (registers.accumulator k K)] : Circuit) (fun _ ↦ True))
    (rippleFirstCell_HPFree mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K))
    (fun _ _ ↦ trivial)
  simpa [coefficientPrefixFirstLeafAdaptive, coefficientPrefixFirstLeaf,
    List.append_assoc] using hseq

private theorem coefficientPrefixSecondLeafAdaptive_coherent
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (equalityControl : Wire)
    (hlayout : CoefficientPrefixLayout registers k K) :
    CoherentlyImplementsOn
      (coefficientPrefixSecondLeafAdaptive registers k K mode target label equalityControl)
      (Quantum.run
        (coefficientPrefixSecondLeaf registers k K mode target label equalityControl))
      (fun state ↦ Clean [registers.cellScratch k K] state) := by
  have hcell := coefficientPrefix_cellLayout (label := label) registers target hlayout
  have haccScratch : registers.cellScratch k K ≠ registers.accumulator k K := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at hcell
    exact Ne.symm hcell.1.2.2.2
  have hseq := coefficientPrefix_coherent_seq_circuits
    (CoherentlyImplementsOn.unitary
      ([.CX equalityControl (registers.accumulator k K)] : Circuit)
      (fun state ↦ Clean [registers.cellScratch k K] state))
    (rippleSecondCellAdaptive_coherent mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K)
      (coefficientPrefix_cellLayout (label := label) registers target hlayout))
    (by simp)
    (by
      intro state hclean wire hwire
      have hwire : wire = registers.cellScratch k K := by simpa using hwire
      subst wire
      simp [Classical.run, Classical.applyGate, upd, haccScratch]
      exact hclean (registers.cellScratch k K) (by simp))
  simpa [coefficientPrefixSecondLeafAdaptive, coefficientPrefixSecondLeaf,
    List.append_assoc] using hseq

private theorem coefficientPrefixFirstLeafAdaptive_wellFormed
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (equalityControl : Wire)
    (hlayout : CoefficientPrefixLayout registers k K)
    (hcontrol : equalityControl ∈ registers.control ::
      (coefficientPrefixTree registers k K).indexWires.dedup ++ registers.path k K) :
    (coefficientPrefixFirstLeafAdaptive registers k K mode target label
      equalityControl).WellFormed := by
  have hcoherent := coefficientPrefixFirstLeaf_wellFormed (label := label) registers mode target
    equalityControl hlayout hcontrol
  rw [coefficientPrefixFirstLeaf, circuitWellFormed_append] at hcoherent
  exact AdaptiveCircuit.WellFormed.seq
    (rippleFirstCellAdaptive_wellFormed mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K)
      (coefficientPrefix_cellLayout (label := label) registers target hlayout))
    ⟨hcoherent.2, trivial⟩

private theorem coefficientPrefixSecondLeafAdaptive_wellFormed
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (equalityControl : Wire)
    (hlayout : CoefficientPrefixLayout registers k K)
    (hcontrol : equalityControl ∈ registers.control ::
      (coefficientPrefixTree registers k K).indexWires.dedup ++ registers.path k K) :
    (coefficientPrefixSecondLeafAdaptive registers k K mode target label
      equalityControl).WellFormed := by
  have hcoherent := coefficientPrefixSecondLeaf_wellFormed (label := label) registers mode target
    equalityControl hlayout hcontrol
  rw [coefficientPrefixSecondLeaf, circuitWellFormed_append] at hcoherent
  exact ⟨hcoherent.1,
    rippleSecondCellAdaptive_wellFormed mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K)
      (coefficientPrefix_cellLayout (label := label) registers target hlayout)⟩

@[simp]
private theorem coefficientPrefixFirstLeaf_toffoliCount
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) :
    eeaToffoliCount
        (coefficientPrefixFirstLeaf registers k K mode target label equalityControl) =
      rippleFirstCellToffoliCost mode := by
  rw [coefficientPrefixFirstLeaf, eeaToffoliCount_append,
    rippleFirstCell_toffoliCount]
  rfl

@[simp]
private theorem coefficientPrefixSecondLeaf_toffoliCount
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) :
    eeaToffoliCount
        (coefficientPrefixSecondLeaf registers k K mode target label equalityControl) =
      rippleSecondCellToffoliCost mode := by
  rw [coefficientPrefixSecondLeaf, eeaToffoliCount_append,
    rippleSecondCell_toffoliCount]
  simp [eeaToffoliCount]

@[simp]
private theorem coefficientPrefixFirstLeaf_cnotCount
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) :
    eeaCnotCount
        (coefficientPrefixFirstLeaf registers k K mode target label equalityControl) = 3 := by
  rw [coefficientPrefixFirstLeaf, eeaCnotCount_append,
    rippleFirstCell_cnotCount]
  rfl

@[simp]
private theorem coefficientPrefixSecondLeaf_cnotCount
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) :
    eeaCnotCount
        (coefficientPrefixSecondLeaf registers k K mode target label equalityControl) = 3 := by
  rw [coefficientPrefixSecondLeaf, eeaCnotCount_append,
    rippleSecondCell_cnotCount]
  rfl

@[simp]
private theorem coefficientPrefixFirstLeaf_tCount
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) :
    ShorECDLP.tCount
        (coefficientPrefixFirstLeaf registers k K mode target label equalityControl) =
      7 * rippleFirstCellToffoliCost mode := by
  rw [coefficientPrefixFirstLeaf, tCount_append, rippleFirstCell_tCount]
  rfl

@[simp]
private theorem coefficientPrefixSecondLeaf_tCount
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) :
    ShorECDLP.tCount
        (coefficientPrefixSecondLeaf registers k K mode target label equalityControl) =
      7 * rippleSecondCellToffoliCost mode := by
  rw [coefficientPrefixSecondLeaf, tCount_append, rippleSecondCell_tCount]
  simp [ShorECDLP.tCount, ShorECDLP.tCost]

private theorem coefficientPrefix_measurementCount_seq
    (first second : AdaptiveCircuit) :
    (first.seq second).measurementCount =
      first.measurementCount + second.measurementCount := by
  induction first with
  | done => simp [AdaptiveCircuit.seq, AdaptiveCircuit.measurementCount]
  | unitary circuit next ih =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.measurementCount, ih]
  | xMeasureReset wire onFalse onTrue ihFalse ihTrue =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.measurementCount,
        ihFalse, ihTrue, Nat.add_max_add_right, Nat.add_assoc]

private theorem coefficientPrefix_tCount_seq
    (first second : AdaptiveCircuit) :
    (first.seq second).tCount = first.tCount + second.tCount := by
  induction first with
  | done => simp [AdaptiveCircuit.seq, AdaptiveCircuit.tCount]
  | unitary circuit next ih =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.tCount, ih, Nat.add_assoc]
  | xMeasureReset wire onFalse onTrue ihFalse ihTrue =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.tCount,
        ihFalse, ihTrue, Nat.add_max_add_right]

@[simp]
private theorem coefficientPrefixFirstLeafAdaptive_measurementCount
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) :
    (coefficientPrefixFirstLeafAdaptive registers k K mode target label
      equalityControl).measurementCount = 1 := by
  rw [coefficientPrefixFirstLeafAdaptive, coefficientPrefix_measurementCount_seq,
    rippleFirstCellAdaptive_measurementCount]
  rfl

@[simp]
private theorem coefficientPrefixSecondLeafAdaptive_measurementCount
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) :
    (coefficientPrefixSecondLeafAdaptive registers k K mode target label
      equalityControl).measurementCount = 1 := by
  rw [coefficientPrefixSecondLeafAdaptive]
  simp only [AdaptiveCircuit.measurementCount,
    rippleSecondCellAdaptive_measurementCount]

@[simp]
private theorem coefficientPrefixFirstLeafAdaptive_tCount
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) :
    (coefficientPrefixFirstLeafAdaptive registers k K mode target label
      equalityControl).tCount = 7 * (rippleFirstCellToffoliCost mode - 1) := by
  rw [coefficientPrefixFirstLeafAdaptive, coefficientPrefix_tCount_seq,
    rippleFirstCellAdaptive_tCount]
  rfl

@[simp]
private theorem coefficientPrefixSecondLeafAdaptive_tCount
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) :
    (coefficientPrefixSecondLeafAdaptive registers k K mode target label
      equalityControl).tCount = 7 * (rippleSecondCellToffoliCost mode - 1) := by
  rw [coefficientPrefixSecondLeafAdaptive]
  simp only [AdaptiveCircuit.tCount, tCount_cons, tCount_nil,
    rippleSecondCellAdaptive_tCount]
  simp [ShorECDLP.tCost]

/-! ## Ordered traversal and whole-state semantics -/

/-- Circuit-free increasing source-order semantics: the frozen boundary bits determine one Boolean
equality pulse per source label, and the first-cell transition is folded over those pulses. -/
def coefficientPrefixFirstTraversalState
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (state : BasisState) : BasisState :=
  ((coefficientPrefixTree registers k K).visitPulses .inc
      (state registers.control) state).foldl
    (fun next pulse => coefficientPrefixFirstLeafState registers k K mode target
      pulse.1 pulse.2 next) state

/-- Circuit-free decreasing source-order semantics, expressed by the reverse pulse fold. -/
def coefficientPrefixSecondTraversalState
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (state : BasisState) : BasisState :=
  ((coefficientPrefixTree registers k K).visitPulses .dec
      (state registers.control) state).foldl
    (fun next pulse => coefficientPrefixSecondLeafState registers k K mode target
      pulse.1 pulse.2 next) state

private theorem coefficientPrefix_foldl_eq_of_cleanWire
    {α : Type} (steps : List α)
    (totalState directState : α → BasisState → BasisState)
    (cleanWire : Wire)
    (hreduces : ∀ step next, next cleanWire = false →
      totalState step next = directState step next)
    (hpreserves : ∀ step next, next cleanWire = false →
      directState step next cleanWire = false)
    (state : BasisState) (hclean : state cleanWire = false) :
    steps.foldl (fun next step => totalState step next) state =
        steps.foldl (fun next step => directState step next) state ∧
      steps.foldl (fun next step => directState step next) state cleanWire = false := by
  induction steps generalizing state with
  | nil => exact ⟨rfl, hclean⟩
  | cons step rest ih =>
      simp only [List.foldl_cons]
      rw [hreduces step state hclean]
      exact ih (directState step state) (hpreserves step state hclean)

theorem run_coefficientPrefixFirstTraversal_state
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (state : BasisState)
    (hlayout : CoefficientPrefixLayout registers k K)
    (hclean : Clean (registers.path k K) state)
    (hcellClean : state (registers.cellScratch k K) = false) :
    Classical.run
        (unaryActionUnitary .inc
          (coefficientPrefixFirstLeaf registers k K mode target)
          (coefficientPrefixTree registers k K) registers.control
          (registers.path k K)) state =
      coefficientPrefixFirstTraversalState registers k K mode target state := by
  let tree := coefficientPrefixTree registers k K
  let decoder := registers.control :: tree.indexWires.dedup ++ registers.path k K
  let physicalLeafState := fun label equalityControl next =>
    Classical.run
      (coefficientPrefixFirstLeaf registers k K mode target label equalityControl) next
  let traceLeafState := fun label active next =>
    coefficientPrefixFirstLeafTraceState registers k K mode target label active next
  have htree : tree.Layout registers.control (registers.path k K) := by
    simpa only [tree, coefficientPrefixTree, CoefficientPrefixRegisters.path] using
      hlayout.tree
  have hruns : UnaryLeafRunsAs
      (coefficientPrefixFirstLeaf registers k K mode target) physicalLeafState := by
    intro label equalityControl next
    rfl
  have hlogical : UnaryLeafRunsLogically physicalLeafState traceLeafState decoder := by
    intro label equalityControl hcontrol next
    exact coefficientPrefix_runFirstLeaf_trace registers mode target equalityControl next
      hlayout (by simpa only [decoder, tree] using hcontrol)
  have hleaf : UnaryLeafPreserves
      (coefficientPrefixFirstLeaf registers k K mode target) decoder := by
    intro label equalityControl _ next wire hwire
    exact coefficientPrefixFirstLeaf_preservesDecoder
      (label := label) registers mode target hlayout equalityControl next wire
      (by simpa only [decoder, tree] using hwire)
  have hlogicalPreserves : LogicalLeafPreserves traceLeafState decoder := by
    simpa only [traceLeafState, decoder, tree] using
      coefficientPrefixFirstLeafTrace_preservesDecoder registers mode target hlayout
  have hlogicalOutside : LogicalLeafRespectsOutside traceLeafState decoder
      registers.control := by
    simpa only [traceLeafState, decoder, tree] using
      coefficientPrefixFirstLeafTrace_respectsOutside registers mode target hlayout
  have htrace : Classical.run
        (unaryActionUnitary .inc
          (coefficientPrefixFirstLeaf registers k K mode target)
          tree registers.control (registers.path k K)) state =
      tree.runLogicalTree .inc traceLeafState
        (state registers.control) state state :=
    run_unaryActionUnitary_as_runLogicalTree .inc
      (coefficientPrefixFirstLeaf registers k K mode target)
      physicalLeafState traceLeafState tree registers.control (registers.path k K)
      decoder state htree hruns hlogical hleaf hlogicalPreserves hlogicalOutside
      (by intro wire hwire; exact hwire) hclean
  let pulses := tree.visitPulses .inc (state registers.control) state
  have hpure := coefficientPrefix_foldl_eq_of_cleanWire pulses
    (fun pulse next => traceLeafState pulse.1 pulse.2 next)
    (fun pulse next => coefficientPrefixFirstLeafState registers k K mode target
      pulse.1 pulse.2 next)
    (registers.cellScratch k K)
    (by
      intro pulse next hcell
      exact coefficientPrefixFirstLeafTrace_eq_direct registers mode target pulse.2 next
        hlayout hcell)
    (by
      intro pulse next hcell
      change coefficientPrefixFirstLeafState registers k K mode target
        pulse.1 pulse.2 next (registers.cellScratch k K) = false
      rw [← coefficientPrefixFirstLeafTrace_eq_direct registers mode target pulse.2 next
        hlayout hcell]
      exact coefficientPrefixFirstLeafTrace_preservesCellScratch registers mode target
        pulse.2 next hlayout hcell)
    state hcellClean
  calc
    Classical.run
        (unaryActionUnitary .inc
          (coefficientPrefixFirstLeaf registers k K mode target)
          (coefficientPrefixTree registers k K) registers.control
          (registers.path k K)) state =
        tree.runLogicalTree .inc traceLeafState
          (state registers.control) state state := by simpa only [tree] using htrace
    _ = pulses.foldl
          (fun next pulse => traceLeafState pulse.1 pulse.2 next) state := by
        simpa only [pulses] using UnaryActionTree.runLogicalTree_eq_foldl
          .inc traceLeafState tree (state registers.control) state state
    _ = pulses.foldl
          (fun next pulse => coefficientPrefixFirstLeafState registers k K mode target
            pulse.1 pulse.2 next) state := hpure.1
    _ = coefficientPrefixFirstTraversalState registers k K mode target state := by
      rfl

theorem run_coefficientPrefixSecondTraversal_state
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (state : BasisState)
    (hlayout : CoefficientPrefixLayout registers k K)
    (hclean : Clean (registers.path k K) state)
    (hcellClean : state (registers.cellScratch k K) = false) :
    Classical.run
        (unaryActionUnitary .dec
          (coefficientPrefixSecondLeaf registers k K mode target)
          (coefficientPrefixTree registers k K) registers.control
          (registers.path k K)) state =
      coefficientPrefixSecondTraversalState registers k K mode target state := by
  let tree := coefficientPrefixTree registers k K
  let decoder := registers.control :: tree.indexWires.dedup ++ registers.path k K
  let physicalLeafState := fun label equalityControl next =>
    Classical.run
      (coefficientPrefixSecondLeaf registers k K mode target label equalityControl) next
  let traceLeafState := fun label active next =>
    coefficientPrefixSecondLeafTraceState registers k K mode target label active next
  have htree : tree.Layout registers.control (registers.path k K) := by
    simpa only [tree, coefficientPrefixTree, CoefficientPrefixRegisters.path] using
      hlayout.tree
  have hruns : UnaryLeafRunsAs
      (coefficientPrefixSecondLeaf registers k K mode target) physicalLeafState := by
    intro label equalityControl next
    rfl
  have hlogical : UnaryLeafRunsLogically physicalLeafState traceLeafState decoder := by
    intro label equalityControl _ next
    exact coefficientPrefix_runSecondLeaf_trace registers k K label mode target
      equalityControl next
  have hleaf : UnaryLeafPreserves
      (coefficientPrefixSecondLeaf registers k K mode target) decoder := by
    intro label equalityControl _ next wire hwire
    exact coefficientPrefixSecondLeaf_preservesDecoder
      (label := label) registers mode target hlayout equalityControl next wire
      (by simpa only [decoder, tree] using hwire)
  have hlogicalPreserves : LogicalLeafPreserves traceLeafState decoder := by
    simpa only [traceLeafState, decoder, tree] using
      coefficientPrefixSecondLeafTrace_preservesDecoder registers mode target hlayout
  have hlogicalOutside : LogicalLeafRespectsOutside traceLeafState decoder
      registers.control := by
    simpa only [traceLeafState, decoder, tree] using
      coefficientPrefixSecondLeafTrace_respectsOutside registers mode target hlayout
  have htrace : Classical.run
        (unaryActionUnitary .dec
          (coefficientPrefixSecondLeaf registers k K mode target)
          tree registers.control (registers.path k K)) state =
      tree.runLogicalTree .dec traceLeafState
        (state registers.control) state state :=
    run_unaryActionUnitary_as_runLogicalTree .dec
      (coefficientPrefixSecondLeaf registers k K mode target)
      physicalLeafState traceLeafState tree registers.control (registers.path k K)
      decoder state htree hruns hlogical hleaf hlogicalPreserves hlogicalOutside
      (by intro wire hwire; exact hwire) hclean
  let pulses := tree.visitPulses .dec (state registers.control) state
  have hpure := coefficientPrefix_foldl_eq_of_cleanWire pulses
    (fun pulse next => traceLeafState pulse.1 pulse.2 next)
    (fun pulse next => coefficientPrefixSecondLeafState registers k K mode target
      pulse.1 pulse.2 next)
    (registers.cellScratch k K)
    (by
      intro pulse next hcell
      exact coefficientPrefixSecondLeafTrace_eq_direct registers mode target pulse.2 next
        hlayout hcell)
    (by
      intro pulse next hcell
      change coefficientPrefixSecondLeafState registers k K mode target
        pulse.1 pulse.2 next (registers.cellScratch k K) = false
      rw [← coefficientPrefixSecondLeafTrace_eq_direct registers mode target pulse.2 next
        hlayout hcell]
      exact coefficientPrefixSecondLeafTrace_preservesCellScratch registers mode target
        pulse.2 next hlayout hcell)
    state hcellClean
  calc
    Classical.run
        (unaryActionUnitary .dec
          (coefficientPrefixSecondLeaf registers k K mode target)
          (coefficientPrefixTree registers k K) registers.control
          (registers.path k K)) state =
        tree.runLogicalTree .dec traceLeafState
          (state registers.control) state state := by simpa only [tree] using htrace
    _ = pulses.foldl
          (fun next pulse => traceLeafState pulse.1 pulse.2 next) state := by
        simpa only [pulses] using UnaryActionTree.runLogicalTree_eq_foldl
          .dec traceLeafState tree (state registers.control) state state
    _ = pulses.foldl
          (fun next pulse => coefficientPrefixSecondLeafState registers k K mode target
            pulse.1 pulse.2 next) state := hpure.1
    _ = coefficientPrefixSecondTraversalState registers k K mode target state := by
      rfl

private theorem coefficientPrefix_decoder_nodup
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K) :
    (registers.control ::
      (coefficientPrefixTree registers k K).indexWires.dedup ++
        registers.path k K).Nodup := by
  have htree : (coefficientPrefixTree registers k K).Layout registers.control
      (registers.path k K) := by
    simpa [coefficientPrefixTree, CoefficientPrefixRegisters.path] using
      hlayout.tree
  exact unaryLayout_decoderNodup htree

private theorem coefficientPrefix_decoder_cell_nodup
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    ((registers.control ::
      (coefficientPrefixTree registers k K).indexWires.dedup ++
        registers.path k K) ++ [registers.cellScratch k K]).Nodup := by
  refine List.nodup_append.mpr
    ⟨coefficientPrefix_decoder_nodup registers hlayout, by simp, ?_⟩
  have houtside := coefficientPrefix_decoder_disjoint_leafRoles
    (label := k) registers target hlayout
  rw [List.disjoint_left] at houtside
  intro wire hwire cell hcell equality
  have hcellEq : cell = registers.cellScratch k K := by simpa using hcell
  subst cell
  apply houtside hwire
  simp only [List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (by simpa using hcell))))

private theorem coefficientPrefixFirstTraversal_preservesDecoderCell
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (state : BasisState)
    (hlayout : CoefficientPrefixLayout registers k K)
    (hclean : Clean (registers.path k K) state) :
    ∀ wire,
      wire ∈ (registers.control ::
        (coefficientPrefixTree registers k K).indexWires.dedup ++
          registers.path k K) ++ [registers.cellScratch k K] →
      Classical.run
          (unaryActionUnitary .inc
            (coefficientPrefixFirstLeaf registers k K mode target)
            (coefficientPrefixTree registers k K) registers.control
            (registers.path k K)) state wire = state wire := by
  let decoder := registers.control ::
    (coefficientPrefixTree registers k K).indexWires.dedup ++ registers.path k K
  let protectedWires := decoder ++ [registers.cellScratch k K]
  have htree : (coefficientPrefixTree registers k K).Layout registers.control
      (registers.path k K) := by
    simpa [coefficientPrefixTree, CoefficientPrefixRegisters.path] using
      hlayout.tree
  have hleaf : UnaryLeafPreserves
      (coefficientPrefixFirstLeaf registers k K mode target) protectedWires := by
    intro label equalityControl _ next wire hwire
    rcases List.mem_append.mp hwire with hdecoder | hcell
    · exact coefficientPrefixFirstLeaf_preservesDecoder
        (label := label) registers mode target hlayout equalityControl next wire
        (by simpa only [protectedWires, decoder] using hdecoder)
    · have hwire : wire = registers.cellScratch k K := by simpa using hcell
      subst wire
      exact coefficientPrefixFirstLeaf_preservesCellScratch
        (label := label) registers mode target equalityControl next hlayout
  exact unaryActionUnitary_preserves .inc
    (coefficientPrefixFirstLeaf registers k K mode target)
    (coefficientPrefixTree registers k K) registers.control (registers.path k K)
    protectedWires state htree hleaf (by
      intro wire hwire
      exact List.mem_append.mpr (Or.inl (by simpa only [decoder] using hwire))) hclean

@[simp]
private theorem coefficientPrefixFirstTraversal_HPFree
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) :
    HPFree
      (unaryActionUnitary .inc
        (coefficientPrefixFirstLeaf registers k K mode target)
        (coefficientPrefixTree registers k K) registers.control
        (registers.path k K)) := by
  apply unaryActionUnitary_HPFree
  intro label equalityControl
  exact coefficientPrefixFirstLeaf_HPFree registers k K mode target label equalityControl

@[simp]
private theorem coefficientPrefixSecondTraversal_HPFree
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) :
    HPFree
      (unaryActionUnitary .dec
        (coefficientPrefixSecondLeaf registers k K mode target)
        (coefficientPrefixTree registers k K) registers.control
        (registers.path k K)) := by
  apply unaryActionUnitary_HPFree
  intro label equalityControl
  exact coefficientPrefixSecondLeaf_HPFree registers k K mode target label equalityControl

private theorem coefficientPrefixFirstTraversal_wellFormed
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    CircuitWellFormed
      (unaryActionUnitary .inc
        (coefficientPrefixFirstLeaf registers k K mode target)
        (coefficientPrefixTree registers k K) registers.control
        (registers.path k K)) := by
  apply unaryActionUnitary_wellFormed
  · simpa [coefficientPrefixTree, CoefficientPrefixRegisters.path] using
      hlayout.tree
  · intro label hlabel equalityControl hcontrol
    exact coefficientPrefixFirstLeaf_wellFormed (label := label) registers mode target
      equalityControl hlayout hcontrol

private theorem coefficientPrefixSecondTraversal_wellFormed
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    CircuitWellFormed
      (unaryActionUnitary .dec
        (coefficientPrefixSecondLeaf registers k K mode target)
        (coefficientPrefixTree registers k K) registers.control
        (registers.path k K)) := by
  apply unaryActionUnitary_wellFormed
  · simpa [coefficientPrefixTree, CoefficientPrefixRegisters.path] using
      hlayout.tree
  · intro label hlabel equalityControl hcontrol
    exact coefficientPrefixSecondLeaf_wellFormed (label := label) registers mode target
      equalityControl hlayout hcontrol

private theorem coefficientPrefixFirstTraversalAdaptive_wellFormed
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    (unaryAdaptiveAction .inc
      (coefficientPrefixFirstLeafAdaptive registers k K mode target)
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K)).WellFormed := by
  apply unaryAdaptiveAction_wellFormed
  · simpa [coefficientPrefixTree, CoefficientPrefixRegisters.path] using
      hlayout.tree
  · intro label hlabel equalityControl hcontrol
    exact coefficientPrefixFirstLeafAdaptive_wellFormed (label := label) registers
      mode target equalityControl hlayout hcontrol

private theorem coefficientPrefixSecondTraversalAdaptive_wellFormed
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    (unaryAdaptiveAction .dec
      (coefficientPrefixSecondLeafAdaptive registers k K mode target)
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K)).WellFormed := by
  apply unaryAdaptiveAction_wellFormed
  · simpa [coefficientPrefixTree, CoefficientPrefixRegisters.path] using
      hlayout.tree
  · intro label hlabel equalityControl hcontrol
    exact coefficientPrefixSecondLeafAdaptive_wellFormed (label := label) registers
      mode target equalityControl hlayout hcontrol

private theorem coefficientPrefixFirstTraversalAdaptive_coherent
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    CoherentlyImplementsOn
      (unaryAdaptiveAction .inc
        (coefficientPrefixFirstLeafAdaptive registers k K mode target)
        (coefficientPrefixTree registers k K) registers.control
        (registers.path k K))
      (Quantum.run
        (unaryActionUnitary .inc
          (coefficientPrefixFirstLeaf registers k K mode target)
          (coefficientPrefixTree registers k K) registers.control
          (registers.path k K)))
      (fun state ↦ Clean (registers.path k K) state ∧
        Clean [registers.cellScratch k K] state) := by
  let decoder := registers.control ::
    (coefficientPrefixTree registers k K).indexWires.dedup ++ registers.path k K
  have hleaf : UnaryLeafPreserves
      (coefficientPrefixFirstLeaf registers k K mode target)
      (decoder ++ [registers.cellScratch k K]) := by
    intro label equalityControl _ state wire hwire
    rcases List.mem_append.mp hwire with hdecoder | hcell
    · exact coefficientPrefixFirstLeaf_preservesDecoder
        (label := label) registers mode target hlayout equalityControl state wire
        (by simpa only [decoder] using hdecoder)
    · have hwire : wire = registers.cellScratch k K := by simpa using hcell
      subst wire
      exact coefficientPrefixFirstLeaf_preservesCellScratch
        (label := label) registers mode target equalityControl state hlayout
  exact unaryAdaptiveAction_coherent_on
    (order := .inc)
    (leafAdaptive := coefficientPrefixFirstLeafAdaptive registers k K mode target)
    (leafUnitary := coefficientPrefixFirstLeaf registers k K mode target)
    (tree := coefficientPrefixTree registers k K)
    (control := registers.control)
    (ancillas := registers.path k K)
    (extraWires := [registers.cellScratch k K])
    (by simpa [coefficientPrefixTree, CoefficientPrefixRegisters.path] using
      hlayout.tree)
    (by simpa only [decoder] using
      coefficientPrefix_decoder_cell_nodup registers target hlayout)
    hleaf (by
      intro label hlabel equalityControl hcontrol
      exact coefficientPrefixFirstLeafAdaptive_coherent registers mode target
        equalityControl hlayout)
    (by intro label equalityControl; simp)

private theorem coefficientPrefixSecondTraversalAdaptive_coherent
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    CoherentlyImplementsOn
      (unaryAdaptiveAction .dec
        (coefficientPrefixSecondLeafAdaptive registers k K mode target)
        (coefficientPrefixTree registers k K) registers.control
        (registers.path k K))
      (Quantum.run
        (unaryActionUnitary .dec
          (coefficientPrefixSecondLeaf registers k K mode target)
          (coefficientPrefixTree registers k K) registers.control
          (registers.path k K)))
      (fun state ↦ Clean (registers.path k K) state ∧
        Clean [registers.cellScratch k K] state) := by
  let decoder := registers.control ::
    (coefficientPrefixTree registers k K).indexWires.dedup ++ registers.path k K
  have hleaf : UnaryLeafPreserves
      (coefficientPrefixSecondLeaf registers k K mode target)
      (decoder ++ [registers.cellScratch k K]) := by
    intro label equalityControl _ state wire hwire
    rcases List.mem_append.mp hwire with hdecoder | hcell
    · exact coefficientPrefixSecondLeaf_preservesDecoder
        (label := label) registers mode target hlayout equalityControl state wire
        (by simpa only [decoder] using hdecoder)
    · have hwire : wire = registers.cellScratch k K := by simpa using hcell
      subst wire
      exact coefficientPrefixSecondLeaf_preservesCellScratch
        (label := label) registers mode target equalityControl state hlayout
  exact unaryAdaptiveAction_coherent_on
    (order := .dec)
    (leafAdaptive := coefficientPrefixSecondLeafAdaptive registers k K mode target)
    (leafUnitary := coefficientPrefixSecondLeaf registers k K mode target)
    (tree := coefficientPrefixTree registers k K)
    (control := registers.control)
    (ancillas := registers.path k K)
    (extraWires := [registers.cellScratch k K])
    (by simpa [coefficientPrefixTree, CoefficientPrefixRegisters.path] using
      hlayout.tree)
    (by simpa only [decoder] using
      coefficientPrefix_decoder_cell_nodup registers target hlayout)
    hleaf (by
      intro label hlabel equalityControl hcontrol
      exact coefficientPrefixSecondLeafAdaptive_coherent registers mode target
        equalityControl hlayout)
    (by intro label equalityControl; simp)

/-- Circuit-free Boolean/source recurrence for the complete prepared-boundary block: seed the
accumulator, run the increasing leaf recurrence, update the sign directly when requested, run the
decreasing leaf recurrence, and clear the accumulator. -/
def coefficientPrefixState
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (state : BasisState) : BasisState :=
  let seeded := state[registers.accumulator k K ↦
    Bool.xor (state (registers.accumulator k K)) (state registers.control)]
  let afterFirst := coefficientPrefixFirstTraversalState registers k K mode target seeded
  let afterSign := if signUpdate then
      afterFirst[registers.sign ↦
        Bool.xor (afterFirst registers.sign) (afterFirst (registers.carry k K))]
    else afterFirst
  let afterSecond := coefficientPrefixSecondTraversalState registers k K mode target afterSign
  afterSecond[registers.accumulator k K ↦
    Bool.xor (afterSecond (registers.accumulator k K))
      (afterSecond registers.control)]

private theorem coefficientPrefix_carry_mem_scratch
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K) :
    registers.carry k K ∈ registers.scratch := by
  exact coefficientPrefix_scratchAt_mem registers hlayout (by omega)

private theorem coefficientPrefix_accumulator_mem_scratch
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K) :
    registers.accumulator k K ∈ registers.scratch := by
  exact coefficientPrefix_scratchAt_mem registers hlayout (by omega)

private theorem coefficientPrefix_cellScratch_mem_scratch
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K) :
    registers.cellScratch k K ∈ registers.scratch := by
  exact coefficientPrefix_scratchAt_mem registers hlayout (by omega)

private theorem coefficientPrefix_fixed_not_mem_scratch
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K) :
    registers.control ∉ registers.scratch ∧ registers.sign ∉ registers.scratch := by
  have hcross := (coefficientPrefix_physical_parts registers hlayout).2.2.2.2.2.1
  constructor
  · intro hmem
    exact hcross registers.control (by simp) registers.control
      (by simp [hmem]) rfl
  · intro hmem
    exact hcross registers.sign (by simp) registers.sign
      (by simp [hmem]) rfl

private theorem coefficientPrefix_cleanPath_of_ready
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (state : BasisState) (hready : CoefficientPrefixReady registers state) :
    Clean (registers.path k K) state := by
  intro wire hwire
  exact hready wire (coefficientPrefix_path_mem_scratch registers k K wire hwire)

private theorem clean_run_singleCX_of_target_not_mem
    (control target : Wire) (wires : List Wire) (state : BasisState)
    (hclean : Clean wires state) (htarget : target ∉ wires) :
    Clean wires (Classical.run ([.CX control target] : Circuit) state) := by
  intro wire hwire
  have hne : wire ≠ target := by
    intro equality
    subst wire
    exact htarget hwire
  simpa [Classical.run_cons, Classical.run_nil, Classical.applyGate, upd, hne] using
    hclean wire hwire

private theorem coefficientPrefixSign_preservesPath
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (signUpdate : Bool) (state : BasisState)
    (hlayout : CoefficientPrefixLayout registers k K)
    (hclean : Clean (registers.path k K) state) :
    Clean (registers.path k K)
      (Classical.run (coefficientPrefixSignCircuit registers k K signUpdate) state) := by
  cases signUpdate with
  | false => simpa [coefficientPrefixSignCircuit] using hclean
  | true =>
      apply clean_run_singleCX_of_target_not_mem
        (registers.carry k K) registers.sign (registers.path k K) state hclean
      intro hsign
      exact (coefficientPrefix_fixed_not_mem_scratch registers hlayout).2
        (coefficientPrefix_path_mem_scratch registers k K registers.sign hsign)

/-- The literal coherent block has the direct source-order prepared-boundary semantics. -/
theorem run_coefficientPrefixUnitary_state
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K)
    (hready : CoefficientPrefixReady registers state) :
    Classical.run
        (coefficientPrefixUnitary registers k K mode signUpdate target) state =
      coefficientPrefixState registers k K mode signUpdate target state := by
  let seeded := state[registers.accumulator k K ↦
    Bool.xor (state (registers.accumulator k K)) (state registers.control)]
  have hseedRun : Classical.run
      ([.CX registers.control (registers.accumulator k K)] : Circuit) state = seeded := by
    rfl
  have hpath : Clean (registers.path k K) state :=
    coefficientPrefix_cleanPath_of_ready registers k K state hready
  have hseededPath : Clean (registers.path k K) seeded := by
    have hphysical := clean_run_singleCX_of_target_not_mem registers.control
      (registers.accumulator k K) (registers.path k K) state hpath
      (coefficientPrefix_path_not_accumulator registers hlayout)
    rw [hseedRun] at hphysical
    exact hphysical
  have hcell : state (registers.cellScratch k K) = false :=
    hready (registers.cellScratch k K)
      (coefficientPrefix_cellScratch_mem_scratch registers hlayout)
  have haccCell : registers.accumulator k K ≠ registers.cellScratch k K := by
    have hcellLayout := coefficientPrefix_cellLayout
      (label := k) registers target hlayout
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at hcellLayout
    exact hcellLayout.1.2.2.2
  have hseededCell : seeded (registers.cellScratch k K) = false := by
    rw [show seeded = state[registers.accumulator k K ↦
        Bool.xor (state (registers.accumulator k K))
          (state registers.control)] by rfl,
      upd_other state (registers.accumulator k K) _ (Ne.symm haccCell)]
    exact hcell
  let afterFirst := coefficientPrefixFirstTraversalState registers k K mode target seeded
  have hfirstRun : Classical.run
        (unaryActionUnitary .inc
          (coefficientPrefixFirstLeaf registers k K mode target)
          (coefficientPrefixTree registers k K) registers.control
          (registers.path k K)) seeded = afterFirst := by
    exact run_coefficientPrefixFirstTraversal_state registers mode target seeded
      hlayout hseededPath hseededCell
  have hfirstPath : Clean (registers.path k K) afterFirst := by
    intro wire hwire
    have hpreserved := coefficientPrefixFirstTraversal_preservesDecoderCell
      registers mode target seeded hlayout hseededPath wire (by
        exact List.mem_append.mpr (Or.inl (by simp [hwire])))
    rw [hfirstRun] at hpreserved
    exact hpreserved.trans (hseededPath wire hwire)
  have hfirstCell : afterFirst (registers.cellScratch k K) = false := by
    have hpreserved := coefficientPrefixFirstTraversal_preservesDecoderCell
      registers mode target seeded hlayout hseededPath
      (registers.cellScratch k K) (by
        exact List.mem_append.mpr (Or.inr (by simp)))
    rw [hfirstRun] at hpreserved
    exact hpreserved.trans hseededCell
  let afterSign := if signUpdate then
      afterFirst[registers.sign ↦
        Bool.xor (afterFirst registers.sign) (afterFirst (registers.carry k K))]
    else afterFirst
  have hsignRun : Classical.run
      (coefficientPrefixSignCircuit registers k K signUpdate) afterFirst = afterSign := by
    cases signUpdate <;> rfl
  have hsignPath : Clean (registers.path k K) afterSign :=
    by
      have hphysical := coefficientPrefixSign_preservesPath registers signUpdate
        afterFirst hlayout hfirstPath
      rw [hsignRun] at hphysical
      exact hphysical
  have hcellSign : registers.cellScratch k K ≠ registers.sign := by
    intro equality
    apply (coefficientPrefix_fixed_not_mem_scratch registers hlayout).2
    rw [← equality]
    exact coefficientPrefix_cellScratch_mem_scratch registers hlayout
  have hsignCell : afterSign (registers.cellScratch k K) = false := by
    cases signUpdate <;>
      simp [afterSign, upd, hcellSign, hfirstCell]
  let afterSecond := coefficientPrefixSecondTraversalState registers k K mode target afterSign
  have hsecondRun : Classical.run
        (unaryActionUnitary .dec
          (coefficientPrefixSecondLeaf registers k K mode target)
          (coefficientPrefixTree registers k K) registers.control
          (registers.path k K)) afterSign = afterSecond := by
    exact run_coefficientPrefixSecondTraversal_state registers mode target afterSign
      hlayout hsignPath hsignCell
  simp only [coefficientPrefixUnitary, coefficientPrefixState,
    Classical.run_append]
  rw [hseedRun, hfirstRun, hsignRun, hsecondRun]
  rfl

private theorem coefficientPrefix_control_ne_accumulator
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K) :
    registers.control ≠ registers.accumulator k K := by
  intro equality
  apply (coefficientPrefix_fixed_not_mem_scratch registers hlayout).1
  rw [equality]
  exact coefficientPrefix_accumulator_mem_scratch registers hlayout

private theorem coefficientPrefix_carry_ne_sign
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K) :
    registers.carry k K ≠ registers.sign := by
  intro equality
  apply (coefficientPrefix_fixed_not_mem_scratch registers hlayout).2
  rw [← equality]
  exact coefficientPrefix_carry_mem_scratch registers hlayout

private theorem coefficientPrefixSign_HPFree
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (signUpdate : Bool) :
    HPFree (coefficientPrefixSignCircuit registers k K signUpdate) := by
  cases signUpdate <;> simp [coefficientPrefixSignCircuit]

private theorem coefficientPrefixSign_wellFormed
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (signUpdate : Bool) (hlayout : CoefficientPrefixLayout registers k K) :
    CircuitWellFormed (coefficientPrefixSignCircuit registers k K signUpdate) := by
  cases signUpdate with
  | false => simp [coefficientPrefixSignCircuit]
  | true =>
      simp [coefficientPrefixSignCircuit, CircuitWellFormed, Gate.WellFormed,
        coefficientPrefix_carry_ne_sign registers hlayout]

/-- The literal coherent prepared-boundary block has no Hadamard or phase gates. -/
@[simp]
theorem coefficientPrefixUnitary_HPFree
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) :
    HPFree (coefficientPrefixUnitary registers k K mode signUpdate target) := by
  simp [coefficientPrefixUnitary,
    coefficientPrefixFirstTraversal_HPFree registers k K mode target,
    coefficientPrefixSecondTraversal_HPFree registers k K mode target,
    coefficientPrefixSign_HPFree registers k K signUpdate]

/-- Physical well-formedness of the literal coherent source block. -/
theorem coefficientPrefixUnitary_wellFormed
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    CircuitWellFormed
      (coefficientPrefixUnitary registers k K mode signUpdate target) := by
  have hseed : CircuitWellFormed
      ([.CX registers.control (registers.accumulator k K)] : Circuit) := by
    simp [CircuitWellFormed, Gate.WellFormed,
      coefficientPrefix_control_ne_accumulator registers hlayout]
  simp only [coefficientPrefixUnitary, circuitWellFormed_append]
  exact ⟨⟨⟨⟨hseed,
    coefficientPrefixFirstTraversal_wellFormed registers mode target hlayout⟩,
    coefficientPrefixSign_wellFormed registers signUpdate hlayout⟩,
    coefficientPrefixSecondTraversal_wellFormed registers mode target hlayout⟩,
    hseed⟩

/-- Every branch of the measurement-uncomputed source block is physically well formed. -/
theorem coefficientPrefixAdaptive_wellFormed
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    (coefficientPrefixAdaptive registers k K mode signUpdate target).WellFormed := by
  have hseed : CircuitWellFormed
      ([.CX registers.control (registers.accumulator k K)] : Circuit) := by
    simp [CircuitWellFormed, Gate.WellFormed,
      coefficientPrefix_control_ne_accumulator registers hlayout]
  rw [coefficientPrefixAdaptive]
  exact ⟨hseed,
    AdaptiveCircuit.WellFormed.seq
      (coefficientPrefixFirstTraversalAdaptive_wellFormed registers mode target hlayout)
      ⟨coefficientPrefixSign_wellFormed registers signUpdate hlayout,
        AdaptiveCircuit.WellFormed.seq
          (coefficientPrefixSecondTraversalAdaptive_wellFormed
            registers mode target hlayout)
          ⟨hseed, trivial⟩⟩⟩

private theorem coefficientPrefix_accumulator_ne_cellScratch
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K) :
    registers.accumulator k K ≠ registers.cellScratch k K := by
  have hroles := coefficientPrefix_scratch_roles_nodup registers hlayout
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hroles
  exact hroles.2.1

private theorem coefficientPrefixFirstTraversal_preservesCleanPathCell
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (state : BasisState)
    (hlayout : CoefficientPrefixLayout registers k K)
    (hclean : Clean (registers.path k K) state ∧
      Clean [registers.cellScratch k K] state) :
    Clean (registers.path k K)
        (Classical.run
          (unaryActionUnitary .inc
            (coefficientPrefixFirstLeaf registers k K mode target)
            (coefficientPrefixTree registers k K) registers.control
            (registers.path k K)) state) ∧
      Clean [registers.cellScratch k K]
        (Classical.run
          (unaryActionUnitary .inc
            (coefficientPrefixFirstLeaf registers k K mode target)
            (coefficientPrefixTree registers k K) registers.control
            (registers.path k K)) state) := by
  have hpreserved := coefficientPrefixFirstTraversal_preservesDecoderCell
    registers mode target state hlayout hclean.1
  constructor
  · intro wire hwire
    rw [hpreserved wire (by
      exact List.mem_append.mpr (Or.inl (by simp [hwire])))]
    exact hclean.1 wire hwire
  · intro wire hwire
    have hwire : wire = registers.cellScratch k K := by simpa using hwire
    subst wire
    rw [hpreserved (registers.cellScratch k K) (by simp)]
    exact hclean.2 (registers.cellScratch k K) (by simp)

private theorem coefficientPrefixSign_preservesCleanPathCell
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (signUpdate : Bool) (state : BasisState)
    (hlayout : CoefficientPrefixLayout registers k K)
    (hclean : Clean (registers.path k K) state ∧
      Clean [registers.cellScratch k K] state) :
    Clean (registers.path k K)
        (Classical.run
          (coefficientPrefixSignCircuit registers k K signUpdate) state) ∧
      Clean [registers.cellScratch k K]
        (Classical.run
          (coefficientPrefixSignCircuit registers k K signUpdate) state) := by
  constructor
  · exact coefficientPrefixSign_preservesPath registers signUpdate state hlayout hclean.1
  · cases signUpdate with
    | false => simpa [coefficientPrefixSignCircuit] using hclean.2
    | true =>
        apply clean_run_singleCX_of_target_not_mem
          (control := registers.carry k K) (target := registers.sign)
          (wires := [registers.cellScratch k K]) (state := state) hclean.2
        intro hsign
        have hsign : registers.sign = registers.cellScratch k K := by simpa using hsign
        apply (coefficientPrefix_fixed_not_mem_scratch registers hlayout).2
        rw [hsign]
        exact coefficientPrefix_cellScratch_mem_scratch registers hlayout

/-- The measurement-uncomputed prepared-boundary block coherently refines the literal source
unitary on every clean shared-scratch input. -/
theorem coefficientPrefixAdaptive_coherent
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    CoherentlyImplementsOn
      (coefficientPrefixAdaptive registers k K mode signUpdate target)
      (Quantum.run (coefficientPrefixUnitary registers k K mode signUpdate target))
      (CoefficientPrefixReady registers) := by
  let seed : Circuit := [.CX registers.control (registers.accumulator k K)]
  let firstCircuit := unaryActionUnitary .inc
    (coefficientPrefixFirstLeaf registers k K mode target)
    (coefficientPrefixTree registers k K) registers.control (registers.path k K)
  let firstAdaptive := unaryAdaptiveAction .inc
    (coefficientPrefixFirstLeafAdaptive registers k K mode target)
    (coefficientPrefixTree registers k K) registers.control (registers.path k K)
  let signCircuit := coefficientPrefixSignCircuit registers k K signUpdate
  let secondCircuit := unaryActionUnitary .dec
    (coefficientPrefixSecondLeaf registers k K mode target)
    (coefficientPrefixTree registers k K) registers.control (registers.path k K)
  let secondAdaptive := unaryAdaptiveAction .dec
    (coefficientPrefixSecondLeafAdaptive registers k K mode target)
    (coefficientPrefixTree registers k K) registers.control (registers.path k K)
  let Valid := fun state ↦ Clean (registers.path k K) state ∧
    Clean [registers.cellScratch k K] state
  have hseed : CoherentlyImplementsOn
      (.unitary seed .done) (Quantum.run seed) (CoefficientPrefixReady registers) :=
    CoherentlyImplementsOn.unitary seed (CoefficientPrefixReady registers)
  have hfirst : CoherentlyImplementsOn firstAdaptive
      (Quantum.run firstCircuit) Valid := by
    simpa only [firstAdaptive, firstCircuit, Valid] using
      coefficientPrefixFirstTraversalAdaptive_coherent registers mode target hlayout
  have hsign : CoherentlyImplementsOn (.unitary signCircuit .done)
      (Quantum.run signCircuit) Valid :=
    CoherentlyImplementsOn.unitary signCircuit Valid
  have hsecond : CoherentlyImplementsOn secondAdaptive
      (Quantum.run secondCircuit) Valid := by
    simpa only [secondAdaptive, secondCircuit, Valid] using
      coefficientPrefixSecondTraversalAdaptive_coherent registers mode target hlayout
  have hfinal : CoherentlyImplementsOn (.unitary seed .done)
      (Quantum.run seed) (fun _ ↦ True) :=
    CoherentlyImplementsOn.unitary seed (fun _ ↦ True)
  have hseedValid : ∀ state, CoefficientPrefixReady registers state →
      Valid (Classical.run seed state) := by
    intro state hready
    constructor
    · exact clean_run_singleCX_of_target_not_mem registers.control
        (registers.accumulator k K) (registers.path k K) state
        (coefficientPrefix_cleanPath_of_ready registers k K state hready)
        (coefficientPrefix_path_not_accumulator registers hlayout)
    · have hcell : Clean [registers.cellScratch k K] state := by
        intro wire hwire
        have hwire : wire = registers.cellScratch k K := by simpa using hwire
        subst wire
        exact hready (registers.cellScratch k K)
          (coefficientPrefix_cellScratch_mem_scratch registers hlayout)
      exact clean_run_singleCX_of_target_not_mem
        (control := registers.control) (target := registers.accumulator k K)
        (wires := [registers.cellScratch k K]) (state := state) hcell
        (by simpa using coefficientPrefix_accumulator_ne_cellScratch registers hlayout)
  have hfirstValid : ∀ state, Valid state →
      Valid (Classical.run firstCircuit state) := by
    intro state hvalid
    simpa only [Valid, firstCircuit] using
      coefficientPrefixFirstTraversal_preservesCleanPathCell registers mode target
        state hlayout hvalid
  have hsignValid : ∀ state, Valid state →
      Valid (Classical.run signCircuit state) := by
    intro state hvalid
    simpa only [Valid, signCircuit] using
      coefficientPrefixSign_preservesCleanPathCell registers signUpdate state hlayout hvalid
  have hsecondFinal := coefficientPrefix_coherent_seq_circuits hsecond hfinal
    (by simpa only [secondCircuit] using
      coefficientPrefixSecondTraversal_HPFree registers k K mode target)
    (fun _ _ ↦ trivial)
  have hsignTail := coefficientPrefix_coherent_seq_circuits hsign hsecondFinal
    (by simpa only [signCircuit] using
      coefficientPrefixSign_HPFree registers k K signUpdate)
    hsignValid
  have hfirstTail := coefficientPrefix_coherent_seq_circuits hfirst hsignTail
    (by simpa only [firstCircuit] using
      coefficientPrefixFirstTraversal_HPFree registers k K mode target)
    hfirstValid
  have hall := coefficientPrefix_coherent_seq_circuits hseed hfirstTail
    (by simp [seed]) hseedValid
  simpa only [coefficientPrefixAdaptive, coefficientPrefixUnitary, seed,
    firstCircuit, firstAdaptive, signCircuit, secondCircuit, secondAdaptive,
    List.append_assoc] using hall

/-! ## Paired source cleanup -/

private theorem coefficientPrefix_targetAt_injective
    (registers : CoefficientPrefixRegisters) {k K left right : Nat}
    (target : CoefficientTarget) (hlayout : CoefficientPrefixLayout registers k K)
    (hleft : left ∈ (coefficientPrefixTree registers k K).labels)
    (hright : right ∈ (coefficientPrefixTree registers k K).labels)
    (hequality : registers.targetAt target k left =
      registers.targetAt target k right) :
    left = right := by
  have hleftBounds := coefficientPrefix_label_bounds registers hlayout hleft
  have hrightBounds := coefficientPrefix_label_bounds registers hlayout hright
  cases target with
  | work1 =>
      have hlength : registers.work1.length = K - k + 1 := hlayout.work1_length
      have hleftIndex : registers.laneAt k left < registers.work1.length := by
        rw [hlength]
        simp only [CoefficientPrefixRegisters.laneAt]
        omega
      have hrightIndex : registers.laneAt k right < registers.work1.length := by
        rw [hlength]
        simp only [CoefficientPrefixRegisters.laneAt]
        omega
      simp only [CoefficientPrefixRegisters.targetAt,
        CoefficientPrefixRegisters.work1At] at hequality
      rw [List.getD_eq_getElem registers.work1 _ hleftIndex,
        List.getD_eq_getElem registers.work1 _ hrightIndex] at hequality
      have hindices :=
        (coefficientPrefix_physical_parts registers hlayout).2.1.getElem_inj_iff.mp
          hequality
      simp only [CoefficientPrefixRegisters.laneAt] at hindices
      omega
  | work2 =>
      have hleftIndex : registers.laneAt k left < registers.work2.length := by
        rw [hlayout.work2_length]
        simp only [CoefficientPrefixRegisters.laneAt]
        omega
      have hrightIndex : registers.laneAt k right < registers.work2.length := by
        rw [hlayout.work2_length]
        simp only [CoefficientPrefixRegisters.laneAt]
        omega
      simp only [CoefficientPrefixRegisters.targetAt,
        CoefficientPrefixRegisters.work2At] at hequality
      rw [List.getD_eq_getElem registers.work2 _ hleftIndex,
        List.getD_eq_getElem registers.work2 _ hrightIndex] at hequality
      have hindices :=
        (coefficientPrefix_physical_parts registers hlayout).2.2.1.getElem_inj_iff.mp
          hequality
      simp only [CoefficientPrefixRegisters.laneAt] at hindices
      omega

private theorem coefficientPrefix_targetAt_not_decoder
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (target : CoefficientTarget) (hlayout : CoefficientPrefixLayout registers k K) :
    registers.targetAt target k label ∉
      registers.control ::
        (coefficientPrefixTree registers k K).indexWires.dedup ++
          registers.path k K := by
  have houtside := coefficientPrefix_decoder_disjoint_leafRoles
    (label := label) registers target hlayout
  rw [List.disjoint_left] at houtside
  intro htarget
  exact houtside htarget (by simp)

private theorem coefficientPrefix_targetAt_not_scratch
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (target : CoefficientTarget) (hlayout : CoefficientPrefixLayout registers k K) :
    registers.targetAt target k label ∉ registers.scratch := by
  intro hscratch
  cases target with
  | work1 =>
      exact (coefficientPrefix_physical_parts registers hlayout).2.2.2.2.2.2.1
        (registers.targetAt .work1 k label)
        (by simpa only [CoefficientPrefixRegisters.targetAt] using
          coefficientPrefix_work1At_mem_any registers hlayout label)
        (registers.targetAt .work1 k label)
        (by simp [hscratch]) rfl
  | work2 =>
      exact (coefficientPrefix_physical_parts registers hlayout).2.2.2.2.2.2.2.1
        (registers.targetAt .work2 k label)
        (by simpa only [CoefficientPrefixRegisters.targetAt] using
          coefficientPrefix_work2At_mem_any registers hlayout label)
        (registers.targetAt .work2 k label)
        (by simp [hscratch]) rfl

private theorem coefficientPrefix_targetAt_ne_addendAt
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (target : CoefficientTarget) (leftLabel rightLabel : Nat)
    (hlayout : CoefficientPrefixLayout registers k K) :
    registers.targetAt target k leftLabel ≠
      registers.addendAt target k rightLabel := by
  cases target with
  | work1 =>
      exact (coefficientPrefix_physical_parts registers hlayout).2.2.2.2.2.2.1
        (registers.targetAt .work1 k leftLabel)
        (by simpa only [CoefficientPrefixRegisters.targetAt] using
          coefficientPrefix_work1At_mem_any registers hlayout leftLabel)
        (registers.addendAt .work1 k rightLabel)
        (by simp only [CoefficientPrefixRegisters.addendAt]
            exact List.mem_append_left _
              (coefficientPrefix_work2At_mem_any registers hlayout rightLabel))
  | work2 =>
      exact Ne.symm
        ((coefficientPrefix_physical_parts registers hlayout).2.2.2.2.2.2.1
          (registers.addendAt .work2 k rightLabel)
          (by simpa only [CoefficientPrefixRegisters.addendAt] using
            coefficientPrefix_work1At_mem_any registers hlayout rightLabel)
          (registers.targetAt .work2 k leftLabel)
          (by simp only [CoefficientPrefixRegisters.targetAt]
              exact List.mem_append_left _
                (coefficientPrefix_work2At_mem_any registers hlayout leftLabel)))

private theorem coefficientPrefixFirstLeaf_usesOnly
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) :
    PaperCircuitUsesOnly
      [equalityControl, registers.accumulator k K,
        registers.targetAt target k label, registers.addendAt target k label,
        registers.carry k K, registers.cellScratch k K]
      (coefficientPrefixFirstLeaf registers k K mode target label equalityControl) := by
  rw [coefficientPrefixFirstLeaf]
  apply PaperCircuitUsesOnly.append
  · apply (rippleFirstCell_usesOnly mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K)).mono
    intro wire hwire
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire ⊢
    aesop
  · simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]

private theorem coefficientPrefixSecondLeaf_usesOnly
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (equalityControl : Wire) :
    PaperCircuitUsesOnly
      [equalityControl, registers.accumulator k K,
        registers.targetAt target k label, registers.addendAt target k label,
        registers.carry k K, registers.cellScratch k K]
      (coefficientPrefixSecondLeaf registers k K mode target label equalityControl) := by
  rw [coefficientPrefixSecondLeaf]
  apply PaperCircuitUsesOnly.append
  · simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]
  · apply (rippleSecondCell_usesOnly mode (registers.accumulator k K)
      (registers.targetAt target k label) (registers.addendAt target k label)
      (registers.carry k K) (registers.cellScratch k K)).mono
    intro wire hwire
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire ⊢
    aesop

private theorem coefficientPrefixUnaryActionUnitary_usesOnly_of
    (order : UnaryOrder) (leafAction : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire) (path support : List Wire)
    (hcontrol : control ∈ support)
    (hindices : ∀ wire, wire ∈ tree.indexWires → wire ∈ support)
    (hpath : ∀ wire, wire ∈ path → wire ∈ support)
    (hleaf : ∀ label, label ∈ tree.labels → ∀ dynamic,
      dynamic ∈ support → PaperCircuitUsesOnly support (leafAction label dynamic)) :
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
            exact hleaf label (by simp [UnaryActionTree.labels, hlabel])
              dynamic hdynamic
          have honeLeaf : ∀ label, label ∈ one.labels → ∀ dynamic,
              dynamic ∈ support →
                PaperCircuitUsesOnly support (leafAction label dynamic) := by
            intro label hlabel dynamic hdynamic
            exact hleaf label (by simp [UnaryActionTree.labels, hlabel])
              dynamic hdynamic
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
          have hempty : PaperCircuitUsesOnly support ([] : Circuit) := by
            simp [PaperCircuitUsesOnly]
          cases order with
          | inc =>
              rw [unaryActionUnitary]
              exact hcompute.append
                (((((hempty.append hzero).append htoggle).append hone).append
                  htoggle).append hcompute)
          | dec =>
              rw [unaryActionUnitary]
              exact hcompute.append
                (((((hempty.append htoggle).append hone).append htoggle).append
                  hzero).append hcompute)

/-- Every gate in the literal prepared-boundary block stays within its physical register record. -/
theorem coefficientPrefixUnitary_usesOnly
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    PaperCircuitUsesOnly registers.allWires
      (coefficientPrefixUnitary registers k K mode signUpdate target) := by
  have hcontrol : registers.control ∈ registers.allWires := by
    simp [CoefficientPrefixRegisters.allWires]
  have hsignWire : registers.sign ∈ registers.allWires := by
    simp [CoefficientPrefixRegisters.allWires]
  have hwork1 : ∀ wire, wire ∈ registers.work1 →
      wire ∈ registers.allWires := by
    intro wire hwire
    simp [CoefficientPrefixRegisters.allWires, hwire]
  have hwork2 : ∀ wire, wire ∈ registers.work2 →
      wire ∈ registers.allWires := by
    intro wire hwire
    simp [CoefficientPrefixRegisters.allWires, hwire]
  have hboundaryMem : ∀ wire, wire ∈ registers.boundary →
      wire ∈ registers.allWires := by
    intro wire hwire
    simp [CoefficientPrefixRegisters.allWires, hwire]
  have hscratch : ∀ wire, wire ∈ registers.scratch →
      wire ∈ registers.allWires := by
    intro wire hwire
    simp [CoefficientPrefixRegisters.allWires, hwire]
  have hcarry := hscratch (registers.carry k K)
    (coefficientPrefix_scratchAt_mem registers hlayout (by omega))
  have haccumulator := hscratch (registers.accumulator k K)
    (coefficientPrefix_scratchAt_mem registers hlayout (by omega))
  have hcell := hscratch (registers.cellScratch k K)
    (coefficientPrefix_scratchAt_mem registers hlayout (by omega))
  have htargetMem : ∀ label,
      registers.targetAt target k label ∈ registers.allWires := by
    intro label
    cases target with
    | work1 =>
        exact hwork1 _ (by
          simpa only [CoefficientPrefixRegisters.targetAt] using
            coefficientPrefix_work1At_mem_any registers hlayout label)
    | work2 =>
        exact hwork2 _ (by
          simpa only [CoefficientPrefixRegisters.targetAt] using
            coefficientPrefix_work2At_mem_any registers hlayout label)
  have haddendMem : ∀ label,
      registers.addendAt target k label ∈ registers.allWires := by
    intro label
    cases target with
    | work1 =>
        exact hwork2 _ (by
          simpa only [CoefficientPrefixRegisters.addendAt] using
            coefficientPrefix_work2At_mem_any registers hlayout label)
    | work2 =>
        exact hwork1 _ (by
          simpa only [CoefficientPrefixRegisters.addendAt] using
            coefficientPrefix_work1At_mem_any registers hlayout label)
  have hseed : PaperCircuitUsesOnly registers.allWires
      ([.CX registers.control (registers.accumulator k K)] : Circuit) := by
    intro gate hgate
    simp only [List.mem_singleton] at hgate
    subst gate
    intro wire hwire
    simp only [gateWires, List.mem_cons, List.not_mem_nil, or_false] at hwire
    rcases hwire with rfl | rfl
    · exact hcontrol
    · exact haccumulator
  have hrole : ∀ label dynamic, dynamic ∈ registers.allWires →
      ∀ wire, wire ∈
        [dynamic, registers.accumulator k K,
          registers.targetAt target k label,
          registers.addendAt target k label, registers.carry k K,
          registers.cellScratch k K] → wire ∈ registers.allWires := by
    intro label dynamic hdynamic wire hwire
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
    rcases hwire with rfl | rfl | htarget | haddend | rfl | rfl
    · exact hdynamic
    · exact haccumulator
    · subst wire
      exact htargetMem label
    · subst wire
      exact haddendMem label
    · exact hcarry
    · exact hcell
  have hindices : ∀ wire,
      wire ∈ (coefficientPrefixTree registers k K).indexWires →
        wire ∈ registers.allWires := by
    intro wire hwire
    have hboundary := quotientSwapTree_indexWires_mem_lengthQ
      (registers.routing k K) hlayout.k_le_K
        (by simpa [CoefficientPrefixRegisters.routing] using hlayout.index_width)
        wire (by simpa using hwire)
    exact hboundaryMem wire (by
      simpa only [CoefficientPrefixRegisters.routing] using hboundary)
  have hpath : ∀ wire, wire ∈ registers.path k K →
      wire ∈ registers.allWires := by
    intro wire hwire
    exact hscratch wire
      (coefficientPrefix_path_mem_scratch registers k K wire hwire)
  have hfirst : PaperCircuitUsesOnly registers.allWires
      (unaryActionUnitary .inc
        (coefficientPrefixFirstLeaf registers k K mode target)
        (coefficientPrefixTree registers k K) registers.control
        (registers.path k K)) := by
    apply coefficientPrefixUnaryActionUnitary_usesOnly_of
      .inc (coefficientPrefixFirstLeaf registers k K mode target)
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) registers.allWires hcontrol hindices hpath
    intro label hlabel dynamic hdynamic
    exact (coefficientPrefixFirstLeaf_usesOnly registers k K mode target
      label dynamic).mono (hrole label dynamic hdynamic)
  have hsecond : PaperCircuitUsesOnly registers.allWires
      (unaryActionUnitary .dec
        (coefficientPrefixSecondLeaf registers k K mode target)
        (coefficientPrefixTree registers k K) registers.control
        (registers.path k K)) := by
    apply coefficientPrefixUnaryActionUnitary_usesOnly_of
      .dec (coefficientPrefixSecondLeaf registers k K mode target)
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) registers.allWires hcontrol hindices hpath
    intro label hlabel dynamic hdynamic
    exact (coefficientPrefixSecondLeaf_usesOnly registers k K mode target
      label dynamic).mono (hrole label dynamic hdynamic)
  have hsign : PaperCircuitUsesOnly registers.allWires
      (coefficientPrefixSignCircuit registers k K signUpdate) := by
    cases signUpdate with
    | false => simp [coefficientPrefixSignCircuit, PaperCircuitUsesOnly]
    | true =>
        simp only [coefficientPrefixSignCircuit, if_true]
        intro gate hgate
        simp only [List.mem_singleton] at hgate
        subst gate
        intro wire hwire
        simp only [gateWires, List.mem_cons, List.not_mem_nil, or_false] at hwire
        rcases hwire with rfl | rfl
        · exact hcarry
        · exact hsignWire
  rw [coefficientPrefixUnitary]
  exact (((hseed.append hfirst).append hsign).append hsecond).append hseed

/-- Whole-state locality outside the declared physical register union. -/
theorem coefficientPrefixUnitary_preservesOutside
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K)
    {wire : Wire} (hwire : wire ∉ registers.allWires) :
    Classical.run
        (coefficientPrefixUnitary registers k K mode signUpdate target) state wire =
      state wire :=
  (coefficientPrefixUnitary_usesOnly registers mode signUpdate target hlayout)
    |>.preservesOutside state hwire

private theorem coefficientPrefix_rippleCell_pair_preserves
    (mode : RippleMode) (control target addend carry scratch : Wire)
    (state : BasisState)
    (hlayout : [control, target, addend, carry, scratch].Nodup) :
    let after := Classical.run
      (rippleSecondCell mode control target addend carry scratch)
      (Classical.run
        (rippleFirstCell mode control target addend carry scratch) state)
    after control = state control ∧ after addend = state addend ∧
      after carry = state carry ∧ after scratch = state scratch := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hlayout
  rcases hlayout with
    ⟨⟨hcontrolTarget, hcontrolAddend, hcontrolCarry, hcontrolScratch⟩,
      ⟨⟨htargetAddend, htargetCarry, htargetScratch⟩,
        ⟨⟨haddendCarry, haddendScratch⟩, ⟨hcarryScratch, _⟩⟩⟩⟩
  cases mode <;> cases hc : state control <;> cases ht : state target <;>
    cases ha : state addend <;> cases hcarry : state carry <;>
    cases hscratch : state scratch <;>
    simp [rippleFirstCell, rippleSecondCell, controlledMaj, controlledUma,
      controlledUmaInv, controlledMajInv, cleanC3X, Classical.run,
      Classical.applyGate, upd, hcontrolTarget, hcontrolAddend,
      hcontrolCarry, hcontrolScratch, htargetAddend, htargetCarry,
      htargetScratch, haddendCarry, haddendScratch, hcarryScratch,
      Ne.symm htargetAddend, Ne.symm htargetCarry,
      Ne.symm htargetScratch, Ne.symm haddendCarry,
      Ne.symm haddendScratch, Ne.symm hcarryScratch,
      hc, ht, ha, hcarry, hscratch]

private theorem coefficientPrefixLeaf_pair_preservesOutsideTarget
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (equalityControl : Wire)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K)
    (hcontrol : equalityControl ∈ registers.control ::
      (coefficientPrefixTree registers k K).indexWires.dedup ++
        registers.path k K) :
    AgreesOutside [registers.targetAt target k label]
      (Classical.run
        (coefficientPrefixFirstLeaf registers k K mode target label equalityControl ++
          coefficientPrefixSecondLeaf registers k K mode target label equalityControl)
        state)
      state := by
  let firstCell := rippleFirstCell mode (registers.accumulator k K)
    (registers.targetAt target k label) (registers.addendAt target k label)
    (registers.carry k K) (registers.cellScratch k K)
  let secondCell := rippleSecondCell mode (registers.accumulator k K)
    (registers.targetAt target k label) (registers.addendAt target k label)
    (registers.carry k K) (registers.cellScratch k K)
  let toggle : Circuit := [.CX equalityControl (registers.accumulator k K)]
  have hcontrolAcc : equalityControl ≠ registers.accumulator k K := by
    have houtside := coefficientPrefix_decoder_disjoint_leafRoles
      (label := label) registers target hlayout
    rw [List.disjoint_left] at houtside
    intro equality
    exact houtside hcontrol (by simp [equality])
  have htoggleWF : CircuitWellFormed toggle := by
    simp [toggle, CircuitWellFormed, Gate.WellFormed, hcontrolAcc]
  have htoggleAdjoint : toggle.adjoint = toggle := by
    simp [toggle, Circuit.adjoint]
  have htoggleCancel : ∀ next,
      Classical.run toggle (Classical.run toggle next) = next := by
    intro next
    have hcancel := run_adjoint_run_classical toggle htoggleWF next
    rwa [htoggleAdjoint] at hcancel
  have hactual : Classical.run
      (coefficientPrefixFirstLeaf registers k K mode target label equalityControl ++
        coefficientPrefixSecondLeaf registers k K mode target label equalityControl)
      state = Classical.run secondCell (Classical.run firstCell state) := by
    simp only [coefficientPrefixFirstLeaf, coefficientPrefixSecondLeaf,
      Classical.run_append, firstCell, secondCell]
    rw [htoggleCancel]
  have hpair := coefficientPrefix_rippleCell_pair_preserves mode
    (registers.accumulator k K) (registers.targetAt target k label)
    (registers.addendAt target k label) (registers.carry k K)
    (registers.cellScratch k K) state
    (coefficientPrefix_cellLayout (label := label) registers target hlayout)
  intro wire hwire
  simp only [List.mem_singleton] at hwire
  rw [hactual]
  by_cases haccumulator : wire = registers.accumulator k K
  · subst wire
    exact hpair.1
  · by_cases haddend : wire = registers.addendAt target k label
    · subst wire
      exact hpair.2.1
    · by_cases hcarry : wire = registers.carry k K
      · subst wire
        exact hpair.2.2.1
      · by_cases hscratch : wire = registers.cellScratch k K
        · subst wire
          exact hpair.2.2.2
        · simpa only [firstCell, secondCell, Classical.run_append] using
            (PaperCircuitUsesOnly.append
            (rippleFirstCell_usesOnly mode (registers.accumulator k K)
              (registers.targetAt target k label) (registers.addendAt target k label)
              (registers.carry k K) (registers.cellScratch k K))
            (rippleSecondCell_usesOnly mode (registers.accumulator k K)
              (registers.targetAt target k label) (registers.addendAt target k label)
              (registers.carry k K) (registers.cellScratch k K))).preservesOutside
            (wire := wire) state
            (by simp [hwire, haccumulator, haddend, hcarry, hscratch])

private theorem coefficientPrefix_avoid_append
    {protectedWires : List Wire} {first second : Circuit}
    (hfirst : PaperCircuitAvoids protectedWires first)
    (hsecond : PaperCircuitAvoids protectedWires second) :
    PaperCircuitAvoids protectedWires (first ++ second) := by
  intro gate hgate wire hwire
  rcases List.mem_append.mp hgate with hgate | hgate
  · exact hfirst gate hgate wire hwire
  · exact hsecond gate hgate wire hwire

private theorem coefficientPrefix_avoid_selfFrame
    {protectedWires : List Wire} {before middle : Circuit}
    (hbefore : PaperCircuitAvoids protectedWires before)
    (hmiddle : ∀ state, AgreesOutside protectedWires
      (Classical.run middle state) state)
    (hcancel : ∀ state,
      Classical.run before (Classical.run before state) = state) :
    ∀ state, AgreesOutside protectedWires
      (Classical.run (before ++ middle ++ before) state) state := by
  intro state wire hwire
  simp only [Classical.run_append]
  have htransport := hbefore.run_agreesOutside (hmiddle (Classical.run before state))
  rw [htransport wire hwire]
  exact congrFun (hcancel state) wire

private theorem coefficientPrefix_avoid_nest
    {innerWires outerWires : List Wire}
    {outerFirst inner outerSecond : Circuit}
    (hinner : ∀ state, AgreesOutside innerWires
      (Classical.run inner state) state)
    (houter : ∀ state, AgreesOutside outerWires
      (Classical.run (outerFirst ++ outerSecond) state) state)
    (hsecond : PaperCircuitAvoids innerWires outerSecond) :
    ∀ state, AgreesOutside (outerWires ++ innerWires)
      (Classical.run (outerFirst ++ inner ++ outerSecond) state) state := by
  intro state wire hwire
  simp only [List.mem_append, not_or] at hwire
  simp only [Classical.run_append]
  have htransport := hsecond.run_agreesOutside
    (hinner (Classical.run outerFirst state))
  rw [htransport wire hwire.2]
  simpa only [Classical.run_append] using houter state wire hwire.1

private theorem coefficientPrefix_zero_decoder_subset
    (indexBit control path : Wire) (zero one : UnaryActionTree)
    (rest : List Wire) :
    ∀ wire, wire ∈ path :: zero.indexWires.dedup ++ rest →
      wire ∈ control ::
        (UnaryActionTree.node indexBit zero one).indexWires.dedup ++
          (path :: rest) := by
  intro wire hwire
  rcases List.mem_cons.mp hwire with rfl | hwire
  · simp
  rcases List.mem_append.mp hwire with hwire | hwire
  · have hindex : wire ∈
        (UnaryActionTree.node indexBit zero one).indexWires.dedup := by
      apply List.mem_dedup.mpr
      simp [UnaryActionTree.indexWires, List.mem_dedup.mp hwire]
    simp [hindex]
  · simp [hwire]

private theorem coefficientPrefix_one_decoder_subset
    (indexBit control path : Wire) (zero one : UnaryActionTree)
    (rest : List Wire) :
    ∀ wire, wire ∈ path :: one.indexWires.dedup ++ rest →
      wire ∈ control ::
        (UnaryActionTree.node indexBit zero one).indexWires.dedup ++
          (path :: rest) := by
  intro wire hwire
  rcases List.mem_cons.mp hwire with rfl | hwire
  · simp
  rcases List.mem_append.mp hwire with hwire | hwire
  · have hindex : wire ∈
        (UnaryActionTree.node indexBit zero one).indexWires.dedup := by
      apply List.mem_dedup.mpr
      simp [UnaryActionTree.indexWires, List.mem_dedup.mp hwire]
    simp [hindex]
  · simp [hwire]

private theorem coefficientPrefix_unaryActionUnitary_avoids
    (order : UnaryOrder) (leafAction : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire)
    (ancillas protectedWires : List Wire)
    (hlayout : tree.Layout control ancillas)
    (hdecoder : ∀ wire,
      wire ∈ control :: tree.indexWires.dedup ++ ancillas →
        wire ∉ protectedWires)
    (hleaf : ∀ label, label ∈ tree.labels →
      ∀ child, child ∈ control :: tree.indexWires.dedup ++ ancillas →
        PaperCircuitAvoids protectedWires (leafAction label child)) :
    PaperCircuitAvoids protectedWires
      (unaryActionUnitary order leafAction tree control ancillas) := by
  induction hlayout with
  | leaf label control ancillas hlocal =>
      exact hleaf label (by simp [UnaryActionTree.labels]) control (by simp)
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      have hzeroSubset := coefficientPrefix_zero_decoder_subset
        indexBit control path zero one rest
      have honeSubset := coefficientPrefix_one_decoder_subset
        indexBit control path zero one rest
      have hzero := ihZero
        (fun wire hwire ↦ hdecoder wire (hzeroSubset wire hwire))
        (fun label hlabel child hchild ↦
          hleaf label (by simp [UnaryActionTree.labels, hlabel]) child
            (hzeroSubset child hchild))
      have hone := ihOne
        (fun wire hwire ↦ hdecoder wire (honeSubset wire hwire))
        (fun label hlabel child hchild ↦
          hleaf label (by simp [UnaryActionTree.labels, hlabel]) child
            (honeSubset child hchild))
      have hcontrol := hdecoder control (by simp)
      have hindex := hdecoder indexBit (by
        simp [UnaryActionTree.indexWires])
      have hpath := hdecoder path (by simp)
      have hcompute : PaperCircuitAvoids protectedWires
          (computeZeroAnd control indexBit path) := by
        simp [PaperCircuitAvoids, computeZeroAnd, gateWires,
          hcontrol, hindex, hpath]
      have htoggle : PaperCircuitAvoids protectedWires
          ([.CX control path] : Circuit) := by
        simp [PaperCircuitAvoids, gateWires, hcontrol, hpath]
      cases order with
      | inc =>
          simp only [unaryActionUnitary]
          repeat' apply coefficientPrefix_avoid_append
          all_goals assumption
      | dec =>
          simp only [unaryActionUnitary]
          repeat' apply coefficientPrefix_avoid_append
          all_goals assumption

private theorem coefficientPrefix_unaryActionPair_preservesOutsideTargets
    (firstLeaf secondLeaf : Nat → Wire → Circuit)
    (targetAt : Nat → Wire)
    (tree : UnaryActionTree) (control : Wire) (ancillas : List Wire)
    (hlayout : tree.Layout control ancillas)
    (hlabels : tree.labels.Nodup)
    (htargetDecoder : ∀ label, label ∈ tree.labels →
      targetAt label ∉ control :: tree.indexWires.dedup ++ ancillas)
    (hpair : ∀ label, label ∈ tree.labels →
      ∀ child, child ∈ control :: tree.indexWires.dedup ++ ancillas →
      ∀ state, AgreesOutside [targetAt label]
        (Classical.run (firstLeaf label child ++ secondLeaf label child) state)
        state)
    (hsecondCross : ∀ label, label ∈ tree.labels →
      ∀ child, child ∈ control :: tree.indexWires.dedup ++ ancillas →
      ∀ other, other ∈ tree.labels → other ≠ label →
        PaperCircuitAvoids [targetAt other] (secondLeaf label child)) :
    ∀ state, AgreesOutside (tree.labels.map targetAt)
      (Classical.run
        (unaryActionUnitary .inc firstLeaf tree control ancillas ++
          unaryActionUnitary .dec secondLeaf tree control ancillas) state)
      state := by
  induction hlayout with
  | leaf label control ancillas hlocal =>
      intro state
      simpa [unaryActionUnitary, UnaryActionTree.labels] using
        hpair label (by simp [UnaryActionTree.labels]) control (by simp) state
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      intro state
      have hzeroSubset := coefficientPrefix_zero_decoder_subset
        indexBit control path zero one rest
      have honeSubset := coefficientPrefix_one_decoder_subset
        indexBit control path zero one rest
      have hparts := List.nodup_append.mp
        (by simpa [UnaryActionTree.labels] using hlabels)
      have hzeroNodup : zero.labels.Nodup := hparts.1
      have honeNodup : one.labels.Nodup := hparts.2.1
      have hlabelCross := hparts.2.2
      have hlabelDisjoint : List.Disjoint zero.labels one.labels := by
        rw [List.disjoint_left]
        intro label hzeroLabel honeLabel
        exact hlabelCross label hzeroLabel label honeLabel rfl
      have hzeroTargetDecoder : ∀ label, label ∈ zero.labels →
          targetAt label ∉ path :: zero.indexWires.dedup ++ rest := by
        intro label hlabel hwire
        exact htargetDecoder label (by
          simp [UnaryActionTree.labels, hlabel]) (hzeroSubset _ hwire)
      have honeTargetDecoder : ∀ label, label ∈ one.labels →
          targetAt label ∉ path :: one.indexWires.dedup ++ rest := by
        intro label hlabel hwire
        exact htargetDecoder label (by
          simp [UnaryActionTree.labels, hlabel]) (honeSubset _ hwire)
      have hzeroPair := ihZero hzeroNodup hzeroTargetDecoder
        (fun label hlabel child hchild next ↦
          hpair label (by simp [UnaryActionTree.labels, hlabel]) child
            (hzeroSubset child hchild) next)
        (fun label hlabel child hchild other hother hne ↦
          hsecondCross label (by simp [UnaryActionTree.labels, hlabel]) child
            (hzeroSubset child hchild) other
            (by simp [UnaryActionTree.labels, hother]) hne)
      have honePair := ihOne honeNodup honeTargetDecoder
        (fun label hlabel child hchild next ↦
          hpair label (by simp [UnaryActionTree.labels, hlabel]) child
            (honeSubset child hchild) next)
        (fun label hlabel child hchild other hother hne ↦
          hsecondCross label (by simp [UnaryActionTree.labels, hlabel]) child
            (honeSubset child hchild) other
            (by simp [UnaryActionTree.labels, hother]) hne)
      let zeroTargets := zero.labels.map targetAt
      let oneTargets := one.labels.map targetAt
      let allTargets := zeroTargets ++ oneTargets
      let compute := computeZeroAnd control indexBit path
      let toggle : Circuit := [.CX control path]
      let firstZero := unaryActionUnitary .inc firstLeaf zero path rest
      let firstOne := unaryActionUnitary .inc firstLeaf one path rest
      let secondZero := unaryActionUnitary .dec secondLeaf zero path rest
      let secondOne := unaryActionUnitary .dec secondLeaf one path rest
      have hdecoderAvoid : ∀ wire,
          wire ∈ control ::
              (UnaryActionTree.node indexBit zero one).indexWires.dedup ++
                (path :: rest) →
            wire ∉ allTargets := by
        intro wire hwire htarget
        simp only [allTargets, zeroTargets, oneTargets, List.mem_append,
          List.mem_map] at htarget
        rcases htarget with ⟨label, hlabel, rfl⟩ | ⟨label, hlabel, rfl⟩
        · exact htargetDecoder label (by
            simp [UnaryActionTree.labels, hlabel]) hwire
        · exact htargetDecoder label (by
            simp [UnaryActionTree.labels, hlabel]) hwire
      have hcomputeAvoids : PaperCircuitAvoids allTargets compute := by
        simp [PaperCircuitAvoids, compute, computeZeroAnd, gateWires,
          hdecoderAvoid control (by simp),
          hdecoderAvoid indexBit (by simp [UnaryActionTree.indexWires]),
          hdecoderAvoid path (by simp)]
      have htoggleAvoids : PaperCircuitAvoids allTargets toggle := by
        simp [PaperCircuitAvoids, toggle, gateWires,
          hdecoderAvoid control (by simp), hdecoderAvoid path (by simp)]
      have hsecondZeroAvoidsOne : PaperCircuitAvoids oneTargets secondZero := by
        apply coefficientPrefix_unaryActionUnitary_avoids .dec secondLeaf zero
          path rest oneTargets hzero
        · intro wire hwire hprotected
          have hwireFull := hzeroSubset wire hwire
          simp only [oneTargets, List.mem_map] at hprotected
          obtain ⟨label, hlabel, rfl⟩ := hprotected
          exact htargetDecoder label (by
            simp [UnaryActionTree.labels, hlabel]) hwireFull
        · intro label hlabel child hchild gate hgate wire hwire hprotected
          simp only [oneTargets, List.mem_map] at hprotected
          obtain ⟨other, hother, rfl⟩ := hprotected
          have hne : other ≠ label := by
            intro equality
            subst other
            exact hlabelDisjoint hlabel hother
          exact hsecondCross label (by
              simp [UnaryActionTree.labels, hlabel]) child
            (hzeroSubset child hchild) other
            (by simp [UnaryActionTree.labels, hother]) hne gate hgate
              (targetAt other) hwire (by simp)
      have hnodeParts : control ≠ indexBit ∧ control ≠ path ∧
          indexBit ≠ path := by
        have htail := (List.nodup_cons.mp hlocal).2
        obtain ⟨hindices, hpaths, hcross⟩ := List.nodup_append.mp htail
        have hcontrolAll := (List.nodup_cons.mp hlocal).1
        have hindexMem : indexBit ∈
            (UnaryActionTree.node indexBit zero one).indexWires.dedup := by
          simp [UnaryActionTree.indexWires]
        exact ⟨
          (fun equality ↦ hcontrolAll (by
            rw [equality]
            exact List.mem_append_left _ hindexMem)),
          (fun equality ↦ hcontrolAll (by
            rw [equality]
            exact List.mem_append_right _ (by simp))),
          hcross indexBit hindexMem path (by simp)⟩
      have hcomputeWF : CircuitWellFormed compute := by
        exact computeZeroAnd_wellFormed control indexBit path
          hnodeParts.1 hnodeParts.2.1 hnodeParts.2.2
      have htoggleWF : CircuitWellFormed toggle := by
        simp [toggle, CircuitWellFormed, Gate.WellFormed, hnodeParts.2.1]
      have hcomputeAdjoint : compute.adjoint = compute := by
        simp [compute, computeZeroAnd, Circuit.adjoint]
      have htoggleAdjoint : toggle.adjoint = toggle := by
        simp [toggle, Circuit.adjoint]
      have hcomputeCancel : ∀ next,
          Classical.run compute (Classical.run compute next) = next := by
        intro next
        have hcancel := run_adjoint_run_classical compute hcomputeWF next
        rwa [hcomputeAdjoint] at hcancel
      have htoggleCancel : ∀ next,
          Classical.run toggle (Classical.run toggle next) = next := by
        intro next
        have hcancel := run_adjoint_run_classical toggle htoggleWF next
        rwa [htoggleAdjoint] at hcancel
      have hzeroFrame : ∀ next, AgreesOutside zeroTargets
          (Classical.run (firstZero ++ secondZero) next) next := by
        simpa [firstZero, secondZero, zeroTargets] using hzeroPair
      have honeFrame : ∀ next, AgreesOutside oneTargets
          (Classical.run (firstOne ++ secondOne) next) next := by
        simpa [firstOne, secondOne, oneTargets] using honePair
      have honeWrapped : ∀ next, AgreesOutside oneTargets
          (Classical.run (toggle ++ (firstOne ++ secondOne) ++ toggle) next)
            next :=
        coefficientPrefix_avoid_selfFrame
          (by
            intro gate hgate wire hwire hprotected
            exact htoggleAvoids gate hgate wire hwire (by
              simp only [allTargets, List.mem_append]
              exact Or.inr hprotected))
          honeFrame htoggleCancel
      have hmiddle : ∀ next, AgreesOutside allTargets
          (Classical.run
            (firstZero ++
              (toggle ++ (firstOne ++ secondOne) ++ toggle) ++ secondZero)
            next) next := by
        simpa [allTargets] using coefficientPrefix_avoid_nest
          honeWrapped hzeroFrame hsecondZeroAvoidsOne
      have hwrapped : ∀ next, AgreesOutside allTargets
          (Classical.run
            (compute ++
              (firstZero ++
                (toggle ++ (firstOne ++ secondOne) ++ toggle) ++ secondZero) ++
              compute) next) next :=
        coefficientPrefix_avoid_selfFrame hcomputeAvoids hmiddle hcomputeCancel
      have hfirstShape :
          unaryActionUnitary .inc firstLeaf
              (.node indexBit zero one) control (path :: rest) =
            compute ++ firstZero ++ toggle ++ firstOne ++ toggle ++ compute := by
        rfl
      have hsecondShape :
          unaryActionUnitary .dec secondLeaf
              (.node indexBit zero one) control (path :: rest) =
            compute ++ toggle ++ secondOne ++ toggle ++ secondZero ++ compute := by
        rfl
      have hcollapse : Classical.run
          (unaryActionUnitary .inc firstLeaf
                (.node indexBit zero one) control (path :: rest) ++
            unaryActionUnitary .dec secondLeaf
                (.node indexBit zero one) control (path :: rest)) state =
          Classical.run
            (compute ++
              (firstZero ++
                (toggle ++ (firstOne ++ secondOne) ++ toggle) ++ secondZero) ++
              compute) state := by
        rw [hfirstShape, hsecondShape]
        simp only [Classical.run_append]
        rw [hcomputeCancel, htoggleCancel]
      rw [hcollapse]
      simpa [allTargets, zeroTargets, oneTargets,
        UnaryActionTree.labels] using hwrapped state

private theorem coefficientPrefixTraversals_pair_preservesOutsideTargets
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (target : CoefficientTarget) (state : BasisState)
    (hlayout : CoefficientPrefixLayout registers k K) :
    AgreesOutside
      ((coefficientPrefixTree registers k K).labels.map
        (registers.targetAt target k))
      (Classical.run
        (unaryActionUnitary .inc
            (coefficientPrefixFirstLeaf registers k K mode target)
            (coefficientPrefixTree registers k K) registers.control
            (registers.path k K) ++
          unaryActionUnitary .dec
            (coefficientPrefixSecondLeaf registers k K mode target)
            (coefficientPrefixTree registers k K) registers.control
            (registers.path k K)) state)
      state := by
  have htree : (coefficientPrefixTree registers k K).Layout registers.control
      (registers.path k K) := by
    simpa [coefficientPrefixTree, CoefficientPrefixRegisters.path] using
      hlayout.tree
  apply coefficientPrefix_unaryActionPair_preservesOutsideTargets
    (coefficientPrefixFirstLeaf registers k K mode target)
    (coefficientPrefixSecondLeaf registers k K mode target)
    (registers.targetAt target k) (coefficientPrefixTree registers k K)
    registers.control (registers.path k K) htree
  · rw [coefficientPrefixTree_labels registers hlayout]
    exact Finset.sort_nodup _ _
  · intro label hlabel
    exact coefficientPrefix_targetAt_not_decoder registers target hlayout
  · intro label hlabel child hchild next
    exact coefficientPrefixLeaf_pair_preservesOutsideTarget registers mode target
      child next hlayout hchild
  · intro label hlabel child hchild other hother hne
    apply PaperCircuitAvoids.ofUsesOnly
      (coefficientPrefixSecondLeaf_usesOnly registers k K mode target label child)
    rw [List.disjoint_left]
    intro protectedWire hprotected hused
    have hprotected : protectedWire = registers.targetAt target k other := by
      simpa using hprotected
    subst protectedWire
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hused
    rcases hused with hchildEq | haccEq | htargetEq | haddendEq | hcarryEq | hcellEq
    · apply coefficientPrefix_targetAt_not_decoder registers target hlayout
      rw [hchildEq]
      exact hchild
    · apply coefficientPrefix_targetAt_not_scratch registers target hlayout
      rw [haccEq]
      exact coefficientPrefix_accumulator_mem_scratch registers hlayout
    · exact hne (coefficientPrefix_targetAt_injective registers target hlayout
        hother hlabel htargetEq)
    · exact coefficientPrefix_targetAt_ne_addendAt registers target other label
        hlayout haddendEq
    · apply coefficientPrefix_targetAt_not_scratch registers target hlayout
      rw [hcarryEq]
      exact coefficientPrefix_carry_mem_scratch registers hlayout
    · apply coefficientPrefix_targetAt_not_scratch registers target hlayout
      rw [hcellEq]
      exact coefficientPrefix_cellScratch_mem_scratch registers hlayout

private theorem coefficientPrefix_sign_not_decoder
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (hlayout : CoefficientPrefixLayout registers k K) :
    registers.sign ∉ registers.control ::
      (coefficientPrefixTree registers k K).indexWires.dedup ++
        registers.path k K := by
  intro hsign
  rcases coefficientPrefix_decoder_classify registers hlayout registers.sign hsign with
    hcontrol | hboundary | hpath
  · have hfixed := (coefficientPrefix_physical_parts registers hlayout).1
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false] at hfixed
    exact hfixed.1 hcontrol.symm
  · exact (coefficientPrefix_physical_parts registers hlayout).2.2.2.2.2.1
      registers.sign (by simp) registers.sign
      (by simp [hboundary]) rfl
  · exact (coefficientPrefix_fixed_not_mem_scratch registers hlayout).2
      (coefficientPrefix_path_mem_scratch registers k K registers.sign hpath)

private theorem coefficientPrefix_sign_not_secondLeafSupport
    (registers : CoefficientPrefixRegisters) {k K label : Nat}
    (target : CoefficientTarget) (child : Wire)
    (hlayout : CoefficientPrefixLayout registers k K)
    (hchild : child ∈ registers.control ::
      (coefficientPrefixTree registers k K).indexWires.dedup ++
        registers.path k K) :
    registers.sign ∉
      [child, registers.accumulator k K, registers.targetAt target k label,
        registers.addendAt target k label, registers.carry k K,
        registers.cellScratch k K] := by
  have hfixedCross :=
    (coefficientPrefix_physical_parts registers hlayout).2.2.2.2.2.1
  have hsignAcc : registers.sign ≠ registers.accumulator k K := by
    intro equality
    apply (coefficientPrefix_fixed_not_mem_scratch registers hlayout).2
    rw [equality]
    exact coefficientPrefix_accumulator_mem_scratch registers hlayout
  have hsignCarry : registers.sign ≠ registers.carry k K := by
    intro equality
    apply (coefficientPrefix_fixed_not_mem_scratch registers hlayout).2
    rw [equality]
    exact coefficientPrefix_carry_mem_scratch registers hlayout
  have hsignCell : registers.sign ≠ registers.cellScratch k K := by
    intro equality
    apply (coefficientPrefix_fixed_not_mem_scratch registers hlayout).2
    rw [equality]
    exact coefficientPrefix_cellScratch_mem_scratch registers hlayout
  have hsignTarget : registers.sign ≠ registers.targetAt target k label := by
    apply hfixedCross registers.sign (by simp)
    cases target with
    | work1 =>
        simp only [CoefficientPrefixRegisters.targetAt]
        exact List.mem_append_left _
          (coefficientPrefix_work1At_mem_any registers hlayout label)
    | work2 =>
        simp only [CoefficientPrefixRegisters.targetAt]
        exact List.mem_append_right registers.work1
          (List.mem_append_left _
            (coefficientPrefix_work2At_mem_any registers hlayout label))
  have hsignAddend : registers.sign ≠ registers.addendAt target k label := by
    apply hfixedCross registers.sign (by simp)
    cases target with
    | work1 =>
        simp only [CoefficientPrefixRegisters.addendAt]
        exact List.mem_append_right registers.work1
          (List.mem_append_left _
            (coefficientPrefix_work2At_mem_any registers hlayout label))
    | work2 =>
        simp only [CoefficientPrefixRegisters.addendAt]
        exact List.mem_append_left _
          (coefficientPrefix_work1At_mem_any registers hlayout label)
  have hsignChild : registers.sign ≠ child := by
    intro equality
    apply coefficientPrefix_sign_not_decoder registers hlayout
    rw [equality]
    exact hchild
  simp [hsignChild, hsignAcc, hsignTarget, hsignAddend, hsignCarry, hsignCell]

private theorem coefficientPrefixSecondTraversal_avoidsSign
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    PaperCircuitAvoids [registers.sign]
      (unaryActionUnitary .dec
        (coefficientPrefixSecondLeaf registers k K mode target)
        (coefficientPrefixTree registers k K) registers.control
        (registers.path k K)) := by
  have htree : (coefficientPrefixTree registers k K).Layout registers.control
      (registers.path k K) := by
    simpa [coefficientPrefixTree, CoefficientPrefixRegisters.path] using
      hlayout.tree
  apply coefficientPrefix_unaryActionUnitary_avoids
    (order := .dec)
    (leafAction := coefficientPrefixSecondLeaf registers k K mode target)
    (tree := coefficientPrefixTree registers k K)
    (control := registers.control)
    (ancillas := registers.path k K)
    (protectedWires := [registers.sign]) htree
  · intro wire hwire
    have hne : wire ≠ registers.sign := by
      intro equality
      apply coefficientPrefix_sign_not_decoder registers hlayout
      rw [← equality]
      exact hwire
    simpa using hne
  · intro label hlabel child hchild
    apply PaperCircuitAvoids.ofUsesOnly
      (coefficientPrefixSecondLeaf_usesOnly registers k K mode target label child)
    rw [List.disjoint_left]
    intro sign hsign hsupport
    have hsign : sign = registers.sign := by simpa using hsign
    subst sign
    exact coefficientPrefix_sign_not_secondLeafSupport registers target child
      hlayout hchild hsupport

private theorem coefficientPrefixSign_agreesOutsideSign
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (signUpdate : Bool) (state : BasisState) :
    AgreesOutside [registers.sign]
      (Classical.run (coefficientPrefixSignCircuit registers k K signUpdate) state)
      state := by
  intro wire hwire
  have hne : wire ≠ registers.sign := by simpa using hwire
  cases signUpdate <;>
    simp [coefficientPrefixSignCircuit, Classical.run,
      Classical.applyGate, upd, hne]

/-- The complete coherent prepared-boundary block restores the shared decoder, carry,
accumulator, and clean-v-chain scratch bank. -/
theorem coefficientPrefixUnitary_clean
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K)
    (hready : CoefficientPrefixReady registers state) :
    CoefficientPrefixReady registers
      (Classical.run
        (coefficientPrefixUnitary registers k K mode signUpdate target) state) := by
  let seed : Circuit := [.CX registers.control (registers.accumulator k K)]
  let firstCircuit := unaryActionUnitary .inc
    (coefficientPrefixFirstLeaf registers k K mode target)
    (coefficientPrefixTree registers k K) registers.control (registers.path k K)
  let signCircuit := coefficientPrefixSignCircuit registers k K signUpdate
  let secondCircuit := unaryActionUnitary .dec
    (coefficientPrefixSecondLeaf registers k K mode target)
    (coefficientPrefixTree registers k K) registers.control (registers.path k K)
  let targets := (coefficientPrefixTree registers k K).labels.map
    (registers.targetAt target k)
  let seeded := Classical.run seed state
  let afterFirst := Classical.run firstCircuit seeded
  let afterSign := Classical.run signCircuit afterFirst
  let afterSecond := Classical.run secondCircuit afterSign
  have hpair : AgreesOutside targets
      (Classical.run secondCircuit (Classical.run firstCircuit seeded)) seeded := by
    simpa only [targets, firstCircuit, secondCircuit, Classical.run_append] using
      coefficientPrefixTraversals_pair_preservesOutsideTargets registers mode target
        seeded hlayout
  have htransport : AgreesOutside [registers.sign] afterSecond
      (Classical.run secondCircuit afterFirst) := by
    exact (coefficientPrefixSecondTraversal_avoidsSign registers mode target hlayout).run_agreesOutside
      (coefficientPrefixSign_agreesOutsideSign registers k K signUpdate afterFirst)
  have hbodyValue : ∀ wire, wire ≠ registers.sign → wire ∉ targets →
      afterSecond wire = seeded wire := by
    intro wire hsign htarget
    calc
      afterSecond wire = Classical.run secondCircuit afterFirst wire :=
        htransport wire (by simpa using hsign)
      _ = seeded wire := hpair wire htarget
  have hshape : Classical.run
      (coefficientPrefixUnitary registers k K mode signUpdate target) state =
      Classical.run seed afterSecond := by
    simp only [coefficientPrefixUnitary, seed, firstCircuit, signCircuit,
      secondCircuit, seeded, afterFirst, afterSign, afterSecond,
      Classical.run_append]
  rw [hshape]
  intro wire hwire
  have hwireSign : wire ≠ registers.sign := by
    intro equality
    apply (coefficientPrefix_fixed_not_mem_scratch registers hlayout).2
    rw [← equality]
    exact hwire
  have hwireTargets : wire ∉ targets := by
    intro htarget
    simp only [targets, List.mem_map] at htarget
    obtain ⟨label, hlabel, rfl⟩ := htarget
    exact coefficientPrefix_targetAt_not_scratch registers target hlayout hwire
  have hbodyWire := hbodyValue wire hwireSign hwireTargets
  by_cases haccumulator : wire = registers.accumulator k K
  · subst wire
    have haccSign : registers.accumulator k K ≠ registers.sign := by
      intro equality
      apply (coefficientPrefix_fixed_not_mem_scratch registers hlayout).2
      rw [← equality]
      exact coefficientPrefix_accumulator_mem_scratch registers hlayout
    have haccTargets : registers.accumulator k K ∉ targets := by
      intro htarget
      simp only [targets, List.mem_map] at htarget
      obtain ⟨label, hlabel, equality⟩ := htarget
      apply coefficientPrefix_targetAt_not_scratch registers target hlayout
      rw [equality]
      exact coefficientPrefix_accumulator_mem_scratch registers hlayout
    have hbodyAcc := hbodyValue (registers.accumulator k K) haccSign haccTargets
    have hcontrolSign : registers.control ≠ registers.sign := by
      have hfixed := (coefficientPrefix_physical_parts registers hlayout).1
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        or_false] at hfixed
      exact hfixed.1
    have hcontrolTargets : registers.control ∉ targets := by
      intro htarget
      simp only [targets, List.mem_map] at htarget
      obtain ⟨label, hlabel, equality⟩ := htarget
      apply coefficientPrefix_targetAt_not_decoder registers target hlayout
      rw [equality]
      simp
    have hbodyControl := hbodyValue registers.control hcontrolSign hcontrolTargets
    simp only [seed, Classical.run, List.foldl, Classical.applyGate]
    rw [hbodyAcc, hbodyControl]
    have hcontrolAcc := coefficientPrefix_control_ne_accumulator registers hlayout
    have hstateAcc := hready (registers.accumulator k K)
      (coefficientPrefix_accumulator_mem_scratch registers hlayout)
    simp [seeded, seed, Classical.run, Classical.applyGate, upd,
      hcontrolAcc, hstateAcc]
  · simp only [seed, Classical.run, List.foldl, Classical.applyGate]
    rw [upd_other _ _ _ haccumulator, hbodyWire]
    simpa [seeded, seed, Classical.run, Classical.applyGate, upd,
      haccumulator] using hready wire hwire

/-- The literal coherent block has the ordinary exact whole-state adjoint round trip. -/
theorem coefficientPrefixUnitary_adjoint_roundtrip
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K) :
    Classical.run
        (coefficientPrefixUnitary registers k K mode signUpdate target).adjoint
        (Classical.run
          (coefficientPrefixUnitary registers k K mode signUpdate target) state) =
      state := by
  exact run_adjoint_run_classical
    (coefficientPrefixUnitary registers k K mode signUpdate target)
    (coefficientPrefixUnitary_wellFormed registers mode signUpdate target hlayout)
    state

/-! ## Constructor-derived resources -/

private theorem coefficientPrefix_leafCostSum_const
    (tree : UnaryActionTree) (control : Wire) (path : List Wire)
    (cost : Nat) (hlayout : tree.Layout control path) :
    tree.leafCostSum (fun _ _ ↦ cost) control path = cost * tree.leaves := by
  induction hlayout with
  | leaf label control path hlocal =>
      simp [UnaryActionTree.leafCostSum, UnaryActionTree.leaves]
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      simp only [UnaryActionTree.leafCostSum, UnaryActionTree.leaves,
        ihZero, ihOne]
      rw [Nat.mul_add]

private theorem coefficientPrefixSign_toffoliCount
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (signUpdate : Bool) :
    eeaToffoliCount (coefficientPrefixSignCircuit registers k K signUpdate) = 0 := by
  cases signUpdate <;> rfl

private theorem coefficientPrefixSign_cnotCount
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (signUpdate : Bool) :
    eeaCnotCount (coefficientPrefixSignCircuit registers k K signUpdate) =
      if signUpdate then 1 else 0 := by
  cases signUpdate <;> rfl

private theorem coefficientPrefixSign_tCount
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (signUpdate : Bool) :
    ShorECDLP.tCount (coefficientPrefixSignCircuit registers k K signUpdate) = 0 := by
  cases signUpdate <;> rfl

/-- Exact coherent Toffoli count of the prepared-boundary prefix block. -/
theorem coefficientPrefixUnitary_toffoliCount
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    eeaToffoliCount
        (coefficientPrefixUnitary registers k K mode signUpdate target) =
      7 * (coefficientPrefixTree registers k K).leaves +
        4 * (coefficientPrefixTree registers k K).internalNodes := by
  have htree : (coefficientPrefixTree registers k K).Layout registers.control
      (registers.path k K) := by
    simpa [coefficientPrefixTree, CoefficientPrefixRegisters.path] using
      hlayout.tree
  have hfirst : (coefficientPrefixTree registers k K).leafCostSum
      (fun label wire ↦ eeaToffoliCount
        (coefficientPrefixFirstLeaf registers k K mode target label wire))
      registers.control (registers.path k K) =
        rippleFirstCellToffoliCost mode *
          (coefficientPrefixTree registers k K).leaves := by
    simpa using coefficientPrefix_leafCostSum_const
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) (rippleFirstCellToffoliCost mode) htree
  have hsecond : (coefficientPrefixTree registers k K).leafCostSum
      (fun label wire ↦ eeaToffoliCount
        (coefficientPrefixSecondLeaf registers k K mode target label wire))
      registers.control (registers.path k K) =
        rippleSecondCellToffoliCost mode *
          (coefficientPrefixTree registers k K).leaves := by
    simpa using coefficientPrefix_leafCostSum_const
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) (rippleSecondCellToffoliCost mode) htree
  simp only [coefficientPrefixUnitary, eeaToffoliCount_append]
  rw [unaryActionUnitary_toffoliCount .inc
      (coefficientPrefixFirstLeaf registers k K mode target)
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) htree,
    unaryActionUnitary_toffoliCount .dec
      (coefficientPrefixSecondLeaf registers k K mode target)
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) htree,
    hfirst, hsecond,
    coefficientPrefixSign_toffoliCount registers k K signUpdate]
  cases mode <;> simp [eeaToffoliCount, rippleFirstCellToffoliCost,
    rippleSecondCellToffoliCost] <;> omega

/-- Exact coherent CNOT count; the optional carry-to-sign update contributes one. -/
theorem coefficientPrefixUnitary_cnotCount
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    eeaCnotCount
        (coefficientPrefixUnitary registers k K mode signUpdate target) =
      2 + (if signUpdate then 1 else 0) +
        6 * (coefficientPrefixTree registers k K).leaves +
        4 * (coefficientPrefixTree registers k K).internalNodes := by
  have htree : (coefficientPrefixTree registers k K).Layout registers.control
      (registers.path k K) := by
    simpa [coefficientPrefixTree, CoefficientPrefixRegisters.path] using
      hlayout.tree
  have hfirst : (coefficientPrefixTree registers k K).leafCostSum
      (fun label wire ↦ eeaCnotCount
        (coefficientPrefixFirstLeaf registers k K mode target label wire))
      registers.control (registers.path k K) =
        3 * (coefficientPrefixTree registers k K).leaves := by
    simpa using coefficientPrefix_leafCostSum_const
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) 3 htree
  have hsecond : (coefficientPrefixTree registers k K).leafCostSum
      (fun label wire ↦ eeaCnotCount
        (coefficientPrefixSecondLeaf registers k K mode target label wire))
      registers.control (registers.path k K) =
        3 * (coefficientPrefixTree registers k K).leaves := by
    simpa using coefficientPrefix_leafCostSum_const
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) 3 htree
  simp only [coefficientPrefixUnitary, eeaCnotCount_append]
  rw [unaryActionUnitary_cnotCount .inc
      (coefficientPrefixFirstLeaf registers k K mode target)
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) htree,
    unaryActionUnitary_cnotCount .dec
      (coefficientPrefixSecondLeaf registers k K mode target)
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) htree,
    hfirst, hsecond,
    coefficientPrefixSign_cnotCount registers k K signUpdate]
  simp [eeaCnotCount]
  omega

/-- Exact Framework T count of the coherent prepared-boundary reference. -/
theorem coefficientPrefixUnitary_tCount
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    ShorECDLP.tCount
        (coefficientPrefixUnitary registers k K mode signUpdate target) =
      49 * (coefficientPrefixTree registers k K).leaves +
        28 * (coefficientPrefixTree registers k K).internalNodes := by
  have htree : (coefficientPrefixTree registers k K).Layout registers.control
      (registers.path k K) := by
    simpa [coefficientPrefixTree, CoefficientPrefixRegisters.path] using
      hlayout.tree
  have hfirst : (coefficientPrefixTree registers k K).leafCostSum
      (fun label wire ↦ ShorECDLP.tCount
        (coefficientPrefixFirstLeaf registers k K mode target label wire))
      registers.control (registers.path k K) =
        (7 * rippleFirstCellToffoliCost mode) *
          (coefficientPrefixTree registers k K).leaves := by
    simpa using coefficientPrefix_leafCostSum_const
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) (7 * rippleFirstCellToffoliCost mode) htree
  have hsecond : (coefficientPrefixTree registers k K).leafCostSum
      (fun label wire ↦ ShorECDLP.tCount
        (coefficientPrefixSecondLeaf registers k K mode target label wire))
      registers.control (registers.path k K) =
        (7 * rippleSecondCellToffoliCost mode) *
          (coefficientPrefixTree registers k K).leaves := by
    simpa using coefficientPrefix_leafCostSum_const
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) (7 * rippleSecondCellToffoliCost mode) htree
  simp only [coefficientPrefixUnitary, tCount_append]
  rw [unaryActionUnitary_tCount .inc
      (coefficientPrefixFirstLeaf registers k K mode target)
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) htree,
    unaryActionUnitary_tCount .dec
      (coefficientPrefixSecondLeaf registers k K mode target)
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) htree,
    hfirst, hsecond, coefficientPrefixSign_tCount registers k K signUpdate]
  cases mode <;> simp [ShorECDLP.tCount, ShorECDLP.tCost,
    rippleFirstCellToffoliCost, rippleSecondCellToffoliCost] <;> omega

/-- Two leaf-local clean-AND erasures and two decoder erasures are measured per visited source
leaf/internal node pair. -/
theorem coefficientPrefixAdaptive_measurementCount
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    (coefficientPrefixAdaptive registers k K mode signUpdate target).measurementCount =
      2 * (coefficientPrefixTree registers k K).leaves +
        2 * (coefficientPrefixTree registers k K).internalNodes := by
  have htree : (coefficientPrefixTree registers k K).Layout registers.control
      (registers.path k K) := by
    simpa [coefficientPrefixTree, CoefficientPrefixRegisters.path] using
      hlayout.tree
  have hfirst : (coefficientPrefixTree registers k K).leafCostSum
      (fun label wire ↦
        (coefficientPrefixFirstLeafAdaptive registers k K mode target label wire).measurementCount)
      registers.control (registers.path k K) =
        (coefficientPrefixTree registers k K).leaves := by
    simpa using coefficientPrefix_leafCostSum_const
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) 1 htree
  have hsecond : (coefficientPrefixTree registers k K).leafCostSum
      (fun label wire ↦
        (coefficientPrefixSecondLeafAdaptive registers k K mode target label wire).measurementCount)
      registers.control (registers.path k K) =
        (coefficientPrefixTree registers k K).leaves := by
    simpa using coefficientPrefix_leafCostSum_const
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) 1 htree
  rw [coefficientPrefixAdaptive]
  simp only [AdaptiveCircuit.measurementCount,
    coefficientPrefix_measurementCount_seq]
  rw [unaryAdaptiveAction_measurementCount .inc
      (coefficientPrefixFirstLeafAdaptive registers k K mode target)
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) htree,
    unaryAdaptiveAction_measurementCount .dec
      (coefficientPrefixSecondLeafAdaptive registers k K mode target)
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) htree,
    hfirst, hsecond]
  omega

/-- Exact worst-branch T count of the measurement-uncomputed prepared-boundary block. -/
theorem coefficientPrefixAdaptive_tCount
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    (coefficientPrefixAdaptive registers k K mode signUpdate target).tCount =
      35 * (coefficientPrefixTree registers k K).leaves +
        14 * (coefficientPrefixTree registers k K).internalNodes := by
  have htree : (coefficientPrefixTree registers k K).Layout registers.control
      (registers.path k K) := by
    simpa [coefficientPrefixTree, CoefficientPrefixRegisters.path] using
      hlayout.tree
  have hfirst : (coefficientPrefixTree registers k K).leafCostSum
      (fun label wire ↦
        (coefficientPrefixFirstLeafAdaptive registers k K mode target label wire).tCount)
      registers.control (registers.path k K) =
        (7 * (rippleFirstCellToffoliCost mode - 1)) *
          (coefficientPrefixTree registers k K).leaves := by
    simpa using coefficientPrefix_leafCostSum_const
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) (7 * (rippleFirstCellToffoliCost mode - 1)) htree
  have hsecond : (coefficientPrefixTree registers k K).leafCostSum
      (fun label wire ↦
        (coefficientPrefixSecondLeafAdaptive registers k K mode target label wire).tCount)
      registers.control (registers.path k K) =
        (7 * (rippleSecondCellToffoliCost mode - 1)) *
          (coefficientPrefixTree registers k K).leaves := by
    simpa using coefficientPrefix_leafCostSum_const
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) (7 * (rippleSecondCellToffoliCost mode - 1)) htree
  rw [coefficientPrefixAdaptive]
  simp only [AdaptiveCircuit.tCount, coefficientPrefix_tCount_seq]
  rw [unaryAdaptiveAction_tCount .inc
      (coefficientPrefixFirstLeafAdaptive registers k K mode target)
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) htree,
    unaryAdaptiveAction_tCount .dec
      (coefficientPrefixSecondLeafAdaptive registers k K mode target)
      (coefficientPrefixTree registers k K) registers.control
      (registers.path k K) htree,
    hfirst, hsecond, coefficientPrefixSign_tCount registers k K signUpdate]
  cases mode <;> simp [ShorECDLP.tCount, ShorECDLP.tCost,
    rippleFirstCellToffoliCost, rippleSecondCellToffoliCost] <;> omega

/-! ## Pinned-source regressions -/

private def coefficientPrefixTreeDepth : UnaryActionTree → Nat
  | .leaf _ => 0
  | .node _ zero one =>
      1 + max (coefficientPrefixTreeDepth zero) (coefficientPrefixTreeDepth one)

/-- A separated path stack with enough cells realizes the recursive unary-decoder layout. -/
private theorem coefficientPrefixTree_layout_of_separated
    (tree : UnaryActionTree) (control : Wire) (path : List Wire)
    (hdepth : coefficientPrefixTreeDepth tree ≤ path.length)
    (hcontrolIndex : control ∉ tree.indexWires)
    (hcontrolPath : control ∉ path)
    (hpathNodup : path.Nodup)
    (hindexPath : ∀ wire ∈ tree.indexWires, wire ∉ path) :
    tree.Layout control path := by
  induction tree generalizing control path with
  | leaf label =>
      exact .leaf label control path (by
        simp only [List.nodup_cons]
        exact ⟨hcontrolPath, hpathNodup⟩)
  | node indexBit zero one ihZero ihOne =>
      cases path with
      | nil => simp [coefficientPrefixTreeDepth] at hdepth
      | cons next rest =>
          have hrestNodup : rest.Nodup :=
            (List.nodup_cons.mp hpathNodup).2
          have hnextRest : next ∉ rest :=
            (List.nodup_cons.mp hpathNodup).1
          have hlocal :
              (control ::
                ((UnaryActionTree.node indexBit zero one).indexWires.dedup ++
                  (next :: rest))).Nodup := by
            rw [List.nodup_cons, List.nodup_append]
            refine ⟨?_, List.nodup_dedup _, hpathNodup, ?_⟩
            · intro hmem
              rw [List.mem_append] at hmem
              exact hmem.elim
                (fun h => hcontrolIndex (by simpa using h)) hcontrolPath
            · intro wire hwire pathWire hpathWire heq
              exact hindexPath wire (by simpa using hwire)
                (by simpa [← heq] using hpathWire)
          exact .node indexBit control next zero one rest hlocal
            (ihZero next rest
              (by simp [coefficientPrefixTreeDepth] at hdepth; omega)
              (by
                intro hmem
                exact hindexPath next
                  (by simp [UnaryActionTree.indexWires, hmem]) (by simp))
              hnextRest hrestNodup
              (by
                intro wire hwire hrest
                exact hindexPath wire
                  (by simp [UnaryActionTree.indexWires, hwire]) (by simp [hrest])))
            (ihOne next rest
              (by simp [coefficientPrefixTreeDepth] at hdepth; omega)
              (by
                intro hmem
                exact hindexPath next
                  (by simp [UnaryActionTree.indexWires, hmem]) (by simp))
              hnextRest hrestNodup
              (by
                intro wire hwire hrest
                exact hindexPath wire
                  (by simp [UnaryActionTree.indexWires, hwire]) (by simp [hrest])))

private def coefficientPrefixSmallRegisters : CoefficientPrefixRegisters where
  control := 0
  sign := 1
  work1 := [2, 3, 4, 5]
  work2 := [6, 7, 8, 9]
  boundary := [10, 11, 12]
  scratch := [13, 14, 15, 16, 17, 18]

/-- Exact highest-varying-bit tree for the four-label prepared-boundary source instance. -/
theorem coefficientPrefixSmall_tree_regression :
    coefficientPrefixTree coefficientPrefixSmallRegisters 2 5 =
      .node 12 (.node 10 (.leaf 2) (.leaf 3))
        (.node 10 (.leaf 4) (.leaf 5)) := by
  decide

private theorem coefficientPrefixSmall_layout :
    CoefficientPrefixLayout coefficientPrefixSmallRegisters 2 5 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  change (coefficientPrefixTree coefficientPrefixSmallRegisters 2 5).Layout
    0 ([13, 14, 15] : List Wire)
  rw [coefficientPrefixSmall_tree_regression]
  exact .node 12 0 13 _ _ ([14, 15] : List Wire) (by decide)
    (.node 10 13 14 _ _ ([15] : List Wire) (by decide)
      (.leaf 2 14 ([15] : List Wire) (by decide))
      (.leaf 3 14 ([15] : List Wire) (by decide)))
    (.node 10 13 14 _ _ ([15] : List Wire) (by decide)
      (.leaf 4 14 ([15] : List Wire) (by decide))
      (.leaf 5 14 ([15] : List Wire) (by decide)))

/-- Closed four-label resource regression for the literal add/sign/work-two source call. -/
theorem coefficientPrefixSmall_resources :
    eeaToffoliCount
        (coefficientPrefixUnitary coefficientPrefixSmallRegisters 2 5
          .add true .work2) = 40 ∧
      eeaCnotCount
        (coefficientPrefixUnitary coefficientPrefixSmallRegisters 2 5
          .add true .work2) = 39 ∧
      ShorECDLP.tCount
        (coefficientPrefixUnitary coefficientPrefixSmallRegisters 2 5
          .add true .work2) = 280 ∧
      (coefficientPrefixAdaptive coefficientPrefixSmallRegisters 2 5
          .add true .work2).measurementCount = 14 ∧
      (coefficientPrefixAdaptive coefficientPrefixSmallRegisters 2 5
          .add true .work2).tCount = 182 := by
  rw [coefficientPrefixUnitary_toffoliCount coefficientPrefixSmallRegisters
      .add true .work2 coefficientPrefixSmall_layout,
    coefficientPrefixUnitary_cnotCount coefficientPrefixSmallRegisters
      .add true .work2 coefficientPrefixSmall_layout,
    coefficientPrefixUnitary_tCount coefficientPrefixSmallRegisters
      .add true .work2 coefficientPrefixSmall_layout,
    coefficientPrefixAdaptive_measurementCount coefficientPrefixSmallRegisters
      .add true .work2 coefficientPrefixSmall_layout,
    coefficientPrefixAdaptive_tCount coefficientPrefixSmallRegisters
      .add true .work2 coefficientPrefixSmall_layout,
    coefficientPrefixSmall_tree_regression]
  norm_num [UnaryActionTree.leaves, UnaryActionTree.internalNodes]

set_option maxRecDepth 10000 in
/-- The small literal source term contains 24 X gates and touches exactly the 17 physical roles
used by the pruned tree; the skipped boundary/path wires remain untouched. -/
theorem coefficientPrefixSmall_surface_regression :
    eeaXCount
        (coefficientPrefixUnitary coefficientPrefixSmallRegisters 2 5
          .add true .work2) = 24 ∧
      qubitCount
        (coefficientPrefixUnitary coefficientPrefixSmallRegisters 2 5
          .add true .work2) = 17 := by
  decide

private def coefficientPrefixNarrowRegisters : CoefficientPrefixRegisters where
  control := 0
  sign := 1
  work1 := [2, 3]
  work2 := [4, 5]
  boundary := [6, 7, 8, 9, 10, 11, 12, 13, 14]
  scratch := [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]

/-- Exact source tree for the first narrow production T-prefix window `(k,K,len_width)=(1,2,9)`. -/
theorem coefficientPrefixNarrow_tree_regression :
    coefficientPrefixTree coefficientPrefixNarrowRegisters 1 2 =
      .node 7 (.leaf 1) (.leaf 2) := by
  decide

/-- Literal source-order comparison for the first narrow production T-prefix call. -/
theorem coefficientPrefixNarrow_source_regression :
    coefficientPrefixUnitary coefficientPrefixNarrowRegisters 1 2
        .sub false .work2 =
      [.CX 0 25] ++
      computeZeroAnd 0 7 15 ++
      controlledUmaInv 25 4 2 24 26 ++ [.CX 15 25] ++
      [.CX 0 15] ++
      controlledUmaInv 25 5 3 24 26 ++ [.CX 15 25] ++
      [.CX 0 15] ++ computeZeroAnd 0 7 15 ++
      computeZeroAnd 0 7 15 ++ [.CX 0 15] ++
      [.CX 15 25] ++ controlledMajInv 25 5 3 24 26 ++
      [.CX 0 15] ++ [.CX 15 25] ++
      controlledMajInv 25 4 2 24 26 ++
      computeZeroAnd 0 7 15 ++ [.CX 0 25] := by
  decide

/-- The first narrow production T-prefix call has an inhabited 27-role physical layout. -/
theorem coefficientPrefixNarrow_layout :
    CoefficientPrefixLayout coefficientPrefixNarrowRegisters 1 2 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  change (coefficientPrefixTree coefficientPrefixNarrowRegisters 1 2).Layout
    0 ([15] : List Wire)
  rw [coefficientPrefixNarrow_tree_regression]
  exact .node 7 0 15 _ _ ([] : List Wire) (by decide)
    (.leaf 1 15 ([] : List Wire) (by decide))
    (.leaf 2 15 ([] : List Wire) (by decide))

/-- Exact resources for the first pinned production T-prefix call: subtract into Work2 without a
sign update. -/
theorem coefficientPrefixNarrow_resources :
    eeaToffoliCount
        (coefficientPrefixUnitary coefficientPrefixNarrowRegisters 1 2
          .sub false .work2) = 18 ∧
      eeaCnotCount
        (coefficientPrefixUnitary coefficientPrefixNarrowRegisters 1 2
          .sub false .work2) = 18 ∧
      ShorECDLP.tCount
        (coefficientPrefixUnitary coefficientPrefixNarrowRegisters 1 2
          .sub false .work2) = 126 ∧
      (coefficientPrefixAdaptive coefficientPrefixNarrowRegisters 1 2
          .sub false .work2).measurementCount = 6 ∧
      (coefficientPrefixAdaptive coefficientPrefixNarrowRegisters 1 2
          .sub false .work2).tCount = 84 := by
  rw [coefficientPrefixUnitary_toffoliCount coefficientPrefixNarrowRegisters
      .sub false .work2 coefficientPrefixNarrow_layout,
    coefficientPrefixUnitary_cnotCount coefficientPrefixNarrowRegisters
      .sub false .work2 coefficientPrefixNarrow_layout,
    coefficientPrefixUnitary_tCount coefficientPrefixNarrowRegisters
      .sub false .work2 coefficientPrefixNarrow_layout,
    coefficientPrefixAdaptive_measurementCount coefficientPrefixNarrowRegisters
      .sub false .work2 coefficientPrefixNarrow_layout,
    coefficientPrefixAdaptive_tCount coefficientPrefixNarrowRegisters
      .sub false .work2 coefficientPrefixNarrow_layout,
    coefficientPrefixNarrow_tree_regression]
  norm_num [UnaryActionTree.leaves, UnaryActionTree.internalNodes]

set_option maxRecDepth 10000 in
/-- The first narrow production call allocates 27 physical roles; its pruned source term touches
exactly ten of them and contains eight X gates. -/
theorem coefficientPrefixNarrow_surface_regression :
    coefficientPrefixNarrowRegisters.allWires.length = 27 ∧
      eeaXCount
        (coefficientPrefixUnitary coefficientPrefixNarrowRegisters 1 2
          .sub false .work2) = 8 ∧
      qubitCount
        (coefficientPrefixUnitary coefficientPrefixNarrowRegisters 1 2
          .sub false .work2) = 10 := by
  decide

private theorem coefficientPrefix_leaves_eq_labels_length
    (tree : UnaryActionTree) :
    tree.leaves = tree.labels.length := by
  induction tree with
  | leaf label => rfl
  | node indexBit zero one ihZero ihOne =>
      simp [UnaryActionTree.leaves, UnaryActionTree.labels, ihZero, ihOne]

private theorem coefficientPrefix_internalNodes_succ_eq_leaves
    (tree : UnaryActionTree) :
    tree.internalNodes + 1 = tree.leaves := by
  induction tree with
  | leaf label => rfl
  | node indexBit zero one ihZero ihOne =>
      simp only [UnaryActionTree.internalNodes, UnaryActionTree.leaves]
      omega

private def coefficientPrefixProductionRegisters : CoefficientPrefixRegisters where
  control := 0
  sign := 1
  work1 := List.range' 2 257
  work2 := List.range' 259 257
  boundary := List.range' 516 9
  scratch := List.range' 525 12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
/-- The advertised production `(k,K,len_width)=(1,257,9)` surface is inhabited by one explicit
537-role physical allocation.  Its nine source bits and nine decoder-path cells are disjoint. -/
theorem coefficientPrefixProduction_layout_inhabited :
    ∃ registers : CoefficientPrefixRegisters,
      registers.allWires.length = 537 ∧
        registers.boundary.length = 9 ∧
        CoefficientPrefixLayout registers 1 257 := by
  refine ⟨coefficientPrefixProductionRegisters, by decide, by decide, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  apply coefficientPrefixTree_layout_of_separated
  · decide
  · decide
  · decide
  · decide
  · decide

set_option maxRecDepth 10000 in
private theorem coefficientPrefixProduction_tree_shape
    (registers : CoefficientPrefixRegisters)
    (hlayout : CoefficientPrefixLayout registers 1 257) :
    (coefficientPrefixTree registers 1 257).leaves = 257 ∧
      (coefficientPrefixTree registers 1 257).internalNodes = 256 := by
  have hleaves : (coefficientPrefixTree registers 1 257).leaves = 257 := by
    rw [coefficientPrefix_leaves_eq_labels_length,
      coefficientPrefixTree_labels registers hlayout, Finset.length_sort]
    simp only [quotientSwapLabels]
    rw [List.toFinset_card_of_nodup (List.nodup_range' 1)]
    rfl
  constructor
  · exact hleaves
  · have hinternal := coefficientPrefix_internalNodes_succ_eq_leaves
      (coefficientPrefixTree registers 1 257)
    omega

set_option maxRecDepth 10000 in
/-- Production-width resources for the pinned 257-lane, 9-bit-boundary source calls.  The one
optional carry-to-sign CNOT distinguishes the additive call from the subtractive call. -/
theorem coefficientPrefixProduction_resources
    (registers : CoefficientPrefixRegisters)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers 1 257)
    (hboundary : registers.boundary.length = 9) :
    eeaToffoliCount
        (coefficientPrefixUnitary registers 1 257 mode signUpdate target) = 2823 ∧
      eeaCnotCount
        (coefficientPrefixUnitary registers 1 257 mode signUpdate target) =
          2568 + (if signUpdate then 1 else 0) ∧
      ShorECDLP.tCount
        (coefficientPrefixUnitary registers 1 257 mode signUpdate target) = 19761 ∧
      (coefficientPrefixAdaptive registers 1 257 mode signUpdate target).measurementCount =
        1026 ∧
      (coefficientPrefixAdaptive registers 1 257 mode signUpdate target).tCount = 12579 := by
  have _hboundaryWidth : registers.boundary.length = 9 := hboundary
  obtain ⟨hleaves, hinternal⟩ :=
    coefficientPrefixProduction_tree_shape registers hlayout
  rw [coefficientPrefixUnitary_toffoliCount registers mode signUpdate target hlayout,
    coefficientPrefixUnitary_cnotCount registers mode signUpdate target hlayout,
    coefficientPrefixUnitary_tCount registers mode signUpdate target hlayout,
    coefficientPrefixAdaptive_measurementCount registers mode signUpdate target hlayout,
    coefficientPrefixAdaptive_tCount registers mode signUpdate target hlayout,
    hleaves, hinternal]
  omega

end

end ShorECDLP.Paper2607_13816
