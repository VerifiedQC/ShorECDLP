import ShorECDLP.Submission.«2607_13816».EEA.MeasuredZeroMapCounts
import ShorECDLP.Submission.«2607_13816».EEA.LengthBlocks
import ShorECDLP.Submission.«2607_13816».Arithmetic.UnitaryPrimitiveCounts
/-!
# Measurement-assisted borrowed-work length writers

Both source writers retain their seed and dirty-controlled CNOT streams, replacing the two
zero maps with their measured refinements. Scratch is restored between the maps. The complete
shared-scratch length-update wrapper and EEA schedule are separate integration boundaries.
-/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
private theorem length_seq
    {a b : AdaptiveCircuit} {u v : Circuit} {P : BasisState → Prop}
    (ha : CoherentlyImplementsOn a (Quantum.run u) P)
    (hb : CoherentlyImplementsOn b (Quantum.run v) P)
    (hu : HPFree u) (hp : ∀ s, P s → P (Classical.run u s)) :
    CoherentlyImplementsOn (a.seq b) (Quantum.run (u ++ v)) P := by
  have h := ha.seq hb (by
    intro s hs
    rw [run_ket_agrees_classical u s hu]
    exact supportedOn_ket P _ (hp s hs))
  apply h.congrIdeal
  intro s _
  exact (Quantum.run_append u v (ket s)).symm

/-- Source highest-position writer with measured upper zero maps. -/
def measuredHighestPositionWrite (k K : Nat) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) :
    AdaptiveCircuit :=
  .unitary (controlledXorConstant control targets (truthMinusOneValue targets.length K) ++ highestPositionDirtyWrites k K targets dirtyAt)
    ((measuredUpperZeroMap k K tree control r t path bitAt dirtyAt).seq
      (.unitary (highestPositionDirtyWrites k K targets dirtyAt)
        (measuredUpperZeroMap k K tree control r t path bitAt dirtyAt)))

/-- The complete measured writer coherently refines the literal strict writer. -/
theorem measuredHighestPositionWrite_coherent (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (hl : LengthWriterLayout k K tree control r t path bitAt dirtyAt targets) :
    CoherentlyImplementsOn (measuredHighestPositionWrite k K tree control r t path bitAt dirtyAt targets)
      (Quantum.run (highestPositionXorWrite k K tree control r t path bitAt dirtyAt targets))
      (fun s => Clean path s ∧ s t = false) := by
  let P := fun s : BasisState => Clean path s ∧ s t = false
  let z := upperZeroMapUnitary k K tree control r t path bitAt dirtyAt
  let w := highestPositionDirtyWrites k K targets dirtyAt
  let seed := controlledXorConstant control targets (truthMinusOneValue targets.length K)
  have hz := measuredUpperZeroMap_coherent k K hkK tree control r t path bitAt dirtyAt hl.toZeroMapLayout
  have hnot : ∀ q, q ∈ path ++ [t] → q ∉ targets := by
    intro q hq
    apply hl.mapWire_not_target
    rcases List.mem_append.mp hq with hp | ht
    · simp [zeroMapWires, zeroMapProtectedWires, hp]
    · have := List.mem_singleton.mp ht
      subst q
      simp [zeroMapWires]
  have wp : ∀ s, P s → P (Classical.run w s) := by
    intro s hs
    constructor
    · intro q hq
      dsimp [w, highestPositionDirtyWrites, rightLengthDirtyWrites]
      rw [dirtyConstantWrites_preservesOutside _ _ _ _ _ _ (hnot q (by simp [hq]))]
      exact hs.1 q hq
    · dsimp [w, highestPositionDirtyWrites, rightLengthDirtyWrites]
      rw [dirtyConstantWrites_preservesOutside _ _ _ _ _ _ (hnot t (by simp))]
      exact hs.2
  have sp : ∀ s, P s → P (Classical.run seed s) := by
    intro s hs
    constructor
    · intro q hq
      rw [controlledXorConstant_preservesOutside _ _ _ _ _ (hnot q (by simp [hq]))]
      exact hs.1 q hq
    · rw [controlledXorConstant_preservesOutside _ _ _ _ _ (hnot t (by simp))]
      exact hs.2
  have zp : ∀ s, P s → P (Classical.run z s) := by
    intro s hs
    have pres : ∀ q, q ∈ path ++ [t] → Classical.run z s q = s q := by
      intro q hq
      apply upperZeroMapUnitary_preserves k K hkK tree control r t path bitAt dirtyAt s
        hl.toZeroMapLayout hs.1 hs.2 q
      · rcases List.mem_append.mp hq with hp | ht
        · intro heq; subst q
          exact hl.range_not_protected (by simp [zeroMapProtectedWires,hp])
        · have heq := List.mem_singleton.mp ht
          subst q
          exact Ne.symm hl.range_ne_temporary
      · intro l hlabel heq
        rcases List.mem_append.mp hq with hp | ht
        · have hd := List.disjoint_of_nodup_append hl.wires
          have hp' : q ∈ zeroMapProtectedWires tree control path := by
            simp [zeroMapProtectedWires, hp]
          exact List.disjoint_left.mp hd hp' (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_append_right _ (List.mem_map.mpr ⟨l,hlabel,heq.symm⟩))))
        · have hh := List.mem_singleton.mp ht
          exact hl.temporary_ne_dirty hlabel (hh.symm.trans heq)
    exact ⟨fun q hq => (pres q (by simp [hq])).trans (hs.1 q hq),
      (pres t (by simp)).trans hs.2⟩
  have hwz := length_seq (CoherentlyImplementsOn.unitary w P) hz (by simp [w,highestPositionDirtyWrites]) wp
  have hzwz := length_seq hz hwz (by simp) zp
  have hpre := CoherentlyImplementsOn.unitary (seed ++ w) P
  have hall := length_seq hpre hzwz (by simp [seed,w,highestPositionDirtyWrites]) (by
    intro s hs
    rw [Classical.run_append]
    exact wp _ (sp s hs))
  convert hall using 1; simp [highestPositionXorWrite,seed,w,List.append_assoc]

/-- Source right-length writer with measured lower zero maps. -/
def measuredRightLengthWrite (n k K : Nat) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) :
    AdaptiveCircuit :=
  .unitary (controlledXorConstant control targets (rightLengthValue n targets.length k) ++ rightLengthDirtyWrites n k K targets dirtyAt)
    ((measuredLowerZeroMap k K tree control r t path bitAt dirtyAt).seq
      (.unitary (rightLengthDirtyWrites n k K targets dirtyAt)
        (measuredLowerZeroMap k K tree control r t path bitAt dirtyAt)))

/-- The complete lower writer has the same coherent refinement contract. -/
theorem measuredRightLengthWrite_coherent (n k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (hl : LengthWriterLayout k K tree control r t path bitAt dirtyAt targets) :
    CoherentlyImplementsOn (measuredRightLengthWrite n k K tree control r t path bitAt dirtyAt targets)
      (Quantum.run (rightLengthXorWrite n k K tree control r t path bitAt dirtyAt targets))
      (fun s => Clean path s ∧ s t = false) := by
  let P := fun s : BasisState => Clean path s ∧ s t = false
  let z := lowerZeroMapUnitary k K tree control r t path bitAt dirtyAt
  let w := rightLengthDirtyWrites n k K targets dirtyAt
  let seed := controlledXorConstant control targets (rightLengthValue n targets.length k)
  have hz := measuredLowerZeroMap_coherent k K hkK tree control r t path bitAt dirtyAt hl.toZeroMapLayout
  have hnot : ∀ q, q ∈ path ++ [t] → q ∉ targets := by
    intro q hq
    apply hl.mapWire_not_target
    rcases List.mem_append.mp hq with hp | ht
    · simp [zeroMapWires, zeroMapProtectedWires, hp]
    · have := List.mem_singleton.mp ht
      subst q
      simp [zeroMapWires]
  have wp : ∀ s, P s → P (Classical.run w s) := by
    intro s hs
    constructor
    · intro q hq
      dsimp [w, highestPositionDirtyWrites, rightLengthDirtyWrites]
      rw [dirtyConstantWrites_preservesOutside _ _ _ _ _ _ (hnot q (by simp [hq]))]
      exact hs.1 q hq
    · dsimp [w, highestPositionDirtyWrites, rightLengthDirtyWrites]
      rw [dirtyConstantWrites_preservesOutside _ _ _ _ _ _ (hnot t (by simp))]
      exact hs.2
  have sp : ∀ s, P s → P (Classical.run seed s) := by
    intro s hs
    constructor
    · intro q hq
      rw [controlledXorConstant_preservesOutside _ _ _ _ _ (hnot q (by simp [hq]))]
      exact hs.1 q hq
    · rw [controlledXorConstant_preservesOutside _ _ _ _ _ (hnot t (by simp))]
      exact hs.2
  have zp : ∀ s, P s → P (Classical.run z s) := by
    intro s hs
    have pres : ∀ q, q ∈ path ++ [t] → Classical.run z s q = s q := by
      intro q hq
      apply lowerZeroMapUnitary_preserves k K hkK tree control r t path bitAt dirtyAt s
        hl.toZeroMapLayout hs.1 hs.2 q
      · rcases List.mem_append.mp hq with hp | ht
        · intro heq; subst q
          exact hl.range_not_protected (by simp [zeroMapProtectedWires,hp])
        · have heq := List.mem_singleton.mp ht
          subst q
          exact Ne.symm hl.range_ne_temporary
      · intro l hlabel heq
        rcases List.mem_append.mp hq with hp | ht
        · have hd := List.disjoint_of_nodup_append hl.wires
          have hp' : q ∈ zeroMapProtectedWires tree control path := by
            simp [zeroMapProtectedWires, hp]
          exact List.disjoint_left.mp hd hp' (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_append_right _ (List.mem_map.mpr ⟨l,hlabel,heq.symm⟩))))
        · have hh := List.mem_singleton.mp ht
          exact hl.temporary_ne_dirty hlabel (hh.symm.trans heq)
    exact ⟨fun q hq => (pres q (by simp [hq])).trans (hs.1 q hq),
      (pres t (by simp)).trans hs.2⟩
  have hwz := length_seq (CoherentlyImplementsOn.unitary w P) hz (by simp [w,rightLengthDirtyWrites]) wp
  have hzwz := length_seq hz hwz (by simp) zp
  have hpre := CoherentlyImplementsOn.unitary (seed ++ w) P
  have hall := length_seq hpre hzwz (by simp [seed,w,rightLengthDirtyWrites]) (by
    intro s hs
    rw [Classical.run_append]
    exact wp _ (sp s hs))
  convert hall using 1; simp [rightLengthXorWrite,seed,w,List.append_assoc]

/-- Every gate and feed-forward branch respects the writer layout. -/
theorem measuredHighestPositionWrite_wellFormed (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (hl : LengthWriterLayout k K tree control r t path bitAt dirtyAt targets) :
    (measuredHighestPositionWrite k K tree control r t path bitAt dirtyAt targets).WellFormed := by
  have hw : CircuitWellFormed (highestPositionDirtyWrites k K targets dirtyAt) := by
    apply dirtyConstantWrites_wellFormed
    intro l hh w hw heq
    apply hl.dirty_not_target (by simpa using hh)
    simpa [heq] using hw
  have hs : CircuitWellFormed (controlledXorConstant control targets (truthMinusOneValue targets.length K)) := by
    apply controlledXorConstant_wellFormed
    intro w hw heq
    exact hl.control_not_target (heq ▸ hw)
  have hm := measuredUpperZeroMap_wellFormed k K hkK tree control r t path bitAt dirtyAt hl.toZeroMapLayout
  exact ⟨(circuitWellFormed_append _ _).mpr ⟨hs,hw⟩,hm.seq ⟨hw,hm⟩⟩

/-- Two measured zero maps supply all Toffolis; seed and dirty writes are CNOT-only. -/
theorem measuredHighestPositionWrite_toffoli (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (hl : tree.Layout control path) (hlabels : tree.labels = zeroMapLabels k K) :
    (primitiveResources (measuredHighestPositionWrite k K tree control r t path bitAt dirtyAt targets)).toffoli =
      12*(K+1-k)-8 := by
  have hw : HPFree (highestPositionDirtyWrites k K targets dirtyAt) := by simp [highestPositionDirtyWrites]
  have hp : HPFree (controlledXorConstant control targets (truthMinusOneValue targets.length K) ++ highestPositionDirtyWrites k K targets dirtyAt) := by
    simp [hw]
  rw [measuredHighestPositionWrite,primitiveResources_unitary_HPFree _ _ hp,primitiveResources_seq,
    primitiveResources_unitary_HPFree _ _ hw]
  simp only [PrimitiveResources.add,eeaToffoliCount_append,controlledXorConstant_toffoliCount,
    highestPositionDirtyWrites,dirtyConstantWrites_toffoliCount,Nat.zero_add]
  rw [measuredUpperZeroMap_toffoli_closed _ _ hkK _ _ _ _ _ _ _ hl hlabels]
  omega

/-- Every gate and feed-forward branch respects the writer layout. -/
theorem measuredRightLengthWrite_wellFormed (n k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (hl : LengthWriterLayout k K tree control r t path bitAt dirtyAt targets) :
    (measuredRightLengthWrite n k K tree control r t path bitAt dirtyAt targets).WellFormed := by
  have hw : CircuitWellFormed (rightLengthDirtyWrites n k K targets dirtyAt) := by
    apply dirtyConstantWrites_wellFormed
    intro l hh w hw heq
    apply hl.dirty_not_target (by simpa using hh)
    simpa [heq] using hw
  have hs : CircuitWellFormed (controlledXorConstant control targets (rightLengthValue n targets.length k)) := by
    apply controlledXorConstant_wellFormed
    intro w hw heq
    exact hl.control_not_target (heq ▸ hw)
  have hm := measuredLowerZeroMap_wellFormed k K hkK tree control r t path bitAt dirtyAt hl.toZeroMapLayout
  exact ⟨(circuitWellFormed_append _ _).mpr ⟨hs,hw⟩,hm.seq ⟨hw,hm⟩⟩

/-- Two measured zero maps supply all Toffolis; seed and dirty writes are CNOT-only. -/
theorem measuredRightLengthWrite_toffoli (n k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (hl : tree.Layout control path) (hlabels : tree.labels = zeroMapLabels k K) :
    (primitiveResources (measuredRightLengthWrite n k K tree control r t path bitAt dirtyAt targets)).toffoli =
      12*(K+1-k)-8 := by
  have hw : HPFree (rightLengthDirtyWrites n k K targets dirtyAt) := by simp [rightLengthDirtyWrites]
  have hp : HPFree (controlledXorConstant control targets (rightLengthValue n targets.length k) ++ rightLengthDirtyWrites n k K targets dirtyAt) := by
    simp [hw]
  rw [measuredRightLengthWrite,primitiveResources_unitary_HPFree _ _ hp,primitiveResources_seq,
    primitiveResources_unitary_HPFree _ _ hw]
  simp only [PrimitiveResources.add,eeaToffoliCount_append,controlledXorConstant_toffoliCount,
    rightLengthDirtyWrites,dirtyConstantWrites_toffoliCount,Nat.zero_add]
  rw [measuredLowerZeroMap_toffoli_closed _ _ hkK _ _ _ _ _ _ _ hl hlabels]
  omega
end
end ShorECDLP.Paper2607_13816
