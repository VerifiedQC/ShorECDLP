import ShorECDLP.Submission.«2607_13816».EEA.MeasuredLengthWriters
/-!
# Measured shared-scratch length updates

The constant arithmetic restores its scratch before the two measured writers run.
The layout permits serial sharing between the constant arithmetic and the scanner.
These refinements preserve arbitrary range and borrowed data inputs.
-/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
/-- The strict upper writer restores the scratch required by the following measured writer. -/
theorem highestPositionWrite_scratch (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (hl : LengthWriterLayout k K tree control r t path bitAt dirtyAt targets)
    (s : BasisState) (hs : Clean path s ∧ s t = false) :
    Clean path (Classical.run (highestPositionXorWrite k K tree control r t path bitAt dirtyAt targets) s) ∧
      Classical.run (highestPositionXorWrite k K tree control r t path bitAt dirtyAt targets) s t = false := by
  let P := fun s : BasisState => Clean path s ∧ s t = false
  let z := upperZeroMapUnitary k K tree control r t path bitAt dirtyAt
  let w := highestPositionDirtyWrites k K targets dirtyAt
  let seed := controlledXorConstant control targets (truthMinusOneValue targets.length K)
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
  change P (Classical.run (seed ++ w ++ z ++ w ++ z) s)
  simp only [Classical.run_append]
  exact zp _ (wp _ (zp _ (wp _ (sp s hs))))

/-- The strict lower writer restores the scratch required by the following measured writer. -/
theorem rightLengthWrite_scratch (n k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (hl : LengthWriterLayout k K tree control r t path bitAt dirtyAt targets)
    (s : BasisState) (hs : Clean path s ∧ s t = false) :
    Clean path (Classical.run (rightLengthXorWrite n k K tree control r t path bitAt dirtyAt targets) s) ∧
      Classical.run (rightLengthXorWrite n k K tree control r t path bitAt dirtyAt targets) s t = false := by
  let P := fun s : BasisState => Clean path s ∧ s t = false
  let z := lowerZeroMapUnitary k K tree control r t path bitAt dirtyAt
  let w := rightLengthDirtyWrites n k K targets dirtyAt
  let seed := controlledXorConstant control targets (rightLengthValue n targets.length k)
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
  change P (Classical.run (seed ++ w ++ z ++ w ++ z) s)
  simp only [Classical.run_append]
  exact zp _ (wp _ (zp _ (wp _ (sp s hs))))

private theorem shared_seq
    {a b : AdaptiveCircuit} {u v : Circuit} {P Q : BasisState → Prop}
    (ha : CoherentlyImplementsOn a (Quantum.run u) P)
    (hb : CoherentlyImplementsOn b (Quantum.run v) Q)
    (hu : HPFree u) (hp : ∀ s, P s → Q (Classical.run u s)) :
    CoherentlyImplementsOn (a.seq b) (Quantum.run (u ++ v)) P := by
  have h := ha.seq hb (by
    intro s hs
    rw [run_ket_agrees_classical u s hu]
    exact supportedOn_ket Q _ (hp s hs))
  apply h.congrIdeal
  intro s _
  exact (Quantum.run_append u v (ket s)).symm

/-- Literal shared-scratch length update with two measured writers. -/
def measuredLenUpdateLtUnary
    (n k K : Nat) (tree : UnaryActionTree)
    (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) : AdaptiveCircuit :=
  .unitary (constMinus lengthRP constants carry (n+2))
    ((measuredHighestPositionWrite k K tree control r t path work2At work1At lengthT).seq
      ((measuredHighestPositionWrite k K tree control r t path work1At work2At lengthT).seq
        (.unitary (constMinus lengthRP constants carry (n+2)) .done)))

/-- Coherent refinement to the original strict length update under its shared layout. -/
theorem measuredLenUpdateLtUnary_coherent
    (n k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire)
    (hpositive : 0 < lengthRP.length) (hlength : constants.length = lengthRP.length)
    (hl : SharedLengthBlockLayout k K tree control r t carry path
      work1At work2At lengthRP lengthT constants) :
    CoherentlyImplementsOn
      (measuredLenUpdateLtUnary n k K tree control r t carry path work1At work2At lengthT lengthRP constants)
      (Quantum.run (lenUpdateLtUnary n k K tree control r t carry path work1At work2At lengthT lengthRP constants))
      (fun s => Clean (constants ++ [carry]) s ∧ Clean path s ∧ s t = false) := by
  let Q := fun s : BasisState => Clean path s ∧ s t = false
  let P := fun s : BasisState => Clean (constants ++ [carry]) s ∧ Q s
  let u := constMinus lengthRP constants carry (n+2)
  have hp : ∀ s, P s → Q (Classical.run u s) := by
    intro s hs
    have hh := constMinus_correct lengthRP constants carry (n+2) s hpositive hlength hl.affine hs.1
    have hn : ∀ q, q ∈ path ++ [t] → q ∉ lengthRP := by
      intro q hq hr
      apply List.disjoint_left.mp hl.affineRegisterDisjoint hr
      rcases List.mem_append.mp hq with hpath | ht
      · simp [lengthBlockNonAffineSupport,hpath]
      · have heq := List.mem_singleton.mp ht
        subst q
        simp [lengthBlockNonAffineSupport]
    exact ⟨fun q hq => (hh.2.2 q (hn q (by simp [hq]))).trans (hs.2.1 q hq),
      (hh.2.2 t (hn t (by simp))).trans hs.2.2⟩
  have hfirst := measuredHighestPositionWrite_coherent k K hkK tree control r t path work2At work1At lengthT hl.work2Bits
  have hsecond := measuredHighestPositionWrite_coherent k K hkK tree control r t path work1At work2At lengthT hl.work1Bits
  have htail := shared_seq hsecond (CoherentlyImplementsOn.unitary u (fun _ => True)) (by simp) (by intros; trivial)
  have hbody := shared_seq hfirst htail (by simp)
    (fun s hs => highestPositionWrite_scratch k K hkK tree control r t path work2At work1At lengthT hl.work2Bits s hs)
  have hall := shared_seq (CoherentlyImplementsOn.unitary u P) hbody (by simp [u]) hp
  convert hall using 1; simp [lenUpdateLtUnary,u,List.append_assoc]

/-- Literal shared-scratch length update with two measured writers. -/
def measuredLenUpdateLrpUnary
    (n k K : Nat) (tree : UnaryActionTree)
    (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) : AdaptiveCircuit :=
  .unitary (addConstant lengthT constants carry 3)
    ((measuredRightLengthWrite n k K tree control r t path work1At work2At lengthRP).seq
      ((measuredRightLengthWrite n k K tree control r t path work2At work1At lengthRP).seq
        (.unitary (subConstant lengthT constants carry 3) .done)))

/-- Coherent refinement to the original strict length update under its shared layout. -/
theorem measuredLenUpdateLrpUnary_coherent
    (n k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire)
    (hlength : constants.length = lengthT.length)
    (hl : SharedLengthBlockLayout k K tree control r t carry path
      work1At work2At lengthT lengthRP constants) :
    CoherentlyImplementsOn
      (measuredLenUpdateLrpUnary n k K tree control r t carry path work1At work2At lengthT lengthRP constants)
      (Quantum.run (lenUpdateLrpUnary n k K tree control r t carry path work1At work2At lengthT lengthRP constants))
      (fun s => Clean (constants ++ [carry]) s ∧ Clean path s ∧ s t = false) := by
  let Q := fun s : BasisState => Clean path s ∧ s t = false
  let P := fun s : BasisState => Clean (constants ++ [carry]) s ∧ Q s
  let u := addConstant lengthT constants carry 3
  have hp : ∀ s, P s → Q (Classical.run u s) := by
    intro s hs
    have hh := addConstant_correct lengthT constants carry 3 s hlength hl.affine hs.1
    have hn : ∀ q, q ∈ path ++ [t] → q ∉ lengthT := by
      intro q hq hr
      apply List.disjoint_left.mp hl.affineRegisterDisjoint hr
      rcases List.mem_append.mp hq with hpath | ht
      · simp [lengthBlockNonAffineSupport,hpath]
      · have heq := List.mem_singleton.mp ht
        subst q
        simp [lengthBlockNonAffineSupport]
    exact ⟨fun q hq => (hh.2.2 q (hn q (by simp [hq]))).trans (hs.2.1 q hq),
      (hh.2.2 t (hn t (by simp))).trans hs.2.2⟩
  have hfirst := measuredRightLengthWrite_coherent n k K hkK tree control r t path work1At work2At lengthRP hl.work1Bits
  have hsecond := measuredRightLengthWrite_coherent n k K hkK tree control r t path work2At work1At lengthRP hl.work2Bits
  have htail := shared_seq hsecond (CoherentlyImplementsOn.unitary (subConstant lengthT constants carry 3) (fun _ => True)) (by simp) (by intros; trivial)
  have hbody := shared_seq hfirst htail (by simp)
    (fun s hs => rightLengthWrite_scratch n k K hkK tree control r t path work1At work2At lengthRP hl.work1Bits s hs)
  have hall := shared_seq (CoherentlyImplementsOn.unitary u P) hbody (by simp [u]) hp
  convert hall using 1; simp [lenUpdateLrpUnary,u,List.append_assoc]


/-- Every emitted gate and measured branch is physically well formed. -/
theorem measuredLenUpdateLtUnary_wellFormed
    (n k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire)
    (hlength : constants.length = lengthRP.length)
    (hl : SharedLengthBlockLayout k K tree control r t carry path
      work1At work2At lengthRP lengthT constants) :
    (measuredLenUpdateLtUnary n k K tree control r t carry path work1At work2At lengthT lengthRP constants).WellFormed := by
  exact ⟨constMinus_wellFormed lengthRP constants carry (n+2) hlength hl.affine,
    (measuredHighestPositionWrite_wellFormed k K hkK tree control r t path work2At work1At lengthT hl.work2Bits).seq
      ((measuredHighestPositionWrite_wellFormed k K hkK tree control r t path work1At work2At lengthT hl.work1Bits).seq
        ⟨constMinus_wellFormed lengthRP constants carry (n+2) hlength hl.affine, trivial⟩)⟩

/-- The two measured writers contribute 24M−16 Toffolis; constant arithmetic is counted literally. -/
theorem measuredLenUpdateLtUnary_toffoli
    (n k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire)
    (hl : tree.Layout control path) (hlabels : tree.labels = zeroMapLabels k K) :
    (primitiveResources (measuredLenUpdateLtUnary n k K tree control r t carry path work1At work2At lengthT lengthRP constants)).toffoli =
      eeaToffoliCount (constMinus lengthRP constants carry (n+2)) + eeaToffoliCount (constMinus lengthRP constants carry (n+2)) + (24*(K+1-k)-16) := by
  rw [measuredLenUpdateLtUnary,primitiveResources_unitary_HPFree _ _ (by simp),
    primitiveResources_seq,primitiveResources_seq,primitiveResources_unitary_HPFree _ _ (by simp)]
  simp only [PrimitiveResources.add]
  rw [measuredHighestPositionWrite_toffoli k K hkK tree control r t path work2At work1At lengthT hl hlabels,
    measuredHighestPositionWrite_toffoli k K hkK tree control r t path work1At work2At lengthT hl hlabels]
  simp only [primitiveResources, gidneyToffoliCount, gidneyGateCount]
  omega

/-- Every emitted gate and measured branch is physically well formed. -/
theorem measuredLenUpdateLrpUnary_wellFormed
    (n k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire)
    (hlength : constants.length = lengthT.length)
    (hl : SharedLengthBlockLayout k K tree control r t carry path
      work1At work2At lengthT lengthRP constants) :
    (measuredLenUpdateLrpUnary n k K tree control r t carry path work1At work2At lengthT lengthRP constants).WellFormed := by
  exact ⟨addConstant_wellFormed lengthT constants carry 3 hlength hl.affine,
    (measuredRightLengthWrite_wellFormed n k K hkK tree control r t path work1At work2At lengthRP hl.work1Bits).seq
      ((measuredRightLengthWrite_wellFormed n k K hkK tree control r t path work2At work1At lengthRP hl.work2Bits).seq
        ⟨subConstant_wellFormed lengthT constants carry 3 hlength hl.affine, trivial⟩)⟩

/-- The two measured writers contribute 24M−16 Toffolis; constant arithmetic is counted literally. -/
theorem measuredLenUpdateLrpUnary_toffoli
    (n k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire)
    (hl : tree.Layout control path) (hlabels : tree.labels = zeroMapLabels k K) :
    (primitiveResources (measuredLenUpdateLrpUnary n k K tree control r t carry path work1At work2At lengthT lengthRP constants)).toffoli =
      eeaToffoliCount (addConstant lengthT constants carry 3) + eeaToffoliCount (subConstant lengthT constants carry 3) + (24*(K+1-k)-16) := by
  rw [measuredLenUpdateLrpUnary,primitiveResources_unitary_HPFree _ _ (by simp),
    primitiveResources_seq,primitiveResources_seq,primitiveResources_unitary_HPFree _ _ (by simp)]
  simp only [PrimitiveResources.add]
  rw [measuredRightLengthWrite_toffoli n k K hkK tree control r t path work1At work2At lengthRP hl hlabels,
    measuredRightLengthWrite_toffoli n k K hkK tree control r t path work2At work1At lengthRP hl hlabels]
  simp only [primitiveResources, gidneyToffoliCount, gidneyGateCount]
  omega
end
end ShorECDLP.Paper2607_13816
