import ShorECDLP.Submission.«2607_13816».Challenge.EEAIntervalPhysical
/-! Structural preservation of gate validity. Generic lemmas assume source syntax validity;
production wrapper lemmas discharge that premise using the fixed source layouts. -/
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

theorem zeroCellProgram_wellFormed (n start : Nat) (base : Bool) (r bit guard target temporary : Wire)
    (h : (measuredZeroCell base r bit guard target temporary).WellFormed) :
    (zeroCellProgram n start base r bit guard target temporary).2.WellFormed := by
  apply prependCompiled_wellFormed _ _ h.1
  exact andEraseProgram_wellFormed _ _ _ _ _
    (h.1 (.CCX r bit temporary) (by simp [measuredZeroPrefix])).1

theorem upperForwardLeafProgram_wellFormed (n start : Nat) (k K : Nat) (control temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire)
    (h : (measuredUpperForwardLeaf k K control temporary bitAt dirtyAt label r).WellFormed) :
    (upperForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold upperForwardLeafProgram
  unfold measuredUpperForwardLeaf at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · split <;> rename_i hd <;> (first | rw [if_pos hd] at h | rw [if_neg hd] at h)
    all_goals exact zeroCellProgram_wellFormed _ _ _ _ _ _ _ _ h
  · trivial

theorem upperReverseLeafProgram_wellFormed (n start : Nat) (k K : Nat) (temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire)
    (h : (measuredUpperReverseLeaf k K temporary bitAt dirtyAt label r).WellFormed) :
    (upperReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold upperReverseLeafProgram
  unfold measuredUpperReverseLeaf at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · exact zeroCellProgram_wellFormed _ _ _ _ _ _ _ _ h
  · trivial

theorem lowerForwardLeafProgram_wellFormed (n start : Nat) (k K : Nat) (control temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire)
    (h : (measuredLowerForwardLeaf k K control temporary bitAt dirtyAt label r).WellFormed) :
    (lowerForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold lowerForwardLeafProgram
  unfold measuredLowerForwardLeaf at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · split <;> rename_i hd <;> (first | rw [if_pos hd] at h | rw [if_neg hd] at h)
    all_goals exact zeroCellProgram_wellFormed _ _ _ _ _ _ _ _ h
  · trivial

theorem lowerReverseLeafProgram_wellFormed (n start : Nat) (k K : Nat) (temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire)
    (h : (measuredLowerReverseLeaf k K temporary bitAt dirtyAt label r).WellFormed) :
    (lowerReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold lowerReverseLeafProgram
  unfold measuredLowerReverseLeaf at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · exact zeroCellProgram_wellFormed _ _ _ _ _ _ _ _ h
  · trivial

theorem rangeLeafProgram_wellFormed (n : Nat) (after : Bool) (r : Wire)
    (leaf : Nat → Wire → FixedSegment n) (source : Nat → Wire → AdaptiveCircuit)
    (hl : ∀ label control start, (source label control).WellFormed → (leaf label control start).2.WellFormed)
    (label : Nat) (dynamic : Wire) (start : Nat)
    (h : (measuredRangeLeaf after r source label dynamic).WellFormed) :
    (rangeLeafProgram n after r leaf label dynamic start).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold rangeLeafProgram
  unfold measuredRangeLeaf at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _ (hl _ _ _ hs.1) (literalProgram_wellFormed _ hs.2.1)
  · exact prependCompiled_wellFormed _ _ h.1 (hl _ _ _ h.2)

theorem rangeScanProgram_wellFormed (n : Nat) (after : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control r : Wire) (path : List Wire)
    (leaf : Nat → Wire → FixedSegment n) (source : Nat → Wire → AdaptiveCircuit)
    (hl : ∀ label control start, (source label control).WellFormed → (leaf label control start).2.WellFormed)
    (start : Nat) (h : (measuredRangeScan after order tree control r path source).WellFormed) :
    (rangeScanProgram n after order tree control r path leaf start).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold rangeScanProgram
  unfold measuredRangeScan at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · apply prependCompiled_wellFormed _ _ h.1
    exact unaryProgram_wellFormed n order _ _ (rangeLeafProgram_wellFormed n true r leaf source hl) tree control path start h.2
  · have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _
      (unaryProgram_wellFormed n order _ _ (rangeLeafProgram_wellFormed n false r leaf source hl) tree control path start hs.1)
      (literalProgram_wellFormed _ hs.2.1)

theorem upperMapProgram_wellFormed (n : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (start : Nat)
    (h : (measuredUpperZeroMap k K tree control r t path bitAt dirtyAt).WellFormed) :
    (upperMapProgram n k K tree control r t path bitAt dirtyAt start).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  unfold upperMapProgram
  apply appendCompiled_wellFormed
  · exact rangeScanProgram_wellFormed _ _ _ _ _ _ _ _ _
      (fun label dynamic cursor hh => upperForwardLeafProgram_wellFormed n cursor k K control t bitAt dirtyAt label dynamic hh) _ hs.1
  · exact rangeScanProgram_wellFormed _ _ _ _ _ _ _ _ _
      (fun label dynamic cursor hh => upperReverseLeafProgram_wellFormed n cursor k K t bitAt dirtyAt label dynamic hh) _ hs.2

theorem lowerMapProgram_wellFormed (n : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (start : Nat)
    (h : (measuredLowerZeroMap k K tree control r t path bitAt dirtyAt).WellFormed) :
    (lowerMapProgram n k K tree control r t path bitAt dirtyAt start).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  unfold lowerMapProgram
  apply appendCompiled_wellFormed
  · exact rangeScanProgram_wellFormed _ _ _ _ _ _ _ _ _
      (fun label dynamic cursor hh => lowerForwardLeafProgram_wellFormed n cursor k K control t bitAt dirtyAt label dynamic hh) _ hs.1
  · exact rangeScanProgram_wellFormed _ _ _ _ _ _ _ _ _
      (fun label dynamic cursor hh => lowerReverseLeafProgram_wellFormed n cursor k K t bitAt dirtyAt label dynamic hh) _ hs.2

theorem upperWriterProgram_wellFormed (n : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat)
    (h : (measuredHighestPositionWrite k K tree control r t path bitAt dirtyAt targets).WellFormed) :
    (upperWriterProgram n k K tree control r t path bitAt dirtyAt targets start).2.WellFormed := by
  unfold measuredHighestPositionWrite at h
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  unfold upperWriterProgram
  apply prependCompiled_wellFormed _ _ h.1
  apply appendCompiled_wellFormed
  · exact upperMapProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hs.1
  · exact prependCompiled_wellFormed _ _ hs.2.1 (upperMapProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hs.2.2)

theorem lowerWriterProgram_wellFormed (n : Nat) (width : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat)
    (h : (measuredRightLengthWrite width k K tree control r t path bitAt dirtyAt targets).WellFormed) :
    (lowerWriterProgram n width k K tree control r t path bitAt dirtyAt targets start).2.WellFormed := by
  unfold measuredRightLengthWrite at h
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  unfold lowerWriterProgram
  apply prependCompiled_wellFormed _ _ h.1
  apply appendCompiled_wellFormed
  · exact lowerMapProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hs.1
  · exact prependCompiled_wellFormed _ _ hs.2.1 (lowerMapProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hs.2.2)

theorem ltUpdateProgram_wellFormed (n : Nat) (width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat)
    (h : (measuredLenUpdateLtUnary width k K tree control r t carry path work1At work2At lengthT lengthRP constants).WellFormed) :
    (ltUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2.WellFormed := by
  unfold measuredLenUpdateLtUnary at h
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  unfold ltUpdateProgram
  have ht := adaptive_seq_wellFormed_parts _ _ hs.2
  apply surroundCompiled_wellFormed _ _ _ h.1 ht.2.1
  exact appendCompiled_wellFormed _ _ (upperWriterProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ hs.1)
    (upperWriterProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ ht.1)

theorem lrpUpdateProgram_wellFormed (n : Nat) (width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat)
    (h : (measuredLenUpdateLrpUnary width k K tree control r t carry path work1At work2At lengthT lengthRP constants).WellFormed) :
    (lrpUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2.WellFormed := by
  unfold measuredLenUpdateLrpUnary at h
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  unfold lrpUpdateProgram
  have ht := adaptive_seq_wellFormed_parts _ _ hs.2
  apply surroundCompiled_wellFormed _ _ _ h.1 ht.2.1
  exact appendCompiled_wellFormed _ _ (lowerWriterProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ hs.1)
    (lowerWriterProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ ht.1)

theorem upperEndProgram_wellFormed (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows)
    (h : (measuredEndUpper r width w).WellFormed) :
    (upperEndProgram n start r width w).2.WellFormed := by
  exact ltUpdateProgram_wellFormed n width w.k4 w.K4 (r.upperTree w) r.control (r.rangeAccumulator w.k4 w.K4) (r.temporary w.k4 w.K4) r.carry (r.path w.k4 w.K4) r.work1At r.work2At r.lengthT r.lengthRP r.constants start h

theorem lowerEndProgram_wellFormed (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows)
    (h : (measuredEndLower r width w).WellFormed) :
    (lowerEndProgram n start r width w).2.WellFormed := by
  exact lrpUpdateProgram_wellFormed n width w.k5 (w.K5Decode width) (r.lowerTree width w) r.control (r.rangeAccumulator w.k5 (w.K5Decode width)) (r.temporary w.k5 (w.K5Decode width)) r.carry (r.path w.k5 (w.K5Decode width)) r.work1At r.work2At r.lengthT r.lengthRP r.constants start h

theorem endProgram_wellFormed (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows)
    (h : (measuredEndIteration r width w).WellFormed) :
    (endProgram n start r width w).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  unfold endProgram
  exact prependCompiled_wellFormed _ _ h.1
    (appendCompiled_wellFormed _ _ (upperEndProgram_wellFormed _ _ _ _ _ hs.1)
      (lowerEndProgram_wellFormed _ _ _ _ _ hs.2))

theorem endInverseProgram_wellFormed (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows)
    (h : (measuredEndIterationInverse r width w).WellFormed) :
    (endInverseProgram n start r width w).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  have ht := adaptive_seq_wellFormed_parts _ _ hs.2
  unfold endInverseProgram
  exact appendCompiled_wellFormed _ _ (lowerEndProgram_wellFormed _ _ _ _ _ hs.1)
    (appendCompiled_wellFormed _ _ (upperEndProgram_wellFormed _ _ _ _ _ ht.1)
      (literalProgram_wellFormed _ ht.2.1))

theorem hProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (h : (measuredBlockHForward r width T).WellFormed) :
    (hProgram n start r width T).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold hProgram
  unfold measuredBlockHForward at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · have hs := adaptive_seq_wellFormed_parts _ _ h.2
    exact surroundCompiled_wellFormed _ _ _ h.1 hs.2.1 (endProgram_wellFormed _ _ _ _ _ hs.1)
  · trivial

theorem hInverseProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (h : (measuredBlockHInverse r width T).WellFormed) :
    (hInverseProgram n start r width T).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold hInverseProgram
  unfold measuredBlockHInverse at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · have hs := adaptive_seq_wellFormed_parts _ _ h.2
    exact surroundCompiled_wellFormed _ _ _ h.1 hs.2.1 (endInverseProgram_wellFormed _ _ _ _ _ hs.1)
  · trivial

attribute [local irreducible] remainderBlockProgram coefficientBlockProgram phaseProgram phaseInverseProgram coefficientInverseProgram intervalInverseProgram
theorem measuredStepProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (h : (measuredIndexedStep r width T).WellFormed) :
    (measuredStepProgram n start r width T).2.WellFormed := by
  unfold measuredStepProgram
  rw [← measuredStepSources_eq r width T] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold measuredStepSegments measuredStepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact remainderBlockProgram_wellFormed n cursor r width (certifiedActiveWindows width T).remainder hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientBlockProgram_wellFormed n cursor r width (certifiedActiveWindows width T).coefficient hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact phaseProgram_wellFormed n cursor r.phaseUpdate r.shiftEpoch hh
  · intro cursor hh
    exact hProgram_wellFormed n cursor r width T hh

theorem measuredInverseStepProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (T : Nat)
    (h : (measuredIndexedStepInverse r 256 T).WellFormed) :
    (measuredInverseStepProgram n start r T).2.WellFormed := by
  unfold measuredInverseStepProgram
  rw [← measuredInverseStepSources_eq r T] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold measuredInverseStepSegments measuredInverseStepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))))
  · intro cursor hh
    exact hInverseProgram_wellFormed n cursor r 256 T hh
  · intro cursor hh
    exact phaseInverseProgram_wellFormed n cursor r.phaseUpdate r.shiftEpoch hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientInverseProgram_wellFormed n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .add true .work2 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientInverseProgram_wellFormed n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .sub false .work2 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact intervalInverseProgram_wellFormed n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .add false .work1 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact intervalInverseProgram_wellFormed n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .sub true .work1 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1

attribute [local irreducible] measuredStepProgram measuredInverseStepProgram measuredIndexedStep measuredIndexedStepInverse

theorem measuredScheduleProgram_wellFormed (n : Nat) (r : IndexedStepRegisters) (width count first start : Nat)
    (h : (measuredIndexedSchedule r width first count).WellFormed) :
    (measuredScheduleProgram n r width count first start).2.WellFormed := by
  induction count generalizing first start with
  | zero => trivial
  | succ count ih =>
    have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _ (measuredStepProgram_wellFormed _ _ _ _ _ hs.1)
      (ih _ _ hs.2)

theorem measuredInverseScheduleProgram_wellFormed (n : Nat) (r : IndexedStepRegisters) (count first start : Nat)
    (h : (measuredIndexedScheduleInverse r 256 first count).WellFormed) :
    (measuredInverseScheduleProgram n r count first start).2.WellFormed := by
  induction count generalizing first start with
  | zero => trivial
  | succ count ih =>
    have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _ (ih _ _ hs.1)
      (measuredInverseStepProgram_wellFormed _ _ _ _ hs.2)

attribute [local irreducible] measuredScheduleProgram measuredInverseScheduleProgram measuredIndexedSchedule measuredIndexedScheduleInverse

theorem measuredEEAForwardProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters)
    (h : (secp256k1MeasuredEEAForward r).WellFormed) : (measuredEEAForwardProgram n start r).2.WellFormed :=
  measuredScheduleProgram_wellFormed _ _ _ _ _ _ h

theorem measuredEEAReverseProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters)
    (h : (secp256k1MeasuredEEAReverse r).WellFormed) : (measuredEEAReverseProgram n start r).2.WellFormed :=
  measuredInverseScheduleProgram_wellFormed _ _ _ _ _ h


attribute [local irreducible] measuredEEAForwardProgram measuredEEAReverseProgram preprocessProgram unpreprocessProgram productionParityProgram
  secp256k1MeasuredEEAForward secp256k1MeasuredEEAReverse eeaPreprocess eeaUnpreprocess secp256k1EEAParityCorrection

theorem measuredForwardWrapperProgram_wellFormed (n start : Nat) : (measuredForwardWrapperProgram n start).2.WellFormed := by
  have h := secp256k1MeasuredEEAForwardWrapper_wellFormed
  unfold measuredForwardWrapperProgram
  rw [← measuredForwardWrapperSources_eq ] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold measuredForwardWrapperSegments measuredForwardWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor hh
    exact preprocessProgram_wellFormed n cursor
  · intro cursor hh
    exact measuredEEAForwardProgram_wellFormed n cursor indexedStepProductionRegisters hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact productionParityProgram_wellFormed n cursor
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1

theorem measuredReverseWrapperProgram_wellFormed (n start : Nat) : (measuredReverseWrapperProgram n start).2.WellFormed := by
  have h := secp256k1MeasuredEEAReverseWrapper_wellFormed
  unfold measuredReverseWrapperProgram
  rw [← measuredReverseWrapperSources_eq ] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold measuredReverseWrapperSegments measuredReverseWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact productionParityProgram_wellFormed n cursor
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact measuredEEAReverseProgram_wellFormed n cursor indexedStepProductionRegisters hh
  · intro cursor hh
    exact unpreprocessProgram_wellFormed n cursor
theorem measuredForwardDataBankProgram_wellFormed (n start : Nat) :
    (measuredForwardDataBankProgram n start).2.WellFormed :=
  (relabelCompiled_wellFormed eeaWorkspaceExchange _).2 (measuredForwardWrapperProgram_wellFormed n start)

theorem measuredReverseDataBankProgram_wellFormed (n start : Nat) :
    (measuredReverseDataBankProgram n start).2.WellFormed :=
  (relabelCompiled_wellFormed eeaWorkspaceExchange _).2 (measuredReverseWrapperProgram_wellFormed n start)

end ShorECDLP.Paper2607_13816.ChallengeMigration
