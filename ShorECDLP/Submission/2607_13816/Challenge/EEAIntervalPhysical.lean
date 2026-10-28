import ShorECDLP.Submission.«2607_13816».Challenge.EEAStructuralPhysical
/-! Structural preservation of gate validity. Generic lemmas assume source syntax validity;
production wrapper lemmas discharge that premise using the fixed source layouts. -/
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
attribute [local irreducible] terminalWork1Clear

theorem dualEraseProgram_wellFormed (n start : Nat) (a i x b j y : Wire) (ha : a ≠ i) (hb : b ≠ j) :
    (dualEraseProgram n start a i x b j y).2.WellFormed :=
  appendCompiled_wellFormed _ _ (zeroEraseProgram_wellFormed _ _ _ _ _ hb)
    (zeroEraseProgram_wellFormed _ _ _ _ _ ha)

theorem dualProgram_wellFormed (n : Nat) (order : UnaryOrder)
    (leaf : Nat → Wire → Wire → (start : Nat) → (count : Nat) × Straight n start (start+count))
    (source : Nat → Wire → Wire → AdaptiveCircuit)
    (hleaf : ∀ label a b start, (source label a b).WellFormed → (leaf label a b start).2.WellFormed)
    (tree : DualUnaryActionTree) (a b : Wire) (xs ys : List Wire) (start : Nat)
    (h : (dualUnaryAdaptiveAction order source tree a b xs ys).WellFormed) :
    (dualProgram n order leaf tree a b xs ys start).2.WellFormed := by
  let WF := fun (start : Nat) (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF start _
  induction tree generalizing a b xs ys start with
  | leaf label => simp only [dualProgram]; exact hleaf label a b start h
  | node i j zero one ihz iho =>
    cases xs with
    | nil => simp only [dualProgram]; trivial
    | cons x xs =>
      cases ys with
      | nil => simp only [dualProgram]; trivial
      | cons y ys =>
        cases order with
        | inc =>
          have hs := adaptive_seq_wellFormed_parts _ _ h.2.2
          have ht := adaptive_seq_wellFormed_parts _ _ hs.2.2
          have ha := (h.1 (.CCX a i x) (by simp [computeZeroAnd])).1
          have hb := (h.2.1 (.CCX b j y) (by simp [computeZeroAnd])).1
          simp only [dualProgram]
          apply prependCompiled_wellFormed _ _ h.1
          apply prependCompiled_wellFormed _ _ h.2.1
          apply appendCompiled_wellFormed _ _ (ihz _ _ _ _ _ hs.1)
          apply prependCompiled_wellFormed _ _ hs.2.1
          apply appendCompiled_wellFormed _ _ (iho _ _ _ _ _ ht.1)
          exact prependCompiled_wellFormed _ _ ht.2.1 (dualEraseProgram_wellFormed _ _ _ _ _ _ _ _ ha hb)
        | dec =>
          have hs := adaptive_seq_wellFormed_parts _ _ h.2.2.2
          have ht := adaptive_seq_wellFormed_parts _ _ hs.2.2
          have ha := (h.1 (.CCX a i x) (by simp [computeZeroAnd])).1
          have hb := (h.2.1 (.CCX b j y) (by simp [computeZeroAnd])).1
          simp only [dualProgram]
          apply prependCompiled_wellFormed _ _ h.1
          apply prependCompiled_wellFormed _ _ h.2.1
          apply prependCompiled_wellFormed _ _ h.2.2.1
          apply appendCompiled_wellFormed _ _ (iho _ _ _ _ _ hs.1)
          apply prependCompiled_wellFormed _ _ hs.2.1
          exact appendCompiled_wellFormed _ _ (ihz _ _ _ _ _ ht.1) (dualEraseProgram_wellFormed _ _ _ _ _ _ _ _ ha hb)


theorem equalityProgram_wellFormed (n start : Nat) (register : List Wire) (value : Nat) (flag : Wire)
    (scratch : List Wire)
    (h : (computeEqConstAdaptive register value flag scratch).WellFormed) :
    (equalityProgram n start register value flag scratch).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  exact prependCompiled_wellFormed _ _ h.1
    (appendCompiled_wellFormed _ _ (vchainProgram_wellFormed _ _ _ _ _ hs.1)
      (literalProgram_wellFormed _ hs.2.1))

theorem toggleEqualityProgram_wellFormed (n start : Nat) (root : Wire) (register : List Wire) (value : Nat)
    (acc flag : Wire) (scratch : List Wire)
    (h : (toggleEqConstUnderControlAdaptive root register value acc flag scratch).WellFormed) :
    (toggleEqualityProgram n start root register value acc flag scratch).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  exact appendCompiled_wellFormed _ _ (equalityProgram_wellFormed _ _ _ _ _ _ hs.1)
    (prependCompiled_wellFormed _ _ hs.2.1 (equalityProgram_wellFormed _ _ _ _ _ _ hs.2.2))

theorem intervalFirstProgram_wellFormed (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire)
    (h : (intervalFirstLeafAdaptive mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).WellFormed) :
    (intervalFirstProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  exact prependCompiled_wellFormed _ _ h.1
    (appendCompiled_wellFormed _ _ (rippleFirstProgram_wellFormed _ _ _ _ _ _ _ _ hs.1)
      (literalProgram_wellFormed _ hs.2.1))

theorem intervalSecondProgram_wellFormed (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire)
    (h : (intervalSecondLeafAdaptive mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).WellFormed) :
    (intervalSecondProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  exact prependCompiled_wellFormed _ _ h.1
    (appendCompiled_wellFormed _ _ (rippleSecondProgram_wellFormed _ _ _ _ _ _ _ _ hs.1)
      (literalProgram_wellFormed _ hs.2.1))

theorem topFirstProgram_wellFormed (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire)
    (h : (topSpecialFirstLeafAdaptive mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).WellFormed) :
    (topFirstProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  have ht := adaptive_seq_wellFormed_parts _ _ hs.2
  exact appendCompiled_wellFormed _ _ (toggleEqualityProgram_wellFormed _ _ _ _ _ _ _ _ hs.1)
    (appendCompiled_wellFormed _ _ (rippleFirstProgram_wellFormed _ _ _ _ _ _ _ _ ht.1)
      (toggleEqualityProgram_wellFormed _ _ _ _ _ _ _ _ ht.2))

theorem topSecondProgram_wellFormed (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire)
    (h : (topSpecialSecondLeafAdaptive mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).WellFormed) :
    (topSecondProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  have ht := adaptive_seq_wellFormed_parts _ _ hs.2
  exact appendCompiled_wellFormed _ _ (toggleEqualityProgram_wellFormed _ _ _ _ _ _ _ _ hs.1)
    (appendCompiled_wellFormed _ _ (rippleSecondProgram_wellFormed _ _ _ _ _ _ _ _ ht.1)
      (toggleEqualityProgram_wellFormed _ _ _ _ _ _ _ _ ht.2))


theorem traversalFirstProgram_wellFormed (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire)
    (h : (intervalFirstTraversalAdaptive mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).WellFormed) :
    (traversalFirstProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2.WellFormed := by
  unfold traversalFirstProgram
  apply dualProgram_wellFormed _ _ _ _ ?_ _ _ _ _ _ _ h
  intro label right left cursor hh
  exact intervalFirstProgram_wellFormed n cursor mode topSpecial rightTop leftTop acc (targetAt label) (addendAt label) carry scratch label right left hh

theorem traversalSecondProgram_wellFormed (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire)
    (h : (intervalSecondTraversalAdaptive mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).WellFormed) :
    (traversalSecondProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2.WellFormed := by
  unfold traversalSecondProgram
  apply dualProgram_wellFormed _ _ _ _ ?_ _ _ _ _ _ _ h
  intro label right left cursor hh
  exact intervalSecondProgram_wellFormed n cursor mode topSpecial rightTop leftTop acc (targetAt label) (addendAt label) carry scratch label right left hh


theorem intervalTopFirstProgram_wellFormed (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget)
    (h : (if intervalHasTopSpecial k K then topSpecialFirstLeafAdaptive mode (intervalTopRelative k K) r.lengthS r.lengthQ (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K)) (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control else .unitary [] .done).WellFormed) :
    (intervalTopFirstProgram n start r k K mode target).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold intervalTopFirstProgram
  split
  · rename_i he
    simp only [he,ite_true] at h
    exact topFirstProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  · trivial

theorem intervalTopSecondProgram_wellFormed (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget)
    (h : (if intervalHasTopSpecial k K then topSpecialSecondLeafAdaptive mode (intervalTopRelative k K) r.lengthS r.lengthQ (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K)) (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control else .unitary [] .done).WellFormed) :
    (intervalTopSecondProgram n start r k K mode target).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold intervalTopSecondProgram
  split
  · rename_i he
    simp only [he,ite_true] at h
    exact topSecondProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  · trivial

attribute [local irreducible] intervalTopFirstProgram intervalTopSecondProgram traversalFirstProgram traversalSecondProgram

theorem intervalProgram_wellFormed (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (h : (intervalAddSub r width k K mode signUpdate target).WellFormed) :
    (intervalProgram n start r width k K mode signUpdate target).2.WellFormed := by
  have h0 := adaptive_seq_wellFormed_parts _ _ h
  have h1 := adaptive_seq_wellFormed_parts _ _ h0.2
  have h2 := adaptive_seq_wellFormed_parts _ _ h1.2
  have h3 := adaptive_seq_wellFormed_parts _ _ h2.2
  have h4 := adaptive_seq_wellFormed_parts _ _ h3.2
  have h5 := adaptive_seq_wellFormed_parts _ _ h4.2
  unfold intervalProgram
  apply prependCompiled_wellFormed _ _ h0.1.1
  apply appendCompiled_wellFormed _ _ (intervalTopFirstProgram_wellFormed _ _ _ _ _ _ _ h1.1)
  apply appendCompiled_wellFormed
  · exact traversalFirstProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h2.1
  · apply prependCompiled_wellFormed _ _ h3.1.1
    apply appendCompiled_wellFormed
    · exact traversalSecondProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h4.1
    · exact appendCompiled_wellFormed _ _ (intervalTopSecondProgram_wellFormed _ _ _ _ _ _ _ h5.1)
        (literalProgram_wellFormed _ h5.2.1)


theorem intervalInverseProgram_wellFormed (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (h : (intervalAddSubInverse r width k K mode signUpdate target).WellFormed) :
    (intervalInverseProgram n start r width k K mode signUpdate target).2.WellFormed :=
  intervalProgram_wellFormed _ _ _ _ _ _ _ _ _ h

theorem sequenceProgram_wellFormed_of_source (n start : Nat) (ps : List (FixedSegment n)) (sources : List AdaptiveCircuit)
    (h : (sequenceCircuit sources).WellFormed)
    (hp : List.Forall₂ (fun p source => ∀ start, source.WellFormed → (p start).2.WellFormed) ps sources) :
    (sequenceProgram n ps start).2.WellFormed := by
  induction hp generalizing start with
  | nil => trivial
  | @cons p source ps sources hp hps ih =>
    have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _ (hp _ hs.1) (ih _ hs.2)

attribute [local irreducible] intervalProgram intervalInverseProgram coefficientProgram coefficientInverseProgram
  phaseProgram phaseInverseProgram intervalAddSub intervalAddSubInverse coefficientPrefixAdaptive coefficientPrefixInverseAdaptive
  phaseUpdateEpochAdaptive phaseUpdateEpochInverseAdaptive

theorem remainderBlockProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow)
    (h : (blockBAdaptive r width w).WellFormed) :
    (remainderBlockProgram n start r width w).2.WellFormed := by
  unfold remainderBlockProgram
  rw [← remainderBlockSources_eq r width w] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold remainderBlockSegments remainderBlockSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact intervalProgram_wellFormed n cursor (r.remainder w) width w.start w.stop .sub true .work1 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact intervalProgram_wellFormed n cursor (r.remainder w) width w.start w.stop .add false .work1 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1

theorem coefficientBlockProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow)
    (h : (blockEAdaptive r width w).WellFormed) :
    (coefficientBlockProgram n start r width w).2.WellFormed := by
  unfold coefficientBlockProgram
  rw [← coefficientBlockSources_eq r width w] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold coefficientBlockSegments coefficientBlockSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientProgram_wellFormed n cursor (r.coefficient w) w.start w.stop .sub false .work2 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientProgram_wellFormed n cursor (r.coefficient w) w.start w.stop .add true .work2 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1

attribute [local irreducible] remainderBlockProgram coefficientBlockProgram blockBAdaptive blockEAdaptive

theorem indexedStepProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (h : (indexedStepAdaptive r width T).WellFormed) :
    (indexedStepProgram n start r width T).2.WellFormed := by
  unfold indexedStepProgram
  rw [← indexedStepSources_eq r width T] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold indexedStepSegments indexedStepSources
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
    exact literalProgram_wellFormed _ hh.1

theorem indexedInverseStepProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (T : Nat)
    (h : (indexedStepInverseAdaptive r 256 T).WellFormed) :
    (indexedInverseStepProgram n start r T).2.WellFormed := by
  unfold indexedInverseStepProgram
  rw [← indexedInverseStepSources_eq r T] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold indexedInverseStepSegments indexedInverseStepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))))
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
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


attribute [local irreducible] indexedStepProgram indexedInverseStepProgram indexedStepAdaptive indexedStepInverseAdaptive

theorem scheduleProgram_wellFormed (n : Nat) (r : IndexedStepRegisters) (width count first start : Nat)
    (h : (indexedScheduleAdaptive r width first count).WellFormed) :
    (scheduleProgram n r width count first start).2.WellFormed := by
  induction count generalizing first start with
  | zero => trivial
  | succ count ih =>
    have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _ (indexedStepProgram_wellFormed _ _ _ _ _ hs.1)
      (ih _ _ hs.2)

theorem inverseScheduleProgram_wellFormed (n : Nat) (r : IndexedStepRegisters) (count first start : Nat)
    (h : (indexedScheduleInverseAdaptive r 256 first count).WellFormed) :
    (inverseScheduleProgram n r count first start).2.WellFormed := by
  induction count generalizing first start with
  | zero => trivial
  | succ count ih =>
    have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _ (ih _ _ hs.1)
      (indexedInverseStepProgram_wellFormed _ _ _ _ hs.2)

attribute [local irreducible] scheduleProgram inverseScheduleProgram indexedScheduleAdaptive indexedScheduleInverseAdaptive

theorem eeaForwardProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters)
    (h : (secp256k1EEAForwardAdaptive r).WellFormed) : (eeaForwardProgram n start r).2.WellFormed :=
  scheduleProgram_wellFormed _ _ _ _ _ _ h

theorem eeaReverseProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters)
    (h : (secp256k1EEAReverseAdaptive r).WellFormed) : (eeaReverseProgram n start r).2.WellFormed :=
  inverseScheduleProgram_wellFormed _ _ _ _ _ h


attribute [local irreducible] eeaForwardProgram eeaReverseProgram preprocessProgram unpreprocessProgram productionParityProgram
  secp256k1EEAForwardAdaptive secp256k1EEAReverseAdaptive eeaPreprocess eeaUnpreprocess secp256k1EEAParityCorrection

theorem forwardWrapperProgram_wellFormed (n start : Nat) : (forwardWrapperProgram n start).2.WellFormed := by
  have h := secp256k1EEAForwardWrapper_wellFormed
  unfold forwardWrapperProgram
  rw [← forwardWrapperSources_eq ] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold forwardWrapperSegments forwardWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor hh
    exact preprocessProgram_wellFormed n cursor
  · intro cursor hh
    exact eeaForwardProgram_wellFormed n cursor indexedStepProductionRegisters hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact productionParityProgram_wellFormed n cursor
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1

theorem reverseWrapperProgram_wellFormed (n start : Nat) : (reverseWrapperProgram n start).2.WellFormed := by
  have h := secp256k1EEAReverseWrapper_wellFormed
  unfold reverseWrapperProgram
  rw [← reverseWrapperSources_eq ] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold reverseWrapperSegments reverseWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact productionParityProgram_wellFormed n cursor
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact eeaReverseProgram_wellFormed n cursor indexedStepProductionRegisters hh
  · intro cursor hh
    exact unpreprocessProgram_wellFormed n cursor
end ShorECDLP.Paper2607_13816.ChallengeMigration
