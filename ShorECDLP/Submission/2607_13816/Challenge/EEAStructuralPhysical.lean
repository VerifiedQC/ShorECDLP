import ShorECDLP.Submission.«2607_13816».Challenge.EEACenterPhysical
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem vchainTailProgram_wellFormed (n : Nat) (controls : List Wire) (acc target : Wire)
    (scratch : List Wire) (start : Nat)
    (h : (mcxVChainTailAdaptive acc controls target scratch).WellFormed) :
    (vchainTailProgram n controls acc target scratch start).2.WellFormed := by
  induction controls generalizing acc scratch start with
  | nil => trivial
  | cons control controls ih =>
    cases controls with
    | nil => exact literalProgram_wellFormed _ h.1
    | cons next controls =>
      cases scratch with
      | nil => trivial
      | cons work scratch =>
        have hs := adaptive_seq_wellFormed_parts _ _ h.2
        apply prependCompiled_wellFormed
        · exact h.1
        · apply appendCompiled_wellFormed
          · exact ih work scratch start hs.1
          · apply andEraseProgram_wellFormed
            have hg := h.1 (.CCX control acc work) (by simp)
            exact hg.1

theorem vchainProgram_wellFormed (n start : Nat) (controls : List Wire) (target : Wire)
    (scratch : List Wire) (h : (mcxVChainAdaptive controls target scratch).WellFormed) :
    (vchainProgram n start controls target scratch).2.WellFormed := by
  cases controls with
  | nil => exact literalProgram_wellFormed _ h.1
  | cons first rest =>
    cases rest with
    | nil => exact literalProgram_wellFormed _ h.1
    | cons second rest => exact vchainTailProgram_wellFormed _ _ _ _ _ _ h

attribute [local irreducible] vchainProgram

theorem rippleMajProgram_wellFormed (n start : Nat) (control target addend carry scratch : Wire)
    (h : (controlledMajAdaptive control target addend carry scratch).WellFormed) :
    (rippleMajProgram n start control target addend carry scratch).2.WellFormed := by
  unfold rippleMajProgram
  exact prependCompiled_wellFormed _ _ h.1 (vchainProgram_wellFormed _ _ _ _ _ h.2)

theorem rippleUmaInvProgram_wellFormed (n start : Nat) (control target addend carry scratch : Wire)
    (h : (controlledUmaInvAdaptive control target addend carry scratch).WellFormed) :
    (rippleUmaInvProgram n start control target addend carry scratch).2.WellFormed := by
  unfold rippleUmaInvProgram
  exact prependCompiled_wellFormed _ _ h.1 (vchainProgram_wellFormed _ _ _ _ _ h.2)

theorem rippleUmaProgram_wellFormed (n start : Nat) (control target addend carry scratch : Wire)
    (h : (controlledUmaAdaptive control target addend carry scratch).WellFormed) :
    (rippleUmaProgram n start control target addend carry scratch).2.WellFormed := by
  unfold rippleUmaProgram
  have hs := adaptive_seq_wellFormed_parts _ _ h
  exact appendCompiled_wellFormed _ _ (vchainProgram_wellFormed _ _ _ _ _ hs.1)
    (literalProgram_wellFormed _ hs.2.1)

theorem rippleMajInvProgram_wellFormed (n start : Nat) (control target addend carry scratch : Wire)
    (h : (controlledMajInvAdaptive control target addend carry scratch).WellFormed) :
    (rippleMajInvProgram n start control target addend carry scratch).2.WellFormed := by
  unfold rippleMajInvProgram
  have hs := adaptive_seq_wellFormed_parts _ _ h
  exact appendCompiled_wellFormed _ _ (vchainProgram_wellFormed _ _ _ _ _ hs.1)
    (literalProgram_wellFormed _ hs.2.1)

theorem rippleFirstProgram_wellFormed (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire)
    (h : (rippleFirstCellAdaptive mode control target addend carry scratch).WellFormed) :
    (rippleFirstProgram n start mode control target addend carry scratch).2.WellFormed := by
  cases mode with
  | add => exact rippleMajProgram_wellFormed _ _ _ _ _ _ _ h
  | sub => exact rippleUmaInvProgram_wellFormed _ _ _ _ _ _ _ h

theorem rippleSecondProgram_wellFormed (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire)
    (h : (rippleSecondCellAdaptive mode control target addend carry scratch).WellFormed) :
    (rippleSecondProgram n start mode control target addend carry scratch).2.WellFormed := by
  cases mode with
  | add => exact rippleUmaProgram_wellFormed _ _ _ _ _ _ _ h
  | sub => exact rippleMajInvProgram_wellFormed _ _ _ _ _ _ _ h


theorem sequenceCircuit_wellFormed_members (sources : List AdaptiveCircuit)
    (h : (sequenceCircuit sources).WellFormed) : ∀ source ∈ sources, source.WellFormed := by
  induction sources with
  | nil => simp
  | cons source rest ih =>
    have hs := adaptive_seq_wellFormed_parts source (sequenceCircuit rest) h
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hs.1
    · exact ih hs.2 c hc

theorem phaseSegments_wellFormed (n : Nat) (r : PhaseUpdateRegisters) (shift : Wire) (core : Circuit)
    (h : (sequenceCircuit (phaseSources r shift core)).WellFormed) :
    ∀ seg ∈ phaseSegments n r shift core, ∀ start, (seg start).2.WellFormed := by
  have hs := sequenceCircuit_wellFormed_members _ h
  have ha := hs (mcxVChainAdaptive (r.withShiftEpoch shift).lengthQ (r.withShiftEpoch shift).zeroQ (r.withShiftEpoch shift).equalityScratch) (by simp [phaseSources])
  have hb := hs (mcxVChainAdaptive (r.withShiftEpoch shift).lengthRPrime (r.withShiftEpoch shift).zeroRPrime (r.withShiftEpoch shift).equalityScratch) (by simp [phaseSources])
  have hc := hs (mcxVChainAdaptive (r.withShiftEpoch shift).lengthS (r.withShiftEpoch shift).zeroS (r.withShiftEpoch shift).equalityScratch) (by simp [phaseSources])
  have hg := (hs (.unitary core .done) (by simp [phaseSources])).1
  intro seg hm start
  simp only [phaseSegments,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact vchainProgram_wellFormed _ _ _ _ _ ha
    | exact vchainProgram_wellFormed _ _ _ _ _ hb
    | exact vchainProgram_wellFormed _ _ _ _ _ hc
    | exact literalProgram_wellFormed _ hg
    | exact literalProgram_wellFormed _ (by simp [CircuitWellFormed,Gate.WellFormed])

theorem phaseProgram_wellFormed (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire)
    (h : (phaseUpdateEpochAdaptive r shift).WellFormed) : (phaseProgram n start r shift).2.WellFormed := by
  apply sequenceProgram_wellFormed
  apply phaseSegments_wellFormed
  rwa [phaseSources_forward]

theorem phaseInverseProgram_wellFormed (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire)
    (h : (phaseUpdateEpochInverseAdaptive r shift).WellFormed) : (phaseInverseProgram n start r shift).2.WellFormed := by
  apply sequenceProgram_wellFormed
  apply phaseSegments_wellFormed
  rwa [phaseSources_inverse]


theorem zeroEraseProgram_wellFormed (n start : Nat) (a b w : Wire) (hab : a ≠ b) :
    (zeroEraseProgram n start a b w).2.WellFormed := by
  apply prependCompiled_wellFormed
  · simp [CircuitWellFormed,Gate.WellFormed]
  · exact appendCompiled_wellFormed _ _ (andEraseProgram_wellFormed _ _ _ _ _ hab)
      (literalProgram_wellFormed _ (by simp [CircuitWellFormed,Gate.WellFormed]))

theorem unaryProgram_wellFormed (n : Nat) (order : UnaryOrder)
    (leaf : Nat → Wire → (start : Nat) → (count : Nat) × Straight n start (start+count))
    (source : Nat → Wire → AdaptiveCircuit)
    (hleaf : ∀ label control start, (source label control).WellFormed → (leaf label control start).2.WellFormed)
    (tree : UnaryActionTree) (control : Wire) (paths : List Wire) (start : Nat)
    (h : (unaryAdaptiveAction order source tree control paths).WellFormed) :
    (unaryProgram n order leaf tree control paths start).2.WellFormed := by
  let WF := fun (start : Nat) (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF start _
  induction tree generalizing control paths start with
  | leaf label =>
    simp only [unaryProgram]
    exact hleaf label control start h
  | node bit zero one ihz iho =>
    cases paths with
    | nil => simp only [unaryProgram]; trivial
    | cons path rest =>
      cases order with
      | inc =>
        have hs := adaptive_seq_wellFormed_parts _ _ h.2
        have ht := adaptive_seq_wellFormed_parts _ _ hs.2.2
        have hab := (h.1 (.CCX control bit path) (by simp [computeZeroAnd])).1
        simp only [unaryProgram]
        apply prependCompiled_wellFormed _ _ h.1
        apply appendCompiled_wellFormed _ _ (ihz _ _ _ hs.1)
        apply prependCompiled_wellFormed _ _ hs.2.1
        apply appendCompiled_wellFormed _ _ (iho _ _ _ ht.1)
        exact prependCompiled_wellFormed _ _ ht.2.1 (zeroEraseProgram_wellFormed _ _ _ _ _ hab)
      | dec =>
        have hs := adaptive_seq_wellFormed_parts _ _ h.2.2
        have ht := adaptive_seq_wellFormed_parts _ _ hs.2.2
        have hab := (h.1 (.CCX control bit path) (by simp [computeZeroAnd])).1
        simp only [unaryProgram]
        apply prependCompiled_wellFormed _ _ h.1
        apply prependCompiled_wellFormed _ _ h.2.1
        apply appendCompiled_wellFormed _ _ (iho _ _ _ hs.1)
        apply prependCompiled_wellFormed _ _ hs.2.1
        exact appendCompiled_wellFormed _ _ (ihz _ _ _ ht.1) (zeroEraseProgram_wellFormed _ _ _ _ _ hab)


attribute [local irreducible] rippleFirstProgram rippleSecondProgram

theorem coefficientFirstProgram_wellFormed (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire)
    (h : (coefficientPrefixFirstLeafAdaptive r k K mode target label control).WellFormed) :
    (coefficientFirstProgram n start r k K mode target label control).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  exact appendCompiled_wellFormed _ _ (rippleFirstProgram_wellFormed _ _ _ _ _ _ _ _ hs.1)
    (literalProgram_wellFormed _ hs.2.1)

theorem coefficientSecondProgram_wellFormed (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire)
    (h : (coefficientPrefixSecondLeafAdaptive r k K mode target label control).WellFormed) :
    (coefficientSecondProgram n start r k K mode target label control).2.WellFormed :=
  prependCompiled_wellFormed _ _ h.1 (rippleSecondProgram_wellFormed _ _ _ _ _ _ _ _ h.2)

attribute [local irreducible] coefficientFirstProgram coefficientSecondProgram

theorem coefficientProgram_wellFormed (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (h : (coefficientPrefixAdaptive r k K mode signUpdate target).WellFormed) :
    (coefficientProgram n start r k K mode signUpdate target).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  have ht := adaptive_seq_wellFormed_parts _ _ hs.2.2
  unfold coefficientProgram
  apply prependCompiled_wellFormed _ _ h.1
  apply appendCompiled_wellFormed
  · exact unaryProgram_wellFormed _ _ _ _
      (fun label control cursor h => coefficientFirstProgram_wellFormed n cursor r k K mode target label control h) _ _ _ _ hs.1
  · apply prependCompiled_wellFormed _ _ hs.2.1
    apply appendCompiled_wellFormed
    · exact unaryProgram_wellFormed _ _ _ _
        (fun label control cursor h => coefficientSecondProgram_wellFormed n cursor r k K mode target label control h) _ _ _ _ ht.1
    · exact literalProgram_wellFormed _ ht.2.1

theorem coefficientInverseProgram_wellFormed (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (h : (coefficientPrefixInverseAdaptive r k K mode signUpdate target).WellFormed) :
    (coefficientInverseProgram n start r k K mode signUpdate target).2.WellFormed :=
  coefficientProgram_wellFormed _ _ _ _ _ _ _ _ h
end ShorECDLP.Paper2607_13816.ChallengeMigration
