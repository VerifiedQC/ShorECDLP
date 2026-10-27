import ShorECDLP.Submission.«2607_13816».Challenge.DecoderSlots
import ShorECDLP.Submission.«2607_13816».EEA.BlockEPrimitiveCounts
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem sequenceProgram_slots_le (n : Nat) (ps : List (FixedSegment n)) (bounds : List Nat)
    (h : List.Forall₂ (fun p bound => ∀ s, (p s).2.gateSlots ≤ bound) ps bounds) (start : Nat) :
    (sequenceProgram n ps start).2.gateSlots ≤ bounds.sum := by
  induction h generalizing start with
  | nil => exact Nat.zero_le _
  | cons hp hs ih =>
    rw [sequenceProgram,appendCompiled_slots]
    simp only [List.sum_cons]
    exact Nat.add_le_add (hp start) (ih _)

theorem coefficientFirstProgram_slots (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire) :
    (coefficientFirstProgram n start r k K mode target label control).2.gateSlots ≤ 17 := by
  have h := rippleFirstProgram_slots n start mode (r.accumulator k K) (r.targetAt target k label)
    (r.addendAt target k label) (r.carry k K) (r.cellScratch k K)
  simp only [coefficientFirstProgram,appendCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  omega

theorem coefficientSecondProgram_slots (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire) :
    (coefficientSecondProgram n start r k K mode target label control).2.gateSlots ≤ 17 := by
  have h := rippleSecondProgram_slots n start mode (r.accumulator k K) (r.targetAt target k label)
    (r.addendAt target k label) (r.carry k K) (r.cellScratch k K)
  simp only [coefficientSecondProgram,prependCompiled_slots,List.length_cons,List.length_nil]
  omega

theorem coefficientProgram_slots (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) :
    (coefficientProgram n start r k K mode signUpdate target).2.gateSlots ≤
      54*(coefficientPrefixTree r k K).internalNodes+37 := by
  have hf (s : Nat) := unaryProgram_slots_le n .inc
    (fun label control cursor => coefficientFirstProgram n cursor r k K mode target label control)
    17 (fun label control cursor => coefficientFirstProgram_slots n cursor r k K mode target label control)
    (coefficientPrefixTree r k K) r.control (r.path k K) s
  have hb (s : Nat) := unaryProgram_slots_le n .dec
    (fun label control cursor => coefficientSecondProgram n cursor r k K mode target label control)
    17 (fun label control cursor => coefficientSecondProgram_slots n cursor r k K mode target label control)
    (coefficientPrefixTree r k K) r.control (r.path k K) s
  have hs : (coefficientPrefixSignCircuit r k K signUpdate).length ≤ 1 := by
    cases signUpdate <;> simp only [coefficientPrefixSignCircuit,Bool.false_eq_true,ite_false,ite_true,List.length_cons,List.length_nil] <;> decide
  simp only [coefficientProgram,appendCompiled_slots,prependCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  grind only
theorem phaseSegments_slots (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) (core : Circuit) :
    (sequenceProgram n (phaseSegments n r shift core) start).2.gateSlots ≤
      8*(r.lengthQ.length+r.lengthRPrime.length+r.lengthS.length)+18+core.length := by
  let inner := r.withShiftEpoch shift
  let a := 4*inner.lengthQ.length+1
  let b := 4*inner.lengthRPrime.length+1
  let c := 4*inner.lengthS.length+1
  have h : List.Forall₂ (fun p bound => ∀ s, (p s).2.gateSlots ≤ bound)
      (phaseSegments n r shift core) ([a,b,1,c,1,core.length,1,c,1,b,a] : List Nat) := by
    unfold phaseSegments
    repeat' apply List.Forall₂.cons
    all_goals first | exact List.Forall₂.nil | intro cursor
    all_goals first | exact vchainProgram_slots n cursor _ _ _ | (simp only [literalProgram_slots,List.length_cons,List.length_nil]; rfl)
  have hb := sequenceProgram_slots_le n _ _ h start
  simp only [List.sum_cons,List.sum_nil,a,b,c,inner,PhaseUpdateRegisters.withShiftEpoch,
    List.length_append,List.length_cons,List.length_nil] at hb
  omega

theorem phaseProgram_slots (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) :
    (phaseProgram n start r shift).2.gateSlots ≤
      8*(r.lengthQ.length+r.lengthRPrime.length+r.lengthS.length)+32 := by
  have h := phaseSegments_slots n start r shift (phaseCoreGates (r.withShiftEpoch shift))
  simp only [phaseCoreGates,List.length_cons,List.length_nil] at h
  exact h

theorem phaseInverseProgram_slots (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) :
    (phaseInverseProgram n start r shift).2.gateSlots ≤
      8*(r.lengthQ.length+r.lengthRPrime.length+r.lengthS.length)+32 := by
  have h := phaseSegments_slots n start r shift (phaseInverseCoreGates (r.withShiftEpoch shift))
  simp only [phaseInverseCoreGates,List.length_cons,List.length_nil] at h
  exact h

theorem zeroCellProgram_slots (n start : Nat) (base : Bool) (r bit guard target temporary : Wire) :
    (zeroCellProgram n start base r bit guard target temporary).2.gateSlots ≤ 7 := by
  cases base <;> simp only [zeroCellProgram,prependCompiled_slots,andEraseProgram_slots,measuredZeroPrefix,
    Bool.false_eq_true,ite_false,ite_true,List.length_append,List.length_cons,List.length_nil] <;> decide

theorem upperForwardLeafProgram_slots (n start k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    (upperForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2.gateSlots ≤ 7 := by
  simp only [upperForwardLeafProgram,compiledIf_slots]
  split
  · split <;> exact zeroCellProgram_slots n start _ _ _ _ _ _
  · exact Nat.zero_le _

theorem upperReverseLeafProgram_slots (n start k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    (upperReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2.gateSlots ≤ 7 := by
  simp only [upperReverseLeafProgram,compiledIf_slots]
  split
  · exact zeroCellProgram_slots n start _ _ _ _ _ _
  · exact Nat.zero_le _

theorem lowerForwardLeafProgram_slots (n start k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    (lowerForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2.gateSlots ≤ 7 := by
  simp only [lowerForwardLeafProgram,compiledIf_slots]
  split
  · split <;> exact zeroCellProgram_slots n start _ _ _ _ _ _
  · exact Nat.zero_le _

theorem lowerReverseLeafProgram_slots (n start k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    (lowerReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2.gateSlots ≤ 7 := by
  simp only [lowerReverseLeafProgram,compiledIf_slots]
  split
  · exact zeroCellProgram_slots n start _ _ _ _ _ _
  · exact Nat.zero_le _

theorem rangeLeafProgram_slots (n : Nat) (after : Bool) (r : Wire)
    (leaf : Nat → Wire → FixedSegment n) (bound : Nat)
    (hl : ∀ label control cursor, (leaf label control cursor).2.gateSlots ≤ bound)
    (label : Nat) (dynamic : Wire) (start : Nat) :
    (rangeLeafProgram n after r leaf label dynamic start).2.gateSlots ≤ bound+1 := by
  have h := hl label r start
  cases after <;> simp only [rangeLeafProgram,compiledIf_slots,Bool.false_eq_true,ite_false,ite_true,
    appendCompiled_slots,prependCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil] <;> omega

theorem rangeScanProgram_slots (n : Nat) (after : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control r : Wire) (path : List Wire)
    (leaf : Nat → Wire → FixedSegment n) (bound : Nat)
    (hl : ∀ label dynamic cursor, (leaf label dynamic cursor).2.gateSlots ≤ bound) (start : Nat) :
    (rangeScanProgram n after order tree control r path leaf start).2.gateSlots ≤
      (bound+1)*(tree.internalNodes+1)+10*tree.internalNodes+1 := by
  have h (a : Bool) := unaryProgram_slots_le n order (rangeLeafProgram n a r leaf) (bound+1)
    (fun label dynamic cursor => rangeLeafProgram_slots n a r leaf bound hl label dynamic cursor)
    tree control path start
  have hf := h false
  have ht := h true
  cases after <;> simp only [rangeScanProgram,compiledIf_slots,Bool.false_eq_true,ite_false,ite_true,
    appendCompiled_slots,prependCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil] <;> omega

theorem upperMapProgram_slots (n k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (start : Nat) :
    (upperMapProgram n k K tree control r t path bitAt dirtyAt start).2.gateSlots ≤ 36*tree.internalNodes+18 := by
  have hf (s : Nat) := rangeScanProgram_slots n true .inc tree control r path
    (fun label dynamic cursor => upperForwardLeafProgram n cursor k K control t bitAt dirtyAt label dynamic) 7
    (fun label dynamic cursor => upperForwardLeafProgram_slots n cursor k K control t bitAt dirtyAt label dynamic) s
  have hb (s : Nat) := rangeScanProgram_slots n false .dec tree control r path
    (fun label dynamic cursor => upperReverseLeafProgram n cursor k K t bitAt dirtyAt label dynamic) 7
    (fun label dynamic cursor => upperReverseLeafProgram_slots n cursor k K t bitAt dirtyAt label dynamic) s
  simp only [upperMapProgram,appendCompiled_slots]
  grind only

theorem lowerMapProgram_slots (n k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (start : Nat) :
    (lowerMapProgram n k K tree control r t path bitAt dirtyAt start).2.gateSlots ≤ 36*tree.internalNodes+18 := by
  have hf (s : Nat) := rangeScanProgram_slots n true .dec tree control r path
    (fun label dynamic cursor => lowerForwardLeafProgram n cursor k K control t bitAt dirtyAt label dynamic) 7
    (fun label dynamic cursor => lowerForwardLeafProgram_slots n cursor k K control t bitAt dirtyAt label dynamic) s
  have hb (s : Nat) := rangeScanProgram_slots n false .inc tree control r path
    (fun label dynamic cursor => lowerReverseLeafProgram n cursor k K t bitAt dirtyAt label dynamic) 7
    (fun label dynamic cursor => lowerReverseLeafProgram_slots n cursor k K t bitAt dirtyAt label dynamic) s
  simp only [lowerMapProgram,appendCompiled_slots]
  grind only

end ShorECDLP.Paper2607_13816.ChallengeMigration
