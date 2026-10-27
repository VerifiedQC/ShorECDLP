import ShorECDLP.Submission.«2607_13816».Challenge.EEALengthSlots
import ShorECDLP.Submission.«2607_13816».EEA.BlockEPrimitiveCounts
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem computeControl_length_le (controls : List Wire) (value : Nat) (target : Wire) (scratch : List Wire) :
    (computeControl controls value target scratch).length ≤ 4*controls.length+1 := by
  have hm := zeroMaskFrom_length_le controls value 0
  have hc := mcxVChain_length_le controls target scratch
  simp only [computeControl,List.length_append,circuit_adjoint_length,zeroMask]
  omega

theorem rControlNonterminal_length_le (conditions : List Wire) (value : Nat) (control : Wire)
    (lengthRPrime : List Wire) (zeroRPrime : Wire) (scratch : List Wire) :
    (rControlNonterminal conditions value control lengthRPrime zeroRPrime scratch).length ≤
      4*lengthRPrime.length+4*conditions.length+7 := by
  have hr := mcxVChain_length_le lengthRPrime zeroRPrime scratch
  have hc := computeControl_length_le (conditions++[zeroRPrime]) (value%2^conditions.length) control scratch
  simp only [List.length_append,List.length_cons,List.length_nil] at hc
  simp only [rControlNonterminal,List.length_append]
  omega

theorem blockB2_length_le (r : IndexedStepRegisters) :
    (blockB2 r).length ≤ 8*r.lengthRPrime.length+31 := by
  have h := rControlNonterminal_length_le [r.phase1,r.phase2] 2 r.control r.lengthRPrime r.terminal r.blockScratch
  change ((rControlNonterminal [r.phase1,r.phase2] 2 r.control r.lengthRPrime r.terminal r.blockScratch ++
    [Gate.CX r.control r.sign]) ++ rControlNonterminal [r.phase1,r.phase2] 2 r.control r.lengthRPrime r.terminal r.blockScratch).length ≤ _
  simp only [List.length_cons,List.length_nil] at h
  simp only [List.length_append,List.length_cons,List.length_nil]
  omega

theorem prepareLatestPaperTBoundary_length256 (r : TBoundaryRegisters)
    (hl : TBoundaryLayout r) (hw : r.width=9) :
    (prepareLatestPaperTBoundary r 256).length = 229 := by
  rw [circuit_length_primitive,prepareLatestPaperTBoundary256_primitive r hl hw]
  rfl

theorem restoreLatestPaperTBoundary_length256 (r : TBoundaryRegisters)
    (hl : TBoundaryLayout r) (hw : r.width=9) :
    (restoreLatestPaperTBoundary r 256).length = 229 := by
  rw [circuit_length_primitive,restoreLatestPaperTBoundary256_primitive r hl hw]
  rfl


theorem remainderBlockProgram_slots9 (n start : Nat) (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow)
    (ht : (r.remainder w).lengthT.length=9) (hq : (r.remainder w).lengthQ.length=9)
    (hs : (r.remainder w).lengthS.length=9) (hw : 9≤(r.remainder w).endpointScratch.length) :
    (remainderBlockProgram n start r width w).2.gateSlots ≤
      24*r.lengthRPrime.length+168*(intervalTree (r.remainder w) w.start w.stop).internalNodes+2633 := by
  let b := 84*(intervalTree (r.remainder w) w.start w.stop).internalNodes+1273
  let a := 4*r.lengthRPrime.length+11
  let c := 4*r.lengthRPrime.length+17
  have hi (s : Nat) (m : RippleMode) (sg : Bool) := intervalProgram_slots9 n s (r.remainder w) width w.start w.stop m sg .work1 ht hq hs hw
  have h1 := rControlNonterminal_length_le [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch
  have h2 := rControlNonterminal_length_le [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)
  have hb := blockB2_length_le r
  simp only [List.length_cons,List.length_nil] at h1 h2
  have h := sequenceProgram_slots_le n (remainderBlockSegments n r width w)
    ([a,b,a,8*r.lengthRPrime.length+31,c,b,c] : List Nat) (by
      unfold remainderBlockSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))))
      · intro s; simpa only [literalProgram_slots,a] using h1
      · intro s; exact hi s .sub true
      · intro s; simpa only [literalProgram_slots,a] using h1
      · intro s; simpa only [literalProgram_slots] using hb
      · intro s; simp only [literalProgram_slots,List.length_append,List.length_cons,List.length_nil,c]; omega
      · intro s; exact hi s .add false
      · intro s; simp only [literalProgram_slots,List.length_append,List.length_cons,List.length_nil,c]; omega) start
  simp only [List.sum_cons,List.sum_nil,a,b,c] at h
  unfold remainderBlockProgram
  omega

theorem coefficientBlockProgram_slots256 (n start : Nat) (r : IndexedStepRegisters) (w : ActiveWindow)
    (hb : TBoundaryLayout r.tBoundary) (hw : r.tBoundary.width=9) :
    (coefficientBlockProgram n start r 256 w).2.gateSlots ≤
      108*(coefficientPrefixTree (r.coefficient w) w.start w.stop).internalNodes+597 := by
  let b := 54*(coefficientPrefixTree (r.coefficient w) w.start w.stop).internalNodes+37
  have hc (s : Nat) (m : RippleMode) (sg : Bool) := coefficientProgram_slots n s (r.coefficient w) w.start w.stop m sg .work2
  have h1 := computeControl_length_le [r.phase2,r.sign] 2 r.terminal r.blockScratch
  have h2 := computeControl_length_le [r.phase1,r.terminal] 1 r.control r.blockScratch
  have h3 := computeControl_length_le [r.phase1] 1 r.control r.blockScratch
  have hp := prepareLatestPaperTBoundary_length256 r.tBoundary hb hw
  have hr := restoreLatestPaperTBoundary_length256 r.tBoundary hb hw
  simp only [List.length_cons,List.length_nil] at h1 h2 h3
  have h := sequenceProgram_slots_le n (coefficientBlockSegments n r 256 w)
    ([256,b,33,b,234] : List Nat) (by
      unfold coefficientBlockSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))
      · intro s; simp only [literalProgram_slots,List.length_append]; omega
      · intro s; exact hc s .sub false
      · intro s; simp only [literalProgram_slots,List.length_append,List.length_cons,List.length_nil]; omega
      · intro s; exact hc s .add true
      · intro s; simp only [literalProgram_slots,List.length_append]; omega) start
  simp only [List.sum_cons,List.sum_nil,b] at h
  unfold coefficientBlockProgram
  omega


def measuredStepSlotBound (r : IndexedStepRegisters) (T : Nat) : Nat :=
  (blockAForward r).length+
    (24*r.lengthRPrime.length+168*(intervalTree (r.remainder (certifiedActiveWindows 256 T).remainder)
      (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop).internalNodes+2633)+
    (blockCForward r).length+(blockDForward r (certifiedActiveWindows 256 T).quotientSwap).length+
    (108*(coefficientPrefixTree (r.coefficient (certifiedActiveWindows 256 T).coefficient)
      (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop).internalNodes+597)+
    (blockFForward r).length+
    (8*(r.phaseUpdate.lengthQ.length+r.phaseUpdate.lengthRPrime.length+r.phaseUpdate.lengthS.length)+32)+hSlotBound r 256 T

theorem measuredStepProgram_slots (n start : Nat) (r : IndexedStepRegisters) (T : Nat)
    (ht : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthT.length=9)
    (hq : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthQ.length=9)
    (hs : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthS.length=9)
    (he : 9≤(r.remainder (certifiedActiveWindows 256 T).remainder).endpointScratch.length)
    (hb : TBoundaryLayout r.tBoundary) (hw : r.tBoundary.width=9) :
    (measuredStepProgram n start r 256 T).2.gateSlots ≤ measuredStepSlotBound r T := by
  let rem := (certifiedActiveWindows 256 T).remainder
  let coef := (certifiedActiveWindows 256 T).coefficient
  have h := sequenceProgram_slots_le n (measuredStepSegments n r 256 T)
    ([(blockAForward r).length,
      24*r.lengthRPrime.length+168*(intervalTree (r.remainder rem) rem.start rem.stop).internalNodes+2633,
      (blockCForward r).length+(blockDForward r (certifiedActiveWindows 256 T).quotientSwap).length,
      108*(coefficientPrefixTree (r.coefficient coef) coef.start coef.stop).internalNodes+597,
      (blockFForward r).length,
      8*(r.phaseUpdate.lengthQ.length+r.phaseUpdate.lengthRPrime.length+r.phaseUpdate.lengthS.length)+32,
      hSlotBound r 256 T] : List Nat) (by
      unfold measuredStepSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))))
      · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _
      · intro s; exact remainderBlockProgram_slots9 n s r 256 rem ht hq hs he
      · intro s; simp only [literalProgram_slots,List.length_append]; exact Nat.le_refl _
      · intro s; exact coefficientBlockProgram_slots256 n s r coef hb hw
      · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _
      · intro s; exact phaseProgram_slots n s r.phaseUpdate r.shiftEpoch
      · intro s; exact hProgram_slots n s r 256 T) start
  simp only [List.sum_cons,List.sum_nil,rem,coef] at h
  unfold measuredStepProgram measuredStepSlotBound
  omega

theorem measuredScheduleProgram_slots_le (n : Nat) (r : IndexedStepRegisters) (width count first bound : Nat)
    (hstep : ∀ T, first≤T → T<first+count → ∀ cursor,
      (measuredStepProgram n cursor r width T).2.gateSlots≤bound) (start : Nat) :
    (measuredScheduleProgram n r width count first start).2.gateSlots ≤ count*bound := by
  induction count generalizing first start with
  | zero => exact Nat.zero_le _
  | succ count ih =>
    have hf := hstep first (by omega) (by omega) start
    have hr := ih (first+1) (by intro T h1 h2; exact hstep T (by omega) (by omega))
      (start+(measuredStepProgram n start r width first).1)
    rw [measuredScheduleProgram,appendCompiled_slots]
    nlinarith


def measuredInverseStepSlotBounds (r : IndexedStepRegisters) (T : Nat) : List Nat :=
  [ hSlotBound r 256 T,
    8*(r.phaseUpdate.lengthQ.length+r.phaseUpdate.lengthRPrime.length+r.phaseUpdate.lengthS.length)+32,
    (((blockFForward r).adjoint ++ prepareLatestPaperTBoundary r.tBoundary 256 ++ computeControl [r.phase1] 1 r.control r.blockScratch)).length,
    54*(coefficientPrefixTree (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop).internalNodes+37,
    ((computeControl [r.phase1] 1 r.control r.blockScratch ++ [Gate.CX r.phase1 r.sign] ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch)).length,
    54*(coefficientPrefixTree (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop).internalNodes+37,
    ((computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256 ++ blockDInverse r (certifiedActiveWindows 256 T).quotientSwap ++ blockCInverse r ++ (([Gate.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [Gate.CCX r.phase2 r.sign r.terminal]))).length,
    84*(intervalTree (r.remainder (certifiedActiveWindows 256 T).remainder) (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop).internalNodes+1273,
    (((([Gate.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [Gate.CCX r.phase2 r.sign r.terminal]) ++ blockB2 r ++ rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch)).length,
    84*(intervalTree (r.remainder (certifiedActiveWindows 256 T).remainder) (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop).internalNodes+1273,
    ((rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch ++ blockAInverse r)).length ]

theorem measuredInverseStepProgram_slots (n start : Nat) (r : IndexedStepRegisters) (T : Nat)
    (ht : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthT.length=9)
    (hq : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthQ.length=9)
    (hs : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthS.length=9)
    (he : 9≤(r.remainder (certifiedActiveWindows 256 T).remainder).endpointScratch.length) :
    (measuredInverseStepProgram n start r T).2.gateSlots ≤ (measuredInverseStepSlotBounds r T).sum := by
  unfold measuredInverseStepProgram
  apply sequenceProgram_slots_le
  unfold measuredInverseStepSegments measuredInverseStepSlotBounds
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))))
  · intro s; exact hInverseProgram_slots n s r 256 T
  · intro s; exact phaseInverseProgram_slots n s r.phaseUpdate r.shiftEpoch
  · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _
  · intro s; exact coefficientProgram_slots n s (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop (RippleMode.add.inverse) true .work2
  · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _
  · intro s; exact coefficientProgram_slots n s (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop (RippleMode.sub.inverse) false .work2
  · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _
  · intro s; exact intervalProgram_slots9 n s (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop (RippleMode.add.inverse) false .work1 ht hq hs he
  · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _
  · intro s; exact intervalProgram_slots9 n s (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop (RippleMode.sub.inverse) true .work1 ht hq hs he
  · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _


theorem measuredInverseScheduleProgram_slots_le (n : Nat) (r : IndexedStepRegisters) (count first bound : Nat)
    (hstep : ∀ T, first≤T → T<first+count → ∀ cursor,
      (measuredInverseStepProgram n cursor r T).2.gateSlots≤bound) (start : Nat) :
    (measuredInverseScheduleProgram n r count first start).2.gateSlots ≤ count*bound := by
  induction count generalizing first start with
  | zero => exact Nat.zero_le _
  | succ count ih =>
    have hr := ih (first+1) (by intro T h1 h2; exact hstep T (by omega) (by omega)) start
    have hf := hstep first (by omega) (by omega)
      (start+(measuredInverseScheduleProgram n r count (first+1) start).1)
    rw [measuredInverseScheduleProgram,appendCompiled_slots]
    nlinarith

theorem intervalTree_nodes_le (r : IntervalRegisters) (k K : Nat) :
    (intervalTree r k K).internalNodes ≤ K := by
  have hn := dualUnaryAction_internalNodes_add_one (intervalTree r k K)
  have hl := dualUnaryAction_leaves_eq_labels_length (intervalTree r k K)
  rw [intervalTree_labels,Finset.length_sort] at hl
  have hc := List.toFinset_card_le (intervalMainLabels k K)
  have hb : (intervalMainLabels k K).length ≤ K+1 := by
    simp only [intervalMainLabels]
    split <;> simp only [List.length_range,intervalLaneCount] <;> omega
  omega

theorem quotientSwapTree_nodes_le (r : QuotientSwapRegisters) (k K : Nat) (hk : k≤K) :
    (quotientSwapTree r k K).internalNodes ≤ K := by
  have hn := unaryAction_internalNodes_add_one (quotientSwapTree r k K)
  have hl := unaryAction_leaves_eq_labels_length (quotientSwapTree r k K)
  rw [quotientSwapTree_labels r hk,Finset.length_sort] at hl
  have hc := List.toFinset_card_le (quotientSwapLabels k K)
  simp only [quotientSwapLabels,List.length_range'] at hc hl
  omega

end ShorECDLP.Paper2607_13816.ChallengeMigration
