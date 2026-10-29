import ShorECDLP.Submission.«2607_13816».Challenge.OuterResources
import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowedPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Challenge.EEAScheduleSlots
import ShorECDLP.Submission.«2607_13816».EEA.WrapperPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.ScheduleLayout
import ShorECDLP.Submission.«2607_13816».EEA.IndexedStepPrimitiveCounts
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem schedule_layout_at {r : IndexedStepRegisters} {width first count : Nat}
    (h : IndexedScheduleLayout r width first count) (offset : Nat) (ho : offset<count) :
    IndexedStepLayout r width (first+offset) := by
  induction h generalizing offset with
  | done => omega
  | @step first count head tail ih =>
    cases offset with
    | zero => simpa using head
    | succ offset => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih offset (by omega)

theorem production_step_layout (T : Nat) (hT : 1≤T) (hmax : T≤1620) :
    IndexedStepLayout indexedStepProductionRegisters 256 T := by
  have h := schedule_layout_at secp256k1ScheduleLayout_production (T-1) (by change T-1<1620; omega)
  simpa [show 1+(T-1)=T by omega] using h

theorem endSlotBound_le (r : EndIterationRegisters) (w : EndIterationWindows)
    (hl : EndIterationLayout r 256 w) (ht : r.lengthT.length=9) :
    endSlotBound r 256 w ≤ 99900 := by
  have hu := r.upperTree_visitLabels w hl.k4_le_K4
  have hd := r.lowerTree_visitLabels 256 w hl.k5_le_decode
  rw [UnaryActionTree.visitLabels_inc] at hu hd
  have hnu := unaryAction_internalNodes_add_one (r.upperTree w)
  have hnd := unaryAction_internalNodes_add_one (r.lowerTree 256 w)
  have hlu := unaryAction_leaves_eq_labels_length (r.upperTree w)
  have hld := unaryAction_leaves_eq_labels_length (r.lowerTree 256 w)
  rw [hu] at hlu
  rw [hd] at hld
  simp only [zeroMapLabels,List.length_map,List.length_range] at hlu hld
  have hk := hl.K4_le_work
  have hk5 : w.K5Decode 256 ≤259 := Nat.min_le_right _ _
  have hr : r.lengthRP.length=9 := hl.lengthRP_length.trans ht
  have hc : r.constants.length≤9 := by
    simp only [EndIterationRegisters.constants,List.length_take,EndIterationRegisters.width,ht]
    exact Nat.min_le_left _ _
  simp only [endSlotBound,endUpperSlotBound,endLowerSlotBound,hl.work1_length,ht,hr,
    zeroMapLabels,List.length_map,List.length_range ]
  omega

theorem production_hProgram_slots (n start T : Nat)
    (hl : IndexedStepLayout indexedStepProductionRegisters 256 T) :
    (hProgram n start indexedStepProductionRegisters 256 T).2.gateSlots≤100000 := by
  by_cases hm : T%4=0
  · have he := endSlotBound_le _ _ (hl.endIteration hm) (by rfl)
    have hp := hProgram_slots n start indexedStepProductionRegisters 256 T
    change (hProgram n start indexedStepProductionRegisters 256 T).2.gateSlots≤100000
    change (hProgram n start indexedStepProductionRegisters 256 T).2.gateSlots≤
      4*9+4*9+15+endSlotBound (indexedStepProductionRegisters.endIteration 256 T) 256 (endIterationWindowsAt 256 T) at hp
    omega
  · simp only [hProgram,compiledIf_slots,if_neg hm,Straight.gateSlots]
    omega


local notation "R" => indexedStepProductionRegisters
attribute [local irreducible] blockAForward blockAInverse blockCForward blockCInverse blockDForward blockDInverse blockFForward
  intervalTree coefficientPrefixTree quotientSwapTree remainderBlockProgram coefficientBlockProgram phaseProgram
  measuredStepProgram measuredEEAForwardProgram measuredScheduleProgram primitiveResources
  canonicalWork2Rotation canonicalWork2InverseRotation terminalEpochCompression terminalWork1Clear
  measuredForwardWrapperProgram measuredReverseWrapperProgram
  hornerProgram hornerInverseProgram multiplyWorkProgram multiplyDataProgram unmultiplyDataProgram fig15SwapOutput
  intervalProgram coefficientProgram measuredInverseStepProgram measuredEEAReverseProgram measuredInverseScheduleProgram


theorem production_blockA_length : (blockAForward R).length=2613 := by
  rw [circuit_length_primitive,blockAForward259_primitive R indexedStepProduction_layout.terminalPadding
    indexedStepProduction_layout.preShift (by simp only [indexedStepProductionRegisters,List.length_range']) (by rfl) (by rfl) (by decide)]
  rfl

theorem production_blockC_length : (blockCForward R).length=42 := by
  rw [circuit_length_primitive,blockCForward9_primitive R (by rfl) (by decide)]
  rfl

theorem production_blockF_length : (blockFForward R).length=1695 := by
  rw [blockFForward]
  rw [circuit_length_primitive,postShiftUnitary259_primitive (R).postShift indexedStepProduction_layout.postShift (by simp only [IndexedStepRegisters.postShift,indexedStepProductionRegisters,List.length_range']) (by rfl)]
  rfl

theorem production_blockD_length (T : Nat) (hl : IndexedStepLayout R 256 T) :
    (blockDForward R (certifiedActiveWindows 256 T).quotientSwap).length≤4000 := by
  let w := (certifiedActiveWindows 256 T).quotientSwap
  have hn := quotientSwapTree_nodes_le ((R).quotient w) w.start w.stop hl.quotient.k_le_K
  have hleaf := unaryAction_internalNodes_add_one (quotientSwapTree ((R).quotient w) w.start w.stop)
  have hk : w.stop≤258 := by simp only [w,certifiedActiveWindows,quotientSwapWindow]; omega
  rw [circuit_length_primitive,blockDForward9_primitive R _ hl.quotient (by rfl) (by rfl) (by decide)]
  change 48+4*(quotientSwapTree ((R).quotient w) w.start w.stop).internalNodes+0+
    (170+2*(quotientSwapTree ((R).quotient w) w.start w.stop).leaves+2*(quotientSwapTree ((R).quotient w) w.start w.stop).internalNodes)+
    (108+(quotientSwapTree ((R).quotient w) w.start w.stop).leaves+2*(quotientSwapTree ((R).quotient w) w.start w.stop).internalNodes)+0≤4000
  omega

theorem production_remainderBlock_slots (n start T : Nat) (hl : IndexedStepLayout R 256 T) :
    (remainderBlockProgram n start R 256 (certifiedActiveWindows 256 T).remainder).2.gateSlots≤47000 := by
  let w := (certifiedActiveWindows 256 T).remainder
  have hn := intervalTree_nodes_le ((R).remainder w) w.start w.stop
  have h := remainderBlockProgram_slots9 n start R 256 w (by rfl) (by rfl) (by rfl) (intervalLengthQ_le_endpointScratch _ _ _ .work1 hl.remainder)
  change _≤24*9+168*(intervalTree ((R).remainder w) w.start w.stop).internalNodes+2633 at h
  have hk : w.stop=259 := rfl
  change (remainderBlockProgram n start R 256 w).2.gateSlots≤47000
  omega

theorem production_coefficientBlock_slots (n start T : Nat) (hl : IndexedStepLayout R 256 T) :
    (coefficientBlockProgram n start R 256 (certifiedActiveWindows 256 T).coefficient).2.gateSlots≤29000 := by
  let w := (certifiedActiveWindows 256 T).coefficient
  have hn := quotientSwapTree_nodes_le (((R).coefficient w).routing w.start w.stop) w.start w.stop hl.coefficient.k_le_K
  have hk : w.stop≤257 := by simp only [w,certifiedActiveWindows,coefficientWindow]; omega
  have h := coefficientBlockProgram_slots256 n start R w hl.tBoundary (by rfl)
  have hn2 : (coefficientPrefixTree ((R).coefficient w) w.start w.stop).internalNodes≤w.stop := by
    simpa only [coefficientPrefixTree] using hn
  change (coefficientBlockProgram n start R 256 w).2.gateSlots≤29000
  omega

theorem production_measuredStep_slots (n start T : Nat) (hl : IndexedStepLayout R 256 T) :
    (measuredStepProgram n start R 256 T).2.gateSlots≤200000 := by
  have hd := production_blockD_length T hl
  have h := sequenceProgram_slots_le n (measuredStepSegments n R 256 T)
    ([2613,47000,4042,29000,1695,248,100000] : List Nat) (by
      unfold measuredStepSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))))
      · intro s; simp only [literalProgram_slots,production_blockA_length]; exact Nat.le_refl _
      · intro s; exact production_remainderBlock_slots n s T hl
      · intro s; simp only [literalProgram_slots,List.length_append,production_blockC_length]; omega
      · intro s; exact production_coefficientBlock_slots n s T hl
      · intro s; simp only [literalProgram_slots,production_blockF_length]; exact Nat.le_refl _
      · intro s; exact phaseProgram_slots n s (R).phaseUpdate (R).shiftEpoch
      · intro s; exact production_hProgram_slots n s T hl) start
  simp only [List.sum_cons,List.sum_nil] at h
  unfold measuredStepProgram
  omega

theorem production_measuredForward_slots (n start : Nat) :
    (measuredEEAForwardProgram n start R).2.gateSlots≤324000000 := by
  have h := measuredScheduleProgram_slots_le n R 256 1620 1 200000
    (by intro T ht hmax s; exact production_measuredStep_slots n s T (production_step_layout T ht (by omega))) start
  simpa only [measuredEEAForwardProgram,secp256k1ScheduleLength] using h


theorem production_hInverseProgram_slots (n start T : Nat)
    (hl : IndexedStepLayout R 256 T) :
    (hInverseProgram n start R 256 T).2.gateSlots≤100000 := by
  by_cases hm : T%4=0
  · have he := endSlotBound_le _ _ (hl.endIteration hm) (by rfl)
    have hp := hInverseProgram_slots n start R 256 T
    change (hInverseProgram n start R 256 T).2.gateSlots≤
      4*9+4*9+15+endSlotBound ((R).endIteration 256 T) 256 (endIterationWindowsAt 256 T) at hp
    omega
  · simp only [hInverseProgram,compiledIf_slots,if_neg hm,Straight.gateSlots]
    omega

theorem production_blockAInverse_length : (blockAInverse R).length=2645 := by
  rw [circuit_length_primitive,blockAInverse259_primitive R indexedStepProduction_layout.terminalPadding
    indexedStepProduction_layout.preShift (by simp only [indexedStepProductionRegisters,List.length_range']) (by rfl) (by rfl) (by decide)]
  rfl

theorem production_blockCInverse_length : (blockCInverse R).length=42 := by
  rw [circuit_length_primitive,blockCInverse9_primitive R (by rfl) (by decide)]
  rfl

theorem production_blockDInverse_length (T : Nat) (hl : IndexedStepLayout R 256 T) :
    (blockDInverse R (certifiedActiveWindows 256 T).quotientSwap).length≤4000 := by
  let w := (certifiedActiveWindows 256 T).quotientSwap
  have hn := quotientSwapTree_nodes_le ((R).quotient w) w.start w.stop hl.quotient.k_le_K
  have hleaf := unaryAction_internalNodes_add_one (quotientSwapTree ((R).quotient w) w.start w.stop)
  have hk : w.stop≤258 := by simp only [w,certifiedActiveWindows,quotientSwapWindow]; omega
  rw [circuit_length_primitive,blockDInverse9_primitive R _ hl.quotient (by rfl) (by rfl) (by decide)]
  change 48+4*(quotientSwapTree ((R).quotient w) w.start w.stop).internalNodes+0+
    (170+2*(quotientSwapTree ((R).quotient w) w.start w.stop).leaves+2*(quotientSwapTree ((R).quotient w) w.start w.stop).internalNodes)+
    (108+(quotientSwapTree ((R).quotient w) w.start w.stop).leaves+2*(quotientSwapTree ((R).quotient w) w.start w.stop).internalNodes)+0≤4000
  omega

theorem production_coefficient_slots (n start T : Nat) (mode : RippleMode) (sg : Bool)
    (hl : IndexedStepLayout R 256 T) :
    (coefficientProgram n start ((R).coefficient (certifiedActiveWindows 256 T).coefficient)
      (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop mode sg .work2).2.gateSlots≤14500 := by
  let w := (certifiedActiveWindows 256 T).coefficient
  have hn := quotientSwapTree_nodes_le (((R).coefficient w).routing w.start w.stop) w.start w.stop hl.coefficient.k_le_K
  have hk : w.stop≤257 := by simp only [w,certifiedActiveWindows,coefficientWindow]; omega
  have h := coefficientProgram_slots n start ((R).coefficient w) w.start w.stop mode sg .work2
  have hn2 : (coefficientPrefixTree ((R).coefficient w) w.start w.stop).internalNodes≤w.stop := by
    simpa only [coefficientPrefixTree] using hn
  change (coefficientProgram n start ((R).coefficient w) w.start w.stop mode sg .work2).2.gateSlots≤14500
  omega

theorem production_interval_slots (n start T : Nat) (mode : RippleMode) (sg : Bool)
    (hl : IndexedStepLayout R 256 T) :
    (intervalProgram n start ((R).remainder (certifiedActiveWindows 256 T).remainder) 256
      (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop mode sg .work1).2.gateSlots≤23500 := by
  let w := (certifiedActiveWindows 256 T).remainder
  have hn := intervalTree_nodes_le ((R).remainder w) w.start w.stop
  have h := intervalProgram_slots9 n start ((R).remainder w) 256 w.start w.stop mode sg .work1 (by rfl) (by rfl) (by rfl)
    (intervalLengthQ_le_endpointScratch _ _ _ .work1 hl.remainder)
  have hk : w.stop=259 := rfl
  change (intervalProgram n start ((R).remainder w) 256 w.start w.stop mode sg .work1).2.gateSlots≤23500
  omega


theorem production_measuredInverseStep_slots (n start T : Nat) (hl : IndexedStepLayout R 256 T) :
    (measuredInverseStepProgram n start R T).2.gateSlots≤200000 := by
  have hd := production_blockDInverse_length T hl
  have hp := prepareLatestPaperTBoundary_length256 (R).tBoundary hl.tBoundary (by rfl)
  have hr := restoreLatestPaperTBoundary_length256 (R).tBoundary hl.tBoundary (by rfl)
  have h1 := computeControl_length_le [(R).phase1] 1 (R).control (R).blockScratch
  have h2 := computeControl_length_le [(R).phase2,(R).sign] 2 (R).terminal (R).blockScratch
  have h3 := computeControl_length_le [(R).phase1,(R).terminal] 1 (R).control (R).blockScratch
  have h4 := rControlNonterminal_length_le [(R).phase1,(R).terminal] 0 (R).control (R).lengthRPrime ((R).blockScratch.getD 0 0) ((R).blockScratch.drop 1)
  have h5 := rControlNonterminal_length_le [(R).phase1] 0 (R).control (R).lengthRPrime (R).terminal (R).blockScratch
  have hb := blockB2_length_le R
  simp only [List.length_cons,List.length_nil] at h1 h2 h3 h4 h5
  change _≤4*9+4*2+7 at h4
  change _≤4*9+4*1+7 at h5
  change _≤8*9+31 at hb
  have h := sequenceProgram_slots_le n (measuredInverseStepSegments n R T)
    ([100000,248,1929,14500,33,14500,4500,23500,210,23500,2700] : List Nat) (by
      unfold measuredInverseStepSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))))))))
      · intro s; exact production_hInverseProgram_slots n s T hl
      · intro s; exact phaseInverseProgram_slots n s (R).phaseUpdate (R).shiftEpoch
      · intro s; simp only [literalProgram_slots,List.length_append,circuit_adjoint_length,production_blockF_length]; omega
      · intro s; exact production_coefficient_slots n s T (RippleMode.add.inverse) true hl
      · intro s; simp only [literalProgram_slots,List.length_append,List.length_cons,List.length_nil]; omega
      · intro s; exact production_coefficient_slots n s T (RippleMode.sub.inverse) false hl
      · intro s; simp only [literalProgram_slots,List.length_append,List.length_cons,List.length_nil,production_blockCInverse_length]; omega
      · intro s; exact production_interval_slots n s T (RippleMode.add.inverse) false hl
      · intro s; simp only [literalProgram_slots,List.length_append,List.length_cons,List.length_nil]; omega
      · intro s; exact production_interval_slots n s T (RippleMode.sub.inverse) true hl
      · intro s; simp only [literalProgram_slots,List.length_append,production_blockAInverse_length]; omega) start
  simp only [List.sum_cons,List.sum_nil] at h
  unfold measuredInverseStepProgram
  omega

theorem production_measuredReverse_slots (n start : Nat) :
    (measuredEEAReverseProgram n start R).2.gateSlots≤324000000 := by
  have h := measuredInverseScheduleProgram_slots_le n R 1620 1 200000
    (by intro T ht hmax s; exact production_measuredInverseStep_slots n s T (production_step_layout T ht (by omega))) start
  simpa only [measuredEEAReverseProgram,secp256k1ScheduleLength] using h


theorem constMinusProgram_slots (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (q c r t : Wire) (hd : input.length=dirty.length+1) (hk : bits.length=input.length) :
    (constMinusProgram n start input dirty bits q c r t).2.gateSlots≤53*input.length := by
  have hi := gidneyProgram_slots_le n start input dirty ((List.range input.length).map (Nat.testBit 1)) q c r t hd (by simp)
  have hb (s : Nat) := gidneyProgram_slots_le n s input dirty bits q c r t hd hk
  simp only [constMinusProgram,prependCompiled_slots,appendCompiled_slots,controlledComplement,List.length_map]
  grind only

theorem eeaCenterProgram_slots (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (hd : input.length=dirty.length) (hk : bits.length=input.length)
    (hp : 0 < input.length) :
    (eeaCenterProgram n start input dirty bits p c r t iter).2.gateSlots≤78*input.length+1 := by
  have ht : input.length=(dirty.take (input.length-1)).length+1 := by simp only [List.length_take,← hd]; omega
  have hc := uncontrolledCompareProgram_slots_le n start input dirty (p/2+1) c r t iter hd
  have hn (s : Nat) := constMinusProgram_slots n s input (dirty.take (input.length-1)) bits iter c r t ht hk
  simp only [eeaCenterProgram,appendCompiled_slots]
  grind only

theorem eeaUncenterProgram_slots (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (hd : input.length=dirty.length) (hk : bits.length=input.length)
    (hp : 0 < input.length) :
    (eeaUncenterProgram n start input dirty bits p c r t iter).2.gateSlots≤78*input.length+1 := by
  have ht : input.length=(dirty.take (input.length-1)).length+1 := by simp only [List.length_take,← hd]; omega
  have hn := constMinusProgram_slots n start input (dirty.take (input.length-1)) bits iter c r t ht hk
  have hc (s : Nat) := uncontrolledCompareProgram_slots_le n s input dirty (p/2+1) c r t iter hd
  simp only [eeaUncenterProgram,appendCompiled_slots]
  grind only

theorem eeaParityProgram_slots (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (c r t iter : Wire) (hd : input.length=dirty.length+1) (hk : bits.length=input.length) :
    (eeaParityProgram n start input dirty bits c r t iter).2.gateSlots≤53*input.length+2 := by
  have h := constMinusProgram_slots n start input dirty bits iter c r t hd hk
  simp only [eeaParityProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  omega

theorem preprocessProgram_slots (n start : Nat) : (preprocessProgram n start).2.gateSlots≤600000 := by
  have hc := eeaCenterProgram_slots n start (List.range' 266 256).reverse (List.range' 4 256)
    (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2 (by simp) (by simp) (by simp)
  have hp : workRegistersPrepare.length=641 := by rw [circuit_length_primitive,workRegistersPrepare_primitive]; rfl
  have hl : eeaLengthSetup.length=518649 := by rw [circuit_length_primitive,eeaLengthSetup_primitive]; rfl
  simp only [List.length_reverse,List.length_range'] at hc
  simp only [preprocessProgram,surroundCompiled_slots,hp,hl]
  omega

theorem unpreprocessProgram_slots (n start : Nat) : (unpreprocessProgram n start).2.gateSlots≤600000 := by
  have hc := eeaUncenterProgram_slots n start (List.range' 266 256).reverse (List.range' 4 256)
    (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2 (by simp) (by simp) (by simp)
  have hp : workRegistersRestore.length=641 := by rw [circuit_length_primitive,workRegistersRestore_primitive]; rfl
  have hl : eeaLengthUndo.length=518649 := by rw [circuit_length_primitive,eeaLengthUndo_primitive]; rfl
  simp only [List.length_reverse,List.length_range'] at hc
  simp only [unpreprocessProgram,surroundCompiled_slots,hp,hl]
  omega

theorem productionParityProgram_slots (n start : Nat) : (productionParityProgram n start).2.gateSlots≤13570 := by
  have h := eeaParityProgram_slots n start (List.range' 263 256) (List.range' 4 255) secp256k1ModulusBits 560 561 562 2 (by simp) (by simp [secp256k1ModulusBits])
  simpa only [List.length_range'] using h


theorem canonicalWork2Rotation_length : canonicalWork2Rotation.length=7866 := by
  rw [circuit_length_primitive,canonicalWork2Rotation_primitive]; rfl

theorem canonicalWork2InverseRotation_length : canonicalWork2InverseRotation.length=7866 := by
  rw [circuit_length_primitive,canonicalWork2InverseRotation_primitive]; rfl

theorem terminalEpochCompression_length : terminalEpochCompression.length=25 := by
  rw [circuit_length_primitive,terminalEpochCompression_primitive]; rfl

theorem terminalWork1Clear_length : terminalWork1Clear.length=251 := by
  rw [circuit_length_primitive,terminalWork1Clear_primitive]; rfl

theorem measuredForwardWrapperProgram_slots (n start : Nat) :
    (measuredForwardWrapperProgram n start).2.gateSlots≤325000000 := by
  have h := sequenceProgram_slots_le n (measuredForwardWrapperSegments n)
    ([600000,324000000,7891,13570,251] : List Nat) (by
      unfold measuredForwardWrapperSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))
      · intro s; exact preprocessProgram_slots n s
      · intro s; exact production_measuredForward_slots n s
      · intro s; simp only [literalProgram_slots,List.length_append,canonicalWork2Rotation_length,terminalEpochCompression_length]; decide
      · intro s; exact productionParityProgram_slots n s
      · intro s; simp only [literalProgram_slots,terminalWork1Clear_length]; decide) start
  simp only [List.sum_cons,List.sum_nil] at h
  unfold measuredForwardWrapperProgram
  omega

theorem measuredReverseWrapperProgram_slots (n start : Nat) :
    (measuredReverseWrapperProgram n start).2.gateSlots≤325000000 := by
  have h := sequenceProgram_slots_le n (measuredReverseWrapperSegments n)
    ([251,13570,7891,324000000,600000] : List Nat) (by
      unfold measuredReverseWrapperSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))
      · intro s; simp only [literalProgram_slots,terminalWork1Clear_length]; decide
      · intro s; exact productionParityProgram_slots n s
      · intro s; simp only [literalProgram_slots,List.length_append,canonicalWork2InverseRotation_length,terminalEpochCompression_length]; decide
      · intro s; exact production_measuredReverse_slots n s
      · intro s; exact unpreprocessProgram_slots n s) start
  simp only [List.sum_cons,List.sum_nil] at h
  unfold measuredReverseWrapperProgram
  omega



end ShorECDLP.Paper2607_13816.ChallengeMigration
