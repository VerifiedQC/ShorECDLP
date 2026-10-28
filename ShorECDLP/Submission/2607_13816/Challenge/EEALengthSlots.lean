import ShorECDLP.Submission.«2607_13816».Challenge.EEACellSlots
import ShorECDLP.Submission.«2607_13816».EEA.BlockEPrimitiveCounts
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem controlledXorConstant_length_le (control : Wire) (targets : List Wire) (value : Nat) :
    (controlledXorConstant control targets value).length ≤ targets.length := by
  induction targets generalizing value with
  | nil => exact Nat.zero_le _
  | cons target targets ih =>
    simp only [controlledXorConstant,List.length_append,List.length_cons]
    split <;> simp only [List.length_cons,List.length_nil] <;> have h := ih (value/2) <;> omega

theorem dirtyConstantWrites_length_le (targets : List Wire) (dirtyAt valueAt : Nat → Nat) (labels : List Nat) :
    (dirtyConstantWrites targets dirtyAt valueAt labels).length ≤ labels.length*targets.length := by
  induction labels with
  | nil => exact Nat.zero_le _
  | cons label labels ih =>
    have h := controlledXorConstant_length_le (dirtyAt label) targets (valueAt label)
    simp only [dirtyConstantWrites,List.length_append,List.length_cons]
    nlinarith

theorem upperWriterProgram_slots (n k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat) :
    (upperWriterProgram n k K tree control r t path bitAt dirtyAt targets start).2.gateSlots ≤
      targets.length+2*((zeroMapLabels k K).length*targets.length)+72*tree.internalNodes+36 := by
  have hm (s : Nat) := upperMapProgram_slots n k K tree control r t path bitAt dirtyAt s
  have hs := controlledXorConstant_length_le control targets (truthMinusOneValue targets.length K)
  have hd := dirtyConstantWrites_length_le targets dirtyAt (highestPositionWriteValue targets.length k) (zeroMapLabels k K).reverse
  simp only [List.length_reverse] at hd
  simp only [upperWriterProgram,prependCompiled_slots,appendCompiled_slots,List.length_append,highestPositionDirtyWrites]
  grind only

theorem lowerWriterProgram_slots (n width k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat) :
    (lowerWriterProgram n width k K tree control r t path bitAt dirtyAt targets start).2.gateSlots ≤
      targets.length+2*((zeroMapLabels k K).length*targets.length)+72*tree.internalNodes+36 := by
  have hm (s : Nat) := lowerMapProgram_slots n k K tree control r t path bitAt dirtyAt s
  have hs := controlledXorConstant_length_le control targets (rightLengthValue width targets.length k)
  have hd := dirtyConstantWrites_length_le targets dirtyAt (rightLengthWriteValue width targets.length K) (zeroMapLabels k K)
  simp only [lowerWriterProgram,prependCompiled_slots,appendCompiled_slots,List.length_append,rightLengthDirtyWrites]
  grind only

theorem surroundCompiled_slots {n start : Nat} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    (surroundCompiled before after p).2.gateSlots = before.length+p.2.gateSlots+after.length := by
  simp only [surroundCompiled,prependCompiled_slots,appendCompiled_slots,literalProgram_slots]
  omega


theorem xorConstant_length_le (wires : List Wire) (value : Nat) :
    (xorConstant wires value).length ≤ wires.length := by
  induction wires generalizing value with
  | nil => exact Nat.zero_le _
  | cons w ws ih =>
    simp only [xorConstant,List.length_append,List.length_cons]
    split <;> simp only [List.length_cons,List.length_nil] <;> have h := ih (value/2) <;> omega

theorem cuccaroAdd_length_le (as bs : List Wire) (carry : Wire) :
    (cuccaroAdd as bs carry).length ≤ 6*as.length := by
  induction as generalizing bs carry with
  | nil => cases bs <;> exact Nat.zero_le _
  | cons a as ih =>
    cases bs with
    | nil => exact Nat.zero_le _
    | cons b bs =>
      have h := ih bs a
      simp only [cuccaroAdd,List.length_append,cuccaroMaj,cuccaroUma,List.length_cons,List.length_nil]
      omega

theorem addConstant_length_le (register constants : List Wire) (carry : Wire) (value : Nat) :
    (addConstant register constants carry value).length ≤ 8*constants.length := by
  have h := xorConstant_length_le constants value
  have hc := cuccaroAdd_length_le constants register carry
  simp only [addConstant,List.length_append]
  omega

theorem subConstant_length_le (register constants : List Wire) (carry : Wire) (value : Nat) :
    (subConstant register constants carry value).length ≤ 8*constants.length := by
  have h := xorConstant_length_le constants value
  have hc := cuccaroAdd_length_le constants register carry
  simp only [subConstant,List.length_append,cuccaroSub,circuit_adjoint_length]
  omega

theorem notRegister_length (register : List Wire) : (notRegister register).length=register.length := by
  induction register with
  | nil => rfl
  | cons w ws ih => simpa only [notRegister,List.length_cons] using congrArg Nat.succ ih

theorem incrementTail_length_le (bits : List Wire) (carry : Wire) (carries : List Wire) :
    (incrementTail bits carry carries).length ≤ 3*bits.length := by
  induction bits generalizing carry carries with
  | nil => exact Nat.zero_le _
  | cons bit bits ih =>
    cases bits with
    | nil => cases carries <;> simp [incrementTail]
    | cons next rest =>
      cases carries with
      | nil => exact Nat.zero_le _
      | cons c cs =>
        have h := ih c cs
        simp only [incrementTail,List.length_append,List.length_cons,List.length_nil]
        simp only [List.length_cons] at h
        omega

theorem uncontrolledIncrement_length_le (bits carries : List Wire) :
    (uncontrolledIncrement bits carries).length ≤ 3*bits.length := by
  cases bits with
  | nil => exact Nat.zero_le _
  | cons low bits =>
    cases bits with
    | nil => simp [uncontrolledIncrement]
    | cons next rest =>
      cases carries with
      | nil => exact Nat.zero_le _
      | cons c cs =>
        have h := incrementTail_length_le (next::rest) c (cs.take rest.length)
        simp only [uncontrolledIncrement,List.length_append,List.length_cons,List.length_nil]
        simp only [List.length_cons] at h
        omega

theorem constMinus_length_le (register constants : List Wire) (carry : Wire) (value : Nat) :
    (constMinus register constants carry value).length ≤ 4*register.length+8*constants.length := by
  have h := uncontrolledIncrement_length_le register (constants.take (register.length-1))
  have ha := addConstant_length_le register constants carry value
  simp only [constMinus,List.length_append,notRegister_length]
  omega


theorem ltUpdateProgram_slots (n width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire)
    (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat) :
    (ltUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2.gateSlots ≤
      2*lengthT.length+4*((zeroMapLabels k K).length*lengthT.length)+144*tree.internalNodes+72+
        8*lengthRP.length+16*constants.length := by
  have h1 (s : Nat) := upperWriterProgram_slots n k K tree control r t path work2At work1At lengthT s
  have h2 (s : Nat) := upperWriterProgram_slots n k K tree control r t path work1At work2At lengthT s
  have hc := constMinus_length_le lengthRP constants carry (width+2)
  simp only [ltUpdateProgram,surroundCompiled_slots,appendCompiled_slots]
  grind only

theorem lrpUpdateProgram_slots (n width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire)
    (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat) :
    (lrpUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2.gateSlots ≤
      2*lengthRP.length+4*((zeroMapLabels k K).length*lengthRP.length)+144*tree.internalNodes+72+
        16*constants.length := by
  have h1 (s : Nat) := lowerWriterProgram_slots n width k K tree control r t path work1At work2At lengthRP s
  have h2 (s : Nat) := lowerWriterProgram_slots n width k K tree control r t path work2At work1At lengthRP s
  have ha := addConstant_length_le lengthT constants carry 3
  have hs := subConstant_length_le lengthT constants carry 3
  simp only [lrpUpdateProgram,surroundCompiled_slots,appendCompiled_slots]
  grind only


def endUpperSlotBound (r : EndIterationRegisters) (w : EndIterationWindows) : Nat :=
  2*r.lengthT.length+4*((zeroMapLabels w.k4 w.K4).length*r.lengthT.length)+
    144*(r.upperTree w).internalNodes+72+8*r.lengthRP.length+16*r.constants.length

def endLowerSlotBound (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) : Nat :=
  2*r.lengthRP.length+4*((zeroMapLabels w.k5 (w.K5Decode width)).length*r.lengthRP.length)+
    144*(r.lowerTree width w).internalNodes+72+16*r.constants.length

theorem upperEndProgram_slots (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    (upperEndProgram n start r width w).2.gateSlots ≤ endUpperSlotBound r w :=
  ltUpdateProgram_slots n width w.k4 w.K4 (r.upperTree w) r.control (r.rangeAccumulator w.k4 w.K4)
    (r.temporary w.k4 w.K4) r.carry (r.path w.k4 w.K4) r.work1At r.work2At r.lengthT r.lengthRP r.constants start

theorem lowerEndProgram_slots (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    (lowerEndProgram n start r width w).2.gateSlots ≤ endLowerSlotBound r width w :=
  lrpUpdateProgram_slots n width w.k5 (w.K5Decode width) (r.lowerTree width w) r.control
    (r.rangeAccumulator w.k5 (w.K5Decode width)) (r.temporary w.k5 (w.K5Decode width)) r.carry
    (r.path w.k5 (w.K5Decode width)) r.work1At r.work2At r.lengthT r.lengthRP r.constants start

theorem controlledWorkSwap_length_le (control : Wire) (left right : List Wire) :
    (controlledWorkSwap control left right).length ≤ 3*left.length := by
  induction left generalizing right with
  | nil => cases right <;> exact Nat.zero_le _
  | cons l ls ih =>
    cases right with
    | nil => exact Nat.zero_le _
    | cons r rs =>
      have h := ih rs
      simp only [controlledWorkSwap,controlledSwap,List.length_append,List.length_cons,List.length_nil]
      omega

def endSlotBound (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) : Nat :=
  3*r.work1.length+endUpperSlotBound r w+endLowerSlotBound r width w

theorem endProgram_slots (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    (endProgram n start r width w).2.gateSlots ≤ endSlotBound r width w := by
  have hu := upperEndProgram_slots n start r width w
  have hl (s : Nat) := lowerEndProgram_slots n s r width w
  have hs := controlledWorkSwap_length_le r.control r.work1 r.work2
  simp only [endProgram,prependCompiled_slots,appendCompiled_slots,endSlotBound]
  grind only

theorem endInverseProgram_slots (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    (endInverseProgram n start r width w).2.gateSlots ≤ endSlotBound r width w := by
  have hu (s : Nat) := upperEndProgram_slots n s r width w
  have hl := lowerEndProgram_slots n start r width w
  have hs := controlledWorkSwap_length_le r.control r.work1.reverse r.work2.reverse
  simp only [List.length_reverse] at hs
  simp only [endInverseProgram,appendCompiled_slots,literalProgram_slots,controlledWorkSwapInverse,endSlotBound]
  grind only


theorem mcxVChainTail_length_le (acc : Wire) (controls : List Wire) (target : Wire) (scratch : List Wire) :
    (mcxVChainTail acc controls target scratch).length ≤ 2*controls.length := by
  induction controls generalizing acc scratch with
  | nil => exact Nat.zero_le _
  | cons c cs ih =>
    cases cs with
    | nil => simp [mcxVChainTail]
    | cons next rest =>
      cases scratch with
      | nil => exact Nat.zero_le _
      | cons s ss =>
        have h := ih s ss
        simp only [mcxVChainTail,List.length_append,List.length_cons,List.length_nil]
        simp only [List.length_cons] at h
        omega

theorem mcxVChain_length_le (controls : List Wire) (target : Wire) (scratch : List Wire) :
    (mcxVChain controls target scratch).length ≤ 2*controls.length+1 := by
  cases controls with
  | nil => simp [mcxVChain]
  | cons c cs =>
    cases cs with
    | nil => simp [mcxVChain]
    | cons next rest =>
      have h := mcxVChainTail_length_le next (c::rest) target scratch
      simp only [mcxVChain,List.length_cons]
      simp only [List.length_cons] at h
      omega

theorem blockHPrefix_length_le (r : IndexedStepRegisters) :
    (blockHPrefix r).length ≤ 2*r.lengthQ.length+2*r.lengthS.length+7 := by
  have hq := mcxVChain_length_le r.lengthQ (r.sourceScratch.getD 0 0) (r.sourceScratch.drop 2)
  have hs := mcxVChain_length_le (r.lengthS++[r.shiftEpoch]) (r.sourceScratch.getD 1 0) (r.sourceScratch.drop 2)
  simp only [List.length_append,List.length_cons,List.length_nil] at hs
  simp only [blockHPrefix,List.length_append,List.length_cons,List.length_nil]
  omega

theorem blockHSuffix_length_le (r : IndexedStepRegisters) :
    (blockHSuffix r).length ≤ 2*r.lengthQ.length+2*r.lengthS.length+7 := by
  have hq := mcxVChain_length_le r.lengthQ (r.sourceScratch.getD 0 0) (r.sourceScratch.drop 2)
  have hs := mcxVChain_length_le (r.lengthS++[r.shiftEpoch]) (r.sourceScratch.getD 1 0) (r.sourceScratch.drop 2)
  simp only [List.length_append,List.length_cons,List.length_nil] at hs
  simp only [blockHSuffix,List.length_append,List.length_cons,List.length_nil]
  omega

def hSlotBound (r : IndexedStepRegisters) (width T : Nat) : Nat :=
  4*r.lengthQ.length+4*r.lengthS.length+15+
    endSlotBound (r.endIteration width T) width (endIterationWindowsAt width T)

theorem hProgram_slots (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) :
    (hProgram n start r width T).2.gateSlots ≤ hSlotBound r width T := by
  have hp := blockHPrefix_length_le r
  have hs := blockHSuffix_length_le r
  have he := endProgram_slots n start (r.endIteration width T) width (endIterationWindowsAt width T)
  simp only [hProgram,compiledIf_slots]
  split
  · simp only [surroundCompiled_slots,List.length_append,List.length_cons,List.length_nil,hSlotBound]
    omega
  · exact Nat.zero_le _

theorem hInverseProgram_slots (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) :
    (hInverseProgram n start r width T).2.gateSlots ≤ hSlotBound r width T := by
  have hp := blockHPrefix_length_le r
  have hs := blockHSuffix_length_le r
  have he := endInverseProgram_slots n start (r.endIteration width T) width (endIterationWindowsAt width T)
  simp only [hInverseProgram,compiledIf_slots]
  split
  · simp only [surroundCompiled_slots,List.length_append,List.length_cons,List.length_nil,hSlotBound]
    omega
  · exact Nat.zero_le _

end ShorECDLP.Paper2607_13816.ChallengeMigration
