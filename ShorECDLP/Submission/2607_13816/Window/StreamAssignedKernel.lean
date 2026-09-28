import ShorECDLP.Submission.«2607_13816».Window.StreamUniform
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
private theorem indexed_wires (start : Nat) (calls : List AdaptiveCircuit) :
    streamFourierWires (indexedStreamCalls start calls)=streamScalarWires calls.length start := by
  unfold streamFourierWires indexedStreamCalls streamScalarWires
  rw [List.flatMap_map]
  have h := congrArg (fun xs : List Nat => xs.flatMap
    (fun k => (List.range' (windowBankStart k) 16).reverse)) (List.zipIdx_map_snd start calls)
  simpa only [List.flatMap_map,Prod.fst_swap] using h
private theorem left_wires (P Q : Point) :
    streamFourierWires (indexedStreamCalls 1 (streamRawLeftCalls P Q))=streamScalarWires 16 1 := by
  simp only [indexed_wires,streamRawLeftCalls,List.length_cons,List.length_map,
    List.length_reverse,List.length_range]
private theorem right_wires (Q : Point) :
    streamFourierWires (indexedStreamCalls 17 (streamRawRightCalls Q))=streamScalarWires 13 17 := by
  simp only [indexed_wires,streamRawRightCalls,List.length_map,List.length_reverse,List.length_range]
private theorem right_after_left (s : BasisState) :
    (streamScalarWires 13 17).map (fourierClear (streamScalarWires 16 1) s)=
    (streamScalarWires 13 17).map s := by
  apply List.map_congr_left
  intro w hw
  rw [fourierClear_apply,if_neg]
  exact (show ∀ w∈streamScalarWires 13 17, w∉streamScalarWires 16 1 by decide +kernel) w hw

theorem streamFourierKernel_ket (P Q : Point) (a b : List Bool) (s : BasisState) :
    measuredFourierKernel .inverse (streamFourierWires (indexedStreamCalls 17 (streamRawRightCalls Q))) b
      (measuredFourierKernel .inverse (streamFourierWires (indexedStreamCalls 1 (streamRawLeftCalls P Q))) a (ket s)) =
      (((((Real.sqrt 2)⁻¹:ℝ):ℂ)^464)*
        dyadicFourierKernel .inverse 256 (fourierWordMSB ((streamScalarWires 16 1).map s)) (fourierWordLSB a)*
        dyadicFourierKernel .inverse 208 (fourierWordMSB ((streamScalarWires 13 17).map s)) (fourierWordLSB b)) •
      ket (fourierClear (streamScalarWires 13 17) (fourierClear (streamScalarWires 16 1) s)) := by
  rw [left_wires,right_wires,measuredFourierKernel_ket,map_smul,measuredFourierKernel_ket,smul_smul,right_after_left]
  have hl : (streamScalarWires 16 1).length=256 := by decide +kernel
  have hr : (streamScalarWires 13 17).length=208 := by decide +kernel
  rw [hl,hr]
  apply congrArg (fun c : ℂ => c • ket (fourierClear (streamScalarWires 13 17) (fourierClear (streamScalarWires 16 1) s)))
  rw [show 464=256+208 from rfl,pow_add]
  ring
private theorem assignment_words (a b : List Bool) (ha : a.length=256) (hb : b.length=208)
    (s : BasisState) :
    (streamScalarWires 16 1).map (phaseWordState
      ((streamScalarWires 16 1).reverse ++ (streamScalarWires 13 17).reverse) (a++b) s)=a.reverse ∧
    (streamScalarWires 13 17).map (phaseWordState
      ((streamScalarWires 16 1).reverse ++ (streamScalarWires 13 17).reverse) (a++b) s)=b.reverse := by
  have hl : (streamScalarWires 16 1).reverse.length=256 := by decide +kernel
  have hr : (streamScalarWires 13 17).reverse.length=208 := by decide +kernel
  rw [phaseWordState_append _ _ a b (ha.trans hl.symm)]
  have hleft : wireValues (streamScalarWires 16 1).reverse
      (phaseWordState (streamScalarWires 13 17).reverse b
        (phaseWordState (streamScalarWires 16 1).reverse a s))=a := by
    calc
      _ = wireValues (streamScalarWires 16 1).reverse
          (phaseWordState (streamScalarWires 16 1).reverse a s) := by
        apply List.map_congr_left
        intro w hw
        apply phaseWordState_frame
        exact (show ∀ w∈(streamScalarWires 16 1).reverse,
          w∉(streamScalarWires 13 17).reverse by decide +kernel) w hw
      _ = a := phaseWordState_word _ (by decide +kernel) a (ha.trans hl.symm) s
  have hright := phaseWordState_word (streamScalarWires 13 17).reverse
    (by decide +kernel) b (hb.trans hr.symm)
    (phaseWordState (streamScalarWires 16 1).reverse a s)
  constructor
  · simpa only [wireValues,List.map_reverse,List.reverse_reverse] using congrArg List.reverse hleft
  · simpa only [wireValues,List.map_reverse,List.reverse_reverse] using congrArg List.reverse hright

private theorem clear_assigned (R : Point) (bits : List Bool) :
    fourierClear (streamScalarWires 13 17) (fourierClear (streamScalarWires 16 1)
      (pointWrite R (phaseWordState
        ((streamScalarWires 16 1).reverse ++ (streamScalarWires 13 17).reverse) bits
        (scalarRootFlip zeroBasisState)))) = pointWrite R (scalarRootFlip zeroBasisState) := by
  funext w
  simp only [fourierClear_apply]
  by_cases hp : w∈pointLogicalWires
  · have hl : w∉streamScalarWires 16 1 := by
      intro hw
      exact (show ∀ w∈streamScalarWires 16 1, w∉pointLogicalWires by decide +kernel) w hw hp
    have hr : w∉streamScalarWires 13 17 := by
      intro hw
      exact (show ∀ w∈streamScalarWires 13 17, w∉pointLogicalWires by decide +kernel) w hw hp
    simp [hl,hr,pointWrite,hp]
  · by_cases hr : w∈streamScalarWires 13 17
    · have hn := (show ∀ w∈streamScalarWires 13 17, w≠836 by decide +kernel) w hr
      simp [hr,pointWrite,hp,scalarRootFlip,upd,hn,zeroBasisState]
    · by_cases hl : w∈streamScalarWires 16 1
      · have hn := (show ∀ w∈streamScalarWires 16 1, w≠836 by decide +kernel) w hl
        simp [hl,hr,pointWrite,hp,scalarRootFlip,upd,hn,zeroBasisState]
      · have hw : w∉((streamScalarWires 16 1).reverse ++ (streamScalarWires 13 17).reverse) := by
          simpa only [List.mem_append,List.mem_reverse,not_or] using And.intro hl hr
        simp only [if_neg hr,if_neg hl,pointWrite,if_neg hp,
          phaseWordState_frame _ _ _ _ hw]
private theorem point_words (R : Point) (s : BasisState) :
    (streamScalarWires 16 1).map (pointWrite R s)=(streamScalarWires 16 1).map s ∧
    (streamScalarWires 13 17).map (pointWrite R s)=(streamScalarWires 13 17).map s := by
  constructor
  · apply List.map_congr_left
    intro w hw
    exact pointWrite_frame R s w
      ((show ∀ w∈streamScalarWires 16 1, w∉pointLogicalWires by decide +kernel) w hw)
  · apply List.map_congr_left
    intro w hw
    exact pointWrite_frame R s w
      ((show ∀ w∈streamScalarWires 13 17, w∉pointLogicalWires by decide +kernel) w hw)

theorem streamFourierKernel_assigned (P Q : Point) (a b x y : List Bool)
    (ha : a.length=256) (hb : b.length=208) :
    measuredFourierKernel .inverse (streamFourierWires (indexedStreamCalls 17 (streamRawRightCalls Q))) y
      (measuredFourierKernel .inverse (streamFourierWires (indexedStreamCalls 1 (streamRawLeftCalls P Q))) x
        (ket (streamPreparedScalarOutput P Q (phaseWordState
          ((streamScalarWires 16 1).reverse ++ (streamScalarWires 13 17).reverse)
          (a++b) (scalarRootFlip zeroBasisState))))) =
      (((((Real.sqrt 2)⁻¹:ℝ):ℂ)^464)*
        dyadicFourierKernel .inverse 256 (boolWordToNat a) (fourierWordLSB x)*
        dyadicFourierKernel .inverse 208 (boolWordToNat b) (fourierWordLSB y)) •
      ket (pointWrite (boolWordToNat a • P+boolWordToNat b • Q) (scalarRootFlip zeroBasisState)) := by
  have hw := assignment_words a b ha hb (scalarRootFlip zeroBasisState)
  rw [streamPreparedScalarOutput,streamScalarValue_preparedFourierWord,
    streamScalarValue_preparedFourierWord,hw.1,hw.2,fourierWordMSB_reverse,fourierWordMSB_reverse,
    streamFourierKernel_ket,clear_assigned]
  rw [(point_words _ _).1,(point_words _ _).2,hw.1,hw.2,
    fourierWordMSB_reverse,fourierWordMSB_reverse]

end
end ShorECDLP.Paper2607_13816
