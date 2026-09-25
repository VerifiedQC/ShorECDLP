import ShorECDLP.Submission.«2607_13816».Window.StreamInterference
/-! Scalar reconstruction in the actual streaming Fourier wire order.
The two clear operations remove the prepared phase words and preserve the point
and root bit. These identities do not assert a sampling probability. -/
namespace ShorECDLP.Paper2607_13816
open Quantum ShorECDLP.Secp256k1
noncomputable section
private theorem msb_append (a b : List Bool) :
    fourierWordMSB (a++b)=2^b.length*fourierWordMSB a+fourierWordMSB b := by
  induction a with
  | nil => simp [fourierWordMSB]
  | cons x xs ih => simp [fourierWordMSB,ih,pow_add]; ring
private theorem word_append (a b : List Bool) :
    boolWordToNat (a++b)=boolWordToNat a+2^a.length*boolWordToNat b := by
  induction a with
  | nil => simp [boolWordToNat]
  | cons x xs ih => simp [boolWordToNat,ih,pow_succ]; ring
private theorem digit_word (j : Nat) (s : BasisState) :
    windowRawDigit j s = boolWordToNat (wireValues (List.range' (windowBankStart j) 16) s) := by
  rw [show List.range' (windowBankStart j) 16 =
    List.range' (windowBankStart j) 15 ++ [windowBankStart j+15] by
      simpa using (List.range'_append (s:=windowBankStart j) (m:=15) (n:=1) (step:=1)).symm]
  simp [windowRawDigit,windowAddressBits,wireValues,word_append,boolWordToNat]
def streamScalarWires (n j : Nat) : List Wire :=
  (List.range' j n).flatMap (fun k => (List.range' (windowBankStart k) 16).reverse)
private theorem wires_succ (n j : Nat) : streamScalarWires (n+1) j =
    (List.range' (windowBankStart j) 16).reverse ++ streamScalarWires n (j+1) := by
  unfold streamScalarWires
  rw [List.range'_succ,List.flatMap_cons]
private theorem wires_length (n j : Nat) : (streamScalarWires n j).length=16*n := by
  induction n generalizing j with
  | zero => simp [streamScalarWires]
  | succ n ih =>
    rw [wires_succ,List.length_append,List.length_reverse,List.length_range',ih]
    omega
theorem streamScalarValue_fourierWord (n j : Nat) (s : BasisState) :
    streamScalarValue n j s = fourierWordMSB ((streamScalarWires n j).map s) := by
  induction n generalizing j with
  | zero => simp [streamScalarValue,streamScalarWires,fourierWordMSB]
  | succ n ih =>
    have hd := digit_word j s
    simp only [wireValues] at hd
    rw [streamScalarValue,wires_succ,List.map_append,msb_append,List.map_reverse,
      fourierWordMSB_reverse,← hd,← ih,List.length_map,wires_length]
    rw [pow_mul]
    ring

private theorem bank_shift (j : Nat) :
    (List.range' (windowBankStart j) 16).map streamPreparedWire =
    List.range' (windowBankStart (j+1)) 16 := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range',Nat.one_mul,streamPreparedWire_bank]
private theorem wires_shift (n j : Nat) :
    (streamScalarWires n j).map streamPreparedWire=streamScalarWires n (j+1) := by
  induction n generalizing j with
  | zero => simp [streamScalarWires]
  | succ n ih => rw [wires_succ,List.map_append,List.map_reverse,bank_shift,ih,wires_succ]
theorem streamScalarValue_preparedFourierWord (n j : Nat) (s : BasisState) :
    streamScalarValue n j (s ∘ streamPreparedWire) =
    fourierWordMSB ((streamScalarWires n (j+1)).map s) := by
  rw [streamScalarValue_fourierWord,← wires_shift,List.map_map]
private theorem indexed_wires (start : Nat) (calls : List AdaptiveCircuit) :
    streamFourierWires (indexedStreamCalls start calls)=streamScalarWires calls.length start := by
  unfold streamFourierWires indexedStreamCalls streamScalarWires
  rw [List.flatMap_map]
  have h := congrArg (fun xs : List Nat => xs.flatMap
    (fun k => (List.range' (windowBankStart k) 16).reverse)) (List.zipIdx_map_snd start calls)
  simpa only [List.flatMap_map,Prod.fst_swap] using h
theorem streamPreparedScalar_fourierWords (P Q : Point) (s : BasisState) :
    streamScalarValue 16 0 (s ∘ streamPreparedWire) =
      fourierWordMSB ((streamFourierWires (indexedStreamCalls 1 (streamRawLeftCalls P Q))).map s) ∧
    streamScalarValue 13 16 (s ∘ streamPreparedWire) =
      fourierWordMSB ((streamFourierWires (indexedStreamCalls 17 (streamRawRightCalls Q))).map s) := by
  simp only [indexed_wires,streamRawLeftCalls,streamRawRightCalls,List.length_cons,
    List.length_map,List.length_reverse,List.length_range]
  exact ⟨streamScalarValue_preparedFourierWord 16 0 s,streamScalarValue_preparedFourierWord 13 16 s⟩

private theorem wires_mem (n j w : Nat) : w ∈ streamScalarWires n j ↔
    windowBankStart j ≤ w ∧ w < windowBankStart (j+n) := by
  induction n generalizing j with
  | zero => simp [streamScalarWires]
  | succ n ih =>
    rw [wires_succ,List.mem_append,List.mem_reverse,List.mem_range'_1,ih]
    simp only [windowBankStart]
    omega
theorem streamPreparedScalar_fourierClear (R : Point) (bits : List Bool) :
    fourierClear (streamScalarWires 13 17) (fourierClear (streamScalarWires 16 1)
      (pointWrite R (phaseWordState (List.range' 871 464) bits (scalarRootFlip zeroBasisState)))) =
    pointWrite R (scalarRootFlip zeroBasisState) := by
  funext w
  simp only [fourierClear_apply]
  by_cases hp : w∈pointLogicalWires
  · have hb := pointLogicalWires_bound w hp
    have hl : w∉streamScalarWires 16 1 := by rw [wires_mem]; simp only [windowBankStart]; dsimp only [Wire] at *; omega
    have hr : w∉streamScalarWires 13 17 := by rw [wires_mem]; simp only [windowBankStart]; dsimp only [Wire] at *; omega
    simp [hl,hr,pointWrite,hp]
  · by_cases hr : w∈streamScalarWires 13 17
    · have hb := (wires_mem 13 17 w).mp hr
      have hn : w≠836 := by simp only [windowBankStart] at hb; dsimp only [Wire] at *; omega
      simp [hr,pointWrite,hp,scalarRootFlip,upd,hn,zeroBasisState]
    · by_cases hl : w∈streamScalarWires 16 1
      · have hb := (wires_mem 16 1 w).mp hl
        have hn : w≠836 := by simp only [windowBankStart] at hb; dsimp only [Wire] at *; omega
        simp [hl,hr,pointWrite,hp,scalarRootFlip,upd,hn,zeroBasisState]
      · have hw : w∉List.range' 871 464 := by
          rw [wires_mem] at hl hr
          simp only [windowBankStart,List.mem_range'_1] at *
          omega
        simp only [if_neg hr,if_neg hl,pointWrite,if_neg hp,
          phaseWordState_frame _ _ _ _ hw]

/-- Clearing the actual two-axis Fourier registers retains the point and root. -/
theorem streamPreparedFourierWires_clear (P Q R : Point) (bits : List Bool) :
    fourierClear (streamFourierWires (indexedStreamCalls 17 (streamRawRightCalls Q)))
      (fourierClear (streamFourierWires (indexedStreamCalls 1 (streamRawLeftCalls P Q)))
        (pointWrite R (phaseWordState (List.range' 871 464) bits
          (scalarRootFlip zeroBasisState)))) = pointWrite R (scalarRootFlip zeroBasisState) := by
  simp only [indexed_wires,streamRawLeftCalls,streamRawRightCalls,List.length_cons,
    List.length_map,List.length_reverse,List.length_range]
  exact streamPreparedScalar_fourierClear R bits

end
end ShorECDLP.Paper2607_13816
