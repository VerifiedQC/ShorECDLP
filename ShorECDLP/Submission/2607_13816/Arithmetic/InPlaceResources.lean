import ShorECDLP.Submission.«2607_13816».Arithmetic.InPlace
/-! Resource composition for the literal Figure 15 schedules.
The component equalities retain the actual adaptive circuit terms. -/
namespace ShorECDLP.Paper2607_13816
open Quantum
private theorem adaptive_tCount_seq (a b : AdaptiveCircuit) :
    (a.seq b).tCount = a.tCount+b.tCount := by
  simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b
private theorem resetThen_tCount (targets : List Wire) (next : List Bool → AdaptiveCircuit)
    (count : Nat) (h : ∀ bs, bs.length=targets.length → (next bs).tCount=count) :
    (measureResetThen targets next).tCount=count := by
  induction targets generalizing next with
  | nil => simpa only [measureResetThen, List.length_nil, Nat.zero_add] using h [] rfl
  | cons t ts ih =>
    change max _ _ = _
    rw [ih _ (by intro bs hb; apply h; simp [hb]),ih _ (by intro bs hb; apply h; simp [hb]),Nat.max_self]
private theorem resetThen_measurements (targets : List Wire) (next : List Bool → AdaptiveCircuit)
    (count : Nat) (h : ∀ bs, bs.length=targets.length → (next bs).measurementCount=count) :
    (measureResetThen targets next).measurementCount=targets.length+count := by
  induction targets generalizing next with
  | nil => simpa only [measureResetThen, List.length_nil, Nat.zero_add] using h [] rfl
  | cons t ts ih =>
    change 1+max _ _ = (ts.length+1)+count
    rw [ih _ (by intro bs hb; apply h; simp [hb]),ih _ (by intro bs hb; apply h; simp [hb]),Nat.max_self]
    omega
private theorem z_correction_T (targets : List Wire) (outcomes : List Bool) :
    ShorECDLP.tCount (registerZCorrection targets outcomes)=0 := by
  induction targets generalizing outcomes with
  | nil => rfl
  | cons w ws ih =>
    cases outcomes with
    | nil => rfl
    | cons b bs =>
      cases b <;> simp only [registerZCorrection, Bool.false_eq_true, ↓reduceIte, ShorECDLP.tCount_append, ih]
      all_goals rfl
private theorem swap_list_T (xs : List Nat) :
    ShorECDLP.tCount (xs.flatMap (fun i =>
      [.CX (580+i) (7+i), .CX (7+i) (580+i), .CX (580+i) (7+i)]))=0 := by
  induction xs with
  | nil => rfl
  | cons i is ih =>
    rw [List.flatMap_cons, ShorECDLP.tCount_append, ih]
    rfl
private theorem swap_T : ShorECDLP.tCount fig15SwapOutput=0 :=
  swap_list_T _
private theorem unitary_T (c : Circuit) :
    (AdaptiveCircuit.unitary c .done).tCount = ShorECDLP.tCount c := by
  change ShorECDLP.tCount c + 0 = _
  omega
private theorem after_T_generic (a b c : AdaptiveCircuit) (z swap : Circuit)
    (hz : ShorECDLP.tCount z = 0) (hs : ShorECDLP.tCount swap = 0) :
    ((((a.seq b).seq (.unitary z .done)).seq c).seq (.unitary swap .done)).tCount = a.tCount+b.tCount+c.tCount := by
  simp only [adaptive_tCount_seq,unitary_T,hz,hs,Nat.add_zero]
private theorem division_after_T (bs : List Bool) : (fig15DivisionAfterReset bs).tCount =
    secp256k1EEAReverseInDataBank.tCount+fig15MultiplyToData.tCount+fig15MultiplyToDataInverse.tCount :=
  after_T_generic _ _ _ _ _ (z_correction_T _ _) swap_T
private theorem division_T_generic (a b : AdaptiveCircuit) (ts : List Wire)
    (next : List Bool → AdaptiveCircuit) (n : Nat)
    (hn : ∀ bs, bs.length=ts.length → (next bs).tCount=n) :
    ((a.seq b).seq (measureResetThen ts next)).tCount=a.tCount+b.tCount+n := by
  rw [adaptive_tCount_seq, adaptive_tCount_seq, resetThen_tCount ts next n hn]
/-- Exact T accounting on the complete adaptive division schedule. -/
theorem secp256k1InPlaceDivision_tCount :
    secp256k1InPlaceDivision.tCount = secp256k1EEAForwardWrapper.tCount +
      fig15MultiplyToWork.tCount + (secp256k1EEAReverseInDataBank.tCount +
      fig15MultiplyToData.tCount + fig15MultiplyToDataInverse.tCount) :=
  division_T_generic _ _ _ _ _ (fun bs _ => division_after_T bs)
private theorem multiplication_after_T_generic (a b c d : AdaptiveCircuit) (z swap : Circuit)
    (hz : ShorECDLP.tCount z=0) (hs : ShorECDLP.tCount swap=0) :
    (((((a.seq b).seq (.unitary z .done)).seq c).seq d).seq (.unitary swap .done)).tCount =
      a.tCount+b.tCount+c.tCount+d.tCount := by
  simp only [adaptive_tCount_seq,unitary_T,hz,hs,Nat.add_zero]
private theorem multiplication_after_T (bs : List Bool) :
    (fig15MultiplicationAfterReset bs).tCount =
      secp256k1EEAForwardInDataBank.tCount+fig15MultiplyToData.tCount+
      fig15MultiplyToDataInverse.tCount+secp256k1EEAReverseInDataBank.tCount :=
  multiplication_after_T_generic _ _ _ _ _ _ (z_correction_T _ _) swap_T
private theorem multiplication_T_generic (a : AdaptiveCircuit) (ts : List Wire)
    (next : List Bool → AdaptiveCircuit) (n : Nat)
    (hn : ∀ bs, bs.length=ts.length → (next bs).tCount=n) :
    (a.seq (measureResetThen ts next)).tCount=a.tCount+n := by
  rw [adaptive_tCount_seq, resetThen_tCount ts next n hn]
/-- Exact T accounting on the complete adaptive multiplication schedule. -/
theorem secp256k1InPlaceMultiplication_tCount :
    secp256k1InPlaceMultiplication.tCount = fig15MultiplyToWork.tCount +
      (secp256k1EEAForwardInDataBank.tCount+fig15MultiplyToData.tCount+
      fig15MultiplyToDataInverse.tCount+secp256k1EEAReverseInDataBank.tCount) :=
  multiplication_T_generic _ _ _ _ (fun bs _ => multiplication_after_T bs)
private theorem unitary_measurements (c : Circuit) :
    (AdaptiveCircuit.unitary c .done).measurementCount=0 := rfl
private theorem after_measurements_generic (a b c : AdaptiveCircuit) (z swap : Circuit) :
    ((((a.seq b).seq (.unitary z .done)).seq c).seq (.unitary swap .done)).measurementCount =
      a.measurementCount+b.measurementCount+c.measurementCount := by
  simp only [modularMeasurements_seq, unitary_measurements, Nat.add_zero]
private theorem division_after_measurements (bs : List Bool) :
    (fig15DivisionAfterReset bs).measurementCount = secp256k1EEAReverseInDataBank.measurementCount+
      fig15MultiplyToData.measurementCount+fig15MultiplyToDataInverse.measurementCount :=
  after_measurements_generic _ _ _ _ _
private theorem division_measurements_generic (a b : AdaptiveCircuit) (ts : List Wire)
    (next : List Bool → AdaptiveCircuit) (n : Nat) (len : Nat) (hlen : ts.length=len)
    (hn : ∀ bs, bs.length=ts.length → (next bs).measurementCount=n) :
    ((a.seq b).seq (measureResetThen ts next)).measurementCount=
      a.measurementCount+b.measurementCount+(len+n) := by
  rw [modularMeasurements_seq, modularMeasurements_seq, resetThen_measurements ts next n hn, hlen]
/-- Counts every measurement, including the 256-bit Y reset. -/
theorem secp256k1InPlaceDivision_measurementCount :
    secp256k1InPlaceDivision.measurementCount = secp256k1EEAForwardWrapper.measurementCount +
      fig15MultiplyToWork.measurementCount + (256+(secp256k1EEAReverseInDataBank.measurementCount +
      fig15MultiplyToData.measurementCount + fig15MultiplyToDataInverse.measurementCount)) :=
  division_measurements_generic _ _ _ _ _ 256 List.length_range' (fun bs _ => division_after_measurements bs)
private theorem multiplication_after_measurements_generic (a b c d : AdaptiveCircuit) (z swap : Circuit) :
    (((((a.seq b).seq (.unitary z .done)).seq c).seq d).seq (.unitary swap .done)).measurementCount =
      a.measurementCount+b.measurementCount+c.measurementCount+d.measurementCount := by
  simp only [modularMeasurements_seq,unitary_measurements,Nat.add_zero]
private theorem multiplication_after_measurements (bs : List Bool) :
    (fig15MultiplicationAfterReset bs).measurementCount =
      secp256k1EEAForwardInDataBank.measurementCount+fig15MultiplyToData.measurementCount+
      fig15MultiplyToDataInverse.measurementCount+secp256k1EEAReverseInDataBank.measurementCount :=
  multiplication_after_measurements_generic _ _ _ _ _ _
private theorem multiplication_measurements_generic (a : AdaptiveCircuit) (ts : List Wire)
    (next : List Bool → AdaptiveCircuit) (n : Nat) (len : Nat) (hlen : ts.length=len)
    (hn : ∀ bs, bs.length=ts.length → (next bs).measurementCount=n) :
    (a.seq (measureResetThen ts next)).measurementCount=a.measurementCount+(len+n) := by
  rw [modularMeasurements_seq, resetThen_measurements ts next n hn, hlen]
/-- Counts every measurement on the actual multiplication schedule. -/
theorem secp256k1InPlaceMultiplication_measurementCount :
    secp256k1InPlaceMultiplication.measurementCount = fig15MultiplyToWork.measurementCount +
      (256+(secp256k1EEAForwardInDataBank.measurementCount+fig15MultiplyToData.measurementCount+
      fig15MultiplyToDataInverse.measurementCount+secp256k1EEAReverseInDataBank.measurementCount)) :=
  multiplication_measurements_generic _ _ _ _ 256 List.length_range' (fun bs _ => multiplication_after_measurements bs)
end ShorECDLP.Paper2607_13816
