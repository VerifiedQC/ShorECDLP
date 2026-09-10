import ShorECDLP.Submission.«2607_13816».Arithmetic.InPlace
import ShorECDLP.Submission.«2607_13816».EEA.ScheduleResources
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
private theorem constant_metrics (acc dirty : List Wire) (bits : List Bool)
    (q c r t : Wire) (ha : acc.length=256) (hd : dirty.length=255) (hb : bits.length=255) :
    (controlledGidneyAddConst acc dirty (true::bits) q c r t).tCount=5348 ∧
    (controlledGidneyAddConst acc dirty (true::bits) q c r t).measurementCount=255 := by
  cases acc with
  | nil => simp at ha
  | cons a rest =>
    cases dirty with
    | nil => simp at hd
    | cons d ds =>
      have ht := controlledGidneyAddConst_tCount_exact a d q c r t rest ds bits (by simp_all) (by simp_all)
      have hm := controlledGidneyAddConst_measurementCount (a::rest) (d::ds) (true::bits) q c r t
        (by simp_all) (by simp_all)
      constructor
      · simpa only [show rest.length=255 by simpa using ha] using ht
      · simpa only [List.all_cons,Bool.not_true,Bool.false_and,Bool.false_eq_true,↓reduceIte,hd] using hm
private theorem comparison_metrics (acc dirty : List Wire) (p : Nat) (c r t f : Wire)
    (ha : acc.length=256) (hd : dirty.length=256) (hp0 : 0<p) (hp : p<2^256) :
    (gidneyCompareGE acc dirty p c r t f).tCount=5369 ∧
    (gidneyCompareGE acc dirty p c r t f).measurementCount=256 := by
  cases acc with
  | nil => simp at ha
  | cons a rest =>
    have h := gidneyCompareGE_metrics a rest dirty p c r t f (by omega) hp0 (by simpa only [ha] using hp)
    exact ⟨by simpa only [ha] using h.2.2.1, by simpa only [ha] using h.2.2.2.1⟩
private theorem four_metrics (a b : Circuit) (c d : AdaptiveCircuit)
    (ha : ShorECDLP.tCount a=5383) (hb : ShorECDLP.tCount b=3591)
    (hc : c.tCount=5369 ∧ c.measurementCount=256)
    (hd : d.tCount=5348 ∧ d.measurementCount=255) :
    (AdaptiveCircuit.unitary a (c.seq (d.seq (.unitary b .done)))).tCount=19691 ∧
    (AdaptiveCircuit.unitary a (c.seq (d.seq (.unitary b .done)))).measurementCount=511 := by
  simp only [AdaptiveCircuit.tCount,AdaptiveCircuit.measurementCount,adaptive_tCount_seq,modularMeasurements_seq,
    ha,hb,hc.1,hc.2,hd.1,hd.2]
  trivial
private theorem modular_add_metrics (input acc : List Wire) (bits : List Bool) (p : Nat)
    (q c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hb : bits.length=255)
    (hp0 : 0<p) (hp : p<2^256) :
    (controlledModularAdd input acc (true::bits) p q c r t f).tCount=19691 ∧
    (controlledModularAdd input acc (true::bits) p q c r t f).measurementCount=511 := by
  have hc := comparison_metrics acc input p c r t f ha hi hp0 hp
  have hd := constant_metrics acc (input.take (acc.length-1)) bits f c r t ha (by simp [ha,hi]) hb
  have hcarry := controlledAddCarry_tCount input acc q c f (by omega)
  have hlt : ShorECDLP.tCount (controlledCompareLT acc input q c f)=3591 := by
    cases acc with
    | nil => simp at ha
    | cons a rest => simpa only [show rest.length=255 by simpa using ha] using
        (controlledCompareLT_counts a rest input q c f (by omega)).2.2.2
  exact four_metrics _ _ _ _ (by simpa only [hi] using hcarry) hlt hc hd
private theorem unitary_pair_metrics (a b : Circuit) (c d : AdaptiveCircuit)
    (ta tb tc td mc md : Nat) (ha : ShorECDLP.tCount a=ta) (hb : ShorECDLP.tCount b=tb)
    (hc : c.tCount=tc ∧ c.measurementCount=mc) (hd : d.tCount=td ∧ d.measurementCount=md) :
    (AdaptiveCircuit.unitary a (c.seq (d.seq (.unitary b .done)))).tCount=ta+(tc+(td+tb)) ∧
    (AdaptiveCircuit.unitary a (c.seq (d.seq (.unitary b .done)))).measurementCount=mc+md := by
  simp only [AdaptiveCircuit.tCount,AdaptiveCircuit.measurementCount,adaptive_tCount_seq,modularMeasurements_seq,
    ha,hb,hc.1,hc.2,hd.1,hd.2,Nat.add_zero,and_self]
private theorem modular_double_metrics (input acc : List Wire) (bits : List Bool) (p : Nat)
    (c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hb : bits.length=255)
    (hp0 : 0<p) (hp : p<2^256) :
    (modularDouble acc input (true::bits) p c r t f).tCount=10717 ∧
    (modularDouble acc input (true::bits) p c r t f).measurementCount=511 := by
  cases acc with
  | nil => simp at ha
  | cons a rest =>
    have hc := comparison_metrics (a::rest) input p c r t f ha hi hp0 hp
    have hd := constant_metrics (a::rest) (input.take rest.length) bits f c r t ha
      (by simp only [List.length_take]; have hh := ha; simp only [List.length_cons] at hh; omega) hb
    exact unitary_pair_metrics _ _ _ _ 0 0 5369 5348 256 255 (doublingShift_counts a f rest).2.2 rfl hc hd
private theorem modular_sub_metrics (input acc : List Wire) (bits : List Bool) (p : Nat)
    (q c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hb : bits.length=255)
    (hp0 : 0<p) (hp : p<2^256) :
    (controlledModularSub input acc (true::bits) p q c r t f).tCount=19691 ∧
    (controlledModularSub input acc (true::bits) p q c r t f).measurementCount=511 := by
  have hc := comparison_metrics acc input p c r t f ha hi hp0 hp
  have hd := constant_metrics acc (input.take (acc.length-1)) bits f c r t ha (by simp [ha,hi]) hb
  have hcarry : ShorECDLP.tCount (controlledSubCarry input acc q c f)=5383 := by
    rw [controlledSubCarry,ShorECDLP.tCount_adjoint,controlledAddCarry_tCount input acc q c f (by omega),hi]
  have hlt : ShorECDLP.tCount (controlledCompareLT acc input q c f)=3591 := by
    cases acc with
    | nil => simp at ha
    | cons a rest => simpa only [show rest.length=255 by simpa using ha] using
        (controlledCompareLT_counts a rest input q c f (by omega)).2.2.2
  exact unitary_pair_metrics _ _ _ _ 3591 5383 5348 5369 255 256 hlt hcarry hd hc
private theorem modular_halve_metrics (input acc : List Wire) (bits : List Bool) (p : Nat)
    (c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hb : bits.length=255)
    (hp0 : 0<p) (hp : p<2^256) :
    (modularHalve acc input (true::bits) p c r t f).tCount=10717 ∧
    (modularHalve acc input (true::bits) p c r t f).measurementCount=511 := by
  cases acc with
  | nil => simp at ha
  | cons a rest =>
    have hc := comparison_metrics (a::rest) input p c r t f ha hi hp0 hp
    have hd := constant_metrics (a::rest) (input.take rest.length) bits f c r t ha
      (by simp only [List.length_take]; have hh := ha; simp only [List.length_cons] at hh; omega) hb
    exact unitary_pair_metrics _ _ _ _ 0 0 5348 5369 255 256 rfl
      ((ShorECDLP.tCount_adjoint _).trans (doublingShift_counts a f rest).2.2) hd hc
private theorem hornerMul_metrics (controls input acc : List Wire) (bits : List Bool) (p : Nat)
    (c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hb : bits.length=255)
    (hp0 : 0<p) (hp : p<2^256) :
    (hornerMul controls input acc (true::bits) p c r t f).tCount=
      controls.length*19691+(controls.length-1)*10717 ∧
    (hornerMul controls input acc (true::bits) p c r t f).measurementCount=(controls.length*2-1)*511 := by
  induction controls with
  | nil => simp [hornerMul,AdaptiveCircuit.tCount,AdaptiveCircuit.measurementCount]
  | cons q qs ih =>
    have hadd := modular_add_metrics input acc bits p q c r t f hi ha hb hp0 hp
    have hdbl := modular_double_metrics input acc bits p f r t c hi ha hb hp0 hp
    rw [hornerMul]
    by_cases hz : qs=[]
    · rw [if_pos hz]
      simp only [adaptive_tCount_seq,modularMeasurements_seq,ih.1,ih.2,hadd.1,hadd.2]
      subst qs
      simp
    · rw [if_neg hz]
      simp only [adaptive_tCount_seq,modularMeasurements_seq,ih.1,ih.2,hadd.1,hadd.2,hdbl.1,hdbl.2,List.length_cons]
      have hn : qs.length ≠ 0 := fun h => hz (List.eq_nil_of_length_eq_zero h)
      omega
private theorem hornerMulInverse_metrics (controls input acc : List Wire) (bits : List Bool) (p : Nat)
    (c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hb : bits.length=255)
    (hp0 : 0<p) (hp : p<2^256) :
    (hornerMulInverse controls input acc (true::bits) p c r t f).tCount=
      controls.length*19691+(controls.length-1)*10717 ∧
    (hornerMulInverse controls input acc (true::bits) p c r t f).measurementCount=(controls.length*2-1)*511 := by
  induction controls with
  | nil => simp [hornerMulInverse,AdaptiveCircuit.tCount,AdaptiveCircuit.measurementCount]
  | cons q qs ih =>
    have hadd := modular_sub_metrics input acc bits p q c r t f hi ha hb hp0 hp
    have hdbl := modular_halve_metrics input acc bits p f r t c hi ha hb hp0 hp
    rw [hornerMulInverse]
    by_cases hz : qs=[]
    · rw [if_pos hz]
      simp only [adaptive_tCount_seq,modularMeasurements_seq,hadd.1,hadd.2,AdaptiveCircuit.tCount,AdaptiveCircuit.measurementCount]
      subst qs
      simp
    · rw [if_neg hz]
      simp only [adaptive_tCount_seq,modularMeasurements_seq,ih.1,ih.2,hadd.1,hadd.2,hdbl.1,hdbl.2,List.length_cons]
      have hn : qs.length ≠ 0 := fun h => hz (List.eq_nil_of_length_eq_zero h)
      omega
private theorem hornerMul_256_metrics (controls input acc : List Wire) (bits tail : List Bool) (p : Nat)
    (c r t f : Wire) (hctrl : controls.length=256) (hi : input.length=256) (ha : acc.length=256)
    (hb : bits.length=256) (he : bits=true::tail) (hp0 : 0<p) (hp : p<2^256) :
    (hornerMul controls input acc bits p c r t f).tCount=7773731 ∧
    (hornerMul controls input acc bits p c r t f).measurementCount=261121 := by
  subst bits
  have ht : tail.length=255 := by simpa using hb
  simpa only [hctrl] using hornerMul_metrics controls input acc tail p c r t f hi ha ht hp0 hp
private theorem hornerMulInverse_256_metrics (controls input acc : List Wire) (bits tail : List Bool) (p : Nat)
    (c r t f : Wire) (hctrl : controls.length=256) (hi : input.length=256) (ha : acc.length=256)
    (hb : bits.length=256) (he : bits=true::tail) (hp0 : 0<p) (hp : p<2^256) :
    (hornerMulInverse controls input acc bits p c r t f).tCount=7773731 ∧
    (hornerMulInverse controls input acc bits p c r t f).measurementCount=261121 := by
  subst bits
  have ht : tail.length=255 := by simpa using hb
  simpa only [hctrl] using hornerMulInverse_metrics controls input acc tail p c r t f hi ha ht hp0 hp
/-- T and measurement counts of the actual Figure 15 arithmetic component. -/
theorem fig15MultiplyToWork_resources : fig15MultiplyToWork.tCount=7773731 ∧ fig15MultiplyToWork.measurementCount=261121 :=
  hornerMul_256_metrics _ _ _ _ secp256k1ReductionConstantBits.tail _ _ _ _ _
    List.length_range' List.length_range' List.length_range'
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
/-- T and measurement counts of the actual Figure 15 arithmetic component. -/
theorem fig15MultiplyToData_resources : fig15MultiplyToData.tCount=7773731 ∧ fig15MultiplyToData.measurementCount=261121 :=
  hornerMul_256_metrics _ _ _ _ secp256k1ReductionConstantBits.tail _ _ _ _ _
    List.length_range' List.length_range' List.length_range'
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
/-- T and measurement counts of the actual Figure 15 arithmetic component. -/
theorem fig15MultiplyToDataInverse_resources : fig15MultiplyToDataInverse.tCount=7773731 ∧ fig15MultiplyToDataInverse.measurementCount=261121 :=
  hornerMulInverse_256_metrics _ _ _ _ (constantBits 256 ShorECDLP.p).tail _ _ _ _ _
    List.length_range' List.length_range' List.length_range'
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem uncenter_measurements (input dirty : List Wire) (modulus : List Bool) (p : Nat)
    (c r t iter : Wire) :
    (eeaUncenter input dirty modulus p c r t iter).measurementCount=
      (eeaCenter input dirty modulus p c r t iter).measurementCount := by
  simp only [eeaUncenter,eeaCenter,modularMeasurements_seq,Nat.add_comm]
private theorem wrapped_measurements (a : AdaptiveCircuit) (c d : Circuit) :
    (AdaptiveCircuit.unitary c (a.seq (.unitary d .done))).measurementCount=a.measurementCount := by
  change (a.seq (.unitary d .done)).measurementCount = _
  rw [modularMeasurements_seq]
  rfl
private theorem unpreprocess_measure_eq : eeaUnpreprocess.measurementCount=eeaPreprocess.measurementCount :=
  (wrapped_measurements _ _ _).trans ((uncenter_measurements _ _ _ _ _ _ _ _).trans
    (wrapped_measurements _ _ _).symm)
private theorem constMinus_measurements (input dirty : List Wire) (modulus : List Bool)
    (q c r t : Wire) (hi : input.length=256) (hd : dirty.length=255)
    (hm : modulus.length=256) (hz : modulus.all (fun b => !b)=false) :
    (controlledConstMinus input dirty modulus q c r t).measurementCount=510 := by
  have hinc := controlledGidneyAddConst_measurementCount input dirty
    ((List.range input.length).map (Nat.testBit 1)) q c r t (by simp) (by omega)
  have hmod := controlledGidneyAddConst_measurementCount input dirty modulus q c r t (by omega) (by omega)
  have hzero : ((List.range 256).map (Nat.testBit 1)).all (fun b => !b)=false := by decide +kernel
  rw [hi,hzero,hd] at hinc
  rw [hz,hd] at hmod
  change ((controlledGidneyAddConst input dirty ((List.range input.length).map (Nat.testBit 1)) q c r t).seq
    (controlledGidneyAddConst input dirty modulus q c r t)).measurementCount=510
  rw [modularMeasurements_seq,hi,hinc,hmod]
  rfl
private theorem parity_measurements_generic (input dirty : List Wire) (modulus : List Bool)
    (c r t iter : Wire) (h : (controlledConstMinus input dirty modulus iter c r t).measurementCount=510) :
    (eeaParityCorrection input dirty modulus c r t iter).measurementCount=510 :=
  (wrapped_measurements _ _ _).trans h
theorem secp256k1EEAParityCorrection_measurementCount :
    secp256k1EEAParityCorrection.measurementCount=510 :=
  parity_measurements_generic _ _ _ _ _ _ _ (constMinus_measurements _ _ _ _ _ _ _
    List.length_range' List.length_range' (by decide +kernel) (by decide +kernel))
private theorem uncenter_T (input dirty : List Wire) (modulus : List Bool) (p : Nat)
    (c r t iter : Wire) : (eeaUncenter input dirty modulus p c r t iter).tCount=
      (eeaCenter input dirty modulus p c r t iter).tCount := by
  simp only [eeaUncenter,eeaCenter,adaptive_tCount_seq,Nat.add_comm]
private theorem wrapped_T (a : AdaptiveCircuit) (c d : Circuit) :
    (AdaptiveCircuit.unitary c (a.seq (.unitary d .done))).tCount=ShorECDLP.tCount c+a.tCount+ShorECDLP.tCount d := by
  change ShorECDLP.tCount c + (a.seq (.unitary d .done)).tCount = _
  rw [adaptive_tCount_seq,unitary_T]
  omega
private theorem wrapped_T_swap (a b : AdaptiveCircuit) (c d e f : Circuit)
    (ha : a.tCount=b.tCount) (hc : ShorECDLP.tCount c=ShorECDLP.tCount f)
    (hd : ShorECDLP.tCount d=ShorECDLP.tCount e) :
    (AdaptiveCircuit.unitary c (a.seq (.unitary d .done))).tCount=
      (AdaptiveCircuit.unitary e (b.seq (.unitary f .done))).tCount := by
  simp only [wrapped_T,ha,hc,hd]
  omega
private theorem unpreprocess_T_eq : eeaUnpreprocess.tCount=eeaPreprocess.tCount := by
  have hl : ShorECDLP.tCount eeaLengthUndo=ShorECDLP.tCount eeaLengthSetup := by
    simp only [eeaLengthUndo,eeaLengthSetup,ShorECDLP.tCount_append]
    omega
  have hw : ShorECDLP.tCount workRegistersRestore=ShorECDLP.tCount workRegistersPrepare := by
    rw [workRegistersRestore_resources.2.2.2.2,workRegistersPrepare_resources.2.2.2.2]
  have hu := uncenter_T (List.range' 266 256).reverse (List.range' 4 256)
    (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2
  exact wrapped_T_swap
    (eeaUncenter (List.range' 266 256).reverse (List.range' 4 256) (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2)
    (eeaCenter (List.range' 266 256).reverse (List.range' 4 256) (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2)
    eeaLengthUndo workRegistersRestore workRegistersPrepare eeaLengthSetup hu hl hw

theorem eeaUnpreprocess_tCount : eeaUnpreprocess.tCount=933541 :=
  unpreprocess_T_eq.trans eeaPreprocess_resources.2.2.2.1
private theorem constMinus_T (input dirty : List Wire) (bits : List Bool)
    (q c r t : Wire) (hi : input.length=256) (hd : dirty.length=255) (hb : bits.length=255) :
    (controlledConstMinus input dirty (true::bits) q c r t).tCount=10696 := by
  have hone := (constant_metrics input dirty (List.replicate 255 false) q c r t hi hd (by simp only [List.length_replicate])).1
  have hmod := (constant_metrics input dirty bits q c r t hi hd hb).1
  have he : ((List.range 256).map (Nat.testBit 1))=true::List.replicate 255 false := by decide +kernel
  have hz : ShorECDLP.tCount (input.map (Gate.CX q))=0 := by
    simp [ShorECDLP.tCount,List.map_map,Function.comp_def,ShorECDLP.tCost]
  change ShorECDLP.tCount (input.map (Gate.CX q)) +
    ((controlledGidneyAddConst input dirty ((List.range input.length).map (Nat.testBit 1)) q c r t).seq
      (controlledGidneyAddConst input dirty (true::bits) q c r t)).tCount=10696
  rw [hz,adaptive_tCount_seq,hi,he,hone,hmod]
private theorem parity_T_generic (input dirty : List Wire) (modulus : List Bool)
    (c r t iter : Wire) (h : (controlledConstMinus input dirty modulus iter c r t).tCount=10696) :
    (eeaParityCorrection input dirty modulus c r t iter).tCount=10696 :=
  (wrapped_T _ _ _).trans (show _=10696 by rw [h]; rfl)
private theorem constMinus_256_T (input dirty : List Wire) (bits tail : List Bool)
    (q c r t : Wire) (hi : input.length=256) (hd : dirty.length=255) (hb : bits.length=256)
    (he : bits=true::tail) : (controlledConstMinus input dirty bits q c r t).tCount=10696 := by
  subst bits
  exact constMinus_T _ _ _ _ _ _ _ hi hd (by simpa only [List.length_cons] using Nat.add_right_cancel (show tail.length+1=255+1 from hb))
theorem secp256k1EEAParityCorrection_tCount : secp256k1EEAParityCorrection.tCount=10696 :=
  parity_T_generic _ _ _ _ _ _ _ (constMinus_256_T _ _ _ secp256k1ModulusBits.tail _ _ _ _
    List.length_range' List.length_range' (by decide +kernel) (by decide +kernel))
private theorem forward_wrapper_T (pre schedule parity : AdaptiveCircuit) (a b : Circuit)
    (hpre : pre.tCount=933541) (hs : schedule.tCount=122179575) (hp : parity.tCount=10696)
    (ha : ShorECDLP.tCount a=18445) (hb : ShorECDLP.tCount b=0) :
    ((((pre.seq schedule).seq (.unitary a .done)).seq parity).seq (.unitary b .done)).tCount=123142257 := by
  simp only [adaptive_tCount_seq,unitary_T,hpre,hs,hp,ha,hb]
private theorem rotation_epoch_T : ShorECDLP.tCount (canonicalWork2Rotation++terminalEpochCompression)=18445 := by
  rw [ShorECDLP.tCount_append,canonicalWork2Rotation_resources.2.2.2.1,terminalEpochCompression_resources.2.2.2.1]
private theorem inverse_rotation_epoch_T : ShorECDLP.tCount (terminalEpochCompression++canonicalWork2InverseRotation)=18445 := by
  rw [ShorECDLP.tCount_append,canonicalWork2InverseRotation_resources.2.2.2.1,terminalEpochCompression_resources.2.2.2.1]
theorem secp256k1EEAForwardWrapper_tCount : secp256k1EEAForwardWrapper.tCount=123142257 :=
  forward_wrapper_T _ _ _ _ _ eeaPreprocess_resources.2.2.2.1 secp256k1EEAForwardAdaptive_tCount
    secp256k1EEAParityCorrection_tCount rotation_epoch_T terminalWork1Clear_resources.2.2.2.1
private theorem reverse_wrapper_T (pre schedule parity : AdaptiveCircuit) (a b : Circuit)
    (hpre : pre.tCount=933541) (hs : schedule.tCount=122179575) (hp : parity.tCount=10696)
    (ha : ShorECDLP.tCount a=0) (hb : ShorECDLP.tCount b=18445) :
    (((((AdaptiveCircuit.unitary a .done).seq parity).seq (.unitary b .done)).seq schedule).seq pre).tCount=123142257 := by
  simp only [adaptive_tCount_seq,unitary_T,hpre,hs,hp,ha,hb]
theorem secp256k1EEAReverseWrapper_tCount : secp256k1EEAReverseWrapper.tCount=123142257 :=
  reverse_wrapper_T _ _ _ _ _ eeaUnpreprocess_tCount secp256k1EEAReverseAdaptive_tCount
    secp256k1EEAParityCorrection_tCount terminalWork1Clear_resources.2.2.2.1 inverse_rotation_epoch_T
private theorem forward_bank_T : secp256k1EEAForwardInDataBank.tCount=123142257 :=
  (AdaptiveCircuit.relabel_tCount _ _).trans secp256k1EEAForwardWrapper_tCount
private theorem reverse_bank_T : secp256k1EEAReverseInDataBank.tCount=123142257 :=
  (AdaptiveCircuit.relabel_tCount _ _).trans secp256k1EEAReverseWrapper_tCount

attribute [local irreducible] eeaPreprocess eeaUnpreprocess AdaptiveCircuit.measurementCount
theorem eeaUnpreprocess_measurementCount : eeaUnpreprocess.measurementCount=766 :=
  unpreprocess_measure_eq.trans eeaPreprocess_resources.2.2.2.2.1
private theorem forward_wrapper_measurements (pre schedule parity : AdaptiveCircuit) (a b : Circuit)
    (hpre : pre.measurementCount=766) (hs : schedule.measurementCount=5278832)
    (hp : parity.measurementCount=510) :
    ((((pre.seq schedule).seq (.unitary a .done)).seq parity).seq (.unitary b .done)).measurementCount=5280108 := by
  simp only [modularMeasurements_seq,AdaptiveCircuit.measurementCount,hpre,hs,hp]
theorem secp256k1EEAForwardWrapper_measurementCount :
    secp256k1EEAForwardWrapper.measurementCount=5280108 :=
  forward_wrapper_measurements _ _ _ _ _ eeaPreprocess_resources.2.2.2.2.1
    secp256k1EEAForwardAdaptive_measurementCount secp256k1EEAParityCorrection_measurementCount
private theorem reverse_wrapper_measurements (pre schedule parity : AdaptiveCircuit) (a b : Circuit)
    (hpre : pre.measurementCount=766) (hs : schedule.measurementCount=5278832)
    (hp : parity.measurementCount=510) :
    (((((AdaptiveCircuit.unitary a .done).seq parity).seq (.unitary b .done)).seq schedule).seq pre).measurementCount=5280108 := by
  simp only [modularMeasurements_seq,AdaptiveCircuit.measurementCount,hpre,hs,hp]
theorem secp256k1EEAReverseWrapper_measurementCount :
    secp256k1EEAReverseWrapper.measurementCount=5280108 :=
  reverse_wrapper_measurements _ _ _ _ _ eeaUnpreprocess_measurementCount
    secp256k1EEAReverseAdaptive_measurementCount secp256k1EEAParityCorrection_measurementCount

private theorem forward_bank_measurements : secp256k1EEAForwardInDataBank.measurementCount=5280108 :=
  (AdaptiveCircuit.relabel_measurementCount _ _).trans secp256k1EEAForwardWrapper_measurementCount
private theorem reverse_bank_measurements : secp256k1EEAReverseInDataBank.measurementCount=5280108 :=
  (AdaptiveCircuit.relabel_measurementCount _ _).trans secp256k1EEAReverseWrapper_measurementCount
attribute [local irreducible] fig15MultiplyToWork fig15MultiplyToData fig15MultiplyToDataInverse
  secp256k1EEAForwardWrapper secp256k1EEAForwardInDataBank secp256k1EEAReverseInDataBank
/-- Worst-branch measurement total of the same complete division circuit as the coherent contract. -/
theorem secp256k1InPlaceDivision_measurements :
    secp256k1InPlaceDivision.measurementCount=11343835 := by
  rw [secp256k1InPlaceDivision_measurementCount,secp256k1EEAForwardWrapper_measurementCount,
    fig15MultiplyToWork_resources.2,reverse_bank_measurements,
    fig15MultiplyToData_resources.2,fig15MultiplyToDataInverse_resources.2]
/-- Worst-branch measurement total of the complete multiplication circuit. -/
theorem secp256k1InPlaceMultiplication_measurements :
    secp256k1InPlaceMultiplication.measurementCount=11343835 := by
  rw [secp256k1InPlaceMultiplication_measurementCount,fig15MultiplyToWork_resources.2,
    forward_bank_measurements,fig15MultiplyToData_resources.2,
    fig15MultiplyToDataInverse_resources.2,reverse_bank_measurements]
/-- Worst-branch T total on the same complete division circuit as the coherent contract. -/
theorem secp256k1InPlaceDivision_T : secp256k1InPlaceDivision.tCount=269605707 := by
  rw [secp256k1InPlaceDivision_tCount,secp256k1EEAForwardWrapper_tCount,
    fig15MultiplyToWork_resources.1,reverse_bank_T,
    fig15MultiplyToData_resources.1,fig15MultiplyToDataInverse_resources.1]
/-- Worst-branch T total on the same complete multiplication circuit as the coherent contract. -/
theorem secp256k1InPlaceMultiplication_T : secp256k1InPlaceMultiplication.tCount=269605707 := by
  rw [secp256k1InPlaceMultiplication_tCount,fig15MultiplyToWork_resources.1,forward_bank_T,
    fig15MultiplyToData_resources.1,fig15MultiplyToDataInverse_resources.1,reverse_bank_T]

end ShorECDLP.Paper2607_13816
