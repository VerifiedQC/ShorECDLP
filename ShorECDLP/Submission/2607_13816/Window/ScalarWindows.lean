import ShorECDLP.Submission.«2607_13816».Window.OddTables
import ShorECDLP.Submission.«2607_13816».Window.PreparedSchedule
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section

def rawWindowDigits : Nat → Nat → BasisState → List Nat
  | 0, _, _ => []
  | n+1, j, s => windowRawDigit j s::rawWindowDigits n (j+1) s

def radixGeometric : Nat → Nat
  | 0 => 0
  | n+1 => 1+65536*radixGeometric n

private theorem axis_delta (P : Point) (hP : P≠0) (hr : order • P=0)
    (start j : Nat) (s : BasisState) (hs : WindowPointValid s) :
    preparedWindowDelta (fun k => oddWindowX P (k-start)) (fun k => oddWindowY P (k-start))
      (fun k => oddWindowTable_valid P hP hr (k-start)) j s=
    signedWindowDigit 16 (windowRawDigit j s) • ((2^(16*(j-start)):Nat) • P)+
      (2^(16*(j-start)):Nat) • signedWindowHalfPoint P order := by
  obtain ⟨hv,A,hA⟩ := hs
  have h1 := preparedWindowCallState_correct (fun k => oddWindowX P (k-start))
    (fun k => oddWindowY P (k-start)) (fun k => oddWindowTable_valid P hP hr (k-start)) j A s hv hA
  have h2 := preparedOddWindowCallAt_correct P hP hr start j A s hv hA
  exact add_left_cancel (pointWrite_injective s (h1.symm.trans h2))

private theorem order_odd : Odd order := by decide +kernel
private theorem half_scalar {G : Type} [AddCommGroup G] (Q : G) (t : Nat) (v : Int) :
    v • (t • (Q+Q))+t • Q=((2*v+1)*(t:Int)) • Q := by
  simp only [smul_add,←natCast_zsmul,smul_smul,←add_zsmul]
  apply congrArg (fun z : Int => z • Q)
  ring

private theorem axis_delta_half (P : Point) (hr : order • P=0) (k value : Nat) :
    signedWindowDigit 16 value • ((2^(16*k):Nat) • P)+(2^(16*k):Nat) • signedWindowHalfPoint P order=
    ((2*(value:Int)-65535)*(65536:Int)^k) • signedWindowHalfPoint P order := by
  have hd := signedWindowHalfPoint_double P order order_odd hr
  have hm := congrArg (fun R : Point => (2^(16*k):Nat) • R) hd.symm
  dsimp only at hm
  rw [hm,half_scalar]
  apply congrArg (fun z : Int => z • signedWindowHalfPoint P order)
  change (2*((value:Int)-32768)+1)*((2^(16*k):Nat):Int)=_
  push_cast
  rw [show (2:Int)^(16*k)=(65536:Int)^k by rw [pow_mul]; norm_num]
  ring

private theorem axis_sum (P : Point) (hP : P≠0) (hr : order • P=0)
    (start n j : Nat) (hj : start≤j) (s : BasisState) (hs : WindowPointValid s) :
    preparedWindowSum (fun k => oddWindowX P (k-start)) (fun k => oddWindowY P (k-start))
      (fun k => oddWindowTable_valid P hP hr (k-start)) n j s=
    ((65536:Int)^(j-start)*(2*(windowValue 65536 (rawWindowDigits n j s):Int)-
      65535*(radixGeometric n:Int))) • signedWindowHalfPoint P order := by
  induction n generalizing j with
  | zero => simp [preparedWindowSum,rawWindowDigits,windowValue,radixGeometric]
  | succ n ih =>
    rw [preparedWindowSum,axis_delta P hP hr start j s hs,axis_delta_half P hr (j-start),
      ih (j+1) (by omega),←add_zsmul]
    apply congrArg (fun z : Int => z • signedWindowHalfPoint P order)
    simp only [rawWindowDigits,windowValue,radixGeometric]
    push_cast
    rw [show j+1-start=(j-start)+1 by omega,pow_succ]
    ring
def axisWindowProgram (P : Point) (hP : P≠0) (hr : order • P=0) (start n : Nat) : AdaptiveCircuit :=
  preparedWindowSchedule (fun k => oddWindowX P (k-start)) (fun k => oddWindowY P (k-start))
    (fun k => oddWindowTable_valid P hP hr (k-start)) n start

def axisWindowState (P : Point) (hP : P≠0) (hr : order • P=0) (start n : Nat) : BasisState → BasisState :=
  preparedWindowScheduleState (fun k => oddWindowX P (k-start)) (fun k => oddWindowY P (k-start))
    (fun k => oddWindowTable_valid P hP hr (k-start)) n start

def axisWindowOffset (P : Point) (n : Nat) : Point :=
  (65535*radixGeometric n) • signedWindowHalfPoint P order

private theorem half_reconstruct {G : Type} [AddCommGroup G] (P Q : G) (hd : Q+Q=P)
    (v c : Nat) : (2*(v:Int)-(c:Int)) • Q=v • P-c • Q := by
  rw [←hd,sub_zsmul,show 2*(v:Int)=(v:Int)+(v:Int) by ring,add_zsmul,nsmul_add]
  simp only [natCast_zsmul,sub_eq_add_neg]

theorem axisWindowState_correct (P : Point) (hP : P≠0) (hr : order • P=0)
    (start n : Nat) (A : Point) (s : BasisState) (hs : PointLookupValid s)
    (hA : pointStateCoordinates s=fig14PointEncoding A) :
    axisWindowState P hP hr start n s=
      pointWrite (A+windowValue 65536 (rawWindowDigits n start s) • P-axisWindowOffset P n) s := by
  rw [axisWindowState,preparedWindowScheduleState_correct _ _ _ n start A s hs hA,
    axis_sum P hP hr start n start (Nat.le_refl _) s ⟨hs,A,hA⟩]
  simp only [Nat.sub_self,pow_zero,one_mul]
  have hc : 65535*(radixGeometric n:Int)=((65535*radixGeometric n:Nat):Int) := by push_cast; rfl
  rw [hc,half_reconstruct P (signedWindowHalfPoint P order)
    (signedWindowHalfPoint_double P order order_odd hr)]
  simp only [axisWindowOffset,sub_eq_add_neg,add_assoc]

theorem axisWindow_coherent (P : Point) (hP : P≠0) (hr : order • P=0) (start n : Nat) :
    CoherentlyImplementsOn (axisWindowProgram P hP hr start n)
      (Finsupp.lmapDomain ℂ ℂ (axisWindowState P hP hr start n)) WindowPointValid :=
  preparedWindowSchedule_coherent _ _ _ n start

theorem axisWindowState_ready (P : Point) (hP : P≠0) (hr : order • P=0)
    (start n : Nat) (s : BasisState) (hs : WindowPointValid s) :
    WindowPointValid (axisWindowState P hP hr start n s) :=
  preparedWindowScheduleState_ready _ _ _ n start s hs

theorem axisWindowState_scalar (P : Point) (hP : P≠0) (hr : order • P=0)
    (start a : Nat) (ha : a<2^257) (A : Point) (s : BasisState) (hs : PointLookupValid s)
    (hA : pointStateCoordinates s=fig14PointEncoding A)
    (hd : rawWindowDigits 17 start s=windowDigits 16 17 a) :
    axisWindowState P hP hr start 17 s=pointWrite (A+a • P-axisWindowOffset P 17) s := by
  rw [axisWindowState_correct P hP hr start 17 A s hs hA,hd]
  have hpow : (2:Nat)^257≤(2^16)^17 := by
    rw [←pow_mul]
    exact pow_le_pow_right₀ (show (1:Nat)≤2 by decide) (show 257≤16*17 by decide)
  have hv := windowValue_digits 16 17 a (lt_of_lt_of_le ha hpow)
  change windowValue 65536 (windowDigits 16 17 a)=a at hv
  rw [hv]

private theorem high_not_point (w : Wire) (hw : 839≤w) : w∉pointLogicalWires := by
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1]
  dsimp only [Wire] at *
  omega

theorem rawWindowDigits_pointWrite (n j : Nat) (P : Point) (s : BasisState) :
    rawWindowDigits n j (pointWrite P s)=rawWindowDigits n j s := by
  have hd (k : Nat) : windowRawDigit k (pointWrite P s)=windowRawDigit k s := by
    have hv : wireValues (windowAddressBits k) (pointWrite P s)=wireValues (windowAddressBits k) s := by
      apply List.map_congr_left
      intro w hw
      apply pointWrite_frame
      apply high_not_point
      simp only [windowAddressBits,List.mem_range'_1,windowBankStart] at hw
      dsimp only [Wire] at *
      omega
    have hb := pointWrite_frame P s (windowBankStart k+15)
      (high_not_point _ (by unfold windowBankStart; dsimp only [Wire]; omega))
    simp only [windowRawDigit,hv,hb]
  induction n generalizing j with
  | zero => rfl
  | succ n ih => simp only [rawWindowDigits,hd,ih]

def scalarWindowsProgram (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) : AdaptiveCircuit :=
  (axisWindowProgram P hP hrP 0 17).seq (axisWindowProgram Q hQ hrQ 17 17)
def scalarWindowsState (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) : BasisState :=
  axisWindowState Q hQ hrQ 17 17 (axisWindowState P hP hrP 0 17 s)

theorem scalarWindows_coherent (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    CoherentlyImplementsOn (scalarWindowsProgram P Q hP hQ hrP hrQ)
      (Finsupp.lmapDomain ℂ ℂ (scalarWindowsState P Q hP hQ hrP hrQ)) WindowPointValid := by
  have h := (axisWindow_coherent P hP hrP 0 17).seq (axisWindow_coherent Q hQ hrQ 17 17) (by
    intro s hs
    simpa [ket] using supportedOn_ket _ _ (axisWindowState_ready P hP hrP 0 17 s hs))
  apply h.congrIdeal
  intro s hs
  simp [LinearMap.comp_apply,ket,scalarWindowsState]

private theorem offsets_cancel {G : Type} [AddCommGroup G] (u v a b : G) :
    u+v+a-u+b-v=a+b := by abel

theorem scalarWindowsState_correct (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : Nat) (ha : a<2^257) (hb : b<2^257)
    (s : BasisState) (hs : PointLookupValid s)
    (hA : pointStateCoordinates s=fig14PointEncoding (axisWindowOffset P 17+axisWindowOffset Q 17))
    (hda : rawWindowDigits 17 0 s=windowDigits 16 17 a)
    (hdb : rawWindowDigits 17 17 s=windowDigits 16 17 b) :
    scalarWindowsState P Q hP hQ hrP hrQ s=pointWrite (a • P+b • Q) s := by
  have h1 := axisWindowState_scalar P hP hrP 0 a ha _ s hs hA hda
  have hv := (axisWindowState_ready P hP hrP 0 17 s ⟨hs,_,hA⟩).1
  have hp : pointStateCoordinates (axisWindowState P hP hrP 0 17 s)=
      fig14PointEncoding (axisWindowOffset P 17+axisWindowOffset Q 17+a • P-axisWindowOffset P 17) := by
    rw [h1,pointWrite_coordinates]
  have hd : rawWindowDigits 17 17 (axisWindowState P hP hrP 0 17 s)=windowDigits 16 17 b := by
    rw [h1,rawWindowDigits_pointWrite,hdb]
  rw [scalarWindowsState,axisWindowState_scalar Q hQ hrQ 17 b hb _ _ hv hp hd,h1,pointWrite_overwrite]
  rw [offsets_cancel]

theorem scalarWindowsState_ready (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) (hs : WindowPointValid s) :
    WindowPointValid (scalarWindowsState P Q hP hQ hrP hrQ s) :=
  axisWindowState_ready Q hQ hrQ 17 17 _ (axisWindowState_ready P hP hrP 0 17 s hs)

theorem scalarWindows_support (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (scalarWindowsProgram P Q hP hQ hrP hrQ).wires ⊆ List.range 839++List.range' 855 544 := by
  intro w hw
  rw [scalarWindowsProgram,modularWires_seq] at hw
  rcases hw with hw | hw
  · have h := preparedWindowSchedule_support (fun k => oddWindowX P (k-0))
      (fun k => oddWindowY P (k-0)) (fun k => oddWindowTable_valid P hP hrP (k-0)) 17 0 hw
    rcases List.mem_append.mp h with h | h
    · exact List.mem_append_left _ h
    · apply List.mem_append_right
      simp only [List.mem_range'_1] at h ⊢
      omega
  · exact preparedWindowSchedule_support _ _ _ 17 17 hw

theorem scalarWindows_qubitCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (scalarWindowsProgram P Q hP hQ hrP hrQ).qubitCount≤1383 := by
  have hs : (scalarWindowsProgram P Q hP hQ hrP hrQ).wires.dedup.toFinset ⊆
      (List.range 839++List.range' 855 544).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (scalarWindows_support P Q hP hQ hrP hrQ (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,List.length_append,List.length_range,List.length_range'] using hc

end
end ShorECDLP.Paper2607_13816
