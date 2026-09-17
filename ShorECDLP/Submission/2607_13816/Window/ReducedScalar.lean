import ShorECDLP.Submission.«2607_13816».Window.DirectScalar
import ShorECDLP.Submission.«2607_13816».Window.ScalarRegisters
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
attribute [local irreducible] AdaptiveCircuit.seq physicalPointLookup preparedWindowCall preparedWindowSchedule axisWindowProgram
def reducedScalarProgram (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) : AdaptiveCircuit :=
  ((physicalPointLookup (firstWindowTable (axisWindowOffset P 16+axisWindowOffset Q 13) P)).seq
    (preparedWindowSchedule (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
      (fun k => oddWindowTable_valid P hP hrP (k-0)) 15 1)).seq
    (axisWindowProgram Q hQ hrQ 17 13)

def reducedScalarState (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) : BasisState :=
  axisWindowState Q hQ hrQ 17 13 (axisWindowState P hP hrP 0 16
    (pointWrite (axisWindowOffset P 16+axisWindowOffset Q 13) s))

theorem reducedScalar_coherent (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    CoherentlyImplementsOn (reducedScalarProgram P Q hP hQ hrP hrQ)
      (Finsupp.lmapDomain ℂ ℂ (reducedScalarState P Q hP hQ hrP hrQ))
      PointInitializeValid := by
  have h := directSchedule_coherent (axisWindowOffset P 16+axisWindowOffset Q 13)
    P Q hP hQ hrP hrQ 15 17 13
  apply h.congrIdeal
  intro s hs
  have he := axisWindowState_split P hP hrP 15
    (pointWrite (axisWindowOffset P 16+axisWindowOffset Q 13) s)
  have he' := congrArg (axisWindowState Q hQ hrQ 17 13) he
  simpa only [ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,
    reducedScalarState] using congrArg ket he'.symm


private theorem axis_scalar (P : Point) (hP : P≠0) (hr : order • P=0)
    (start n a : Nat) (ha : a<(2^16)^n) (A : Point) (s : BasisState) (hs : PointLookupValid s)
    (hA : pointStateCoordinates s=fig14PointEncoding A)
    (hd : rawWindowDigits n start s=windowDigits 16 n a) :
    axisWindowState P hP hr start n s=pointWrite (A+a • P-axisWindowOffset P n) s := by
  rw [axisWindowState_correct P hP hr start n A s hs hA,hd]
  have hv := windowValue_digits 16 n a ha
  change windowValue 65536 (windowDigits 16 n a)=a at hv
  rw [hv]

theorem reducedScalarState_correct (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : Nat) (ha : a<2^256) (hb : b<2^208)
    (s : BasisState) (hs : PointInitializeValid s)
    (hda : rawWindowDigits 16 0 s=windowDigits 16 16 a)
    (hdb : rawWindowDigits 13 17 s=windowDigits 16 13 b) :
    reducedScalarState P Q hP hQ hrP hrQ s=pointWrite (a • P+b • Q) s := by
  let A := axisWindowOffset P 16+axisWindowOffset Q 13
  let s₀ := pointWrite A s
  have hv₀ := pointInitialize_ready A s hs
  have ha' : a<(2^16)^16 := by simpa only [←pow_mul] using ha
  have hb' : b<(2^16)^13 := by simpa only [←pow_mul] using hb
  have h1 := axis_scalar P hP hrP 0 16 a ha' A s₀ hv₀.1 (pointWrite_coordinates A s)
    (by simpa only [s₀,rawWindowDigits_pointWrite] using hda)
  have hv := (axisWindowState_ready P hP hrP 0 16 s₀ hv₀).1
  have hp : pointStateCoordinates (axisWindowState P hP hrP 0 16 s₀)=
      fig14PointEncoding (A+a • P-axisWindowOffset P 16) := by rw [h1,pointWrite_coordinates]
  have hd : rawWindowDigits 13 17 (axisWindowState P hP hrP 0 16 s₀)=windowDigits 16 13 b := by
    rw [h1,rawWindowDigits_pointWrite]
    simpa only [s₀,rawWindowDigits_pointWrite] using hdb
  change axisWindowState Q hQ hrQ 17 13 (axisWindowState P hP hrP 0 16 s₀)=_
  rw [axis_scalar Q hQ hrQ 17 13 b hb' _ _ hv hp hd,h1,pointWrite_overwrite]
  have he : A+a • P-axisWindowOffset P 16+b • Q-axisWindowOffset Q 13=a • P+b • Q := by
    dsimp [A]; abel
  rw [he]
  exact pointWrite_overwrite _ _ _
private theorem schedule_support (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) (n j : Nat) :
    (preparedWindowSchedule x y hc n j).wires ⊆ List.range 839++List.range' (windowBankStart j) (16*n) := by
  induction n generalizing j with
  | zero => simp [preparedWindowSchedule,AdaptiveCircuit.wires]
  | succ n ih =>
    intro w hw
    rw [preparedWindowSchedule,modularWires_seq] at hw
    rcases hw with hw | hw
    · have hb := preparedWindowCall_support x y hc j hw
      simp only [List.mem_append,List.mem_range,List.mem_range'_1,windowBankStart] at hb ⊢
      dsimp only [Wire] at *
      omega
    · have ht := ih (j+1) hw
      simp only [List.mem_append,List.mem_range,List.mem_range'_1,windowBankStart] at ht ⊢
      dsimp only [Wire] at *
      omega

theorem reducedScalar_support (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (reducedScalarProgram P Q hP hQ hrP hrQ).wires ⊆ List.range 839++(List.range' 855 256++List.range' 1127 208) := by
  intro w hw
  rw [reducedScalarProgram,modularWires_seq,modularWires_seq] at hw
  rcases hw with (hw | hw) | hw
  · rw [physicalPointLookup] at hw
    have h := directPointLookup_support
      (firstWindowTable (axisWindowOffset P 16+axisWindowOffset Q 13) P)
      (List.range' 855 16) (List.range' 519 16) 836 hw
    simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at h
    simp only [List.mem_append,List.mem_range,List.mem_range'_1]
    dsimp only [Wire] at *
    omega
  · have h := schedule_support (fun k => oddWindowX P (k-0))
      (fun k => oddWindowY P (k-0)) (fun k => oddWindowTable_valid P hP hrP (k-0)) 15 1 hw
    simp only [List.mem_append,List.mem_range,List.mem_range'_1,windowBankStart] at h ⊢
    dsimp only [Wire] at *
    omega
  · rw [axisWindowProgram] at hw
    have h := schedule_support _ _ _ 13 17 hw
    simp only [List.mem_append,List.mem_range,List.mem_range'_1,windowBankStart] at h ⊢
    dsimp only [Wire] at *
    omega

theorem reducedScalar_qubitCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (reducedScalarProgram P Q hP hQ hrP hrQ).qubitCount≤1303 := by
  have hs : (reducedScalarProgram P Q hP hQ hrP hrQ).wires.dedup.toFinset ⊆
      (List.range 839++(List.range' 855 256++List.range' 1127 208)).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (reducedScalar_support P Q hP hQ hrP hrQ (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,List.length_append,List.length_range,List.length_range'] using hc


private theorem register_bound (n j : Nat) (s : BasisState) : scalarRegisterValue n j s<2^(16*n) := by
  simpa only [scalarRegisterValue,wireValues,List.length_map,List.length_range'] using
    boolWordToNat_lt_pow_two (wireValues (List.range' (windowBankStart j) (16*n)) s)

def reducedScalarOutput (P Q : Point) (s : BasisState) : BasisState :=
  pointWrite (scalarRegisterValue 16 0 s • P+scalarRegisterValue 13 17 s • Q) s

theorem reducedScalarState_registers (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) (hs : PointInitializeValid s) :
    reducedScalarState P Q hP hQ hrP hrQ s=reducedScalarOutput P Q s :=
  reducedScalarState_correct P Q hP hQ hrP hrQ _ _ (register_bound 16 0 s)
    (register_bound 13 17 s) s hs (rawWindowDigits_register 16 0 s) (rawWindowDigits_register 13 17 s)

theorem reducedScalar_registers_coherent (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    CoherentlyImplementsOn (reducedScalarProgram P Q hP hQ hrP hrQ)
      (Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q)) PointInitializeValid := by
  apply (reducedScalar_coherent P Q hP hQ hrP hrQ).congrIdeal
  intro s hs
  simp only [ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,reducedScalarState_registers P Q hP hQ hrP hrQ s hs]
end
end ShorECDLP.Paper2607_13816
