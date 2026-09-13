import ShorECDLP.Submission.«2607_13816».Window.PointInitialize
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
private theorem word_append (a b : List Bool) :
    boolWordToNat (a++b)=boolWordToNat a+2^a.length*boolWordToNat b := by
  induction a with
  | nil => simp [boolWordToNat]
  | cons x xs ih =>
    simp only [List.cons_append,boolWordToNat,List.length_cons,ih,pow_succ]
    ring

private theorem raw_word (j : Nat) (s : BasisState) :
    windowRawDigit j s=boolWordToNat (wireValues (List.range' (windowBankStart j) 16) s) := by
  have he := List.range'_append_1 (s:=windowBankStart j) (m:=15) (n:=1)
  rw [←he]
  change windowRawDigit j s=boolWordToNat
    (wireValues (List.range' (windowBankStart j) 15) s ++ [s (windowBankStart j+15)])
  rw [word_append]
  simp only [wireValues,List.length_map,List.length_range']
  change windowRawDigit j s=boolWordToNat (wireValues (windowAddressBits j) s)+
    32768*((s (windowBankStart j+15)).toNat+2*0)
  simp only [Nat.mul_zero,Nat.add_zero]
  rfl

def scalarRegisterValue (n j : Nat) (s : BasisState) : Nat :=
  boolWordToNat (wireValues (List.range' (windowBankStart j) (16*n)) s)

private theorem register_succ (n j : Nat) (s : BasisState) :
    scalarRegisterValue (n+1) j s=windowRawDigit j s+65536*scalarRegisterValue n (j+1) s := by
  rw [scalarRegisterValue,show 16*(n+1)=16+16*n by omega,←List.range'_append_1]
  simp only [wireValues,List.map_append,word_append,List.length_map,List.length_range']
  change boolWordToNat (wireValues (List.range' (windowBankStart j) 16) s)+
    65536*boolWordToNat (wireValues (List.range' (windowBankStart j+16) (16*n)) s)=_
  rw [←raw_word]
  have he : windowBankStart j+16=windowBankStart (j+1) := by unfold windowBankStart; omega
  rw [he]
  rfl

theorem rawWindowDigits_register (n j : Nat) (s : BasisState) :
    rawWindowDigits n j s=windowDigits 16 n (scalarRegisterValue n j s) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    rw [rawWindowDigits,windowDigits,register_succ]
    have hb := windowRawDigit_bound j s
    have hd : (windowRawDigit j s+65536*scalarRegisterValue n (j+1) s)/65536=
        scalarRegisterValue n (j+1) s := by omega
    simp only [show 2^16=65536 from rfl,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hb,hd]
    rw [ih]
def scalarInputValue (j : Nat) (s : BasisState) : Nat :=
  boolWordToNat (wireValues (List.range' (windowBankStart j) 257) s)
def ScalarPaddingClean (j : Nat) (s : BasisState) : Prop :=
  wireValues (List.range' (windowBankStart j+257) 15) s=List.replicate 15 false

private theorem zero_word (n : Nat) : boolWordToNat (List.replicate n false)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,boolWordToNat,Bool.toNat_false,ih,Nat.mul_zero,Nat.add_zero]

private theorem word_range_split (start m n : Nat) (s : BasisState) :
    boolWordToNat (wireValues (List.range' start (m+n)) s)=
      boolWordToNat (wireValues (List.range' start m) s)+
        2^m*boolWordToNat (wireValues (List.range' (start+m) n) s) := by
  rw [←List.range'_append_1]
  simp only [wireValues,List.map_append,word_append,List.length_map,List.length_range']

theorem scalarRegisterValue_input (j : Nat) (s : BasisState) (hp : ScalarPaddingClean j s) :
    scalarRegisterValue 17 j s=scalarInputValue j s := by
  rw [scalarRegisterValue,show 16*17=257+15 by rfl,word_range_split]
  have hz : boolWordToNat (wireValues (List.range' (windowBankStart j+257) 15) s)=0 :=
    (congrArg boolWordToNat hp).trans (zero_word 15)
  rw [hz,Nat.mul_zero,Nat.add_zero]
  rfl

theorem scalarInputValue_bound (j : Nat) (s : BasisState) : scalarInputValue j s<2^257 := by
  simpa only [scalarInputValue,wireValues,List.length_map,List.length_range'] using
    boolWordToNat_lt_pow_two (wireValues (List.range' (windowBankStart j) 257) s)

theorem rawWindowDigits_input (j : Nat) (s : BasisState) (hp : ScalarPaddingClean j s) :
    rawWindowDigits 17 j s=windowDigits 16 17 (scalarInputValue j s) := by
  rw [rawWindowDigits_register,scalarRegisterValue_input j s hp]

theorem initializedScalarState_registers (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) (hs : PointInitializeValid s)
    (hp : ScalarPaddingClean 0 s) (hq : ScalarPaddingClean 17 s) :
    initializedScalarState P Q hP hQ hrP hrQ s=
      pointWrite (scalarInputValue 0 s • P+scalarInputValue 17 s • Q) s :=
  initializedScalarState_correct P Q hP hQ hrP hrQ _ _ (scalarInputValue_bound 0 s)
    (scalarInputValue_bound 17 s) s hs (rawWindowDigits_input 0 s hp) (rawWindowDigits_input 17 s hq)

def ScalarRegistersValid (s : BasisState) : Prop :=
  PointInitializeValid s ∧ ScalarPaddingClean 0 s ∧ ScalarPaddingClean 17 s
def scalarRegisterOutput (P Q : Point) (s : BasisState) : BasisState :=
  pointWrite (scalarInputValue 0 s • P+scalarInputValue 17 s • Q) s

theorem initializedScalar_registers_coherent (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    CoherentlyImplementsOn (initializedScalarProgram P Q hP hQ hrP hrQ)
      (Finsupp.lmapDomain ℂ ℂ (scalarRegisterOutput P Q)) ScalarRegistersValid := by
  obtain ⟨cs,ha,hm⟩ := initializedScalar_coherent P Q hP hQ hrP hrQ
  have h : CoherentlyImplementsOn (initializedScalarProgram P Q hP hQ hrP hrQ)
      (Finsupp.lmapDomain ℂ ℂ (initializedScalarState P Q hP hQ hrP hrQ)) ScalarRegistersValid :=
    ⟨cs,ha.imp (fun b c h s hs => h s hs.1),hm⟩
  apply h.congrIdeal
  intro s hs
  simp only [ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
  rw [initializedScalarState_registers P Q hP hQ hrP hrQ s hs.1 hs.2.1 hs.2.2]
  rfl

theorem scalarRegisterOutput_frame (P Q : Point) (s : BasisState) (w : Wire)
    (hw : w∉pointLogicalWires) : scalarRegisterOutput P Q s w=s w :=
  pointWrite_frame _ s w hw

theorem scalarInputValue_pointWrite (j : Nat) (P : Point) (s : BasisState) :
    scalarInputValue j (pointWrite P s)=scalarInputValue j s := by
  unfold scalarInputValue
  apply congrArg boolWordToNat
  apply List.map_congr_left
  intro w hw
  apply pointWrite_frame
  simp only [List.mem_range'_1,windowBankStart] at hw
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1]
  dsimp only [Wire] at *
  omega

theorem scalarRegisterOutput_inputs (P Q : Point) (s : BasisState) (j : Nat) :
    scalarInputValue j (scalarRegisterOutput P Q s)=scalarInputValue j s :=
  scalarInputValue_pointWrite j _ s

end
end ShorECDLP.Paper2607_13816
