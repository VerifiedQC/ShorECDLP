import ShorECDLP.Submission.«2607_13816».Arithmetic.PointStages
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
private theorem zero_bits (bits : List Bool) : bits.all (fun b => !b)=true ↔ boolWordToNat bits=0 := by
  induction bits with
  | nil => simp [boolWordToNat]
  | cons b bs ih => cases b <;> simp [boolWordToNat,ih]
private theorem constant256_counts (A D : List Wire) (K : List Bool) (q c r t : Wire)
    (hA : A.length=256) (hD : D.length=255) (hK : K.length=256) :
    (controlledGidneyAddConst A D K q c r t).tCount=(if boolWordToNat K=0 then 0 else 5348) ∧
    (controlledGidneyAddConst A D K q c r t).measurementCount=(if boolWordToNat K=0 then 0 else 255) := by
  have hm := controlledGidneyAddConst_measurementCount A D K q c r t (hA.trans hK.symm) (by omega)
  simp only [hD,zero_bits] at hm
  refine ⟨?_,hm⟩
  by_cases hz : boolWordToNat K=0
  · have hh := (zero_bits K).mpr hz
    simp [controlledGidneyAddConst,hh,hz,AdaptiveCircuit.tCount]
  · rw [if_neg hz]
    cases A with
    | nil => simp at hA
    | cons a as =>
      cases D with
      | nil => simp at hD
      | cons d ds =>
        cases K with
        | nil => simp at hK
        | cons k ks =>
          have he := controlledGidneyAddConst_tCount_nonzero a d q c r t k as ds ks
            (by simp only [List.length_cons] at hA hK; omega)
            (by simp only [List.length_cons] at hA hD; omega) (fun h => hz ((zero_bits _).mp h))
          have hl : as.length=255 := by simpa using hA
          simpa only [hl] using he
private theorem comparison256_counts (A D : List Wire) (k : Nat) (c r t f : Wire)
    (hA : A.length=256) (hD : D.length=256) (hk : 0<k) (hkB : k<2^256) :
    (gidneyCompareGE A D k c r t f).tCount=5369 ∧
    (gidneyCompareGE A D k c r t f).measurementCount=256 := by
  cases A with
  | nil => simp at hA
  | cons a as =>
    have hh := gidneyCompareGE_metrics a as D k c r t f (hA.trans hD.symm) hk (by simpa only [hA] using hkB)
    simpa only [hA] using And.intro hh.2.2.1 hh.2.2.2.1
private theorem controlledLT256_counts (A D : List Wire) (k : Nat) (q c r t f : Wire)
    (hA : A.length=256) (hD : D.length=256) (hk : k<2^256) :
    (controlledGidneyCompareLT A D k q c r t f).tCount=(if k=0 then 0 else 5369) ∧
    (controlledGidneyCompareLT A D k q c r t f).measurementCount=(if k=0 then 0 else 256) := by
  by_cases hz : k=0
  · simp [controlledGidneyCompareLT,hz,AdaptiveCircuit.tCount,AdaptiveCircuit.measurementCount]
  · cases A with
    | nil => simp at hA
    | cons a as =>
      have hh := controlledGidneyCompareLT_metrics a as D k q c r t f (hA.trans hD.symm)
        (by omega) (by simpa only [hA] using hk)
      simpa only [hA,if_neg hz] using And.intro hh.2.1 hh.2.2.1
private theorem seq_T (a b : AdaptiveCircuit) : (a.seq b).tCount=a.tCount+b.tCount := by
  simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b
/-- Exact constant-modular-add costs, including the zero-constant shortcut. -/
theorem controlledConstantModularAdd256_counts (A D : List Wire) (K : List Bool) (q c r t f : Wire)
    (hA : A.length=256) (hD : D.length=256) (hK : K.length=256) (hk : boolWordToNat K<ShorECDLP.p) :
    (controlledConstantModularAdd A D K secp256k1ReductionConstantBits ShorECDLP.p q c r t f).tCount=
      (if boolWordToNat K=0 then 10717 else 26803) ∧
    (controlledConstantModularAdd A D K secp256k1ReductionConstantBits ShorECDLP.p q c r t f).measurementCount=
      (if boolWordToNat K=0 then 511 else 1278) := by
  have hd : (D.take (A.length-1)).length=255 := by simp [hA,hD]
  have h1 := constant256_counts A _ K q c r t hA hd hK
  have h2 := controlledLT256_counts A D (boolWordToNat K) q c r t f hA hD (hk.trans (by decide +kernel))
  have h3 := comparison256_counts A D ShorECDLP.p c r t f hA hD ShorECDLP.Secp256k1.p_prime.pos (by decide +kernel)
  have h4 := constant256_counts A _ secp256k1ReductionConstantBits f c r t hA hd (by decide +kernel)
  have hc : boolWordToNat secp256k1ReductionConstantBits ≠ 0 := by decide +kernel
  simp only [if_neg hc] at h4
  simp only [controlledConstantModularAdd,seq_T,modularMeasurements_seq,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
  split <;> constructor <;> rfl
private theorem uncontrolledConstant256_counts (A D : List Wire) (K : List Bool) (c r t : Wire)
    (hA : A.length=256) (hD : D.length=255) (hK : K.length=256) :
    (gidneyAddConst A D K c r t).tCount=(if boolWordToNat K=0 then 0 else 5348) ∧
    (gidneyAddConst A D K c r t).measurementCount=(if boolWordToNat K=0 then 0 else 255) := by
  simp only [gidneyAddConst,constantControlProgram_tCount,constantControlProgram_measurements]
  exact constant256_counts A D K _ c r t hA hD hK
private theorem uncontrolledLT256_counts (A D : List Wire) (k : Nat) (c r t f : Wire)
    (hA : A.length=256) (hD : D.length=256) (hk : k<2^256) :
    (gidneyCompareLT A D k c r t f).tCount=(if k=0 then 0 else 5369) ∧
    (gidneyCompareLT A D k c r t f).measurementCount=(if k=0 then 0 else 256) := by
  by_cases hz : k=0
  · simp [gidneyCompareLT,hz,AdaptiveCircuit.tCount,AdaptiveCircuit.measurementCount]
  · have hh := comparison256_counts A D k c r t f hA hD (by omega) hk
    have hlarge : ¬2^A.length≤k := by rw [hA]; omega
    simpa [gidneyCompareLT,hz,hlarge,AdaptiveCircuit.tCount,ShorECDLP.tCount,tCost,
      AdaptiveCircuit.measurementCount] using hh

theorem uncontrolledConstantModularAdd256_counts (A D : List Wire) (K : List Bool) (c r t f : Wire)
    (hA : A.length=256) (hD : D.length=256) (hK : K.length=256) (hk : boolWordToNat K<ShorECDLP.p) :
    (uncontrolledConstantModularAdd A D K secp256k1ReductionConstantBits ShorECDLP.p c r t f).tCount=
      (if boolWordToNat K=0 then 10717 else 26803) ∧
    (uncontrolledConstantModularAdd A D K secp256k1ReductionConstantBits ShorECDLP.p c r t f).measurementCount=
      (if boolWordToNat K=0 then 511 else 1278) := by
  have hd : (D.take (A.length-1)).length=255 := by simp [hA,hD]
  have h1 := uncontrolledConstant256_counts A _ K c r t hA hd hK
  have h2 := uncontrolledLT256_counts A D (boolWordToNat K) c r t f hA hD (hk.trans (by decide +kernel))
  have h3 := comparison256_counts A D ShorECDLP.p c r t f hA hD ShorECDLP.Secp256k1.p_prime.pos (by decide +kernel)
  have h4 := constant256_counts A _ secp256k1ReductionConstantBits f c r t hA hd (by decide +kernel)
  have hc : boolWordToNat secp256k1ReductionConstantBits ≠ 0 := by decide +kernel
  simp only [if_neg hc] at h4
  simp only [uncontrolledConstantModularAdd,seq_T,modularMeasurements_seq,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
  split <;> constructor <;> rfl

private theorem controlledGE256_counts (A D : List Wire) (q c r t f : Wire)
    (hA : A.length=256) (hD : D.length=256) :
    (controlledGidneyCompareGE A D 1 q c r t f).tCount=5369 ∧
    (controlledGidneyCompareGE A D 1 q c r t f).measurementCount=256 := by
  have hh := controlledLT256_counts A D 1 q c r t f hA hD (by decide)
  have hlarge : ¬2^A.length≤1 := by rw [hA]; decide
  simpa [controlledGidneyCompareLT,hlarge,AdaptiveCircuit.tCount,ShorECDLP.tCount,tCost,
    AdaptiveCircuit.measurementCount] using hh

/-- Negation has a fixed cost, including its two nonzero tests. -/
theorem controlledModularNegate256_counts (A D : List Wire) (q c r t f : Wire)
    (hA : A.length=256) (hD : D.length=256) :
    (controlledModularNegate A D secp256k1ModulusBits q c r t f).tCount=21434 ∧
    (controlledModularNegate A D secp256k1ModulusBits q c r t f).measurementCount=1022 := by
  have hd : (D.take (A.length-1)).length=255 := by simp [hA,hD]
  have h1 := controlledGE256_counts A D q c r t f hA hD
  have h2 := constant256_counts A _ ((List.range A.length).map (Nat.testBit 1)) q c r t hA hd (by simp [hA])
  have h3 := constant256_counts A _ secp256k1ModulusBits f c r t hA hd (by decide +kernel)
  have hk : boolWordToNat ((List.range A.length).map (Nat.testBit 1)) ≠ 0 := by rw [hA]; decide +kernel
  have hp : boolWordToNat secp256k1ModulusBits ≠ 0 := by decide +kernel
  simp only [if_neg hk] at h2
  simp only [if_neg hp] at h3
  have hc : ShorECDLP.tCount (controlledComplement A q)=0 := by
    simp [controlledComplement,ShorECDLP.tCount,List.map_map,Function.comp_def,tCost]
  simp only [controlledModularNegate,seq_T,modularMeasurements_seq,AdaptiveCircuit.tCount,
    AdaptiveCircuit.measurementCount,hc,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]
  constructor <;> trivial

end ShorECDLP.Paper2607_13816
