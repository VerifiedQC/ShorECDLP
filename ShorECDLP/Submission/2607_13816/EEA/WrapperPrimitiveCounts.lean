import ShorECDLP.Submission.«2607_13816».EEA.LengthPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.WrapperUnitaryPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.AdderPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.ComparatorPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.InversePrimitiveCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
private theorem wrapper_unitary_next (g : Circuit) (next : AdaptiveCircuit) :
    primitiveResources (.unitary g next)=(primitiveResources (.unitary g .done)).add (primitiveResources next) :=
  primitiveResources_seq (.unitary g .done) next
private theorem controlledComplement_primitive (input : List Wire) (q : Wire) :
    primitiveResources (.unitary (controlledComplement input q) .done)=
      (⟨0,0,input.length,0,0,0⟩ : PrimitiveResources) := by
  induction input with
  | nil => rfl
  | cons a input ih =>
    change primitiveResources (.unitary [.CX q a] (.unitary (controlledComplement input q) .done))=_
    rw [wrapper_unitary_next,ih]
    simp [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
      gidneyToffoliCount,AdaptiveCircuit.measurementCount,primitiveXCost,primitiveHCost,primitivePhaseCost,Nat.add_comm]
/-- Every source constant-minus stage includes both measured adders and the complement. -/
theorem controlledConstMinus256_primitive_bounds (input dirty : List Wire) (modulus : List Bool)
    (q c r t : Wire) (hi : input.length=256) (hd : dirty.length=255) (hm : modulus.length=256) :
    let v := primitiveResources (controlledConstMinus input dirty modulus q c r t)
    v.x≤2044 ∧ v.h≤2040 ∧ v.cnot≤7906 ∧ v.toffoli≤1528 ∧ v.phase=0 ∧ v.measurements≤510 := by
  have h1 := controlledGidneyAddConst256_primitive_bounds input dirty
    ((List.range input.length).map (Nat.testBit 1)) q c r t hi hd (by simp [hi])
  have hp := controlledGidneyAddConst256_primitive_bounds input dirty modulus q c r t hi hd hm
  dsimp only at h1 hp ⊢
  simp only [hi] at h1
  rw [controlledConstMinus,wrapper_unitary_next]
  simp only [primitiveResources_seq,
    controlledComplement_primitive,hi,PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
/-- Centering includes a threshold comparison and complete constant-minus transform. -/
theorem eeaCenter256_primitive_bounds (input dirty : List Wire) (modulus : List Bool) (p : Nat)
    (c r t iter : Wire) (hi : input.length=256) (hd : dirty.length=256) (hm : modulus.length=256) :
    let v := primitiveResources (eeaCenter input dirty modulus p c r t iter)
    v.x≤6395 ∧ v.h≤3064 ∧ v.cnot≤11745 ∧ v.toffoli≤2295 ∧ v.phase=0 ∧ v.measurements≤766 := by
  have hc := gidneyCompareGE256_primitive_bounds input dirty (p/2+1) c r t iter hi hd
  have hm := controlledConstMinus256_primitive_bounds input (dirty.take (input.length-1)) modulus iter c r t
    hi (by simp [hi,hd]) hm
  dsimp only at hc hm ⊢
  simp only [eeaCenter,primitiveResources_seq,PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
theorem eeaUncenter256_primitive_bounds (input dirty : List Wire) (modulus : List Bool) (p : Nat)
    (c r t iter : Wire) (hi : input.length=256) (hd : dirty.length=256) (hm : modulus.length=256) :
    let v := primitiveResources (eeaUncenter input dirty modulus p c r t iter)
    v.x≤6395 ∧ v.h≤3064 ∧ v.cnot≤11745 ∧ v.toffoli≤2295 ∧ v.phase=0 ∧ v.measurements≤766 := by
  have hc := eeaCenter256_primitive_bounds input dirty modulus p c r t iter hi hd hm
  dsimp only at hc ⊢
  simp only [eeaCenter,eeaUncenter,primitiveResources_seq,PrimitiveResources.add] at hc ⊢
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
theorem eeaParityCorrection256_primitive_bounds (input dirty : List Wire) (modulus : List Bool)
    (c r t iter : Wire) (hi : input.length=256) (hd : dirty.length=255) (hm : modulus.length=256) :
    let v := primitiveResources (eeaParityCorrection input dirty modulus c r t iter)
    v.x≤2046 ∧ v.h≤2040 ∧ v.cnot≤7906 ∧ v.toffoli≤1528 ∧ v.phase=0 ∧ v.measurements≤510 := by
  have hb := controlledConstMinus256_primitive_bounds input dirty modulus iter c r t hi hd hm
  dsimp only at hb ⊢
  have hx : primitiveResources (.unitary [.X iter] .done)=(⟨1,0,0,0,0,0⟩ : PrimitiveResources) := rfl
  rw [eeaParityCorrection,wrapper_unitary_next]
  simp only [primitiveResources_seq,hx,PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum
attribute [local irreducible] primitiveResources eeaPreprocess eeaUnpreprocess eeaCenter eeaUncenter eeaLengthSetup eeaLengthUndo workRegistersPrepare workRegistersRestore secp256k1EEAForwardAdaptive secp256k1EEAReverseAdaptive secp256k1EEAForwardWrapper secp256k1EEAReverseWrapper secp256k1EEAReversePostprocessing secp256k1EEAParityCorrection canonicalWork2Rotation canonicalWork2InverseRotation terminalEpochCompression terminalWork1Clear
private theorem preprocess_primitive_sum (v : PrimitiveResources)
    (h : v.x≤6395 ∧ v.h≤3064 ∧ v.cnot≤11745 ∧ v.toffoli≤2295 ∧ v.phase=0 ∧ v.measurements≤766) :
    let w := (⟨251,0,390,0,0,0⟩ : PrimitiveResources).add (v.add ⟨386546,0,1035,131068,0,0⟩)
    w.x≤393192 ∧ w.h≤3064 ∧ w.cnot≤13170 ∧ w.toffoli≤133363 ∧ w.phase=0 ∧ w.measurements≤766 := by
  dsimp only [PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
private theorem unpreprocess_primitive_sum (v : PrimitiveResources)
    (h : v.x≤6395 ∧ v.h≤3064 ∧ v.cnot≤11745 ∧ v.toffoli≤2295 ∧ v.phase=0 ∧ v.measurements≤766) :
    let w := (⟨386546,0,1035,131068,0,0⟩ : PrimitiveResources).add (v.add ⟨251,0,390,0,0,0⟩)
    w.x≤393192 ∧ w.h≤3064 ∧ w.cnot≤13170 ∧ w.toffoli≤133363 ∧ w.phase=0 ∧ w.measurements≤766 := by
  dsimp only [PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
theorem eeaPreprocess_primitive_bounds :
    let v := primitiveResources eeaPreprocess
    v.x≤393192 ∧ v.h≤3064 ∧ v.cnot≤13170 ∧ v.toffoli≤133363 ∧ v.phase=0 ∧ v.measurements≤766 := by
  have hv : primitiveResources eeaPreprocess =
      (primitiveResources (.unitary workRegistersPrepare .done)).add
        ((primitiveResources (eeaCenter (List.range' 266 256).reverse (List.range' 4 256)
          (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2)).add
            (primitiveResources (.unitary eeaLengthSetup .done))) := by
    rw [eeaPreprocess,wrapper_unitary_next,primitiveResources_seq]
  rw [hv,workRegistersPrepare_primitive,eeaLengthSetup_primitive]
  apply preprocess_primitive_sum
  exact eeaCenter256_primitive_bounds _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp)
theorem eeaUnpreprocess_primitive_bounds :
    let v := primitiveResources eeaUnpreprocess
    v.x≤393192 ∧ v.h≤3064 ∧ v.cnot≤13170 ∧ v.toffoli≤133363 ∧ v.phase=0 ∧ v.measurements≤766 := by
  have hv : primitiveResources eeaUnpreprocess =
      (primitiveResources (.unitary eeaLengthUndo .done)).add
        ((primitiveResources (eeaUncenter (List.range' 266 256).reverse (List.range' 4 256)
          (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2)).add
            (primitiveResources (.unitary workRegistersRestore .done))) := by
    rw [eeaUnpreprocess,wrapper_unitary_next,primitiveResources_seq]
  rw [hv,workRegistersRestore_primitive,eeaLengthUndo_primitive]
  apply unpreprocess_primitive_sum
  exact eeaUncenter256_primitive_bounds _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp)
theorem secp256k1EEAParityCorrection_primitive_bounds :
    let v := primitiveResources secp256k1EEAParityCorrection
    v.x≤2046 ∧ v.h≤2040 ∧ v.cnot≤7906 ∧ v.toffoli≤1528 ∧ v.phase=0 ∧ v.measurements≤510 := by
  rw [secp256k1EEAParityCorrection]
  exact eeaParityCorrection256_primitive_bounds _ _ _ _ _ _ _ (by simp) (by simp) (by decide +kernel)
private theorem forward_wrapper_sum (a : PrimitiveResources) (ha : a.x≤393192 ∧ a.h≤3064 ∧ a.cnot≤13170 ∧ a.toffoli≤133363 ∧ a.phase=0 ∧ a.measurements≤766) (b : PrimitiveResources) (hb : b.x≤2046 ∧ b.h≤2040 ∧ b.cnot≤7906 ∧ b.toffoli≤1528 ∧ b.phase=0 ∧ b.measurements≤510) :
    let v := (((a.add (⟨19045616,10557664,29716831,17454225,0,5278832⟩ : PrimitiveResources)).add ((⟨6,0,5240,2620,0,0⟩ : PrimitiveResources).add (⟨10,0,0,15,0,0⟩ : PrimitiveResources))).add b).add (⟨251,0,0,0,0,0⟩ : PrimitiveResources)
    v.x≤19441121 ∧ v.h≤10562768 ∧ v.cnot≤29743147 ∧ v.toffoli≤17591751 ∧ v.phase=0 ∧ v.measurements≤5280108 := by
  dsimp only [PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
/-- All six primitive budgets follow the actual secp256k1EEAForwardWrapper composition. -/
theorem secp256k1EEAForwardWrapper_primitive_bounds :
    let v := primitiveResources secp256k1EEAForwardWrapper
    v.x≤19441121 ∧ v.h≤10562768 ∧ v.cnot≤29743147 ∧ v.toffoli≤17591751 ∧ v.phase=0 ∧ v.measurements≤5280108 := by
  have hv : primitiveResources secp256k1EEAForwardWrapper=((((primitiveResources eeaPreprocess).add (⟨19045616,10557664,29716831,17454225,0,5278832⟩ : PrimitiveResources)).add ((⟨6,0,5240,2620,0,0⟩ : PrimitiveResources).add (⟨10,0,0,15,0,0⟩ : PrimitiveResources))).add (primitiveResources secp256k1EEAParityCorrection)).add (⟨251,0,0,0,0,0⟩ : PrimitiveResources) := by
    simp only [secp256k1EEAForwardWrapper,primitiveResources_seq,primitiveResources_unitary_append,secp256k1EEAForwardPrimitive_certificate,canonicalWork2Rotation_primitive,terminalEpochCompression_primitive,terminalWork1Clear_primitive]
  rw [hv]
  exact forward_wrapper_sum _ eeaPreprocess_primitive_bounds _ secp256k1EEAParityCorrection_primitive_bounds
private theorem reverse_post_sum (a : PrimitiveResources) (ha : a.x≤2046 ∧ a.h≤2040 ∧ a.cnot≤7906 ∧ a.toffoli≤1528 ∧ a.phase=0 ∧ a.measurements≤510) :
    let v := ((⟨251,0,0,0,0,0⟩ : PrimitiveResources).add a).add ((⟨10,0,0,15,0,0⟩ : PrimitiveResources).add (⟨6,0,5240,2620,0,0⟩ : PrimitiveResources))
    v.x≤2313 ∧ v.h≤2040 ∧ v.cnot≤13146 ∧ v.toffoli≤4163 ∧ v.phase=0 ∧ v.measurements≤510 := by
  dsimp only [PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
/-- All six primitive budgets follow the actual secp256k1EEAReversePostprocessing composition. -/
theorem secp256k1EEAReversePostprocessing_primitive_bounds :
    let v := primitiveResources secp256k1EEAReversePostprocessing
    v.x≤2313 ∧ v.h≤2040 ∧ v.cnot≤13146 ∧ v.toffoli≤4163 ∧ v.phase=0 ∧ v.measurements≤510 := by
  have hv : primitiveResources secp256k1EEAReversePostprocessing=((⟨251,0,0,0,0,0⟩ : PrimitiveResources).add (primitiveResources secp256k1EEAParityCorrection)).add ((⟨10,0,0,15,0,0⟩ : PrimitiveResources).add (⟨6,0,5240,2620,0,0⟩ : PrimitiveResources)) := by
    simp only [secp256k1EEAReversePostprocessing,primitiveResources_seq,primitiveResources_unitary_append,canonicalWork2InverseRotation_primitive,terminalEpochCompression_primitive,terminalWork1Clear_primitive]
  rw [hv]
  exact reverse_post_sum _ secp256k1EEAParityCorrection_primitive_bounds
private theorem reverse_wrapper_sum (a : PrimitiveResources) (ha : a.x≤2313 ∧ a.h≤2040 ∧ a.cnot≤13146 ∧ a.toffoli≤4163 ∧ a.phase=0 ∧ a.measurements≤510) (b : PrimitiveResources) (hb : b.x≤393192 ∧ b.h≤3064 ∧ b.cnot≤13170 ∧ b.toffoli≤133363 ∧ b.phase=0 ∧ b.measurements≤766) :
    let v := (a.add (⟨19097456,10557664,29716831,17454225,0,5278832⟩ : PrimitiveResources)).add b
    v.x≤19492961 ∧ v.h≤10562768 ∧ v.cnot≤29743147 ∧ v.toffoli≤17591751 ∧ v.phase=0 ∧ v.measurements≤5280108 := by
  dsimp only [PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
/-- All six primitive budgets follow the actual secp256k1EEAReverseWrapper composition. -/
theorem secp256k1EEAReverseWrapper_primitive_bounds :
    let v := primitiveResources secp256k1EEAReverseWrapper
    v.x≤19492961 ∧ v.h≤10562768 ∧ v.cnot≤29743147 ∧ v.toffoli≤17591751 ∧ v.phase=0 ∧ v.measurements≤5280108 := by
  have hv : primitiveResources secp256k1EEAReverseWrapper=((primitiveResources secp256k1EEAReversePostprocessing).add (⟨19097456,10557664,29716831,17454225,0,5278832⟩ : PrimitiveResources)).add (primitiveResources eeaUnpreprocess) := by
    simp only [secp256k1EEAReverseWrapper,primitiveResources_seq,secp256k1EEAReversePrimitive_certificate]
  rw [hv]
  exact reverse_wrapper_sum _ secp256k1EEAReversePostprocessing_primitive_bounds _ eeaUnpreprocess_primitive_bounds
end ShorECDLP.Paper2607_13816
