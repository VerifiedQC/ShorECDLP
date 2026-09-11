import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstantPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.UnitaryPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.AdderPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.ComparatorPrimitiveCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Six primitive bounds for the actual controlled variable modular addition. -/
theorem controlledModularAdd256_primitive_bounds (input acc : List Wire) (correction : List Bool)
    (p : Nat) (q c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : correction.length=256) :
    let v := primitiveResources (controlledModularAdd input acc correction p q c r t f)
    v.x≤5889 ∧ v.h≤2044 ∧ v.cnot≤9712 ∧ v.toffoli≤2813 ∧ v.phase=0 ∧ v.measurements≤511 := by
  have hd : (input.take (acc.length-1)).length=255 := by simp [hi,ha]
  have hb := gidneyCompareGE256_primitive_bounds acc input p c r t f ha hi
  have hc := controlledGidneyAddConst256_primitive_bounds acc (input.take (acc.length-1)) correction f c r t ha hd hk
  have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
  dsimp only at hb hc ⊢
  simp only [controlledModularAdd,controlledAddCarry256_primitive _ _ _ _ _ hi ha,
    primitiveResources_seq,controlledCompareLT256_primitive _ _ _ _ _ ha hi,
    hdone,PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩

/-- Subtraction uses a measured modulus addition and the coherent carry inverse. -/
theorem controlledModularSub256_primitive_bounds (input acc : List Wire) (modulus : List Bool)
    (p : Nat) (q c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : modulus.length=256) :
    let v := primitiveResources (controlledModularSub input acc modulus p q c r t f)
    v.x≤5889 ∧ v.h≤2044 ∧ v.cnot≤9712 ∧ v.toffoli≤2813 ∧ v.phase=0 ∧ v.measurements≤511 := by
  have hd : (input.take (acc.length-1)).length=255 := by simp [hi,ha]
  have hb := gidneyCompareGE256_primitive_bounds acc input p c r t f ha hi
  have hc := controlledGidneyAddConst256_primitive_bounds acc (input.take (acc.length-1)) modulus f c r t ha hd hk
  have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
  dsimp only at hb hc ⊢
  simp only [controlledModularSub,controlledCompareLT256_primitive _ _ _ _ _ ha hi,
    primitiveResources_seq,controlledSubCarry256_primitive _ _ _ _ _ hi ha,
    hdone,PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum
private theorem primitive_flag_cx (a f : Wire) (next : AdaptiveCircuit) :
    primitiveResources (.unitary [.CX a f] next)=
      (⟨0,0,1,0,0,0⟩ : PrimitiveResources).add (primitiveResources next) := by
  simp [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
    gidneyToffoliCount,primitiveXCost,primitiveHCost,primitivePhaseCost,AdaptiveCircuit.measurementCount]

/-- Primitive bounds for the literal shift/reduce/erase doubling circuit. -/
theorem modularDouble256_primitive_bounds (acc dirty : List Wire) (correction : List Bool)
    (p : Nat) (c r t f : Wire) (ha : acc.length=256) (hd : dirty.length=256)
    (hk : correction.length=256) :
    let v := primitiveResources (modularDouble acc dirty correction p c r t f)
    v.x≤5373 ∧ v.h≤2044 ∧ v.cnot≤8432 ∧ v.toffoli≤1531 ∧ v.phase=0 ∧ v.measurements≤511 := by
  cases acc with
  | nil => simp at ha
  | cons a rest =>
    have hr : rest.length=255 := by simpa using ha
    have hdt : (dirty.take rest.length).length=255 := by simp [hr,hd]
    have hb := gidneyCompareGE256_primitive_bounds (a::rest) dirty p c r t f ha hd
    have hc := controlledGidneyAddConst256_primitive_bounds (a::rest) (dirty.take rest.length) correction f c r t ha hdt hk
    have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
    dsimp only at hb hc ⊢
    simp only [modularDouble,doublingShift256_primitive _ _ ha,primitiveResources_seq,
      primitive_flag_cx,hdone,PrimitiveResources.add]
    exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩

/-- Halving counts its measured correction and the actual inverse shift. -/
theorem modularHalve256_primitive_bounds (acc dirty : List Wire) (modulus : List Bool)
    (p : Nat) (c r t f : Wire) (ha : acc.length=256) (hd : dirty.length=256)
    (hk : modulus.length=256) :
    let v := primitiveResources (modularHalve acc dirty modulus p c r t f)
    v.x≤5373 ∧ v.h≤2044 ∧ v.cnot≤8432 ∧ v.toffoli≤1531 ∧ v.phase=0 ∧ v.measurements≤511 := by
  cases acc with
  | nil => simp at ha
  | cons a rest =>
    have hr : rest.length=255 := by simpa using ha
    have hdt : (dirty.take rest.length).length=255 := by simp [hr,hd]
    have hb := gidneyCompareGE256_primitive_bounds (a::rest) dirty p c r t f ha hd
    have hc := controlledGidneyAddConst256_primitive_bounds (a::rest) (dirty.take rest.length) modulus f c r t ha hdt hk
    have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
    dsimp only at hb hc ⊢
    simp only [modularHalve,primitive_flag_cx,primitiveResources_seq,
      primitiveResources_unitary_adjoint,doublingShift256_primitive _ _ ha,hdone,PrimitiveResources.add]
    exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
end ShorECDLP.Paper2607_13816

namespace ShorECDLP.Paper2607_13816
/-- Exact controlled modular addition, including arbitrary constant shortcuts. -/
theorem controlledModularAdd256_primitive_exact (input acc : List Wire) (correction : List Bool)
    (p : Nat) (q c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : correction.length=256) :
    primitiveResources (controlledModularAdd input acc correction p q c r t f)=
      (⟨516,0,2048,1282,0,0⟩ : PrimitiveResources).add
        ((constantGE256Primitives false p).add (constantAdder256Primitives true correction)) := by
  have hd : (input.take (acc.length-1)).length=255 := by simp [hi,ha]
  have hb := gidneyCompareGE256_primitive_exact acc input p c r t f ha hi
  have hc := controlledGidneyAddConst256_primitive_exact acc (input.take (acc.length-1)) correction f c r t ha hd hk
  change primitiveResources (gidneyCompareGE acc input p c r t f)=constantGE256Primitives false p at hb
  change primitiveResources (controlledGidneyAddConst acc (input.take (acc.length-1)) correction f c r t)=constantAdder256Primitives true correction at hc
  have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
  simp only [controlledModularAdd,controlledAddCarry256_primitive _ _ _ _ _ hi ha,
    primitiveResources_seq,controlledCompareLT256_primitive _ _ _ _ _ ha hi,hb,hc,hdone,
    PrimitiveResources.add,PrimitiveResources.mk.injEq]
  omega
/-- Exact subtraction has the reversed stages and the same constant-dependent vector. -/
theorem controlledModularSub256_primitive_exact (input acc : List Wire) (modulus : List Bool)
    (p : Nat) (q c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : modulus.length=256) :
    primitiveResources (controlledModularSub input acc modulus p q c r t f)=
      (⟨516,0,2048,1282,0,0⟩ : PrimitiveResources).add
        ((constantGE256Primitives false p).add (constantAdder256Primitives true modulus)) := by
  have hd : (input.take (acc.length-1)).length=255 := by simp [hi,ha]
  have hb := gidneyCompareGE256_primitive_exact acc input p c r t f ha hi
  have hc := controlledGidneyAddConst256_primitive_exact acc (input.take (acc.length-1)) modulus f c r t ha hd hk
  change primitiveResources (gidneyCompareGE acc input p c r t f)=constantGE256Primitives false p at hb
  change primitiveResources (controlledGidneyAddConst acc (input.take (acc.length-1)) modulus f c r t)=constantAdder256Primitives true modulus at hc
  have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
  simp only [controlledModularSub,controlledCompareLT256_primitive _ _ _ _ _ ha hi,
    primitiveResources_seq,controlledSubCarry256_primitive _ _ _ _ _ hi ha,hb,hc,hdone,
    PrimitiveResources.add,PrimitiveResources.mk.injEq]
  omega
end ShorECDLP.Paper2607_13816

namespace ShorECDLP.Paper2607_13816
/-- Exact doubling separates its 768 shift/flag CNOTs from measured correction. -/
theorem modularDouble256_primitive_exact (acc dirty : List Wire) (correction : List Bool)
    (p : Nat) (c r t f : Wire) (ha : acc.length=256) (hd : dirty.length=256)
    (hk : correction.length=256) :
    primitiveResources (modularDouble acc dirty correction p c r t f)=
      (⟨0,0,768,0,0,0⟩ : PrimitiveResources).add
        ((constantGE256Primitives false p).add (constantAdder256Primitives true correction)) := by
  cases acc with
  | nil => simp at ha
  | cons a rest =>
    have hr : rest.length=255 := by simpa using ha
    have hdt : (dirty.take rest.length).length=255 := by simp [hr,hd]
    have hb := gidneyCompareGE256_primitive_exact (a::rest) dirty p c r t f ha hd
    have hc := controlledGidneyAddConst256_primitive_exact (a::rest) (dirty.take rest.length) correction f c r t ha hdt hk
    change primitiveResources (gidneyCompareGE (a::rest) dirty p c r t f)=constantGE256Primitives false p at hb
    change primitiveResources (controlledGidneyAddConst (a::rest) (dirty.take rest.length) correction f c r t)=constantAdder256Primitives true correction at hc
    have hdone : primitiveResources (.unitary [.CX a f] .done)=(⟨0,0,1,0,0,0⟩ : PrimitiveResources) := rfl
    simp only [modularDouble,doublingShift256_primitive _ _ ha,primitiveResources_seq,
      hb,hc,hdone,PrimitiveResources.add,PrimitiveResources.mk.injEq]
    omega
/-- Exact halving counts the inverse shift and measured modulus addition. -/
theorem modularHalve256_primitive_exact (acc dirty : List Wire) (modulus : List Bool)
    (p : Nat) (c r t f : Wire) (ha : acc.length=256) (hd : dirty.length=256)
    (hk : modulus.length=256) :
    primitiveResources (modularHalve acc dirty modulus p c r t f)=
      (⟨0,0,768,0,0,0⟩ : PrimitiveResources).add
        ((constantGE256Primitives false p).add (constantAdder256Primitives true modulus)) := by
  cases acc with
  | nil => simp at ha
  | cons a rest =>
    have hr : rest.length=255 := by simpa using ha
    have hdt : (dirty.take rest.length).length=255 := by simp [hr,hd]
    have hb := gidneyCompareGE256_primitive_exact (a::rest) dirty p c r t f ha hd
    have hc := controlledGidneyAddConst256_primitive_exact (a::rest) (dirty.take rest.length) modulus f c r t ha hdt hk
    change primitiveResources (gidneyCompareGE (a::rest) dirty p c r t f)=constantGE256Primitives false p at hb
    change primitiveResources (controlledGidneyAddConst (a::rest) (dirty.take rest.length) modulus f c r t)=constantAdder256Primitives true modulus at hc
    have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
    have hcx (next : Quantum.AdaptiveCircuit) : primitiveResources (.unitary [.CX a f] next)=
        (⟨0,0,1,0,0,0⟩ : PrimitiveResources).add (primitiveResources next) := by
      simp [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
        gidneyToffoliCount,primitiveXCost,primitiveHCost,primitivePhaseCost,Quantum.AdaptiveCircuit.measurementCount]
    simp only [modularHalve,hcx,primitiveResources_seq,primitiveResources_unitary_adjoint,
      doublingShift256_primitive _ _ ha,hb,hc,hdone,PrimitiveResources.add,PrimitiveResources.mk.injEq]
    omega
end ShorECDLP.Paper2607_13816
