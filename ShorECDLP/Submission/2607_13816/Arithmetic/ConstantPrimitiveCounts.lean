import ShorECDLP.Submission.«2607_13816».Arithmetic.ComparatorPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.AdderPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.ModularNegate
import ShorECDLP.Submission.«2607_13816».Arithmetic.UncontrolledModular
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Primitive upper bounds for the actual five-stage constant modular addition. -/
theorem controlledConstantModularAdd256_primitive_bounds (target dirty : List Wire)
    (constant correction : List Bool) (p : Nat) (q c r t f : Wire)
    (hi : target.length=256) (hd : dirty.length=256)
    (hk : constant.length=256) (hcorr : correction.length=256) :
    let v := primitiveResources (controlledConstantModularAdd target dirty constant correction p q c r t f)
    v.x≤7419 ∧ v.h≤5112 ∧ v.cnot≤19169 ∧ v.toffoli≤3829 ∧ v.phase=0 ∧ v.measurements≤1278 := by
  have hd' : (dirty.take (target.length-1)).length=255 := by simp [hi,hd]
  have ha := controlledGidneyAddConst256_primitive_bounds target (dirty.take (target.length-1)) constant q c r t hi hd' hk
  have hb := controlledGidneyCompareLT256_primitive_bounds target dirty (boolWordToNat constant) q c r t f hi hd
  have hc := gidneyCompareGE256_primitive_bounds target dirty p c r t f hi hd
  have he := controlledGidneyAddConst256_primitive_bounds target (dirty.take (target.length-1)) correction f c r t hi hd' hcorr
  dsimp only at ha hb hc he ⊢
  simp only [controlledConstantModularAdd,primitiveResources_seq,PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩

/-- Budget for the source's five-stage unconditional modular constant addition. -/
theorem uncontrolledConstantModularAdd256_primitive_bounds (target dirty : List Wire)
    (constant correction : List Bool) (p : Nat) (c r t f : Wire)
    (hi : target.length=256) (hd : dirty.length=256)
    (hk : constant.length=256) (hcorr : correction.length=256) :
    let v := primitiveResources (uncontrolledConstantModularAdd target dirty constant correction p c r t f)
    v.x≤18924 ∧ v.h≤5112 ∧ v.cnot≤19167 ∧ v.toffoli≤3829 ∧ v.phase=0 ∧ v.measurements≤1278 := by
  have hd' : (dirty.take (target.length-1)).length=255 := by simp [hi,hd]
  have ha := gidneyAddConst256_primitive_bounds target (dirty.take (target.length-1)) constant c r t hi hd' hk
  have hb := gidneyCompareLT256_primitive_bounds target dirty (boolWordToNat constant) c r t f hi hd
  have hc := gidneyCompareGE256_primitive_bounds target dirty p c r t f hi hd
  have he := controlledGidneyAddConst256_primitive_bounds target (dirty.take (target.length-1)) correction f c r t hi hd' hcorr
  dsimp only at ha hb hc he ⊢
  simp only [uncontrolledConstantModularAdd,primitiveResources_seq,PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩

/-- Budget for nonzero detection, complement, increment, modulus correction and flag erasure. -/
theorem controlledModularNegate256_primitive_bounds (target dirty : List Wire)
    (modulus : List Bool) (q c r t f : Wire)
    (hi : target.length=256) (hd : dirty.length=256) (hk : modulus.length=256) :
    let v := primitiveResources (controlledModularNegate target dirty modulus q c r t f)
    v.x≤3068 ∧ v.h≤4088 ∧ v.cnot≤15584 ∧ v.toffoli≤3062 ∧ v.phase=0 ∧ v.measurements≤1022 := by
  have hd' : (dirty.take (target.length-1)).length=255 := by simp [hi,hd]
  have ha := controlledGidneyCompareGE256_primitive_bounds target dirty 1 q c r t f hi hd
  have hb := controlledGidneyAddConst256_primitive_bounds target (dirty.take (target.length-1))
    ((List.range target.length).map (Nat.testBit 1)) q c r t hi hd' (by simp [hi])
  have hc := controlledGidneyAddConst256_primitive_bounds target (dirty.take (target.length-1)) modulus f c r t hi hd' hk
  have hunit (next : AdaptiveCircuit) :
      primitiveResources (.unitary (controlledComplement target q) next) =
        (⟨0,0,256,0,0,0⟩ : PrimitiveResources).add (primitiveResources next) := by
    have hg : primitiveResources (.unitary (controlledComplement target q) next) =
        (⟨0,0,target.length,0,0,0⟩ : PrimitiveResources).add (primitiveResources next) := by
      simp [primitiveResources,PrimitiveResources.add,controlledComplement,gidneyGateCount,
        primitiveXCost,primitiveHCost,primitivePhaseCost,gidneyCnotCount,gidneyToffoliCount,
        AdaptiveCircuit.measurementCount,List.map_map,Function.comp_def]
    simpa only [hi] using hg
  dsimp only at ha hb hc ⊢
  simp only [controlledModularNegate,primitiveResources_seq,hunit,PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
end ShorECDLP.Paper2607_13816
