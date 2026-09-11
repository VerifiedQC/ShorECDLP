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

namespace ShorECDLP.Paper2607_13816
/-- Exact width-256 adder formula; fixed control moves the extra CNOTs to X. -/
def constantAdder256Primitives (controlled : Bool) (constant : List Bool) : PrimitiveResources :=
  let extra := 8*(constant.headD false).toNat+10*constantBitWeight (constant.tail.take 254)+
    (constant.tail.getLastD false).toNat
  if constant.all (fun b => !b) then ⟨0,0,0,0,0,0⟩
  else if controlled then ⟨1022,1020,1276+extra,764,0,255⟩
  else ⟨1022+extra,1020,1276,764,0,255⟩
/-- Exact width-256 threshold formula with both source shortcuts. -/
def constantGE256Primitives (controlled : Bool) (p : Nat) : PrimitiveResources :=
  let bits := (List.range 256).map (Nat.testBit (2^256-p))
  let extra := 7*(bits.headD false).toNat+9*constantBitWeight bits.tail
  if p=0 then if controlled then ⟨0,0,1,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
  else if 2^256≤p then ⟨0,0,0,0,0,0⟩
  else if controlled then ⟨512,1024,1537+extra,767,0,256⟩
  else ⟨512+extra,1024,1537,767,0,256⟩
/-- Exact LT formula accounts for its flag complement only when it is present. -/
def constantLT256Primitives (controlled : Bool) (p : Nat) : PrimitiveResources :=
  let bits := (List.range 256).map (Nat.testBit (2^256-p))
  let extra := 7*(bits.headD false).toNat+9*constantBitWeight bits.tail
  if p=0 then ⟨0,0,0,0,0,0⟩
  else if 2^256≤p then if controlled then ⟨0,0,1,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
  else if controlled then ⟨512,1024,1538+extra,767,0,256⟩
  else ⟨513+extra,1024,1537,767,0,256⟩

/-- Exact primitive vector for all five actual controlled modular stages. -/
theorem controlledConstantModularAdd256_primitive_exact (target dirty : List Wire)
    (constant correction : List Bool) (p : Nat) (q c r t f : Wire)
    (hi : target.length=256) (hd : dirty.length=256)
    (hk : constant.length=256) (hcorr : correction.length=256) :
    primitiveResources (controlledConstantModularAdd target dirty constant correction p q c r t f)=
      (constantAdder256Primitives true constant).add
        ((constantLT256Primitives true (boolWordToNat constant)).add
          ((constantGE256Primitives false p).add
            ((constantAdder256Primitives true correction).add
              (constantLT256Primitives true (boolWordToNat constant))))) := by
  have hd' : (dirty.take (target.length-1)).length=255 := by simp [hi,hd]
  simp only [controlledConstantModularAdd,primitiveResources_seq,
    controlledGidneyAddConst256_primitive_exact target (dirty.take (target.length-1)) constant q c r t hi hd' hk,
    controlledGidneyAddConst256_primitive_exact target (dirty.take (target.length-1)) correction f c r t hi hd' hcorr,
    controlledGidneyCompareLT256_primitive_exact target dirty (boolWordToNat constant) q c r t f hi hd,
    gidneyCompareGE256_primitive_exact target dirty p c r t f hi hd,
    constantAdder256Primitives,constantLT256Primitives,constantGE256Primitives,Bool.false_eq_true,if_false,if_true]

/-- Exact primitive vector for all five actual unconditional modular stages. -/
theorem uncontrolledConstantModularAdd256_primitive_exact (target dirty : List Wire)
    (constant correction : List Bool) (p : Nat) (c r t f : Wire)
    (hi : target.length=256) (hd : dirty.length=256)
    (hk : constant.length=256) (hcorr : correction.length=256) :
    primitiveResources (uncontrolledConstantModularAdd target dirty constant correction p c r t f)=
      (constantAdder256Primitives false constant).add
        ((constantLT256Primitives false (boolWordToNat constant)).add
          ((constantGE256Primitives false p).add
            ((constantAdder256Primitives true correction).add
              (constantLT256Primitives false (boolWordToNat constant))))) := by
  have hd' : (dirty.take (target.length-1)).length=255 := by simp [hi,hd]
  simp only [uncontrolledConstantModularAdd,primitiveResources_seq,
    gidneyAddConst256_primitive_exact target (dirty.take (target.length-1)) constant c r t hi hd' hk,
    controlledGidneyAddConst256_primitive_exact target (dirty.take (target.length-1)) correction f c r t hi hd' hcorr,
    gidneyCompareLT256_primitive_exact target dirty (boolWordToNat constant) c r t f hi hd,
    gidneyCompareGE256_primitive_exact target dirty p c r t f hi hd,
    constantAdder256Primitives,constantLT256Primitives,constantGE256Primitives,Bool.false_eq_true,if_false,if_true]
end ShorECDLP.Paper2607_13816

namespace ShorECDLP.Paper2607_13816
/-- Exact primitive vector of nonzero detection, complement, increment and correction. -/
theorem controlledModularNegate256_primitive_exact (target dirty : List Wire)
    (modulus : List Bool) (q c r t f : Wire)
    (hi : target.length=256) (hd : dirty.length=256) (hk : modulus.length=256) :
    primitiveResources (controlledModularNegate target dirty modulus q c r t f)=
      (constantGE256Primitives true 1).add
        ((⟨0,0,256,0,0,0⟩ : PrimitiveResources).add
          ((constantAdder256Primitives true ((List.range 256).map (Nat.testBit 1))).add
            ((constantAdder256Primitives true modulus).add (constantGE256Primitives true 1)))) := by
  have hd' : (dirty.take (target.length-1)).length=255 := by simp [hi,hd]
  have hunit (next : Quantum.AdaptiveCircuit) :
      primitiveResources (.unitary (controlledComplement target q) next)=
        (⟨0,0,256,0,0,0⟩ : PrimitiveResources).add (primitiveResources next) := by
    have hg : primitiveResources (.unitary (controlledComplement target q) next)=
        (⟨0,0,target.length,0,0,0⟩ : PrimitiveResources).add (primitiveResources next) := by
      simp [primitiveResources,PrimitiveResources.add,controlledComplement,gidneyGateCount,
        primitiveXCost,primitiveHCost,primitivePhaseCost,gidneyCnotCount,gidneyToffoliCount,
        Quantum.AdaptiveCircuit.measurementCount,List.map_map,Function.comp_def]
    simpa only [hi] using hg
  simp only [controlledModularNegate,primitiveResources_seq,hunit]
  rw [controlledGidneyCompareGE256_primitive_exact target dirty 1 q c r t f hi hd,
    controlledGidneyAddConst256_primitive_exact target (dirty.take (target.length-1))
      ((List.range target.length).map (Nat.testBit 1)) q c r t hi hd' (by simp [hi]),
    controlledGidneyAddConst256_primitive_exact target (dirty.take (target.length-1)) modulus f c r t hi hd' hk]
  simp only [constantAdder256Primitives,constantGE256Primitives,hi,if_true]
end ShorECDLP.Paper2607_13816
