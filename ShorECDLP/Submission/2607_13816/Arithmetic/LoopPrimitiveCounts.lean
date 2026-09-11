import ShorECDLP.Submission.«2607_13816».Arithmetic.ModularPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.HornerInverse
import ShorECDLP.Submission.«2607_13816».Arithmetic.SquareInverse
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Primitive budgets along the actual Horner recurrence. -/
theorem hornerMul256_primitive_bounds (controls input acc : List Wire) (correction : List Bool)
    (p : Nat) (c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : correction.length=256) :
    let v := primitiveResources (hornerMul controls input acc correction p c r t f)
    let n := controls.length
    v.x≤5889*n+5373*(n-1) ∧ v.h≤2044*n+2044*(n-1) ∧
    v.cnot≤9712*n+8432*(n-1) ∧ v.toffoli≤2813*n+1531*(n-1) ∧
    v.phase=0 ∧ v.measurements≤511*n+511*(n-1) := by
  have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
  induction controls with
  | nil => simp [hornerMul,hdone]
  | cons q qs ih =>
    have hadd := controlledModularAdd256_primitive_bounds input acc correction p q c r t f hi ha hk
    have hdbl := modularDouble256_primitive_bounds acc input correction p f r t c ha hi hk
    dsimp only at ih hadd hdbl ⊢
    by_cases hz : qs=[]
    · subst qs
      simpa only [hornerMul,if_pos rfl,primitiveResources_seq,hdone,PrimitiveResources.add,
        List.length_cons,List.length_nil,Nat.zero_add,Nat.add_zero,Nat.mul_zero,Nat.mul_one,
        Nat.sub_self] using hadd
    · have hn : 0<qs.length := by cases qs <;> simp_all
      simp only [hornerMul,if_neg hz,primitiveResources_seq,PrimitiveResources.add,List.length_cons]
      exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩

/-- Primitive budgets along the actual inverse Horner recurrence. -/
theorem hornerMulInverse256_primitive_bounds (controls input acc : List Wire) (modulus : List Bool)
    (p : Nat) (c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : modulus.length=256) :
    let v := primitiveResources (hornerMulInverse controls input acc modulus p c r t f)
    let n := controls.length
    v.x≤5889*n+5373*(n-1) ∧ v.h≤2044*n+2044*(n-1) ∧
    v.cnot≤9712*n+8432*(n-1) ∧ v.toffoli≤2813*n+1531*(n-1) ∧
    v.phase=0 ∧ v.measurements≤511*n+511*(n-1) := by
  have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
  induction controls with
  | nil => simp [hornerMulInverse,hdone]
  | cons q qs ih =>
    have hadd := controlledModularSub256_primitive_bounds input acc modulus p q c r t f hi ha hk
    have hdbl := modularHalve256_primitive_bounds acc input modulus p f r t c ha hi hk
    dsimp only at ih hadd hdbl ⊢
    by_cases hz : qs=[]
    · subst qs
      simpa only [hornerMulInverse,if_pos rfl,primitiveResources_seq,hdone,PrimitiveResources.add,
        List.length_cons,List.length_nil,Nat.zero_add,Nat.add_zero,Nat.mul_zero,Nat.mul_one,
        Nat.sub_self] using hadd
    · have hn : 0<qs.length := by cases qs <;> simp_all
      simp only [hornerMulInverse,if_neg hz,primitiveResources_seq,PrimitiveResources.add,List.length_cons]
      exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
/-- Readable production-width specialization of the same loop budget. -/
theorem hornerMul256_full_primitive_bounds (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hn : controls.length=256) (hi : input.length=256)
    (ha : acc.length=256) (hk : bits.length=256) :
    let v := primitiveResources (hornerMul controls input acc bits p c r t f)
    v.x≤2877699 ∧ v.h≤1044484 ∧ v.cnot≤4636432 ∧ v.toffoli≤1110533 ∧
    v.phase=0 ∧ v.measurements≤261121 := by
  have h := hornerMul256_primitive_bounds controls input acc bits p c r t f hi ha hk
  simpa only [hn] using h

/-- Readable production-width specialization of the same loop budget. -/
theorem hornerMulInverse256_full_primitive_bounds (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hn : controls.length=256) (hi : input.length=256)
    (ha : acc.length=256) (hk : bits.length=256) :
    let v := primitiveResources (hornerMulInverse controls input acc bits p c r t f)
    v.x≤2877699 ∧ v.h≤1044484 ∧ v.cnot≤4636432 ∧ v.toffoli≤1110533 ∧
    v.phase=0 ∧ v.measurements≤261121 := by
  have h := hornerMulInverse256_primitive_bounds controls input acc bits p c r t f hi ha hk
  simpa only [hn] using h

end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- The actual copied-control wrapper adds exactly two CNOT gates. -/
theorem squareAdd256_primitive_bounds (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : bits.length=256) :
    let v := primitiveResources (squareAdd input acc bits p q copied c r t f)
    v.x≤5889 ∧ v.h≤2044 ∧ v.cnot≤9714 ∧ v.toffoli≤2813 ∧ v.phase=0 ∧ v.measurements≤511 := by
  have h := controlledModularAdd256_primitive_bounds input acc bits p copied c r t f hi ha hk
  have hcx (next : AdaptiveCircuit) : primitiveResources (.unitary [.CX q copied] next)=
      (⟨0,0,1,0,0,0⟩ : PrimitiveResources).add (primitiveResources next) := by
    simp [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
      gidneyToffoliCount,primitiveXCost,primitiveHCost,primitivePhaseCost,AdaptiveCircuit.measurementCount]
  have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
  dsimp only at h ⊢
  simp only [squareAdd,hcx,primitiveResources_seq,hdone,PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
/-- The actual copied-control wrapper adds exactly two CNOT gates. -/
theorem squareSub256_primitive_bounds (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : bits.length=256) :
    let v := primitiveResources (squareSub input acc bits p q copied c r t f)
    v.x≤5889 ∧ v.h≤2044 ∧ v.cnot≤9714 ∧ v.toffoli≤2813 ∧ v.phase=0 ∧ v.measurements≤511 := by
  have h := controlledModularSub256_primitive_bounds input acc bits p copied c r t f hi ha hk
  have hcx (next : AdaptiveCircuit) : primitiveResources (.unitary [.CX q copied] next)=
      (⟨0,0,1,0,0,0⟩ : PrimitiveResources).add (primitiveResources next) := by
    simp [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
      gidneyToffoliCount,primitiveXCost,primitiveHCost,primitivePhaseCost,AdaptiveCircuit.measurementCount]
  have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
  dsimp only at h ⊢
  simp only [squareSub,hcx,primitiveResources_seq,hdone,PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
/-- Primitive budgets along the actual square recurrence. -/
theorem squareLoop256_primitive_bounds (controls input acc : List Wire) (correction : List Bool)
    (p : Nat) (copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : correction.length=256) :
    let v := primitiveResources (squareLoop controls input acc correction p copied c r t f)
    let n := controls.length
    v.x≤5889*n+5373*(n-1) ∧ v.h≤2044*n+2044*(n-1) ∧
    v.cnot≤9714*n+8432*(n-1) ∧ v.toffoli≤2813*n+1531*(n-1) ∧
    v.phase=0 ∧ v.measurements≤511*n+511*(n-1) := by
  have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
  induction controls with
  | nil => simp [squareLoop,hdone]
  | cons q qs ih =>
    have hadd := squareAdd256_primitive_bounds input acc correction p q copied c r t f hi ha hk
    have hdbl := modularDouble256_primitive_bounds acc input correction p f r t c ha hi hk
    dsimp only at ih hadd hdbl ⊢
    by_cases hz : qs=[]
    · subst qs
      simpa only [squareLoop,if_pos rfl,primitiveResources_seq,hdone,PrimitiveResources.add,
        List.length_cons,List.length_nil,Nat.zero_add,Nat.add_zero,Nat.mul_zero,Nat.mul_one,
        Nat.sub_self] using hadd
    · have hn : 0<qs.length := by cases qs <;> simp_all
      simp only [squareLoop,if_neg hz,primitiveResources_seq,PrimitiveResources.add,List.length_cons]
      exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩

/-- Primitive budgets along the actual inverse square recurrence. -/
theorem squareLoopInverse256_primitive_bounds (controls input acc : List Wire) (modulus : List Bool)
    (p : Nat) (copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : modulus.length=256) :
    let v := primitiveResources (squareLoopInverse controls input acc modulus p copied c r t f)
    let n := controls.length
    v.x≤5889*n+5373*(n-1) ∧ v.h≤2044*n+2044*(n-1) ∧
    v.cnot≤9714*n+8432*(n-1) ∧ v.toffoli≤2813*n+1531*(n-1) ∧
    v.phase=0 ∧ v.measurements≤511*n+511*(n-1) := by
  have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
  induction controls with
  | nil => simp [squareLoopInverse,hdone]
  | cons q qs ih =>
    have hadd := squareSub256_primitive_bounds input acc modulus p q copied c r t f hi ha hk
    have hdbl := modularHalve256_primitive_bounds acc input modulus p f r t c ha hi hk
    dsimp only at ih hadd hdbl ⊢
    by_cases hz : qs=[]
    · subst qs
      simpa only [squareLoopInverse,if_pos rfl,primitiveResources_seq,hdone,PrimitiveResources.add,
        List.length_cons,List.length_nil,Nat.zero_add,Nat.add_zero,Nat.mul_zero,Nat.mul_one,
        Nat.sub_self] using hadd
    · have hn : 0<qs.length := by cases qs <;> simp_all
      simp only [squareLoopInverse,if_neg hz,primitiveResources_seq,PrimitiveResources.add,List.length_cons]
      exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
/-- Readable production-width specialization of the same loop budget. -/
theorem squareLoop256_full_primitive_bounds (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (hn : controls.length=256) (hi : input.length=256)
    (ha : acc.length=256) (hk : bits.length=256) :
    let v := primitiveResources (squareLoop controls input acc bits p copied c r t f)
    v.x≤2877699 ∧ v.h≤1044484 ∧ v.cnot≤4636944 ∧ v.toffoli≤1110533 ∧
    v.phase=0 ∧ v.measurements≤261121 := by
  have h := squareLoop256_primitive_bounds controls input acc bits p copied c r t f hi ha hk
  simpa only [hn] using h

/-- Readable production-width specialization of the same loop budget. -/
theorem squareLoopInverse256_full_primitive_bounds (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (hn : controls.length=256) (hi : input.length=256)
    (ha : acc.length=256) (hk : bits.length=256) :
    let v := primitiveResources (squareLoopInverse controls input acc bits p copied c r t f)
    v.x≤2877699 ∧ v.h≤1044484 ∧ v.cnot≤4636944 ∧ v.toffoli≤1110533 ∧
    v.phase=0 ∧ v.measurements≤261121 := by
  have h := squareLoopInverse256_primitive_bounds controls input acc bits p copied c r t f hi ha hk
  simpa only [hn] using h

end ShorECDLP.Paper2607_13816

namespace ShorECDLP.Paper2607_13816
/-- Repetition scales each component of a structural resource vector. -/
def PrimitiveResources.scale (n : Nat) (a : PrimitiveResources) : PrimitiveResources :=
  ⟨n*a.x,n*a.h,n*a.cnot,n*a.toffoli,n*a.phase,n*a.measurements⟩
private theorem loopVector_step (n : Nat) (a b : PrimitiveResources) (hn : 0<n) :
    (a.scale n).add ((b.scale (n-1)).add (b.add a))=
      (a.scale (n+1)).add (b.scale n) := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [PrimitiveResources.scale,PrimitiveResources.add,PrimitiveResources.mk.injEq,
      Nat.succ_sub_one,Nat.add_mul,Nat.one_mul]
    omega
/-- Exact Horner vector: one modular add per control and one double between controls. -/
theorem hornerMul256_primitive_exact (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : bits.length=256) :
    let measured := (constantGE256Primitives false p).add (constantAdder256Primitives true bits)
    let add := (⟨516,0,2048,1282,0,0⟩ : PrimitiveResources).add measured
    let dbl := (⟨0,0,768,0,0,0⟩ : PrimitiveResources).add measured
    primitiveResources (hornerMul controls input acc bits p c r t f)=
      (add.scale controls.length).add (dbl.scale (controls.length-1)) := by
  dsimp only
  have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
  induction controls with
  | nil => simp [hornerMul,hdone,PrimitiveResources.scale,PrimitiveResources.add]
  | cons q qs ih =>
    have hadd := controlledModularAdd256_primitive_exact input acc bits p q c r t f hi ha hk
    have hdbl := modularDouble256_primitive_exact acc input bits p f r t c ha hi hk
    by_cases hz : qs=[]
    · subst qs
      simpa only [hornerMul,if_pos rfl,primitiveResources_seq,hdone,PrimitiveResources.add,
        PrimitiveResources.scale,List.length_cons,List.length_nil,Nat.zero_add,Nat.add_zero,
        Nat.zero_mul,Nat.one_mul,Nat.sub_self] using hadd
    · have hn : 0<qs.length := List.length_pos_iff.mpr hz
      simp only [hornerMul,if_neg hz,primitiveResources_seq,hadd,hdbl,ih,List.length_cons]
      have hs := loopVector_step qs.length
        ((⟨516,0,2048,1282,0,0⟩ : PrimitiveResources).add
          ((constantGE256Primitives false p).add (constantAdder256Primitives true bits)))
        ((⟨0,0,768,0,0,0⟩ : PrimitiveResources).add
          ((constantGE256Primitives false p).add (constantAdder256Primitives true bits))) hn
      simpa only [PrimitiveResources.add,Nat.add_sub_cancel,Nat.add_assoc] using hs
/-- Exact inverse Horner vector for subtraction and halving in source order. -/
theorem hornerMulInverse256_primitive_exact (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : bits.length=256) :
    let measured := (constantGE256Primitives false p).add (constantAdder256Primitives true bits)
    let add := (⟨516,0,2048,1282,0,0⟩ : PrimitiveResources).add measured
    let dbl := (⟨0,0,768,0,0,0⟩ : PrimitiveResources).add measured
    primitiveResources (hornerMulInverse controls input acc bits p c r t f)=
      (add.scale controls.length).add (dbl.scale (controls.length-1)) := by
  dsimp only
  have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
  induction controls with
  | nil => simp [hornerMulInverse,hdone,PrimitiveResources.scale,PrimitiveResources.add]
  | cons q qs ih =>
    have hadd := controlledModularSub256_primitive_exact input acc bits p q c r t f hi ha hk
    have hdbl := modularHalve256_primitive_exact acc input bits p f r t c ha hi hk
    by_cases hz : qs=[]
    · subst qs
      simpa only [hornerMulInverse,if_pos rfl,primitiveResources_seq,hdone,PrimitiveResources.add,
        PrimitiveResources.scale,List.length_cons,List.length_nil,Nat.zero_add,Nat.add_zero,
        Nat.zero_mul,Nat.one_mul,Nat.sub_self] using hadd
    · have hn : 0<qs.length := List.length_pos_iff.mpr hz
      simp only [hornerMulInverse,if_neg hz,primitiveResources_seq,hadd,hdbl,ih,List.length_cons]
      have hs := loopVector_step qs.length
        ((⟨516,0,2048,1282,0,0⟩ : PrimitiveResources).add
          ((constantGE256Primitives false p).add (constantAdder256Primitives true bits)))
        ((⟨0,0,768,0,0,0⟩ : PrimitiveResources).add
          ((constantGE256Primitives false p).add (constantAdder256Primitives true bits))) hn
      simp only [PrimitiveResources.add,Nat.add_sub_cancel,PrimitiveResources.mk.injEq] at hs ⊢
      omega
end ShorECDLP.Paper2607_13816

namespace ShorECDLP.Paper2607_13816
/-- Exact copied-control squareAdd adds two CNOTs to the actual modular stage. -/
theorem squareAdd256_primitive_exact (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : bits.length=256) :
    primitiveResources (squareAdd input acc bits p q copied c r t f)=
      (⟨516,0,2050,1282,0,0⟩ : PrimitiveResources).add
        ((constantGE256Primitives false p).add (constantAdder256Primitives true bits)) := by
  have h := controlledModularAdd256_primitive_exact input acc bits p copied c r t f hi ha hk
  have hcx (next : Quantum.AdaptiveCircuit) : primitiveResources (.unitary [.CX q copied] next)=
      (⟨0,0,1,0,0,0⟩ : PrimitiveResources).add (primitiveResources next) := by
    simp [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
      gidneyToffoliCount,primitiveXCost,primitiveHCost,primitivePhaseCost,Quantum.AdaptiveCircuit.measurementCount]
  have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
  simp only [squareAdd,hcx,primitiveResources_seq,h,hdone,PrimitiveResources.add,PrimitiveResources.mk.injEq]
  omega
/-- Exact copied-control squareSub adds two CNOTs to the actual modular stage. -/
theorem squareSub256_primitive_exact (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : bits.length=256) :
    primitiveResources (squareSub input acc bits p q copied c r t f)=
      (⟨516,0,2050,1282,0,0⟩ : PrimitiveResources).add
        ((constantGE256Primitives false p).add (constantAdder256Primitives true bits)) := by
  have h := controlledModularSub256_primitive_exact input acc bits p copied c r t f hi ha hk
  have hcx (next : Quantum.AdaptiveCircuit) : primitiveResources (.unitary [.CX q copied] next)=
      (⟨0,0,1,0,0,0⟩ : PrimitiveResources).add (primitiveResources next) := by
    simp [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
      gidneyToffoliCount,primitiveXCost,primitiveHCost,primitivePhaseCost,Quantum.AdaptiveCircuit.measurementCount]
  have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
  simp only [squareSub,hcx,primitiveResources_seq,h,hdone,PrimitiveResources.add,PrimitiveResources.mk.injEq]
  omega
/-- Exact square vector: one modular add per control and one double between controls. -/
theorem squareLoop256_primitive_exact (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : bits.length=256) :
    let measured := (constantGE256Primitives false p).add (constantAdder256Primitives true bits)
    let add := (⟨516,0,2050,1282,0,0⟩ : PrimitiveResources).add measured
    let dbl := (⟨0,0,768,0,0,0⟩ : PrimitiveResources).add measured
    primitiveResources (squareLoop controls input acc bits p copied c r t f)=
      (add.scale controls.length).add (dbl.scale (controls.length-1)) := by
  dsimp only
  have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
  induction controls with
  | nil => simp [squareLoop,hdone,PrimitiveResources.scale,PrimitiveResources.add]
  | cons q qs ih =>
    have hadd := squareAdd256_primitive_exact input acc bits p q copied c r t f hi ha hk
    have hdbl := modularDouble256_primitive_exact acc input bits p f r t c ha hi hk
    by_cases hz : qs=[]
    · subst qs
      simpa only [squareLoop,if_pos rfl,primitiveResources_seq,hdone,PrimitiveResources.add,
        PrimitiveResources.scale,List.length_cons,List.length_nil,Nat.zero_add,Nat.add_zero,
        Nat.zero_mul,Nat.one_mul,Nat.sub_self] using hadd
    · have hn : 0<qs.length := List.length_pos_iff.mpr hz
      simp only [squareLoop,if_neg hz,primitiveResources_seq,hadd,hdbl,ih,List.length_cons]
      have hs := loopVector_step qs.length
        ((⟨516,0,2050,1282,0,0⟩ : PrimitiveResources).add
          ((constantGE256Primitives false p).add (constantAdder256Primitives true bits)))
        ((⟨0,0,768,0,0,0⟩ : PrimitiveResources).add
          ((constantGE256Primitives false p).add (constantAdder256Primitives true bits))) hn
      simpa only [PrimitiveResources.add,Nat.add_sub_cancel,Nat.add_assoc] using hs
/-- Exact inverse square vector for subtraction and halving in source order. -/
theorem squareLoopInverse256_primitive_exact (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : bits.length=256) :
    let measured := (constantGE256Primitives false p).add (constantAdder256Primitives true bits)
    let add := (⟨516,0,2050,1282,0,0⟩ : PrimitiveResources).add measured
    let dbl := (⟨0,0,768,0,0,0⟩ : PrimitiveResources).add measured
    primitiveResources (squareLoopInverse controls input acc bits p copied c r t f)=
      (add.scale controls.length).add (dbl.scale (controls.length-1)) := by
  dsimp only
  have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
  induction controls with
  | nil => simp [squareLoopInverse,hdone,PrimitiveResources.scale,PrimitiveResources.add]
  | cons q qs ih =>
    have hadd := squareSub256_primitive_exact input acc bits p q copied c r t f hi ha hk
    have hdbl := modularHalve256_primitive_exact acc input bits p f r t c ha hi hk
    by_cases hz : qs=[]
    · subst qs
      simpa only [squareLoopInverse,if_pos rfl,primitiveResources_seq,hdone,PrimitiveResources.add,
        PrimitiveResources.scale,List.length_cons,List.length_nil,Nat.zero_add,Nat.add_zero,
        Nat.zero_mul,Nat.one_mul,Nat.sub_self] using hadd
    · have hn : 0<qs.length := List.length_pos_iff.mpr hz
      simp only [squareLoopInverse,if_neg hz,primitiveResources_seq,hadd,hdbl,ih,List.length_cons]
      have hs := loopVector_step qs.length
        ((⟨516,0,2050,1282,0,0⟩ : PrimitiveResources).add
          ((constantGE256Primitives false p).add (constantAdder256Primitives true bits)))
        ((⟨0,0,768,0,0,0⟩ : PrimitiveResources).add
          ((constantGE256Primitives false p).add (constantAdder256Primitives true bits))) hn
      simp only [PrimitiveResources.add,Nat.add_sub_cancel,PrimitiveResources.mk.injEq] at hs ⊢
      omega
end ShorECDLP.Paper2607_13816

namespace ShorECDLP.Paper2607_13816
private theorem productionGEVector : constantGE256Primitives false (2^256-(2^32+977))=
    (⟨573,1024,1537,767,0,256⟩ : PrimitiveResources) := by decide +kernel
private theorem productionReductionVector : constantAdder256Primitives true secp256k1ReductionConstantBits=
    (⟨1022,1020,1344,764,0,255⟩ : PrimitiveResources) := by decide +kernel
private theorem productionModulusVector : constantAdder256Primitives true secp256k1ModulusBits=
    (⟨1022,1020,3765,764,0,255⟩ : PrimitiveResources) := by decide +kernel
/-- Exact production-width hornerMul vector, independent of physical register labels. -/
theorem hornerMul256_secp_primitive_exact (controls input acc : List Wire) (c r t f : Wire)
    (hn : controls.length=256) (hi : input.length=256) (ha : acc.length=256) :
    primitiveResources (hornerMul controls input acc secp256k1ReductionConstantBits (2^256-(2^32+977)) c r t f)=
      (⟨947141,1044484,2192319,1110533,0,261121⟩ : PrimitiveResources) := by
  have hh := hornerMul256_primitive_exact controls input acc secp256k1ReductionConstantBits
    (2^256-(2^32+977)) c r t f hi ha (by decide +kernel)
  dsimp only at hh
  rw [productionGEVector,productionReductionVector,hn] at hh
  exact hh
/-- Exact production-width hornerMulInverse vector, independent of physical register labels. -/
theorem hornerMulInverse256_secp_primitive_exact (controls input acc : List Wire) (c r t f : Wire)
    (hn : controls.length=256) (hi : input.length=256) (ha : acc.length=256) :
    primitiveResources (hornerMulInverse controls input acc secp256k1ModulusBits (2^256-(2^32+977)) c r t f)=
      (⟨947141,1044484,3429450,1110533,0,261121⟩ : PrimitiveResources) := by
  have hh := hornerMulInverse256_primitive_exact controls input acc secp256k1ModulusBits
    (2^256-(2^32+977)) c r t f hi ha (by decide +kernel)
  dsimp only at hh
  rw [productionGEVector,productionModulusVector,hn] at hh
  exact hh
/-- Exact production-width squareLoop vector, independent of physical register labels. -/
theorem squareLoop256_secp_primitive_exact (controls input acc : List Wire) (copied c r t f : Wire)
    (hn : controls.length=256) (hi : input.length=256) (ha : acc.length=256) :
    primitiveResources (squareLoop controls input acc secp256k1ReductionConstantBits (2^256-(2^32+977)) copied c r t f)=
      (⟨947141,1044484,2192831,1110533,0,261121⟩ : PrimitiveResources) := by
  have hh := squareLoop256_primitive_exact controls input acc secp256k1ReductionConstantBits
    (2^256-(2^32+977)) copied c r t f hi ha (by decide +kernel)
  dsimp only at hh
  rw [productionGEVector,productionReductionVector,hn] at hh
  exact hh
/-- Exact production-width squareLoopInverse vector, independent of physical register labels. -/
theorem squareLoopInverse256_secp_primitive_exact (controls input acc : List Wire) (copied c r t f : Wire)
    (hn : controls.length=256) (hi : input.length=256) (ha : acc.length=256) :
    primitiveResources (squareLoopInverse controls input acc secp256k1ModulusBits (2^256-(2^32+977)) copied c r t f)=
      (⟨947141,1044484,3429962,1110533,0,261121⟩ : PrimitiveResources) := by
  have hh := squareLoopInverse256_primitive_exact controls input acc secp256k1ModulusBits
    (2^256-(2^32+977)) copied c r t f hi ha (by decide +kernel)
  dsimp only at hh
  rw [productionGEVector,productionModulusVector,hn] at hh
  exact hh
end ShorECDLP.Paper2607_13816
