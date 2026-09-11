import ShorECDLP.Submission.«2607_13816».Arithmetic.InPlace
import ShorECDLP.Submission.«2607_13816».Arithmetic.AdaptivePrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.WrapperPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.LoopPrimitiveCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
attribute [local irreducible] primitiveResources secp256k1EEAForwardWrapper secp256k1EEAReverseWrapper
  secp256k1EEAForwardInDataBank secp256k1EEAReverseInDataBank fig15MultiplyToWork fig15MultiplyToData
  fig15MultiplyToDataInverse fig15DivisionAfterReset fig15MultiplicationAfterReset
  secp256k1InPlaceDivision secp256k1InPlaceMultiplication
/-- Borrowing the data bank only relabels the complete forward wrapper. -/
theorem secp256k1EEAForwardInDataBank_primitive_bounds :
    let v := primitiveResources secp256k1EEAForwardInDataBank
    v.x≤19441121 ∧ v.h≤10562768 ∧ v.cnot≤29743147 ∧ v.toffoli≤17591751 ∧
      v.phase=0 ∧ v.measurements≤5280108 := by
  rw [secp256k1EEAForwardInDataBank,primitiveResources_relabel]
  exact secp256k1EEAForwardWrapper_primitive_bounds
/-- The explicit reverse wrapper has identical counts after the bank exchange. -/
theorem secp256k1EEAReverseInDataBank_primitive_bounds :
    let v := primitiveResources secp256k1EEAReverseInDataBank
    v.x≤19492961 ∧ v.h≤10562768 ∧ v.cnot≤29743147 ∧ v.toffoli≤17591751 ∧
      v.phase=0 ∧ v.measurements≤5280108 := by
  rw [secp256k1EEAReverseInDataBank,primitiveResources_relabel]
  exact secp256k1EEAReverseWrapper_primitive_bounds
theorem fig15MultiplyToWork_primitive_bounds :
    let v := primitiveResources fig15MultiplyToWork
    v.x≤2877699 ∧ v.h≤1044484 ∧ v.cnot≤4636432 ∧ v.toffoli≤1110533 ∧
      v.phase=0 ∧ v.measurements≤261121 := by
  rw [fig15MultiplyToWork]
  apply hornerMul256_full_primitive_bounds <;> simp [secp256k1ReductionConstantBits]
theorem fig15MultiplyToData_primitive_bounds :
    let v := primitiveResources fig15MultiplyToData
    v.x≤2877699 ∧ v.h≤1044484 ∧ v.cnot≤4636432 ∧ v.toffoli≤1110533 ∧
      v.phase=0 ∧ v.measurements≤261121 := by
  rw [fig15MultiplyToData]
  apply hornerMul256_full_primitive_bounds <;> simp [secp256k1ReductionConstantBits]
theorem fig15MultiplyToDataInverse_primitive_bounds :
    let v := primitiveResources fig15MultiplyToDataInverse
    v.x≤2877699 ∧ v.h≤1044484 ∧ v.cnot≤4636432 ∧ v.toffoli≤1110533 ∧
      v.phase=0 ∧ v.measurements≤261121 := by
  rw [fig15MultiplyToDataInverse]
  apply hornerMulInverse256_full_primitive_bounds <;> simp
private theorem swapOutputList_primitive (xs : List Nat) :
    primitiveResources (.unitary (xs.flatMap (fun i =>
      [.CX (580+i) (7+i),.CX (7+i) (580+i),.CX (580+i) (7+i)])) .done)=
      (⟨0,0,3*xs.length,0,0,0⟩ : PrimitiveResources) := by
  induction xs with
  | nil => unfold primitiveResources; rfl
  | cons i xs ih =>
    rw [List.flatMap_cons,primitiveResources_unitary_append,ih]
    have hh : primitiveResources (.unitary
        [.CX (580+i) (7+i),.CX (7+i) (580+i),.CX (580+i) (7+i)] .done)=
        (⟨0,0,3,0,0,0⟩ : PrimitiveResources) := by unfold primitiveResources; rfl
    rw [hh]
    simp [PrimitiveResources.add,Nat.mul_add,Nat.add_comm]
/-- The source bank exchange emits 256 explicit three-CNOT swaps. -/
theorem fig15SwapOutput_primitive : primitiveResources (.unitary fig15SwapOutput .done)=
    (⟨0,0,768,0,0,0⟩ : PrimitiveResources) := by
  rw [fig15SwapOutput,swapOutputList_primitive,List.length_range]
private theorem fig15DivisionAfterReset_primitive_sum (a : PrimitiveResources) (ha : a.x≤19492961 ∧ a.h≤10562768 ∧ a.cnot≤29743147 ∧ a.toffoli≤17591751 ∧ a.phase=0 ∧ a.measurements≤5280108) (b : PrimitiveResources) (hb : b.x≤2877699 ∧ b.h≤1044484 ∧ b.cnot≤4636432 ∧ b.toffoli≤1110533 ∧ b.phase=0 ∧ b.measurements≤261121) (c : PrimitiveResources) (hc : c.x≤2877699 ∧ c.h≤1044484 ∧ c.cnot≤4636432 ∧ c.toffoli≤1110533 ∧ c.phase=0 ∧ c.measurements≤261121) (n : Nat) (hn : n≤256) :
    let v := (((a.add b).add (⟨n,2*n,0,0,0,0⟩ : PrimitiveResources)).add c).add (⟨0,0,768,0,0,0⟩ : PrimitiveResources)
    v.x≤25248615 ∧ v.h≤12652248 ∧ v.cnot≤39016779 ∧ v.toffoli≤19812817 ∧ v.phase=0 ∧ v.measurements≤5802350 := by
  dsimp only [PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
/-- Every 256-bit reset history is included in the continuation budget. -/
theorem fig15DivisionAfterReset_primitive_bounds (bs : List Bool) (hb : bs.length=256) :
    let v := primitiveResources (fig15DivisionAfterReset bs)
    v.x≤25248615 ∧ v.h≤12652248 ∧ v.cnot≤39016779 ∧ v.toffoli≤19812817 ∧ v.phase=0 ∧ v.measurements≤5802350 := by
  have hv : primitiveResources (fig15DivisionAfterReset bs)=((((primitiveResources secp256k1EEAReverseInDataBank).add (primitiveResources fig15MultiplyToData)).add (⟨bs.count true,2*bs.count true,0,0,0,0⟩ : PrimitiveResources)).add (primitiveResources fig15MultiplyToDataInverse)).add (⟨0,0,768,0,0,0⟩ : PrimitiveResources) := by
    simp only [fig15DivisionAfterReset,primitiveResources_seq,registerZCorrection_primitive (List.range' 580 256) bs (by simpa using hb.symm),fig15SwapOutput_primitive]
  rw [hv]
  exact fig15DivisionAfterReset_primitive_sum _ secp256k1EEAReverseInDataBank_primitive_bounds _ fig15MultiplyToData_primitive_bounds _ fig15MultiplyToDataInverse_primitive_bounds _ (by have hh : bs.count true≤bs.length := List.count_le_length; omega)
private theorem fig15MultiplicationAfterReset_primitive_sum (a : PrimitiveResources) (ha : a.x≤19441121 ∧ a.h≤10562768 ∧ a.cnot≤29743147 ∧ a.toffoli≤17591751 ∧ a.phase=0 ∧ a.measurements≤5280108) (b : PrimitiveResources) (hb : b.x≤2877699 ∧ b.h≤1044484 ∧ b.cnot≤4636432 ∧ b.toffoli≤1110533 ∧ b.phase=0 ∧ b.measurements≤261121) (c : PrimitiveResources) (hc : c.x≤2877699 ∧ c.h≤1044484 ∧ c.cnot≤4636432 ∧ c.toffoli≤1110533 ∧ c.phase=0 ∧ c.measurements≤261121) (d : PrimitiveResources) (hd : d.x≤19492961 ∧ d.h≤10562768 ∧ d.cnot≤29743147 ∧ d.toffoli≤17591751 ∧ d.phase=0 ∧ d.measurements≤5280108) (n : Nat) (hn : n≤256) :
    let v := ((((a.add b).add (⟨n,2*n,0,0,0,0⟩ : PrimitiveResources)).add c).add d).add (⟨0,0,768,0,0,0⟩ : PrimitiveResources)
    v.x≤44689736 ∧ v.h≤23215016 ∧ v.cnot≤68759926 ∧ v.toffoli≤37404568 ∧ v.phase=0 ∧ v.measurements≤11082458 := by
  dsimp only [PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
/-- Every 256-bit reset history is included in the continuation budget. -/
theorem fig15MultiplicationAfterReset_primitive_bounds (bs : List Bool) (hb : bs.length=256) :
    let v := primitiveResources (fig15MultiplicationAfterReset bs)
    v.x≤44689736 ∧ v.h≤23215016 ∧ v.cnot≤68759926 ∧ v.toffoli≤37404568 ∧ v.phase=0 ∧ v.measurements≤11082458 := by
  have hv : primitiveResources (fig15MultiplicationAfterReset bs)=(((((primitiveResources secp256k1EEAForwardInDataBank).add (primitiveResources fig15MultiplyToData)).add (⟨bs.count true,2*bs.count true,0,0,0,0⟩ : PrimitiveResources)).add (primitiveResources fig15MultiplyToDataInverse)).add (primitiveResources secp256k1EEAReverseInDataBank)).add (⟨0,0,768,0,0,0⟩ : PrimitiveResources) := by
    simp only [fig15MultiplicationAfterReset,primitiveResources_seq,registerZCorrection_primitive (List.range' 580 256) bs (by simpa using hb.symm),fig15SwapOutput_primitive]
  rw [hv]
  exact fig15MultiplicationAfterReset_primitive_sum _ secp256k1EEAForwardInDataBank_primitive_bounds _ fig15MultiplyToData_primitive_bounds _ fig15MultiplyToDataInverse_primitive_bounds _ secp256k1EEAReverseInDataBank_primitive_bounds _ (by have hh : bs.count true≤bs.length := List.count_le_length; omega)
private theorem fig15DivisionReset_primitive_bounds :
    let v := primitiveResources (measureResetThen (List.range' 580 256) fig15DivisionAfterReset)
    v.x≤25248615 ∧ v.h≤12652248 ∧ v.cnot≤39016779 ∧ v.toffoli≤19812817 ∧ v.phase=0 ∧ v.measurements≤5802606 := by
  have hh := measureResetThen_primitive_bounds (List.range' 580 256) fig15DivisionAfterReset
    (⟨25248615,12652248,39016779,19812817,0,5802350⟩ : PrimitiveResources) (fun bs hb => fig15DivisionAfterReset_primitive_bounds bs (by simpa using hb))
  simpa only [List.length_range'] using hh
private theorem fig15Division_primitive_sum (a : PrimitiveResources) (ha : a.x≤19441121 ∧ a.h≤10562768 ∧ a.cnot≤29743147 ∧ a.toffoli≤17591751 ∧ a.phase=0 ∧ a.measurements≤5280108) (b : PrimitiveResources) (hb : b.x≤2877699 ∧ b.h≤1044484 ∧ b.cnot≤4636432 ∧ b.toffoli≤1110533 ∧ b.phase=0 ∧ b.measurements≤261121) (c : PrimitiveResources) (hc : c.x≤25248615 ∧ c.h≤12652248 ∧ c.cnot≤39016779 ∧ c.toffoli≤19812817 ∧ c.phase=0 ∧ c.measurements≤5802606) :
    let v := (a.add b).add c
    v.x≤47567435 ∧ v.h≤24259500 ∧ v.cnot≤73396358 ∧ v.toffoli≤38515101 ∧ v.phase=0 ∧ v.measurements≤11343835 := by
  dsimp only [PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
/-- Complete Figure 15 budget includes all reset histories and H-X-H corrections. -/
theorem secp256k1InPlaceDivision_primitive_bounds :
    let v := primitiveResources secp256k1InPlaceDivision
    v.x≤47567435 ∧ v.h≤24259500 ∧ v.cnot≤73396358 ∧ v.toffoli≤38515101 ∧ v.phase=0 ∧ v.measurements≤11343835 := by
  rw [secp256k1InPlaceDivision]
  simp only [primitiveResources_seq]
  exact fig15Division_primitive_sum _ secp256k1EEAForwardWrapper_primitive_bounds _ fig15MultiplyToWork_primitive_bounds _ fig15DivisionReset_primitive_bounds
private theorem fig15MultiplicationReset_primitive_bounds :
    let v := primitiveResources (measureResetThen (List.range' 580 256) fig15MultiplicationAfterReset)
    v.x≤44689736 ∧ v.h≤23215016 ∧ v.cnot≤68759926 ∧ v.toffoli≤37404568 ∧ v.phase=0 ∧ v.measurements≤11082714 := by
  have hh := measureResetThen_primitive_bounds (List.range' 580 256) fig15MultiplicationAfterReset
    (⟨44689736,23215016,68759926,37404568,0,11082458⟩ : PrimitiveResources) (fun bs hb => fig15MultiplicationAfterReset_primitive_bounds bs (by simpa using hb))
  simpa only [List.length_range'] using hh
private theorem fig15Multiplication_primitive_sum (a : PrimitiveResources) (ha : a.x≤2877699 ∧ a.h≤1044484 ∧ a.cnot≤4636432 ∧ a.toffoli≤1110533 ∧ a.phase=0 ∧ a.measurements≤261121) (b : PrimitiveResources) (hb : b.x≤44689736 ∧ b.h≤23215016 ∧ b.cnot≤68759926 ∧ b.toffoli≤37404568 ∧ b.phase=0 ∧ b.measurements≤11082714) :
    let v := a.add b
    v.x≤47567435 ∧ v.h≤24259500 ∧ v.cnot≤73396358 ∧ v.toffoli≤38515101 ∧ v.phase=0 ∧ v.measurements≤11343835 := by
  dsimp only [PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
/-- Complete Figure 15 budget includes all reset histories and H-X-H corrections. -/
theorem secp256k1InPlaceMultiplication_primitive_bounds :
    let v := primitiveResources secp256k1InPlaceMultiplication
    v.x≤47567435 ∧ v.h≤24259500 ∧ v.cnot≤73396358 ∧ v.toffoli≤38515101 ∧ v.phase=0 ∧ v.measurements≤11343835 := by
  rw [secp256k1InPlaceMultiplication]
  simp only [primitiveResources_seq]
  exact fig15Multiplication_primitive_sum _ fig15MultiplyToWork_primitive_bounds _ fig15MultiplicationReset_primitive_bounds
end ShorECDLP.Paper2607_13816
