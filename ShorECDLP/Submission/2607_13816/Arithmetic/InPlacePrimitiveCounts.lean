import ShorECDLP.Submission.«2607_13816».EEA.MeasuredPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.InPlace
import ShorECDLP.Submission.«2607_13816».Arithmetic.AdaptivePrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.WrapperPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.LoopPrimitiveCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
attribute [local irreducible] primitiveResources secp256k1MeasuredEEAForwardWrapper secp256k1MeasuredEEAReverseWrapper
  secp256k1MeasuredEEAForwardInDataBank secp256k1MeasuredEEAReverseInDataBank fig15MultiplyToWork fig15MultiplyToData
  fig15MultiplyToDataInverse fig15DivisionAfterReset fig15MultiplicationAfterReset
  secp256k1InPlaceDivision secp256k1InPlaceMultiplication
/-- Borrowing the data bank only relabels the complete forward wrapper. -/
theorem secp256k1MeasuredEEAForwardInDataBank_primitive_bounds :
    let v := primitiveResources secp256k1MeasuredEEAForwardInDataBank
    v.x≤19441121 ∧ v.h≤13926240 ∧ v.cnot≤31424883 ∧ v.toffoli≤15910015 ∧
      v.phase=0 ∧ v.measurements≤6961844 := by
  rw [secp256k1MeasuredEEAForwardInDataBank,primitiveResources_relabel]
  exact secp256k1MeasuredEEAForwardWrapper_primitive_bounds
/-- The explicit reverse wrapper has identical counts after the bank exchange. -/
theorem secp256k1MeasuredEEAReverseInDataBank_primitive_bounds :
    let v := primitiveResources secp256k1MeasuredEEAReverseInDataBank
    v.x≤19492961 ∧ v.h≤13926240 ∧ v.cnot≤31424883 ∧ v.toffoli≤15910015 ∧
      v.phase=0 ∧ v.measurements≤6961844 := by
  rw [secp256k1MeasuredEEAReverseInDataBank,primitiveResources_relabel]
  exact secp256k1MeasuredEEAReverseWrapper_primitive_bounds
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
private theorem fig15DivisionAfterReset_primitive_sum (a : PrimitiveResources) (ha : a.x≤19492961 ∧ a.h≤13926240 ∧ a.cnot≤31424883 ∧ a.toffoli≤15910015 ∧ a.phase=0 ∧ a.measurements≤6961844) (b : PrimitiveResources) (hb : b.x≤2877699 ∧ b.h≤1044484 ∧ b.cnot≤4636432 ∧ b.toffoli≤1110533 ∧ b.phase=0 ∧ b.measurements≤261121) (c : PrimitiveResources) (hc : c.x≤2877699 ∧ c.h≤1044484 ∧ c.cnot≤4636432 ∧ c.toffoli≤1110533 ∧ c.phase=0 ∧ c.measurements≤261121) (n : Nat) (hn : n≤256) :
    let v := (((a.add b).add (⟨n,2*n,0,0,0,0⟩ : PrimitiveResources)).add c).add (⟨0,0,768,0,0,0⟩ : PrimitiveResources)
    v.x≤25248615 ∧ v.h≤16015720 ∧ v.cnot≤40698515 ∧ v.toffoli≤18131081 ∧ v.phase=0 ∧ v.measurements≤7484086 := by
  dsimp only [PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
/-- Every 256-bit reset history is included in the continuation budget. -/
theorem fig15DivisionAfterReset_primitive_bounds (bs : List Bool) (hb : bs.length=256) :
    let v := primitiveResources (fig15DivisionAfterReset bs)
    v.x≤25248615 ∧ v.h≤16015720 ∧ v.cnot≤40698515 ∧ v.toffoli≤18131081 ∧ v.phase=0 ∧ v.measurements≤7484086 := by
  have hv : primitiveResources (fig15DivisionAfterReset bs)=((((primitiveResources secp256k1MeasuredEEAReverseInDataBank).add (primitiveResources fig15MultiplyToData)).add (⟨bs.count true,2*bs.count true,0,0,0,0⟩ : PrimitiveResources)).add (primitiveResources fig15MultiplyToDataInverse)).add (⟨0,0,768,0,0,0⟩ : PrimitiveResources) := by
    simp only [fig15DivisionAfterReset,primitiveResources_seq,registerZCorrection_primitive (List.range' 580 256) bs (by simpa using hb.symm),fig15SwapOutput_primitive]
  rw [hv]
  exact fig15DivisionAfterReset_primitive_sum _ secp256k1MeasuredEEAReverseInDataBank_primitive_bounds _ fig15MultiplyToData_primitive_bounds _ fig15MultiplyToDataInverse_primitive_bounds _ (by have hh : bs.count true≤bs.length := List.count_le_length; omega)
private theorem fig15MultiplicationAfterReset_primitive_sum (a : PrimitiveResources) (ha : a.x≤19441121 ∧ a.h≤13926240 ∧ a.cnot≤31424883 ∧ a.toffoli≤15910015 ∧ a.phase=0 ∧ a.measurements≤6961844) (b : PrimitiveResources) (hb : b.x≤2877699 ∧ b.h≤1044484 ∧ b.cnot≤4636432 ∧ b.toffoli≤1110533 ∧ b.phase=0 ∧ b.measurements≤261121) (c : PrimitiveResources) (hc : c.x≤2877699 ∧ c.h≤1044484 ∧ c.cnot≤4636432 ∧ c.toffoli≤1110533 ∧ c.phase=0 ∧ c.measurements≤261121) (d : PrimitiveResources) (hd : d.x≤19492961 ∧ d.h≤13926240 ∧ d.cnot≤31424883 ∧ d.toffoli≤15910015 ∧ d.phase=0 ∧ d.measurements≤6961844) (n : Nat) (hn : n≤256) :
    let v := ((((a.add b).add (⟨n,2*n,0,0,0,0⟩ : PrimitiveResources)).add c).add d).add (⟨0,0,768,0,0,0⟩ : PrimitiveResources)
    v.x≤44689736 ∧ v.h≤29941960 ∧ v.cnot≤72123398 ∧ v.toffoli≤34041096 ∧ v.phase=0 ∧ v.measurements≤14445930 := by
  dsimp only [PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
/-- Every 256-bit reset history is included in the continuation budget. -/
theorem fig15MultiplicationAfterReset_primitive_bounds (bs : List Bool) (hb : bs.length=256) :
    let v := primitiveResources (fig15MultiplicationAfterReset bs)
    v.x≤44689736 ∧ v.h≤29941960 ∧ v.cnot≤72123398 ∧ v.toffoli≤34041096 ∧ v.phase=0 ∧ v.measurements≤14445930 := by
  have hv : primitiveResources (fig15MultiplicationAfterReset bs)=(((((primitiveResources secp256k1MeasuredEEAForwardInDataBank).add (primitiveResources fig15MultiplyToData)).add (⟨bs.count true,2*bs.count true,0,0,0,0⟩ : PrimitiveResources)).add (primitiveResources fig15MultiplyToDataInverse)).add (primitiveResources secp256k1MeasuredEEAReverseInDataBank)).add (⟨0,0,768,0,0,0⟩ : PrimitiveResources) := by
    simp only [fig15MultiplicationAfterReset,primitiveResources_seq,registerZCorrection_primitive (List.range' 580 256) bs (by simpa using hb.symm),fig15SwapOutput_primitive]
  rw [hv]
  exact fig15MultiplicationAfterReset_primitive_sum _ secp256k1MeasuredEEAForwardInDataBank_primitive_bounds _ fig15MultiplyToData_primitive_bounds _ fig15MultiplyToDataInverse_primitive_bounds _ secp256k1MeasuredEEAReverseInDataBank_primitive_bounds _ (by have hh : bs.count true≤bs.length := List.count_le_length; omega)
private theorem fig15DivisionReset_primitive_bounds :
    let v := primitiveResources (measureResetThen (List.range' 580 256) fig15DivisionAfterReset)
    v.x≤25248615 ∧ v.h≤16015720 ∧ v.cnot≤40698515 ∧ v.toffoli≤18131081 ∧ v.phase=0 ∧ v.measurements≤7484342 := by
  have hh := measureResetThen_primitive_bounds (List.range' 580 256) fig15DivisionAfterReset
    (⟨25248615,16015720,40698515,18131081,0,7484086⟩ : PrimitiveResources) (fun bs hb => fig15DivisionAfterReset_primitive_bounds bs (by simpa using hb))
  simpa only [List.length_range'] using hh
private theorem fig15Division_primitive_sum (a : PrimitiveResources) (ha : a.x≤19441121 ∧ a.h≤13926240 ∧ a.cnot≤31424883 ∧ a.toffoli≤15910015 ∧ a.phase=0 ∧ a.measurements≤6961844) (b : PrimitiveResources) (hb : b.x≤2877699 ∧ b.h≤1044484 ∧ b.cnot≤4636432 ∧ b.toffoli≤1110533 ∧ b.phase=0 ∧ b.measurements≤261121) (c : PrimitiveResources) (hc : c.x≤25248615 ∧ c.h≤16015720 ∧ c.cnot≤40698515 ∧ c.toffoli≤18131081 ∧ c.phase=0 ∧ c.measurements≤7484342) :
    let v := (a.add b).add c
    v.x≤47567435 ∧ v.h≤30986444 ∧ v.cnot≤76759830 ∧ v.toffoli≤35151629 ∧ v.phase=0 ∧ v.measurements≤14707307 := by
  dsimp only [PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
/-- Complete Figure 15 budget includes all reset histories and H-X-H corrections. -/
theorem secp256k1InPlaceDivision_primitive_bounds :
    let v := primitiveResources secp256k1InPlaceDivision
    v.x≤47567435 ∧ v.h≤30986444 ∧ v.cnot≤76759830 ∧ v.toffoli≤35151629 ∧ v.phase=0 ∧ v.measurements≤14707307 := by
  rw [secp256k1InPlaceDivision]
  simp only [primitiveResources_seq]
  exact fig15Division_primitive_sum _ secp256k1MeasuredEEAForwardWrapper_primitive_bounds _ fig15MultiplyToWork_primitive_bounds _ fig15DivisionReset_primitive_bounds
private theorem fig15MultiplicationReset_primitive_bounds :
    let v := primitiveResources (measureResetThen (List.range' 580 256) fig15MultiplicationAfterReset)
    v.x≤44689736 ∧ v.h≤29941960 ∧ v.cnot≤72123398 ∧ v.toffoli≤34041096 ∧ v.phase=0 ∧ v.measurements≤14446186 := by
  have hh := measureResetThen_primitive_bounds (List.range' 580 256) fig15MultiplicationAfterReset
    (⟨44689736,29941960,72123398,34041096,0,14445930⟩ : PrimitiveResources) (fun bs hb => fig15MultiplicationAfterReset_primitive_bounds bs (by simpa using hb))
  simpa only [List.length_range'] using hh
private theorem fig15Multiplication_primitive_sum (a : PrimitiveResources) (ha : a.x≤2877699 ∧ a.h≤1044484 ∧ a.cnot≤4636432 ∧ a.toffoli≤1110533 ∧ a.phase=0 ∧ a.measurements≤261121) (b : PrimitiveResources) (hb : b.x≤44689736 ∧ b.h≤29941960 ∧ b.cnot≤72123398 ∧ b.toffoli≤34041096 ∧ b.phase=0 ∧ b.measurements≤14446186) :
    let v := a.add b
    v.x≤47567435 ∧ v.h≤30986444 ∧ v.cnot≤76759830 ∧ v.toffoli≤35151629 ∧ v.phase=0 ∧ v.measurements≤14707307 := by
  dsimp only [PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
/-- Complete Figure 15 budget includes all reset histories and H-X-H corrections. -/
theorem secp256k1InPlaceMultiplication_primitive_bounds :
    let v := primitiveResources secp256k1InPlaceMultiplication
    v.x≤47567435 ∧ v.h≤30986444 ∧ v.cnot≤76759830 ∧ v.toffoli≤35151629 ∧ v.phase=0 ∧ v.measurements≤14707307 := by
  rw [secp256k1InPlaceMultiplication]
  simp only [primitiveResources_seq]
  exact fig15Multiplication_primitive_sum _ fig15MultiplyToWork_primitive_bounds _ fig15MultiplicationReset_primitive_bounds
end ShorECDLP.Paper2607_13816

namespace ShorECDLP.Paper2607_13816
open Quantum
/-- A linear per-outcome continuation attains its componentwise maximum at all true. -/
private theorem measureResetThen_primitive_linear (targets : List Wire)
    (next : List Bool → Quantum.AdaptiveCircuit) (base delta : PrimitiveResources)
    (h : ∀ bs, bs.length=targets.length → primitiveResources (next bs)=
      base.add (delta.scale (bs.count true))) :
    primitiveResources (measureResetThen targets next)=
      (base.add (delta.scale targets.length)).add ⟨0,0,0,0,0,targets.length⟩ := by
  induction targets generalizing next base with
  | nil =>
    simpa only [measureResetThen,List.length_nil,List.count_nil,PrimitiveResources.add,
      PrimitiveResources.scale,Nat.zero_mul,Nat.add_zero] using h [] rfl
  | cons w ws ih =>
    have h0 : ∀ bs, bs.length=ws.length → primitiveResources (next (false::bs))=
        base.add (delta.scale (bs.count true)) := by
      intro bs hb
      simpa only [List.count_cons] using h (false::bs) (by simp [hb])
    have h1 : ∀ bs, bs.length=ws.length → primitiveResources (next (true::bs))=
        (base.add delta).add (delta.scale (bs.count true)) := by
      intro bs hb
      rw [h (true::bs) (by simp [hb])]
      simp only [List.count_cons]
      change base.add (delta.scale (bs.count true+1))=(base.add delta).add (delta.scale (bs.count true))
      simp only [PrimitiveResources.scale,PrimitiveResources.add,
        PrimitiveResources.mk.injEq,Nat.add_mul,Nat.one_mul]
      omega
    have a := ih (fun bs => next (false::bs)) base h0
    have b := ih (fun bs => next (true::bs)) (base.add delta) h1
    rw [measureResetThen,primitiveResources_branch,a,b]
    simp only [PrimitiveResources.branch,PrimitiveResources.scale,PrimitiveResources.add,
      List.length_cons,PrimitiveResources.mk.injEq,Nat.add_mul,Nat.one_mul]
    omega
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum
attribute [local irreducible] primitiveResources hornerMulInverse
/-- Relabeling the forward EEA wrapper preserves its exact vector. -/
theorem secp256k1MeasuredEEAForwardInDataBank_primitive_exact : primitiveResources secp256k1MeasuredEEAForwardInDataBank=
    (⟨19437345,13926240,31417379,15910015,0,6961844⟩ : PrimitiveResources) := by
  rw [secp256k1MeasuredEEAForwardInDataBank,primitiveResources_relabel,secp256k1MeasuredEEAForwardWrapper_primitive_exact]
/-- Relabeling the independently compiled reverse wrapper preserves its exact vector. -/
theorem secp256k1MeasuredEEAReverseInDataBank_primitive_exact : primitiveResources secp256k1MeasuredEEAReverseInDataBank=
    (⟨19489185,13926240,31417379,15910015,0,6961844⟩ : PrimitiveResources) := by
  rw [secp256k1MeasuredEEAReverseInDataBank,primitiveResources_relabel,secp256k1MeasuredEEAReverseWrapper_primitive_exact]
theorem fig15MultiplyToWork_primitive_exact : primitiveResources fig15MultiplyToWork=
    (⟨947141,1044484,2192319,1110533,0,261121⟩ : PrimitiveResources) := by
  rw [fig15MultiplyToWork]
  apply hornerMul256_secp_primitive_exact <;> simp
theorem fig15MultiplyToData_primitive_exact : primitiveResources fig15MultiplyToData=
    (⟨947141,1044484,2192319,1110533,0,261121⟩ : PrimitiveResources) := by
  rw [fig15MultiplyToData]
  apply hornerMul256_secp_primitive_exact <;> simp
theorem fig15MultiplyToDataInverse_primitive_exact : primitiveResources fig15MultiplyToDataInverse=
    (⟨947141,1044484,3429450,1110533,0,261121⟩ : PrimitiveResources) := by
  unfold fig15MultiplyToDataInverse
  have bits : constantBits 256 ShorECDLP.p = secp256k1ModulusBits := by decide +kernel
  rw [bits]
  apply hornerMulInverse256_secp_primitive_exact <;> simp
/-- Exact continuation count keeps the selected Z corrections visible. -/
theorem fig15DivisionAfterReset_primitive_exact (bs : List Bool) (hb : bs.length=256) :
    primitiveResources (fig15DivisionAfterReset bs)=
      (⟨21383467+bs.count true,16015208+2*bs.count true,37039916,18131081,0,7484086⟩ : PrimitiveResources) := by
  simp only [fig15DivisionAfterReset,primitiveResources_seq,
    registerZCorrection_primitive (List.range' 580 256) bs (by simpa using hb.symm),
    fig15SwapOutput_primitive,secp256k1MeasuredEEAReverseInDataBank_primitive_exact,
    fig15MultiplyToData_primitive_exact,fig15MultiplyToDataInverse_primitive_exact,
    PrimitiveResources.add,PrimitiveResources.mk.injEq]
  simp [Nat.add_comm, Nat.add_left_comm]
/-- Exact multiplication continuation counts both EEA directions and the selected corrections. -/
theorem fig15MultiplicationAfterReset_primitive_exact (bs : List Bool) (hb : bs.length=256) :
    primitiveResources (fig15MultiplicationAfterReset bs)=
      (⟨40820812+bs.count true,29941448+2*bs.count true,68457295,34041096,0,14445930⟩ : PrimitiveResources) := by
  simp only [fig15MultiplicationAfterReset,primitiveResources_seq,
    registerZCorrection_primitive (List.range' 580 256) bs (by simpa using hb.symm),
    fig15SwapOutput_primitive,secp256k1MeasuredEEAForwardInDataBank_primitive_exact,
    secp256k1MeasuredEEAReverseInDataBank_primitive_exact,fig15MultiplyToData_primitive_exact,
    fig15MultiplyToDataInverse_primitive_exact,PrimitiveResources.add,PrimitiveResources.mk.injEq]
  simp [Nat.add_comm, Nat.add_left_comm]
private theorem fig15DivisionReset_primitive_exact :
    primitiveResources (measureResetThen (List.range' 580 256) fig15DivisionAfterReset)=
      (⟨21383723,16015720,37039916,18131081,0,7484342⟩ : PrimitiveResources) := by
  have hh := measureResetThen_primitive_linear (List.range' 580 256) fig15DivisionAfterReset
    ⟨21383467,16015208,37039916,18131081,0,7484086⟩ ⟨1,2,0,0,0,0⟩ (by
      intro bs hb
      rw [fig15DivisionAfterReset_primitive_exact bs (by simpa using hb)]
      simp [PrimitiveResources.scale,PrimitiveResources.add,Nat.mul_comm])
  simpa only [List.length_range'] using hh
private theorem fig15MultiplicationReset_primitive_exact :
    primitiveResources (measureResetThen (List.range' 580 256) fig15MultiplicationAfterReset)=
      (⟨40821068,29941960,68457295,34041096,0,14446186⟩ : PrimitiveResources) := by
  have hh := measureResetThen_primitive_linear (List.range' 580 256) fig15MultiplicationAfterReset
    ⟨40820812,29941448,68457295,34041096,0,14445930⟩ ⟨1,2,0,0,0,0⟩ (by
      intro bs hb
      rw [fig15MultiplicationAfterReset_primitive_exact bs (by simpa using hb)]
      simp [PrimitiveResources.scale,PrimitiveResources.add,Nat.mul_comm])
  simpa only [List.length_range'] using hh
/-- Complete exact Figure 15 division vector, including the worst reset history. -/
theorem secp256k1InPlaceDivision_primitive_exact : primitiveResources secp256k1InPlaceDivision=
    (⟨41768209,30986444,70649614,35151629,0,14707307⟩ : PrimitiveResources) := by
  rw [secp256k1InPlaceDivision]
  simp only [primitiveResources_seq,secp256k1MeasuredEEAForwardWrapper_primitive_exact,
    fig15MultiplyToWork_primitive_exact,fig15DivisionReset_primitive_exact]
  rfl
/-- Complete exact Figure 15 multiplication vector on the same physical program. -/
theorem secp256k1InPlaceMultiplication_primitive_exact : primitiveResources secp256k1InPlaceMultiplication=
    (⟨41768209,30986444,70649614,35151629,0,14707307⟩ : PrimitiveResources) := by
  rw [secp256k1InPlaceMultiplication]
  simp only [primitiveResources_seq,fig15MultiplyToWork_primitive_exact,
    fig15MultiplicationReset_primitive_exact]
  rfl
end ShorECDLP.Paper2607_13816
