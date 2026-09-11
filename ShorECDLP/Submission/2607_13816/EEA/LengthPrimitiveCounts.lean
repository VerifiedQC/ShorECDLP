import ShorECDLP.Submission.«2607_13816».EEA.Preprocess
import ShorECDLP.Submission.«2607_13816».EEA.LengthInitialize
import ShorECDLP.Submission.«2607_13816».EEA.ControlPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.EndIteration
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Reversible known-workspace clearing adds only the two explicit constant masks. -/
theorem knownScratchControl_primitive (controls : List Wire) (pattern : Nat) (target : Wire)
    (scratch : List Wire) (known : Nat) (hs : controls.length-2≤scratch.length) :
    primitiveResources (.unitary (knownScratchControl controls pattern target scratch known) .done)=
      (⟨2*zeroBitCount pattern 0 controls.length+(if controls.length=0 then 1 else 0)+
          2*(constantBits scratch.length known).count true,0,
        mcxVChainCnotCost controls.length,mcxVChainToffoliCost controls.length,0,0⟩ : PrimitiveResources) := by
  have hx : primitiveResources (.unitary (xorConstant scratch known) .done)=
      (⟨(constantBits scratch.length known).count true,0,0,0,0,0⟩ : PrimitiveResources) := by
    rw [primitiveResources_unitary_HPFree _ _ (xorConstant_HPFree _ _),
      xorConstant_xCount,xorConstant_cnotCount,xorConstant_toffoliCount]
    rfl
  have hc := computeControl_primitive controls pattern target scratch hs
  simp only [computeControl,primitiveResources_unitary_append,primitiveResources_unitary_adjoint] at hc
  simp only [knownScratchControl,knownScratchMCX,primitiveResources_unitary_append,
    primitiveResources_unitary_adjoint,hx]
  have regroup (a b : PrimitiveResources) (x : Nat) :
      (a.add (((⟨x,0,0,0,0,0⟩ : PrimitiveResources).add b).add ⟨x,0,0,0,0,0⟩)).add a=
        ((a.add b).add a).add ⟨2*x,0,0,0,0,0⟩ := by
    cases a; cases b
    simp only [PrimitiveResources.add]
    congr 1 <;> omega
  rw [regroup,hc]
  rfl
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum
private theorem controlledXorConstant_primitive (control : Wire) (targets : List Wire) (value : Nat) :
    primitiveResources (.unitary (controlledXorConstant control targets value) .done)=
      (⟨0,0,lowBitCount targets.length value,0,0,0⟩ : PrimitiveResources) := by
  rw [primitiveResources_unitary_HPFree _ _ (controlledXorConstant_HPFree _ _ _),
    controlledXorConstant_xCount,controlledXorConstant_cnotCount,
    controlledXorConstant_toffoliCount]
  rfl
/-- Primitive cost of each emitted first-one row, including both borrowed-workspace masks. -/
def lengthInitializeCasePrimitive (width scratchWidth known : Nat) (row : List Wire × Nat × Nat) : PrimitiveResources :=
  ⟨4*zeroBitCount row.2.1 0 row.1.length+2*(if row.1.length=0 then 1 else 0)+
      4*(constantBits scratchWidth known).count true,0,
    2*mcxVChainCnotCost row.1.length+lowBitCount width row.2.2,
    2*mcxVChainToffoliCost row.1.length,0,0⟩
theorem lengthInitializeCase_primitive (controls : List Wire) (pattern : Nat) (targets : List Wire)
    (encoded : Nat) (flag : Wire) (scratch : List Wire) (known : Nat)
    (hs : controls.length-2≤scratch.length) :
    primitiveResources (.unitary (lengthInitializeCase controls pattern targets encoded flag scratch known) .done)=
      lengthInitializeCasePrimitive targets.length scratch.length known (controls,pattern,encoded) := by
  simp only [lengthInitializeCase,primitiveResources_unitary_append,
    knownScratchControl_primitive _ _ _ _ _ hs,controlledXorConstant_primitive,
    lengthInitializeCasePrimitive,PrimitiveResources.add]
  congr 1 <;> omega
/-- Scalar row accumulation follows the same concrete first-one scan. -/
theorem lengthInitializeScan_primitive (targets : List Wire) (flag : Wire) (scratch : List Wire)
    (known : Nat) (rows : List (List Wire × Nat × Nat))
    (hs : ∀ row ∈ rows, row.1.length-2≤scratch.length) :
    primitiveResources (.unitary (lengthInitializeScan targets flag scratch known rows) .done)=
      (rows.map (lengthInitializeCasePrimitive targets.length scratch.length known)).foldr
        PrimitiveResources.add ⟨0,0,0,0,0,0⟩ := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    rw [lengthInitializeScan,primitiveResources_unitary_append,
      lengthInitializeCase_primitive _ _ _ _ _ _ _ (hs row (by simp)),
      ih (by intro r hr; exact hs r (by simp [hr]))]
    rfl
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- The complete scalar vector follows the same first-one table. -/
theorem lengthInitialize_primitive (input targets : List Wire) (flag : Wire) (scratch : List Wire)
    (known : Nat) (hs : input.length-2≤scratch.length) :
    primitiveResources (.unitary (lengthInitialize input targets flag scratch known) .done)=
      ((lengthInitializeCases input targets.length).map
        (lengthInitializeCasePrimitive targets.length scratch.length known)).foldr
          PrimitiveResources.add ⟨0,0,0,0,0,0⟩ := by
  apply lengthInitializeScan_primitive
  intro row hr
  simp only [lengthInitializeCases,List.mem_append,List.mem_map,List.mem_singleton] at hr
  rcases hr with ⟨first,_,rfl⟩ | rfl
  · simp only [List.length_take]; omega
  · exact hs
/-- Numeric vector of the actual production length scan, including known-workspace masks. -/
theorem eeaLengthScan_primitive :
    primitiveResources (.unitary (lengthInitialize (List.range' 266 256) (List.range' 549 9) 558
      ((List.range' 7 256).reverse.take 254) (2^256-2^32-977)) .done)=
      (⟨386528,0,1035,131068,0,0⟩ : PrimitiveResources) := by
  rw [lengthInitialize_primitive _ _ _ _ _ (by simp)]
  decide +kernel
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum
private theorem lengthWordSet_primitive (start : Nat) :
    primitiveResources (.unitary (xorConstant (List.range' start 9) 511) .done)=
      (⟨9,0,0,0,0,0⟩ : PrimitiveResources) := by
  rw [primitiveResources_unitary_HPFree _ _ (xorConstant_HPFree _ _),
    xorConstant_xCount,xorConstant_cnotCount,xorConstant_toffoliCount]
  simp only [List.length_range']
  rfl
/-- Length preprocessing includes both all-one counter words and the complete scan. -/
theorem eeaLengthSetup_primitive : primitiveResources (.unitary eeaLengthSetup .done)=
    (⟨386546,0,1035,131068,0,0⟩ : PrimitiveResources) := by
  simp only [eeaLengthSetup,primitiveResources_unitary_append,lengthWordSet_primitive,eeaLengthScan_primitive]
  rfl
/-- Source reverse initialization emits the same scan and two word masks in reverse order. -/
theorem eeaLengthUndo_primitive : primitiveResources (.unitary eeaLengthUndo .done)=
    (⟨386546,0,1035,131068,0,0⟩ : PrimitiveResources) := by
  simp only [eeaLengthUndo,primitiveResources_unitary_append,lengthWordSet_primitive,eeaLengthScan_primitive]
  rfl
end ShorECDLP.Paper2607_13816
