import ShorECDLP.Submission.«2607_13816».Arithmetic.UnitaryPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.AdaptiveWrapper
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Primitive vector of the actual fixed workRegistersPrepare gate stream. -/
theorem workRegistersPrepare_primitive :
    primitiveResources (.unitary workRegistersPrepare .done)=
      (⟨251,0,390,0,0,0⟩ : PrimitiveResources) := by
  have h := workRegistersPrepare_resources
  have hx : eeaXCount workRegistersPrepare=251 := by decide +kernel
  rw [primitiveResources_unitary_HPFree _ _ h.2.1,h.2.2.1,h.2.2.2.1,hx]
  rfl
/-- Primitive vector of the actual fixed workRegistersRestore gate stream. -/
theorem workRegistersRestore_primitive :
    primitiveResources (.unitary workRegistersRestore .done)=
      (⟨251,0,390,0,0,0⟩ : PrimitiveResources) := by
  have h := workRegistersRestore_resources
  have hx : eeaXCount workRegistersRestore=251 := by decide +kernel
  rw [primitiveResources_unitary_HPFree _ _ h.2.1,h.2.2.1,h.2.2.2.1,hx]
  rfl
/-- Primitive vector of the actual fixed canonicalWork2Rotation gate stream. -/
theorem canonicalWork2Rotation_primitive :
    primitiveResources (.unitary canonicalWork2Rotation .done)=
      (⟨6,0,5240,2620,0,0⟩ : PrimitiveResources) := by
  have h := canonicalWork2Rotation_resources
  rw [primitiveResources_unitary_HPFree _ _ canonicalWork2Rotation_HPFree, h.1,h.2.1,h.2.2.1]
  rfl
/-- Primitive vector of the actual fixed canonicalWork2InverseRotation gate stream. -/
theorem canonicalWork2InverseRotation_primitive :
    primitiveResources (.unitary canonicalWork2InverseRotation .done)=
      (⟨6,0,5240,2620,0,0⟩ : PrimitiveResources) := by
  have h := canonicalWork2InverseRotation_resources
  rw [primitiveResources_unitary_HPFree _ _ canonicalWork2InverseRotation_HPFree, h.1,h.2.1,h.2.2.1]
  rfl
/-- Primitive vector of the actual fixed terminalEpochCompression gate stream. -/
theorem terminalEpochCompression_primitive :
    primitiveResources (.unitary terminalEpochCompression .done)=
      (⟨10,0,0,15,0,0⟩ : PrimitiveResources) := by
  decide +kernel
/-- Primitive vector of the actual fixed terminalWork1Clear gate stream. -/
theorem terminalWork1Clear_primitive :
    primitiveResources (.unitary terminalWork1Clear .done)=
      (⟨251,0,0,0,0,0⟩ : PrimitiveResources) := by
  decide +kernel
end ShorECDLP.Paper2607_13816
