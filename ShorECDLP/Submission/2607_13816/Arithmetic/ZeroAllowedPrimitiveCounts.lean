import ShorECDLP.Submission.«2607_13816».Arithmetic.InPlacePrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowed
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Reversing a mask changes its order, not its primitive vector. -/
theorem computeEqConst_primitive (r : List Wire) (value : Nat) (flag : Wire) (scratch : List Wire)
    (hs : r.length-2≤scratch.length) :
    primitiveResources (.unitary (computeEqConst r value flag scratch) .done)=
      (⟨2*zeroBitCount value 0 r.length+(if r.length=0 then 1 else 0),0,
        mcxVChainCnotCost r.length,mcxVChainToffoliCost r.length,0,0⟩ : PrimitiveResources) := by
  have hv : primitiveResources (.unitary (computeEqConst r value flag scratch) .done)=
      primitiveResources (.unitary (computeControl r value flag scratch) .done) := by
    simp only [computeEqConst,computeControl,primitiveResources_unitary_append,primitiveResources_unitary_adjoint]
  rw [hv,computeControl_primitive r value flag scratch hs]
private theorem zeroPrepareEq_primitive :
    primitiveResources (.unitary (computeEqConst (263::List.range' 264 255) 0 837 (List.range' 7 254)) .done)=
      (⟨512,0,0,509,0,0⟩ : PrimitiveResources) := by
  rw [computeEqConst_primitive _ _ _ _ (by simp)]
  decide +kernel
/-- Zero handling adds a 256-bit equality predicate and one CNOT. -/
theorem fig15ZeroPrepare_primitive : primitiveResources (.unitary fig15ZeroPrepare .done)=
    (⟨512,0,1,509,0,0⟩ : PrimitiveResources) := by
  rw [fig15ZeroPrepare,nonzeroInputPrepare,primitiveResources_unitary_append,zeroPrepareEq_primitive]
  rfl
theorem fig15ZeroRestore_primitive : primitiveResources (.unitary fig15ZeroRestore .done)=
    (⟨512,0,1,509,0,0⟩ : PrimitiveResources) := by
  rw [fig15ZeroRestore,nonzeroInputRestore,primitiveResources_unitary_append,zeroPrepareEq_primitive]
  rfl
private theorem zeroAllowed_primitive_sum (v : PrimitiveResources)
    (h : v.x≤47567435 ∧ v.h≤24259500 ∧ v.cnot≤73396358 ∧ v.toffoli≤38515101 ∧
      v.phase=0 ∧ v.measurements≤11343835) :
    let w := ((⟨512,0,1,509,0,0⟩ : PrimitiveResources).add v).add ⟨512,0,1,509,0,0⟩
    w.x≤47568459 ∧ w.h≤24259500 ∧ w.cnot≤73396360 ∧ w.toffoli≤38516119 ∧
      w.phase=0 ∧ w.measurements≤11343835 := by
  dsimp only [PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
attribute [local irreducible] primitiveResources secp256k1InPlaceDivision secp256k1InPlaceMultiplication
/-- The complete zero-allowed division includes both equality-predicate masks. -/
theorem secp256k1ZeroAllowedDivision_primitive_bounds :
    let v := primitiveResources secp256k1ZeroAllowedDivision
    v.x≤47568459 ∧ v.h≤24259500 ∧ v.cnot≤73396360 ∧ v.toffoli≤38516119 ∧
      v.phase=0 ∧ v.measurements≤11343835 := by
  rw [secp256k1ZeroAllowedDivision]
  simp only [primitiveResources_seq,fig15ZeroPrepare_primitive,fig15ZeroRestore_primitive]
  exact zeroAllowed_primitive_sum _ secp256k1InPlaceDivision_primitive_bounds
theorem secp256k1ZeroAllowedMultiplication_primitive_bounds :
    let v := primitiveResources secp256k1ZeroAllowedMultiplication
    v.x≤47568459 ∧ v.h≤24259500 ∧ v.cnot≤73396360 ∧ v.toffoli≤38516119 ∧
      v.phase=0 ∧ v.measurements≤11343835 := by
  rw [secp256k1ZeroAllowedMultiplication]
  simp only [primitiveResources_seq,fig15ZeroPrepare_primitive,fig15ZeroRestore_primitive]
  exact zeroAllowed_primitive_sum _ secp256k1InPlaceMultiplication_primitive_bounds
end ShorECDLP.Paper2607_13816

namespace ShorECDLP.Paper2607_13816
/-- The exact zero-allowed division vector includes both equality masks. -/
theorem secp256k1ZeroAllowedDivision_primitive_exact :
    primitiveResources secp256k1ZeroAllowedDivision =
      (⟨41769233,24259500,67286144,38516119,0,11343835⟩ : PrimitiveResources) := by
  rw [secp256k1ZeroAllowedDivision]
  simp only [primitiveResources_seq,fig15ZeroPrepare_primitive,fig15ZeroRestore_primitive,
    secp256k1InPlaceDivision_primitive_exact]
  rfl
/-- The exact zero-allowed multiplication vector includes both equality masks. -/
theorem secp256k1ZeroAllowedMultiplication_primitive_exact :
    primitiveResources secp256k1ZeroAllowedMultiplication =
      (⟨41769233,24259500,67286144,38516119,0,11343835⟩ : PrimitiveResources) := by
  rw [secp256k1ZeroAllowedMultiplication]
  simp only [primitiveResources_seq,fig15ZeroPrepare_primitive,fig15ZeroRestore_primitive,
    secp256k1InPlaceMultiplication_primitive_exact]
  rfl
end ShorECDLP.Paper2607_13816
