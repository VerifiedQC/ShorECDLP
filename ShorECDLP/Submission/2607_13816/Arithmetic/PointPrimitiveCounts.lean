import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowedPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstantPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointCircuit
namespace ShorECDLP.Paper2607_13816
open Quantum
attribute [local irreducible] primitiveResources fig14ConstantX fig14ControlledConstantX fig14ControlledConstantY fig14Negate fig14SquareSubtract secp256k1ZeroAllowedDivision secp256k1ZeroAllowedMultiplication
theorem fig14ConstantX_primitive_bounds (k : Nat) :
    let v := primitiveResources (fig14ConstantX k)
    v.x≤18924 ∧ v.h≤5112 ∧ v.cnot≤19167 ∧ v.toffoli≤3829 ∧ v.phase=0 ∧ v.measurements≤1278 := by
  rw [fig14ConstantX]
  apply uncontrolledConstantModularAdd256_primitive_bounds <;> simp [secp256k1ReductionConstantBits]
theorem fig14ControlledConstantX_primitive_bounds (k : Nat) :
    let v := primitiveResources (fig14ControlledConstantX k)
    v.x≤7419 ∧ v.h≤5112 ∧ v.cnot≤19169 ∧ v.toffoli≤3829 ∧ v.phase=0 ∧ v.measurements≤1278 := by
  rw [fig14ControlledConstantX]
  apply controlledConstantModularAdd256_primitive_bounds <;> simp [secp256k1ReductionConstantBits]
theorem fig14ControlledConstantY_primitive_bounds (k : Nat) :
    let v := primitiveResources (fig14ControlledConstantY k)
    v.x≤7419 ∧ v.h≤5112 ∧ v.cnot≤19169 ∧ v.toffoli≤3829 ∧ v.phase=0 ∧ v.measurements≤1278 := by
  rw [fig14ControlledConstantY]
  apply controlledConstantModularAdd256_primitive_bounds <;> simp [secp256k1ReductionConstantBits]
theorem fig14Negate_primitive_bounds :
    let v := primitiveResources (fig14Negate)
    v.x≤3068 ∧ v.h≤4088 ∧ v.cnot≤15584 ∧ v.toffoli≤3062 ∧ v.phase=0 ∧ v.measurements≤1022 := by
  rw [fig14Negate]
  apply controlledModularNegate256_primitive_bounds <;> simp
theorem squareSubtract256_primitive_bounds (x y acc : List Wire) (correction modulus : List Bool)
    (p : Nat) (q copied c r t f : Wire) (hx : x.length=256) (hy : y.length=256)

    (ha : acc.length=256) (hcorr : correction.length=256) (hmod : modulus.length=256) :
    let v := primitiveResources (squareSubtract x y acc correction modulus p q copied c r t f)
    v.x≤5761287 ∧ v.h≤2091012 ∧ v.cnot≤9283600 ∧ v.toffoli≤2223879 ∧ v.phase=0 ∧ v.measurements≤522753 := by
  have h1 := squareLoop256_full_primitive_bounds y y acc correction p copied c r t f hy hy ha hcorr
  have h2 := controlledModularSub256_primitive_bounds acc x modulus p q copied f r c ha hx hmod
  have h3 := squareLoopInverse256_full_primitive_bounds y y acc modulus p copied c r t f hy hy ha hmod
  dsimp only at h1 h2 h3 ⊢
  simp only [squareSubtract,primitiveResources_seq,PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
theorem fig14SquareSubtract_primitive_bounds :
    let v := primitiveResources fig14SquareSubtract
    v.x≤5761287 ∧ v.h≤2091012 ∧ v.cnot≤9283600 ∧ v.toffoli≤2223879 ∧ v.phase=0 ∧ v.measurements≤522753 := by
  rw [fig14SquareSubtract]
  apply squareSubtract256_primitive_bounds <;> simp [secp256k1ReductionConstantBits]
private theorem pointCoordinate_primitive_sum (a : PrimitiveResources)
    (ha : a.x≤18924 ∧ a.h≤5112 ∧ a.cnot≤19167 ∧ a.toffoli≤3829 ∧ a.phase=0 ∧ a.measurements≤1278) (b : PrimitiveResources)
    (hb : b.x≤7419 ∧ b.h≤5112 ∧ b.cnot≤19169 ∧ b.toffoli≤3829 ∧ b.phase=0 ∧ b.measurements≤1278) (c : PrimitiveResources)
    (hc : c.x≤47568459 ∧ c.h≤24259500 ∧ c.cnot≤73396360 ∧ c.toffoli≤38516119 ∧ c.phase=0 ∧ c.measurements≤11343835) (d : PrimitiveResources)
    (hd : d.x≤5761287 ∧ d.h≤2091012 ∧ d.cnot≤9283600 ∧ d.toffoli≤2223879 ∧ d.phase=0 ∧ d.measurements≤522753) (e : PrimitiveResources)
    (he : e.x≤7419 ∧ e.h≤5112 ∧ e.cnot≤19169 ∧ e.toffoli≤3829 ∧ e.phase=0 ∧ e.measurements≤1278) (f : PrimitiveResources)
    (hf : f.x≤47568459 ∧ f.h≤24259500 ∧ f.cnot≤73396360 ∧ f.toffoli≤38516119 ∧ f.phase=0 ∧ f.measurements≤11343835) (g : PrimitiveResources)
    (hg : g.x≤3068 ∧ g.h≤4088 ∧ g.cnot≤15584 ∧ g.toffoli≤3062 ∧ g.phase=0 ∧ g.measurements≤1022) (h : PrimitiveResources)
    (hh : h.x≤18924 ∧ h.h≤5112 ∧ h.cnot≤19167 ∧ h.toffoli≤3829 ∧ h.phase=0 ∧ h.measurements≤1278) :
    let v := ((((((((a.add b).add c).add d).add e).add f).add g).add h).add b)
    v.x≤100961378 ∧ v.h≤50639660 ∧ v.cnot≤156187745 ∧ v.toffoli≤79278324 ∧ v.phase=0 ∧ v.measurements≤23217835 := by
  dsimp only [PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
/-- All nine literal coordinate stages contribute to this common bound. -/
theorem fig14CoordinateProgram_primitive_bounds (x y : Nat) :
    let v := primitiveResources (fig14CoordinateProgram x y)
    v.x≤100961378 ∧ v.h≤50639660 ∧ v.cnot≤156187745 ∧ v.toffoli≤79278324 ∧ v.phase=0 ∧ v.measurements≤23217835 := by
  rw [fig14CoordinateProgram]
  simp only [primitiveResources_seq]
  exact pointCoordinate_primitive_sum
    _ (fig14ConstantX_primitive_bounds ((ShorECDLP.p-x)%ShorECDLP.p))
    _ (fig14ControlledConstantY_primitive_bounds ((ShorECDLP.p-y)%ShorECDLP.p))
    _ (secp256k1ZeroAllowedDivision_primitive_bounds)
    _ (fig14SquareSubtract_primitive_bounds)
    _ (fig14ControlledConstantX_primitive_bounds ((3*x)%ShorECDLP.p))
    _ (secp256k1ZeroAllowedMultiplication_primitive_bounds)
    _ (fig14Negate_primitive_bounds)
    _ (fig14ConstantX_primitive_bounds (x%ShorECDLP.p))
end ShorECDLP.Paper2607_13816

namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Executable constant-stage vector, retaining all zero and threshold shortcuts. -/
def pointConstantPrimitives (controlled : Bool) (k : Nat) : PrimitiveResources :=
  (constantAdder256Primitives controlled (constantBits 256 k)).add
    ((constantLT256Primitives controlled (boolWordToNat (constantBits 256 k))).add
      ((constantGE256Primitives false ShorECDLP.p).add
        ((constantAdder256Primitives true secp256k1ReductionConstantBits).add
          (constantLT256Primitives controlled (boolWordToNat (constantBits 256 k))))))
attribute [local irreducible] primitiveResources
theorem fig14ConstantX_primitive_exact (k : Nat) :
    primitiveResources (fig14ConstantX k)=pointConstantPrimitives false k := by
  rw [fig14ConstantX,pointConstantPrimitives]
  apply uncontrolledConstantModularAdd256_primitive_exact <;> simp [secp256k1ReductionConstantBits]
theorem fig14ControlledConstantX_primitive_exact (k : Nat) :
    primitiveResources (fig14ControlledConstantX k)=pointConstantPrimitives true k := by
  rw [fig14ControlledConstantX,pointConstantPrimitives]
  apply controlledConstantModularAdd256_primitive_exact <;> simp [secp256k1ReductionConstantBits]
theorem fig14ControlledConstantY_primitive_exact (k : Nat) :
    primitiveResources (fig14ControlledConstantY k)=pointConstantPrimitives true k := by
  rw [fig14ControlledConstantY,pointConstantPrimitives]
  apply controlledConstantModularAdd256_primitive_exact <;> simp [secp256k1ReductionConstantBits]
theorem fig14Negate_primitive_exact : primitiveResources fig14Negate=
    (⟨3068,4088,12983,3062,0,1022⟩ : PrimitiveResources) := by
  rw [fig14Negate]
  rw [controlledModularNegate256_primitive_exact _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp)]
  decide +kernel
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum
attribute [local irreducible] primitiveResources squareLoopInverse
private theorem pointModulusBits : constantBits 256 ShorECDLP.p=secp256k1ModulusBits := by decide +kernel
private theorem pointGE : constantGE256Primitives false ShorECDLP.p=
    (⟨573,1024,1537,767,0,256⟩ : PrimitiveResources) := by decide +kernel
private theorem pointModulus : constantAdder256Primitives true secp256k1ModulusBits=
    (⟨1022,1020,3765,764,0,255⟩ : PrimitiveResources) := by decide +kernel
/-- Exact square compute/subtract/uncompute vector on arbitrary width-256 banks. -/
theorem squareSubtract256_secp_primitive_exact (x y acc : List Wire) (q copied c r t f : Wire)
    (hx : x.length=256) (hy : y.length=256) (ha : acc.length=256) :
    primitiveResources (squareSubtract x y acc secp256k1ReductionConstantBits secp256k1ModulusBits
      ShorECDLP.p q copied c r t f)=
      (⟨1896393,2091012,5630143,2223879,0,522753⟩ : PrimitiveResources) := by
  have hp : (2^256-(2^32+977) : Nat)=ShorECDLP.p := by decide +kernel
  have h1 := squareLoop256_secp_primitive_exact y y acc copied c r t f hy hy ha
  have h2 := controlledModularSub256_primitive_exact acc x secp256k1ModulusBits ShorECDLP.p q copied f r c ha hx (by decide +kernel)
  have h3 := squareLoopInverse256_secp_primitive_exact y y acc copied c r t f hy hy ha
  rw [hp] at h1 h3
  rw [pointGE,pointModulus] at h2
  rw [squareSubtract,primitiveResources_seq,primitiveResources_seq,h1,h2,h3]
  rfl
theorem fig14SquareSubtract_primitive_exact : primitiveResources fig14SquareSubtract=
    (⟨1896393,2091012,5630143,2223879,0,522753⟩ : PrimitiveResources) := by
  unfold fig14SquareSubtract
  rw [pointModulusBits]
  apply squareSubtract256_secp_primitive_exact <;> simp
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
/-- Exact nine-stage count formula, parameterized by the classical point coordinates. -/
def pointCoordinatePrimitives (x y : Nat) : PrimitiveResources :=
  let a := pointConstantPrimitives false ((ShorECDLP.p-x)%ShorECDLP.p)
  let b := pointConstantPrimitives true ((ShorECDLP.p-y)%ShorECDLP.p)
  let field : PrimitiveResources := ⟨41769233,24259500,67286144,38516119,0,11343835⟩
  ((((((((a.add b).add field).add ⟨1896393,2091012,5630143,2223879,0,522753⟩).add
    (pointConstantPrimitives true ((3*x)%ShorECDLP.p))).add field).add
    ⟨3068,4088,12983,3062,0,1022⟩).add (pointConstantPrimitives false (x%ShorECDLP.p))).add b)
/-- Every literal coordinate stage contributes its exact primitive vector. -/
theorem fig14CoordinateProgram_primitive_exact (x y : Nat) :
    primitiveResources (fig14CoordinateProgram x y)=pointCoordinatePrimitives x y := by
  rw [fig14CoordinateProgram,pointCoordinatePrimitives]
  simp only [primitiveResources_seq,fig14ConstantX_primitive_exact,
    fig14ControlledConstantX_primitive_exact,fig14ControlledConstantY_primitive_exact,
    secp256k1ZeroAllowedDivision_primitive_exact,secp256k1ZeroAllowedMultiplication_primitive_exact,
    fig14SquareSubtract_primitive_exact,fig14Negate_primitive_exact]
end ShorECDLP.Paper2607_13816
