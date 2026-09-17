import ShorECDLP.Submission.«2607_13816».Window.LookupPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Window.SignedPoint
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointCorrectionPrimitiveCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
attribute [local irreducible] primitiveResources

private theorem correction_at_primitive {x y : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) (q : Wire) :
    primitiveResources (.unitary (pointCorrectionAt hC q) .done)=
      pointWordPrimitives (pointCorrectionWordEdges hC) := by
  have h := primitiveResources_relabel (Equiv.swap 836 q) (.unitary (pointCorrectionCircuit hC) .done)
  exact h.trans (pointCorrectionCircuit_primitive_exact hC)
/-- Exact selected-point correction payload plus its separate sixteen-bit decoder. -/
def correctionTablePrimitives (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) : PrimitiveResources :=
  let tree := tableAddressTree correctionTableBits 0 1
  let leaf := fun a => pointWordPrimitives (pointCorrectionWordEdges (hc a))
  ⟨tree.leafCostSum (fun a _ => (leaf a).x) 836 correctionTablePath+4*65535,
   tree.leafCostSum (fun a _ => (leaf a).h) 836 correctionTablePath+2*65535,
   tree.leafCostSum (fun a _ => (leaf a).cnot) 836 correctionTablePath+3*65535,
   tree.leafCostSum (fun a _ => (leaf a).toffoli) 836 correctionTablePath+65535,
   tree.leafCostSum (fun a _ => (leaf a).phase) 836 correctionTablePath,
   tree.leafCostSum (fun a _ => (leaf a).measurements) 836 correctionTablePath+65535⟩

theorem correctionTableProgram_primitive (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    primitiveResources (correctionTableProgram x y hc)=correctionTablePrimitives x y hc := by
  have h := unaryAction_primitive .inc (fun a q => pointCorrectionAt (hc a) q)
    (tableAddressTree correctionTableBits 0 1) 836 correctionTablePath
    (tableAddressTree_layout _ _ _ _ _ (by decide +kernel) (by decide +kernel))
  have hn := tableAddressTree_nodes correctionTableBits 0 1
  have hl : correctionTableBits.length=16 := rfl
  rw [hl] at hn
  have he : (tableAddressTree correctionTableBits 0 1).internalNodes=65535 := by omega
  simp only [correction_at_primitive,he] at h
  exact h

def signedPointPrimitives (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) : PrimitiveResources :=
  (signedCoordinatePrimitives (fun a => (x a).val) (fun a => (y a).val)).add
    (correctionTablePrimitives (signedCorrectionX x) (signedCorrectionY y)
      (signedCorrection_nonsingular x y hc))
/-- Same total signed-point program: five coordinate queries and an exceptional correction traversal. -/
theorem signedLookupPointProgram_primitive (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    primitiveResources (signedLookupPointProgram x y hc)=signedPointPrimitives x y hc := by
  rw [signedLookupPointProgram,primitiveResources_seq,signedLookupCoordinateProgram_primitive,
    correctionTableProgram_primitive]
  rfl

end
end ShorECDLP.Paper2607_13816
