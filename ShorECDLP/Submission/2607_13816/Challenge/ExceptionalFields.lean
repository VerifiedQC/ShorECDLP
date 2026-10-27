import ShorECDLP.Challenge.PointFields
import ShorECDLP.Submission.«2607_13816».Challenge.FixedMatching
namespace ShorECDLP.Paper2607_13816
open ShorECDLP ShorECDLP.Secp256k1
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩

theorem exceptionalImage_coordinateEquiv (x y r s : Fp) :
    fig14CoordinateEquiv x y (r,s) = Challenge.exceptionalImage x y r s := by
  change (-(r + -x - ((s + -y) * (Challenge.exceptionalDenominator (r + -x))⁻¹) *
    ((s + -y) * (Challenge.exceptionalDenominator (r + -x))⁻¹) + 3*x) + x,
    ((s + -y) * (Challenge.exceptionalDenominator (r + -x))⁻¹) *
      Challenge.exceptionalDenominator (r + -x - ((s + -y) * (Challenge.exceptionalDenominator (r + -x))⁻¹) *
        ((s + -y) * (Challenge.exceptionalDenominator (r + -x))⁻¹) + 3*x) + -y) = _
  simp only [Challenge.exceptionalImage, div_eq_mul_inv, pow_two, sub_eq_add_neg]
  have hw : r + -x + -((s + -y) * (Challenge.exceptionalDenominator (r + -x))⁻¹ *
      ((s + -y) * (Challenge.exceptionalDenominator (r + -x))⁻¹)) + 3*x =
      r + 2*x + -((s + -y) * (Challenge.exceptionalDenominator (r + -x))⁻¹ *
      ((s + -y) * (Challenge.exceptionalDenominator (r + -x))⁻¹)) := by ring
  rw [hw]
  congr 1; ring

namespace ChallengeMigration
open ShorECDLP.Challenge

theorem pointCoordinates_encoding (P : Point) :
    pointCoordinates P = fig14PointEncoding P := by cases P <;> rfl

theorem pointCoordinates_neg (P : Point) :
    pointCoordinates (-P) = ((pointCoordinates P).1,
      (pointCoordinates P).2.1, -(pointCoordinates P).2.2) := by
  cases P with
  | zero => change pointCoordinates (-(0 : Point)) = _; simp [pointCoordinates]
  | some h => simp [WeierstrassCurve.Affine.Point.neg_some, pointCoordinates, curve]

/-- Decode two fixed public fields; no point-dependent callback is submission data. -/
noncomputable def exceptionFieldCoordinates (P : Point) (infinity : Bool)
    (fx fy : PointField) : Bool × (Fp × Fp) :=
  (infinity, (fieldValue P fx : Fp), (fieldValue P fy : Fp))

/-- The four raw pairs, before the tail-matching adjustment. -/
noncomputable def protectedExceptionPairs (P : Point) :
    List ((Bool × (Fp × Fp)) × (Bool × (Fp × Fp))) :=
  let di := decide (fieldValue P .doubleInfinity = 1);
  [(exceptionFieldCoordinates P true .exceptionalZeroX .exceptionalZeroY,
      exceptionFieldCoordinates P false .x .y),
   (exceptionFieldCoordinates P false .negDoubleX .negY,
      exceptionFieldCoordinates P di .doubleX .doubleY),
   (exceptionFieldCoordinates P false .exceptionalNegX .exceptionalNegY, (true,0,0)),
   (exceptionFieldCoordinates P di .exceptionalNegDoubleX .exceptionalNegDoubleY,
      exceptionFieldCoordinates P false .x .negY)]

theorem protectedExceptionPairs_length (P : Point) :
    (protectedExceptionPairs P).length = 4 := rfl

theorem doubleInfinity_eq (P : Point) :
    decide (fieldValue P .doubleInfinity = 1) = (pointCoordinates (P+P)).1 := by
  simp only [fieldValue, doubledCoordinates]
  by_cases h : (pointCoordinates (P+P)).1 = true <;> simp [h]

theorem encodedImage_fields (x y : Fp) (P : Point) :
    fig14EncodedEquiv x y (fig14PointEncoding P) =
      ((pointCoordinates P).1, exceptionalImage x y (pointCoordinates P).2.1
        (pointCoordinates P).2.2) := by
  cases P with
  | zero => exact Prod.ext rfl (exceptionalImage_coordinateEquiv x y 0 0)
  | @some r t h => exact Prod.ext rfl (exceptionalImage_coordinateEquiv x y r t)

theorem protectedExceptionPairs_eq {x y : Fp} (hC : curve.toAffine.Nonsingular x y) :
    protectedExceptionPairs (.some hC) = fixedExceptionPairs hC := by
  have hm : -((.some hC : Point)+(.some hC)) + .some hC = -(.some hC : Point) := by abel
  simp only [protectedExceptionPairs, fixedExceptionPairs, fixedExceptionInputs, List.map_cons,
    List.map_nil, doubleInfinity_eq]
  simp only [encodedImage_fields]
  simp only [← pointCoordinates_encoding, zero_add, neg_add_cancel, hm, pointCoordinates_neg]
  simp only [exceptionFieldCoordinates, fieldValue, doubledCoordinates,
    ZMod.natCast_zmod_val]
  simp only [pointCoordinates, exceptionalImage_self, Prod.mk.eta]
theorem protectedExceptionPairs_correct {x y : Fp}
    (hC : curve.toAffine.Nonsingular x y) (P : Point) :
    runFiniteSwaps (finiteMatchingSwaps (protectedExceptionPairs (.some hC)))
      (fig14EncodedEquiv x y (fig14PointEncoding P)) =
      fig14PointEncoding (P + .some hC) := by
  rw [protectedExceptionPairs_eq hC]
  exact fixedExceptionSwaps_correct hC P

end ChallengeMigration
end ShorECDLP.Paper2607_13816
