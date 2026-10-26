import ShorECDLP.Challenge.Template

namespace ShorECDLP.Challenge
open Secp256k1

@[simp] theorem exceptionalDenominator_zero : exceptionalDenominator 0 = 1 := by
  simp [exceptionalDenominator]

theorem exceptionalDenominator_ne_zero (z : Fp) : exceptionalDenominator z ≠ 0 := by
  unfold exceptionalDenominator
  split_ifs with h
  · exact one_ne_zero
  · exact h

/-- The zero denominator at the self point is replaced by one. -/
theorem exceptionalImage_self (x y : Fp) : exceptionalImage x y x y = (-2*x, -y) := by
  simp [exceptionalImage]

/-- The negative-point exceptional image retains the zero-replacement branch. -/
theorem exceptionalImage_neg (x y : Fp) :
    exceptionalImage x y x (-y) =
      (4*y^2 - 2*x, (-2*y) * exceptionalDenominator (3*x - 4*y^2) - y) := by
  have hu : (-y-y) / exceptionalDenominator (x-x) = -2*y := by simp; ring
  unfold exceptionalImage
  rw [hu]
  dsimp only
  have hw : x + 2*x - (-2*y)^2 = 3*x - 4*y^2 := by ring
  rw [hw]
  congr 1
  ring

/-- Infinity has canonical zero coordinates for every coordinate field and
one for each infinity flag, including the doubled point. -/
theorem fieldValue_zero (f : PointField) :
    fieldValue 0 f = if f = .infinity ∨ f = .doubleInfinity then 1 else 0 := by
  cases f <;> simp [fieldValue, pointCoordinates, doubledCoordinates, exceptionalImage,
    exceptionalDenominator]

/-- Doubling uses the actual group law, hence also its infinity cases. -/
theorem doubledCoordinates_eq (P : Point) :
    doubledCoordinates P = pointCoordinates (P+P) := rfl

end ShorECDLP.Challenge
