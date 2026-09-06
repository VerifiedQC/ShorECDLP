import ShorECDLP.Math.BitcoinCurve

namespace ShorECDLP
namespace Secp256k1

variable [Fact (Nat.Prime p)]

@[simp]
theorem negY_eq_neg (x y : Fp) :
    curve.toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY, curve]

def genericNumerator (y₁ y₂ : Fp) : Fp :=
  y₁ - y₂

def genericDenominator (x₁ x₂ : Fp) : Fp :=
  x₁ - x₂

def genericSlope (x₁ y₁ x₂ y₂ : Fp) : Fp :=
  genericNumerator y₁ y₂ * (genericDenominator x₁ x₂)⁻¹

def genericX (x₁ y₁ x₂ y₂ : Fp) : Fp :=
  let l := genericSlope x₁ y₁ x₂ y₂
  l ^ 2 - x₁ - x₂

def genericY (x₁ y₁ x₂ y₂ : Fp) : Fp :=
  let l := genericSlope x₁ y₁ x₂ y₂
  let x₃ := genericX x₁ y₁ x₂ y₂
  l * (x₁ - x₃) - y₁

def doubleNumerator (x : Fp) : Fp :=
  3 * x ^ 2

def doubleDenominator (y : Fp) : Fp :=
  2 * y

def doubleSlope (x y : Fp) : Fp :=
  doubleNumerator x * (doubleDenominator y)⁻¹

def doubleX (x y : Fp) : Fp :=
  let l := doubleSlope x y
  l ^ 2 - 2 * x

def doubleY (x y : Fp) : Fp :=
  let l := doubleSlope x y
  let x₃ := doubleX x y
  l * (x - x₃) - y

theorem genericDenominator_ne_zero
    {x₁ x₂ : Fp}
    (hx : x₁ ≠ x₂) :
    genericDenominator x₁ x₂ ≠ 0 := by
  simpa [genericDenominator] using sub_ne_zero.mpr hx

theorem doubleDenominator_ne_zero
    {y : Fp}
    (hy : y ≠ -y) :
    doubleDenominator y ≠ 0 := by
  intro h
  apply hy
  rw [eq_neg_iff_add_eq_zero]
  simpa [doubleDenominator, two_mul] using h

theorem genericSlope_eq_mathlib
    {x₁ y₁ x₂ y₂ : Fp}
    (hx : x₁ ≠ x₂) :
    genericSlope x₁ y₁ x₂ y₂ =
      curve.toAffine.slope x₁ x₂ y₁ y₂ := by
  rw [curve.toAffine.slope_of_X_ne hx]
  simp [genericSlope, genericNumerator, genericDenominator, div_eq_mul_inv]

theorem genericX_eq_mathlib
    {x₁ y₁ x₂ y₂ : Fp}
    (hx : x₁ ≠ x₂) :
    genericX x₁ y₁ x₂ y₂ =
      curve.toAffine.addX x₁ x₂
        (curve.toAffine.slope x₁ x₂ y₁ y₂) := by
  simp [genericX, genericSlope_eq_mathlib hx,
    WeierstrassCurve.Affine.addX, curve]

theorem genericY_eq_mathlib
    {x₁ y₁ x₂ y₂ : Fp}
    (hx : x₁ ≠ x₂) :
    genericY x₁ y₁ x₂ y₂ =
      curve.toAffine.addY x₁ x₂ y₁
        (curve.toAffine.slope x₁ x₂ y₁ y₂) := by
  simp only [genericY]
  rw [genericSlope_eq_mathlib hx, genericX_eq_mathlib hx]
  rw [WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, negY_eq_neg]
  ring_nf

theorem doubleSlope_eq_mathlib
    {x y : Fp}
    (hy : y ≠ -y) :
    doubleSlope x y =
      curve.toAffine.slope x x y y := by
  have hy' : y ≠ curve.toAffine.negY x y := by
    simpa [WeierstrassCurve.Affine.negY, curve] using hy
  rw [curve.toAffine.slope_of_Y_ne rfl hy']
  simp [doubleSlope, doubleNumerator, doubleDenominator,
    curve, curveA, div_eq_mul_inv, two_mul]

theorem doubleX_eq_mathlib
    {x y : Fp}
    (hy : y ≠ -y) :
    doubleX x y =
      curve.toAffine.addX x x
        (curve.toAffine.slope x x y y) := by
  simp [doubleX, doubleSlope_eq_mathlib hy,
    WeierstrassCurve.Affine.addX, curve]
  ring

theorem doubleY_eq_mathlib
    {x y : Fp}
    (hy : y ≠ -y) :
    doubleY x y =
      curve.toAffine.addY x x y
        (curve.toAffine.slope x x y y) := by
  simp only [doubleY]
  rw [doubleSlope_eq_mathlib hy, doubleX_eq_mathlib hy]
  rw[WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, negY_eq_neg]
  ring

theorem generic_nonsingular
    {x₁ y₁ x₂ y₂ : Fp}
    (h₁ : curve.toAffine.Nonsingular x₁ y₁)
    (h₂ : curve.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) :
    curve.toAffine.Nonsingular
      (genericX x₁ y₁ x₂ y₂)
      (genericY x₁ y₁ x₂ y₂) := by
  rw [genericX_eq_mathlib hx, genericY_eq_mathlib hx]
  exact curve.toAffine.nonsingular_add h₁ h₂
    (fun hxy => hx hxy.left)

def genericAdd
    {x₁ y₁ x₂ y₂ : Fp}
    (h₁ : curve.toAffine.Nonsingular x₁ y₁)
    (h₂ : curve.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) :
    Point :=
  .some (generic_nonsingular h₁ h₂ hx)

theorem genericAdd_correct
    {x₁ y₁ x₂ y₂ : Fp}
    (h₁ : curve.toAffine.Nonsingular x₁ y₁)
    (h₂ : curve.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) :
    genericAdd h₁ h₂ hx =
      (.some h₁ : Point) + (.some h₂ : Point) := by
  unfold genericAdd
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨genericX_eq_mathlib hx, genericY_eq_mathlib hx⟩

theorem double_nonsingular
    {x y : Fp}
    (h : curve.toAffine.Nonsingular x y)
    (hy : y ≠ -y) :
    curve.toAffine.Nonsingular
      (doubleX x y)
      (doubleY x y) := by
  rw [doubleX_eq_mathlib hy, doubleY_eq_mathlib hy]
  apply curve.toAffine.nonsingular_add h h
  rintro ⟨_, hy'⟩
  apply hy
  simpa [WeierstrassCurve.Affine.negY, curve] using hy'

def doublePoint
    {x y : Fp}
    (h : curve.toAffine.Nonsingular x y)
    (hy : y ≠ -y) :
    Point :=
  .some (double_nonsingular h hy)

theorem doublePoint_correct
    {x y : Fp}
    (h : curve.toAffine.Nonsingular x y)
    (hy : y ≠ -y) :
    doublePoint h hy =
      (.some h : Point) + (.some h : Point) := by
  unfold doublePoint
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (by simpa [WeierstrassCurve.Affine.negY, curve] using hy)]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨doubleX_eq_mathlib hy, doubleY_eq_mathlib hy⟩

theorem inverseAdd_correct
    {x₁ y₁ x₂ y₂ : Fp}
    (h₁ : curve.toAffine.Nonsingular x₁ y₁)
    (h₂ : curve.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ = x₂)
    (hy : y₁ = -y₂) :
    (.some h₁ : Point) + (.some h₂ : Point) = 0 := by
  apply WeierstrassCurve.Affine.Point.add_of_Y_eq hx
  simpa [WeierstrassCurve.Affine.negY, curve] using hy

theorem y_eq_of_x_eq_of_not_inverse
    {x₁ y₁ x₂ y₂ : Fp}
    (h₁ : curve.toAffine.Nonsingular x₁ y₁)
    (h₂ : curve.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ = x₂)
    (hinv : y₁ ≠ -y₂) :
    y₁ = y₂ := by
  apply curve.toAffine.Y_eq_of_Y_ne h₁.left h₂.left hx
  simpa [WeierstrassCurve.Affine.negY, curve] using hinv

theorem self_not_inverse_of_x_eq_of_not_inverse
    {x₁ y₁ x₂ y₂ : Fp}
    (h₁ : curve.toAffine.Nonsingular x₁ y₁)
    (h₂ : curve.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ = x₂)
    (hinv : y₁ ≠ -y₂) :
    y₁ ≠ -y₁ := by
  have hy := y_eq_of_x_eq_of_not_inverse h₁ h₂ hx hinv
  intro h
  apply hinv
  exact h.trans (congrArg Neg.neg hy)

def affineAdd : Point → Point → Point
  | .zero, Q => Q
  | P, .zero => P
  | @WeierstrassCurve.Affine.Point.some _ _ _ x₁ y₁ h₁,
    @WeierstrassCurve.Affine.Point.some _ _ _ x₂ y₂ h₂ =>
      if hx : x₁ = x₂ then
        if hinv : y₁ = -y₂ then
          0
        else
          doublePoint h₁
            (self_not_inverse_of_x_eq_of_not_inverse
              h₁ h₂ hx hinv)
      else
        genericAdd h₁ h₂ hx

@[simp]
theorem affineAdd_zero_left (P : Point) :
    affineAdd 0 P = P := by
  rfl

@[simp]
theorem affineAdd_zero_right (P : Point) :
    affineAdd P 0 = P := by
  cases P <;> rfl

theorem affineAdd_inverse
    {x₁ y₁ x₂ y₂ : Fp}
    (h₁ : curve.toAffine.Nonsingular x₁ y₁)
    (h₂ : curve.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ = x₂)
    (hinv : y₁ = -y₂) :
    affineAdd (.some h₁) (.some h₂) = 0 := by
  unfold affineAdd
  simp [hx, hinv]

theorem affineAdd_generic
    {x₁ y₁ x₂ y₂ : Fp}
    (h₁ : curve.toAffine.Nonsingular x₁ y₁)
    (h₂ : curve.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) :
    affineAdd (.some h₁) (.some h₂) =
      genericAdd h₁ h₂ hx := by
  unfold affineAdd
  simp [hx]

theorem affineAdd_doubling
    {x₁ y₁ x₂ y₂ : Fp}
    (h₁ : curve.toAffine.Nonsingular x₁ y₁)
    (h₂ : curve.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ = x₂)
    (hinv : y₁ ≠ -y₂) :
    affineAdd (.some h₁) (.some h₂) =
      (.some h₁ : Point) + (.some h₂ : Point) := by
  have hy := y_eq_of_x_eq_of_not_inverse h₁ h₂ hx hinv
  subst x₂
  subst y₂
  unfold affineAdd
  simp [hinv]
  exact doublePoint_correct h₁ hinv

theorem affineAdd_correct (P Q : Point) :
    affineAdd P Q = P + Q := by
  cases P with
  | zero =>
      rfl
  | some h₁ =>
      cases Q with
      | zero =>
          rfl
      | some h₂ =>
          rename_i x₁ y₁ x₂ y₂
          by_cases hx : x₁ = x₂
          · by_cases hinv : y₁ = -y₂
            · calc
                affineAdd (.some h₁) (.some h₂) = 0 :=
                  affineAdd_inverse h₁ h₂ hx hinv
                _ = (.some h₁ : Point) + .some h₂ :=
                  (inverseAdd_correct h₁ h₂ hx hinv).symm
            · exact affineAdd_doubling h₁ h₂ hx hinv
          · calc
              affineAdd (.some h₁) (.some h₂) =
                  genericAdd h₁ h₂ hx :=
                affineAdd_generic h₁ h₂ hx
              _ = (.some h₁ : Point) + .some h₂ :=
                genericAdd_correct h₁ h₂ hx

end Secp256k1
end ShorECDLP
