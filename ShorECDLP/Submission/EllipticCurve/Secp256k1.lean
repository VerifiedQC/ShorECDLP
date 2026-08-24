import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.ReduceModChar
import ShorECDLP.Submission.Field

/-
# The secp256k1 curve and its standard generator (M2, spec layer)

This module fixes the single mathematical point type used by the elliptic-curve part of the
submission: Mathlib's nonsingular affine Weierstrass points on `y² = x³ + 7` over `Fp`.  It also
defines the standard secp256k1 generator and machine-checks its equation and nonsingularity.

There are deliberately no point encodings, register widths, circuits, wires, or layouts here.
Those implementation choices refine this point type in later M2 modules.  Likewise, this module
does not assert that the generator has order `order`: that substantially stronger certificate is
not implied merely by primality of `p` and is left for a module that genuinely proves it.
-/

namespace ShorECDLP
namespace Secp256k1

/-- The standard generator's `x` coordinate, represented canonically in `[0, p)`. -/
def generatorX : Nat :=
  55066263022277343669578718895168534326250603453777594175500187360389116729240

/-- The standard generator's `y` coordinate, represented canonically in `[0, p)`. -/
def generatorY : Nat :=
  32670510020758816978083085130507043184471273380659243275938904335757337482424

/-- The short-Weierstrass secp256k1 curve `y² = x³ + 7` over `Fp`. -/
def curve : WeierstrassCurve Fp where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := curveA
  a₆ := curveB

/-- The canonical mathematical type of secp256k1 points used throughout the submission. -/
abbrev Point := curve.toAffine.Point

/-- The generator's natural `x` representative is canonical modulo `p`. -/
theorem generatorX_lt_p : generatorX < p := by
  norm_num [generatorX, p]

/-- The generator's natural `y` representative is canonical modulo `p`. -/
theorem generatorY_lt_p : generatorY < p := by
  norm_num [generatorY, p]

/-- Casting the generator's `x` coordinate to `Fp` preserves its canonical representative. -/
@[simp]
theorem generatorX_val : (generatorX : Fp).val = generatorX :=
  ZMod.val_natCast_of_lt generatorX_lt_p

/-- Casting the generator's `y` coordinate to `Fp` preserves its canonical representative. -/
@[simp]
theorem generatorY_val : (generatorY : Fp).val = generatorY :=
  ZMod.val_natCast_of_lt generatorY_lt_p

/-- The secp256k1 discriminant is nonzero in `Fp`. -/
theorem curve_discriminant_ne_zero : curve.Δ ≠ 0 := by
  have hΔ : curve.Δ = (-21168 : Fp) := by
    simp [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, curveA, curveB]
    norm_num
  rw [hΔ]
  intro h
  have hdvd : (p : Int) ∣ (-21168 : Int) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (-21168) p).mp h
  norm_num [p] at hdvd

/-- Under the published primality hypothesis for `p`, `curve` is an elliptic curve in Mathlib's
sense: its discriminant is a unit. -/
instance [Fact (Nat.Prime p)] : curve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr curve_discriminant_ne_zero⟩

/-- The standard generator coordinates satisfy the secp256k1 curve equation. -/
theorem generator_equation :
    curve.toAffine.Equation (generatorX : Fp) (generatorY : Fp) := by
  rw [curve.toAffine.equation_iff]
  change ((generatorY : Fp) ^ 2 = (generatorX : Fp) ^ 3 + 7)
  simp only [generatorX, generatorY]
  unfold Fp p
  reduce_mod_char

/-- The standard generator is a nonsingular affine point. -/
theorem generator_nonsingular :
    curve.toAffine.Nonsingular (generatorX : Fp) (generatorY : Fp) :=
  (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
    generator_equation

/-- The standard secp256k1 generator as a value of the canonical point type. -/
def G : Point :=
  .some generator_nonsingular

/-- Reveal affine coordinates while representing the point at infinity by `none`. -/
def coordinates : Point → Option (Fp × Fp)
  | .zero => none
  | @WeierstrassCurve.Affine.Point.some _ _ _ x y _ => some (x, y)

@[simp]
theorem coordinates_zero : coordinates (0 : Point) = none :=
  rfl

@[simp]
theorem coordinates_some {x y : Fp} (h : curve.toAffine.Nonsingular x y) :
    coordinates (.some h) = some (x, y) :=
  rfl

/-- The standard generator exposes exactly the published affine coordinates. -/
@[simp]
theorem coordinates_G :
    coordinates G = some ((generatorX : Fp), (generatorY : Fp)) :=
  rfl

/-- The standard generator is not the point at infinity. -/
theorem G_ne_zero : G ≠ 0 :=
  WeierstrassCurve.Affine.Point.some_ne_zero generator_nonsingular

end Secp256k1
end ShorECDLP
