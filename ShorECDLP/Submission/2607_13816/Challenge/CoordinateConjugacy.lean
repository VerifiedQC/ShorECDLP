import ShorECDLP.Submission.«2607_13816».Arithmetic.PointCorrection
namespace ShorECDLP.Paper2607_13816
open ShorECDLP ShorECDLP.Secp256k1
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩
private def factor (x : Fp) : Fp := if x=0 then 1 else x
private theorem coordinateFormula (x₂ y₂ x y : Fp) :
    fig14CoordinateEquiv x₂ y₂ (x,y)=
      let a := x-x₂
      let b := y-y₂
      let u := b*(factor a)⁻¹
      let v := a-u*u
      let w := v+3*x₂
      let z := u*factor w
      (-w+x₂,z-y₂) := by
  change (let a := x + -x₂
          let b := y + -y₂
          let u := b*(factor a)⁻¹
          let v := a-u*u
          let w := v+3*x₂
          let z := u*factor w
          (-w+x₂,z + -y₂)) = _
  simp only [sub_eq_add_neg]

theorem fig14CoordinateEquiv_negY (x y u v : Fp) :
    ((fig14CoordinateEquiv x (-y) (u,v)).1, -(fig14CoordinateEquiv x (-y) (u,v)).2) =
      fig14CoordinateEquiv x y (u,-v) := by
  simp only [coordinateFormula,sub_neg_eq_add]
  have hn : -v-y = -(v+y) := by ring
  simp only [hn,neg_mul,mul_neg,neg_neg]
  congr 1
  ring
def encodedNegY (z : Bool × (Fp × Fp)) : Bool × (Fp × Fp) := (z.1,(z.2.1,-z.2.2))
@[simp] theorem encodedNegY_involution (z : Bool × (Fp × Fp)) : encodedNegY (encodedNegY z) = z := by
  simp [encodedNegY]
theorem fig14PointEncoding_neg (P : Point) : fig14PointEncoding (-P) = encodedNegY (fig14PointEncoding P) := by
  cases P with
  | zero =>
    change fig14PointEncoding (-(0 : Point)) = _
    rw [neg_zero]; rfl
  | @some x y h => simp [fig14PointEncoding,encodedNegY,WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.negY,curve]

theorem fig14EncodedEquiv_negY (x y : Fp) (z : Bool × (Fp × Fp)) :
    encodedNegY (fig14EncodedEquiv x (-y) z) = fig14EncodedEquiv x y (encodedNegY z) := by
  exact congrArg (Prod.mk z.1) (fig14CoordinateEquiv_negY x y z.2.1 z.2.2)

theorem signedCorrection_negY {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (P : Point) :
    encodedNegY (runFiniteSwaps (fig14CorrectionSwaps hC)
      (encodedNegY (fig14EncodedEquiv x (-y) (fig14PointEncoding P)))) =
      fig14PointEncoding (P - .some hC) := by
  rw [fig14EncodedEquiv_negY,← fig14PointEncoding_neg,fig14CorrectionSwaps_correct,← fig14PointEncoding_neg]
  congr 1
  simp [sub_eq_add_neg,add_comm]
end ShorECDLP.Paper2607_13816
