import ShorECDLP.Submission.«2607_13816».Arithmetic.PointGeneric
namespace ShorECDLP.Paper2607_13816
open ShorECDLP ShorECDLP.Secp256k1
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩

/-- Inputs excluded by the two potentially zero Figure 14 factors, together
with infinity. Finset removes duplicates without assumptions on the point's order. -/
noncomputable def fig14ExceptionalPoints (C : Secp256k1.Point) : Finset Secp256k1.Point := by
  classical
  exact {0,C,-C,-(C+C)}
private theorem same_X_eq_or_neg {x₁ y₁ x₂ y₂ : Fp}
    (h₁ : curve.toAffine.Nonsingular x₁ y₁) (h₂ : curve.toAffine.Nonsingular x₂ y₂)
    (hx : x₁=x₂) : (.some h₁ : Secp256k1.Point)=.some h₂ ∨
      (.some h₁ : Secp256k1.Point)=-(.some h₂ : Secp256k1.Point) := by
  by_cases hy : y₁=-y₂
  · right
    rw [WeierstrassCurve.Affine.Point.neg_some,WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hx,by simpa only [negY_eq_neg] using hy⟩
  · left
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hx,y_eq_of_x_eq_of_not_inverse h₁ h₂ hx hy⟩

theorem fig14ExceptionalPoints_card_le (C : Secp256k1.Point) :
    (fig14ExceptionalPoints C).card≤4 := by
  classical
  simpa [fig14ExceptionalPoints] using List.toFinset_card_le [0,C,-C,-(C+C)]

/-- Outside this finite set, both explicit nonzero conditions of the proved
coordinate formula hold. The result also covers constants with coinciding exceptions. -/
theorem fig14_nonexceptional_factors {x₁ y₁ x₂ y₂ : Fp}
    (h₁ : curve.toAffine.Nonsingular x₁ y₁) (h₂ : curve.toAffine.Nonsingular x₂ y₂)
    (hout : (.some h₁ : Secp256k1.Point) ∉ fig14ExceptionalPoints (.some h₂)) :
    x₁≠x₂ ∧ x₂≠genericX x₁ y₁ x₂ y₂ := by
  classical
  have hx : x₁≠x₂ := by
    intro he
    rcases same_X_eq_or_neg h₁ h₂ he with h | h
    · exact hout (by simp [fig14ExceptionalPoints,h])
    · exact hout (by simp [fig14ExceptionalPoints,h])
  refine ⟨hx,?_⟩
  intro he
  have hd := generic_nonsingular h₁ h₂ hx
  have hadd : (.some hd : Secp256k1.Point)=(.some h₁ : Secp256k1.Point)+(.some h₂ : Secp256k1.Point) :=
    genericAdd_correct h₁ h₂ hx
  rcases same_X_eq_or_neg hd h₂ he.symm with h | h
  · have hh := eq_sub_of_add_eq (hadd.symm.trans h)
    have hp0 : (.some h₁ : Secp256k1.Point)=0 := hh.trans (sub_self _)
    exact hout (by simp [fig14ExceptionalPoints,hp0])
  · have hh := eq_sub_of_add_eq (hadd.symm.trans h)
    have hp : (.some h₁ : Secp256k1.Point)=-((.some h₂ : Secp256k1.Point)+(.some h₂ : Secp256k1.Point)) := by
      simpa only [sub_eq_add_neg,neg_add] using hh
    exact hout (by simp [fig14ExceptionalPoints,hp])

attribute [local irreducible] fig14CoordinateState

/-- Outside the finite exception set, the actual enabled coordinate circuit
produces a nonsingular affine point equal to the total group-law sum. -/
theorem fig14CoordinateState_nonexceptional (x₂ y₂ : Nat)
    (hx₂ : x₂<ShorECDLP.p) (hy₂ : y₂<ShorECDLP.p)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) (hq : s 836=true)
    (h₁ : curve.toAffine.Nonsingular
      (boolWordToNat (wireValues (List.range' 263 256) s))
      (boolWordToNat (wireValues (List.range' 580 256) s)))
    (h₂ : curve.toAffine.Nonsingular (x₂ : Fp) (y₂ : Fp))
    (hout : (.some h₁ : Secp256k1.Point) ∉ fig14ExceptionalPoints (.some h₂)) :
    ∃ ho : curve.toAffine.Nonsingular
        (boolWordToNat (wireValues (List.range' 263 256) (fig14CoordinateState x₂ y₂ s)))
        (boolWordToNat (wireValues (List.range' 580 256) (fig14CoordinateState x₂ y₂ s))),
      (.some ho : Secp256k1.Point)=(.some h₁ : Secp256k1.Point)+(.some h₂ : Secp256k1.Point) := by
  have hf := fig14_nonexceptional_factors h₁ h₂ hout
  have hv := fig14CoordinateState_generic x₂ y₂ hx₂ hy₂ s hs hq hf.1 hf.2
  have ho : curve.toAffine.Nonsingular
      (boolWordToNat (wireValues (List.range' 263 256) (fig14CoordinateState x₂ y₂ s)))
      (boolWordToNat (wireValues (List.range' 580 256) (fig14CoordinateState x₂ y₂ s))) := by
    rw [hv.1,hv.2]
    exact generic_nonsingular h₁ h₂ hf.1
  refine ⟨ho,?_⟩
  calc
    (.some ho : Secp256k1.Point)=genericAdd h₁ h₂ hf.1 := by
      rw [genericAdd,WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hv.1,hv.2⟩
    _ = (.some h₁ : Secp256k1.Point)+(.some h₂ : Secp256k1.Point) := genericAdd_correct h₁ h₂ hf.1
end ShorECDLP.Paper2607_13816
