import ShorECDLP.Submission.«2607_13816».Arithmetic.PointExceptions
import ShorECDLP.Submission.«2607_13816».Arithmetic.FiniteCorrection
namespace ShorECDLP.Paper2607_13816
open ShorECDLP ShorECDLP.Secp256k1
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩
/-- Canonical point coordinates with a separate infinity bit. -/
def fig14PointEncoding : Secp256k1.Point → Bool × (Fp × Fp)
  | .zero => (true,(0,0))
  | .some (x:=x) (y:=y) _ => (false,(x,y))
theorem fig14PointEncoding_injective : Function.Injective fig14PointEncoding := by
  intro P Q h
  cases P with
  | zero => cases Q <;> simp_all [fig14PointEncoding]
  | @some x y hP =>
    cases Q with
    | zero => simp [fig14PointEncoding] at h
    | @some u v hQ =>
      simp only [fig14PointEncoding,Prod.mk.injEq,true_and] at h
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact h
private def pointDecidableEq : DecidableEq ShorECDLP.Secp256k1.Point := fun P Q =>
  if h : fig14PointEncoding P=fig14PointEncoding Q then isTrue (fig14PointEncoding_injective h)
  else isFalse (fun he => h (congrArg fig14PointEncoding he))
local instance : DecidableEq ShorECDLP.Secp256k1.Point := pointDecidableEq
/-- Deterministic exceptional-point order, deduplicated by canonical coordinates. -/
def fig14ExceptionalList (C : ShorECDLP.Secp256k1.Point) : List ShorECDLP.Secp256k1.Point :=
  [0,C,-C,-(C+C)].dedup
theorem fig14ExceptionalList_mem (C P : ShorECDLP.Secp256k1.Point) :
    P ∈ fig14ExceptionalList C ↔ P ∈ fig14ExceptionalPoints C := by
  classical
  simp [fig14ExceptionalList,fig14ExceptionalPoints]
theorem fig14ExceptionalList_length (C : ShorECDLP.Secp256k1.Point) :
    (fig14ExceptionalList C).length ≤ 4 := (List.dedup_sublist _).length_le

/-- Apply the coordinate permutation while preserving the infinity bit. -/
def fig14EncodedEquiv (x₂ y₂ : Fp) : Equiv.Perm (Bool × (Fp × Fp)) :=
  Equiv.prodCongr (Equiv.refl Bool) (fig14CoordinateEquiv x₂ y₂)

private theorem coordinateEquiv_generic (x₂ y₂ x y : Fp)
    (hx : x≠x₂) (hw : x₂≠genericX x y x₂ y₂) :
    fig14CoordinateEquiv x₂ y₂ (x,y)=(genericX x y x₂ y₂,genericY x y x₂ y₂) := by
  have he := fig14CoordinateValues_equiv x₂.val y₂.val x.val y.val (ZMod.val_lt x₂) (ZMod.val_lt y₂)
  have hg := fig14CoordinateValues_generic x₂.val y₂.val x.val y.val (ZMod.val_lt x₂) (ZMod.val_lt y₂)
    (by simpa using hx) (by simpa using hw)
  have hp : (((fig14CoordinateValues x₂.val y₂.val true x.val y.val).1 : Fp),
      ((fig14CoordinateValues x₂.val y₂.val true x.val y.val).2 : Fp))=
      (genericX (x.val : Fp) y.val x₂.val y₂.val,genericY (x.val : Fp) y.val x₂.val y₂.val) :=
    Prod.ext hg.1 hg.2
  simpa using he.symm.trans hp

theorem fig14EncodedEquiv_nonexceptional {x₂ y₂ : Fp}
    (hC : curve.toAffine.Nonsingular x₂ y₂) (P : Secp256k1.Point)
    (hout : P ∉ fig14ExceptionalPoints (.some hC)) :
    fig14EncodedEquiv x₂ y₂ (fig14PointEncoding P)=fig14PointEncoding (P+(.some hC)) := by
  classical
  cases P with
  | zero => exact False.elim (hout (by change (0 : Secp256k1.Point) ∈ _; simp [fig14ExceptionalPoints]))
  | @some x y hP =>
    have hf := fig14_nonexceptional_factors hP hC hout
    rw [← genericAdd_correct hP hC hf.1]
    change (false,fig14CoordinateEquiv x₂ y₂ (x,y))=(false,(genericX x y x₂ y₂,genericY x y x₂ y₂))
    rw [coordinateEquiv_generic x₂ y₂ x y hf.1 hf.2]

/-- A concrete matching from the exceptional coordinate outputs to group-law outputs. -/
def fig14CorrectionPairs {x₂ y₂ : Fp} (hC : curve.toAffine.Nonsingular x₂ y₂) :
    List ((Bool × (Fp × Fp)) × (Bool × (Fp × Fp))) :=
  (fig14ExceptionalList (.some hC)).map (fun P =>
    (fig14EncodedEquiv x₂ y₂ (fig14PointEncoding P),fig14PointEncoding (P+(.some hC))))
/-- Ordered transpositions correcting all exceptional points, including infinity. -/
def fig14CorrectionSwaps {x₂ y₂ : Fp} (hC : curve.toAffine.Nonsingular x₂ y₂) :=
  finiteMatchingSwaps (fig14CorrectionPairs hC)

theorem fig14CorrectionSwaps_length {x₂ y₂ : Fp} (hC : curve.toAffine.Nonsingular x₂ y₂) :
    (fig14CorrectionSwaps hC).length≤4 := by
  rw [fig14CorrectionSwaps,finiteMatchingSwaps_length,fig14CorrectionPairs,List.length_map]
  exact fig14ExceptionalList_length _
/-- The explicit sequence of at most four transpositions makes the encoded
coordinate permutation agree with total addition by every finite constant point. -/
theorem fig14CorrectionSwaps_correct {x₂ y₂ : Fp} (hC : curve.toAffine.Nonsingular x₂ y₂)
    (P : Secp256k1.Point) :
    runFiniteSwaps (fig14CorrectionSwaps hC)
      (fig14EncodedEquiv x₂ y₂ (fig14PointEncoding P))=fig14PointEncoding (P+(.some hC)) := by
  rw [fig14CorrectionSwaps,finiteMatchingSwaps_apply]
  apply finiteMatchingPermutation_comp
    (fun Q => fig14EncodedEquiv x₂ y₂ (fig14PointEncoding Q))
    (fun Q => fig14PointEncoding (Q+(.some hC)))
    (fig14ExceptionalList (.some hC)) (List.nodup_dedup _)
  · exact (fig14EncodedEquiv x₂ y₂).injective.comp fig14PointEncoding_injective
  · intro Q R h
    exact add_right_cancel (fig14PointEncoding_injective h)
  · intro Q hQ
    exact fig14EncodedEquiv_nonexceptional hC Q (by simpa only [fig14ExceptionalList_mem] using hQ)
end ShorECDLP.Paper2607_13816
