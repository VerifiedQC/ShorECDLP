import ShorECDLP.Math.PhaseApproximation
import Mathlib.Analysis.Fourier.ZMod
namespace ShorECDLP.Quantum.OrderFinding
open PhaseEstimation
open scoped BigOperators
 theorem eigenvalue_add
    (x y : ℝ) :
    eigenvalue (x + y) =
      eigenvalue x * eigenvalue y := by
  unfold eigenvalue
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

 theorem eigenvalue_neg
    (x : ℝ) :
    eigenvalue (-x) = (eigenvalue x)⁻¹ := by
  unfold eigenvalue
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

 theorem star_eigenvalue
    (x : ℝ) :
    starRingEnd ℂ (eigenvalue x) =
      eigenvalue (-x) := by
  unfold eigenvalue
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.ext_iff]

 theorem eigenvalue_int_div_eq_stdAddChar
    {r : ℕ}
    [NeZero r]
    (z : ℤ) :
    eigenvalue ((z : ℝ) / (r : ℝ)) =
      ZMod.stdAddChar (z : ZMod r) := by
  rw [ZMod.stdAddChar_coe]
  unfold eigenvalue
  congr 1
  push_cast
  ring

 theorem sum_stdAddChar_mul
    {r : ℕ}
    [NeZero r]
    (t : ZMod r) :
    (∑ j : ZMod r, ZMod.stdAddChar (t * j)) =
      if t = 0 then (r : ℂ) else 0 := by
  by_cases ht : t = 0
  · simp only [ht, if_true, zero_mul, AddChar.map_zero_eq_one,
      Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  · simp only [if_neg ht]
    exact
      AddChar.sum_eq_zero_of_ne_one
        (ZMod.isPrimitive_stdAddChar r ht)

 theorem character_sum
    {r : ℕ}
    (hr : Nat.Prime r)
    (k l : Fin r) :
    (∑ j : Fin r,
        starRingEnd ℂ
            (eigenvalue
              (-((k.val * j.val : ℕ) : ℝ) / (r : ℝ))) *
          eigenvalue
            (-((l.val * j.val : ℕ) : ℝ) / (r : ℝ))) =
      if k = l then (r : ℂ) else 0 := by
  have hr0 : 0 < r := hr.pos
  letI : NeZero r := ⟨Nat.ne_of_gt hr0⟩
  have hterm :
      ∀ j : Fin r,
        starRingEnd ℂ
            (eigenvalue
              (-((k.val * j.val : ℕ) : ℝ) / (r : ℝ))) *
          eigenvalue
            (-((l.val * j.val : ℕ) : ℝ) / (r : ℝ)) =
        ZMod.stdAddChar
          (((k.val : ZMod r) - (l.val : ZMod r)) * (j.val : ZMod r)) := by
    intro j
    rw [star_eigenvalue]
    rw [← eigenvalue_add]
    calc
      eigenvalue
          (-(-↑(k.val * j.val : ℕ) / ↑r) +
            -↑(l.val * j.val : ℕ) / ↑r) =
        eigenvalue ((((k.val : ℤ) - (l.val : ℤ)) * (j.val : ℤ) : ℤ) /
            (r : ℝ)) := by
          congr 1
          push_cast
          ring
      _ = ZMod.stdAddChar
          (((((k.val : ℤ) - (l.val : ℤ)) * (j.val : ℤ) : ℤ) : ZMod r)) := by
          rw [eigenvalue_int_div_eq_stdAddChar]
      _ = ZMod.stdAddChar
          (((k.val : ZMod r) - (l.val : ZMod r)) * (j.val : ZMod r)) := by
          congr 1
          push_cast
          ring
  simp_rw [hterm]
  rw [Fintype.sum_equiv (ZMod.finEquiv r).toEquiv]
  · have h :=
      sum_stdAddChar_mul
        ((k.val : ZMod r) - (l.val : ZMod r))
    rw [h]
    by_cases hkl : k = l
    · subst l
      simp
    · have hne :
        (k.val : ZMod r) - (l.val : ZMod r) ≠ 0 := by
        intro hz
        have hz' :
            (k.val : ZMod r) = (l.val : ZMod r) := sub_eq_zero.mp hz
        have hklt := k.isLt
        have hllt := l.isLt
        have hv :
            k.val = l.val := by
          rw [ZMod.natCast_eq_natCast_iff'] at hz'
          simpa [Nat.mod_eq_of_lt hklt, Nat.mod_eq_of_lt hllt] using hz'
        exact hkl (Fin.ext hv)
      simp [hkl, hne]
  · intro j
    have hjcast :
        (j.val : ZMod r) = (ZMod.finEquiv r).toEquiv j := by
      apply ZMod.val_injective r
      cases r with
      | zero => exact False.elim (Nat.not_lt_zero _ j.isLt)
      | succ n =>
          cases j with
          | mk val hlt =>
              simp [ZMod.finEquiv, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
              change val = val
              rfl
    rw [hjcast]

 theorem character_sum_zero_index
    {r : ℕ}
    (hr : Nat.Prime r)
    (j : Fin r) :
    (∑ k : Fin r,
        eigenvalue
          (-((k.val * j.val : ℕ) : ℝ) / (r : ℝ))) =
      if j.val = 0 then (r : ℂ) else 0 := by
  have hr0 : 0 < r := hr.pos
  letI : NeZero r := ⟨Nat.ne_of_gt hr0⟩
  have hterm :
      ∀ k : Fin r,
        eigenvalue
            (-((k.val * j.val : ℕ) : ℝ) / (r : ℝ)) =
          ZMod.stdAddChar
            (-((j.val : ZMod r) * (k.val : ZMod r))) := by
    intro k
    calc
      eigenvalue (-↑(k.val * j.val : ℕ) / ↑r) =
        eigenvalue ((-((k.val : ℤ) * (j.val : ℤ)) : ℤ) / (r : ℝ)) := by
          congr 1
          push_cast
          ring
      _ = ZMod.stdAddChar
          (((-((k.val : ℤ) * (j.val : ℤ)) : ℤ) : ZMod r)) := by
          rw [eigenvalue_int_div_eq_stdAddChar]
      _ = ZMod.stdAddChar
          (-((j.val : ZMod r) * (k.val : ZMod r))) := by
          congr 1
          push_cast
          ring
  simp_rw [hterm]
  rw [Fintype.sum_equiv (ZMod.finEquiv r).toEquiv]
  · have h :=
      sum_stdAddChar_mul
        (-(j.val : ZMod r))
    rw [h]
    by_cases hj : j.val = 0
    · simp [hj]
    · have hjz :
        -(j.val : ZMod r) ≠ 0 := by
        intro hz
        have hz' : (j.val : ZMod r) = 0 := by
          simpa using neg_eq_zero.mp hz
        have :
            j.val % r = 0 := by
          rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff'] at hz'
          simpa using hz'
        have hval : j.val = 0 := by
          simpa [Nat.mod_eq_of_lt j.isLt] using this
        exact hj hval
      simp [hj, hjz]
  · intro k
    have hkcast :
        (k.val : ZMod r) = (ZMod.finEquiv r).toEquiv k := by
      apply ZMod.val_injective r
      cases r with
      | zero => exact False.elim (Nat.not_lt_zero _ k.isLt)
      | succ n =>
          cases k with
          | mk val hlt =>
              simp [ZMod.finEquiv, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
              change val = val
              rfl
    rw [hkcast]
    rw [neg_mul]


end ShorECDLP.Quantum.OrderFinding
