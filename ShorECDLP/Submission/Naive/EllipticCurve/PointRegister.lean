import ShorECDLP.Submission.Naive.EllipticCurve.PointEncoding

/-!
# secp256k1 point-register slices

The public point register uses the 513-bit layout from `PointEncoding.lean`: one finite-point tag,
then 256 little-endian `x` bits, then 256 little-endian `y` bits.  This module exposes those
three slices and proves the facts needed to move a public coordinate into the 257-bit arithmetic
registers used by the field circuits.

No circuit is defined here.  In particular, `padCoordinate` appends a clean most-significant wire
to a 256-bit coordinate register; the later arithmetic layer chooses how to copy into that layout.
-/

namespace ShorECDLP.Secp256k1.PointRegister

/-- The one-bit finite/infinity tag at the low end of a point register. -/
def tag (pointReg : List Wire) : List Wire :=
  pointReg.take 1

/-- The 256-bit little-endian affine `x` slice. -/
def x (pointReg : List Wire) : List Wire :=
  (pointReg.drop 1).take 256

/-- The 256-bit little-endian affine `y` slice. -/
def y (pointReg : List Wire) : List Wire :=
  (pointReg.drop 257).take 256

/-- Add one clean most-significant wire to a 256-bit coordinate register. -/
def padCoordinate (coordinate : List Wire) (high : Wire) : List Wire :=
  coordinate ++ [high]

theorem tag_length (pointReg : List Wire) (hlen : pointReg.length = pointWidth) :
    (tag pointReg).length = 1 := by
  simp [tag, pointWidth, hlen]

theorem x_length (pointReg : List Wire) (hlen : pointReg.length = pointWidth) :
    (x pointReg).length = 256 := by
  simp [x, pointWidth, hlen]

theorem y_length (pointReg : List Wire) (hlen : pointReg.length = pointWidth) :
    (y pointReg).length = 256 := by
  simp [y, pointWidth, hlen]

theorem padCoordinate_length (coordinate : List Wire) (high : Wire)
    (hlen : coordinate.length = 256) :
    (padCoordinate coordinate high).length = 257 := by
  simp [padCoordinate, hlen]

/-- The three public slices reconstruct an exactly 513-bit point register. -/
theorem tag_x_y (pointReg : List Wire) (hlen : pointReg.length = pointWidth) :
    tag pointReg ++ x pointReg ++ y pointReg = pointReg := by
  have hyall : (pointReg.drop 257).take 256 = pointReg.drop 257 := by
    apply List.take_of_length_le
    simp [pointWidth, hlen]
  simp only [tag, x, y, hyall]
  rw [← List.take_add]
  exact List.take_append_drop 257 pointReg

/-- Duplicate-freedom of the public register transfers to its complete sliced layout. -/
theorem tag_x_y_nodup (pointReg : List Wire)
    (hlen : pointReg.length = pointWidth)
    (hnd : pointReg.Nodup) :
    (tag pointReg ++ x pointReg ++ y pointReg).Nodup := by
  rw [tag_x_y pointReg hlen]
  exact hnd

private theorem regValue_append (xs ys : List Wire) (s : BasisState) :
    regValue (xs ++ ys) s =
      regValue xs s + 2 ^ xs.length * regValue ys s := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.cons_append, regValue_cons, ih, List.length_cons, Nat.pow_succ]
      ring

/-- Reading the whole point register agrees with reading its tag, `x`, and `y` slices. -/
theorem regValue_decompose (pointReg : List Wire) (s : BasisState)
    (hlen : pointReg.length = pointWidth) :
    regValue pointReg s =
      regValue (tag pointReg) s +
        2 * regValue (x pointReg) s +
        2 ^ 257 * regValue (y pointReg) s := by
  calc
    regValue pointReg s =
        regValue (tag pointReg ++ x pointReg ++ y pointReg) s := by
      rw [tag_x_y pointReg hlen]
    _ = _ := by
      rw [regValue_append, regValue_append, List.length_append,
        tag_length pointReg hlen, x_length pointReg hlen]
      norm_num only [pow_one]

private theorem regValue_lt_two_pow (ws : List Wire) (s : BasisState) :
    regValue ws s < 2 ^ ws.length := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
      rw [regValue_cons, List.length_cons, Nat.pow_succ]
      by_cases h : s w <;> simp [h] <;> omega

private theorem coordinate_lt : p < 2 ^ 256 := by
  norm_num [p]

/-- A basis state holding a finite point exposes exactly its canonical affine coordinates. -/
theorem slices_of_regValue_some
    (pointReg : List Wire) (s : BasisState)
    {xCoordinate yCoordinate : Fp}
    (hcurve : curve.toAffine.Nonsingular xCoordinate yCoordinate)
    (hlen : pointReg.length = pointWidth)
    (hvalue : regValue pointReg s = encodeNat (.some hcurve)) :
    regValue (tag pointReg) s = 1 ∧
      regValue (x pointReg) s = xCoordinate.val ∧
      regValue (y pointReg) s = yCoordinate.val := by
  have hdecomp := regValue_decompose pointReg s hlen
  rw [hvalue, encodeNat_some hcurve] at hdecomp
  have htag := regValue_lt_two_pow (tag pointReg) s
  rw [tag_length pointReg hlen] at htag
  have hx := regValue_lt_two_pow (x pointReg) s
  rw [x_length pointReg hlen] at hx
  have hy := regValue_lt_two_pow (y pointReg) s
  rw [y_length pointReg hlen] at hy
  have hxCoordinate : xCoordinate.val < 2 ^ 256 :=
    xCoordinate.val_lt.trans coordinate_lt
  have hyCoordinate : yCoordinate.val < 2 ^ 256 :=
    yCoordinate.val_lt.trans coordinate_lt
  omega

/-- The canonical infinity code reads as zero in every public slice. -/
theorem slices_of_regValue_zero
    (pointReg : List Wire) (s : BasisState)
    (hlen : pointReg.length = pointWidth)
    (hvalue : regValue pointReg s = encodeNat (0 : Point)) :
    regValue (tag pointReg) s = 0 ∧
      regValue (x pointReg) s = 0 ∧
      regValue (y pointReg) s = 0 := by
  have hdecomp := regValue_decompose pointReg s hlen
  rw [hvalue, encodeNat_zero] at hdecomp
  omega

private theorem writeReg_not_mem
    (r : List Wire) (value : Nat) (s : BasisState)
    {i : Wire} (hi : i ∉ r) :
    writeReg r value s i = s i := by
  induction r generalizing value s with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.mem_cons, not_or] at hi
      simp only [writeReg]
      rw [ih (value := value / 2) (s := s[w ↦ value.testBit 0]) hi.2]
      exact upd_other s w _ hi.1

private theorem regValue_writeReg_of_lt
    (r : List Wire) (value : Nat) (s : BasisState)
    (hnd : r.Nodup)
    (hvalue : value < 2 ^ r.length) :
    regValue r (writeReg r value s) = value := by
  induction r generalizing value s with
  | nil =>
      simp only [List.length_nil, pow_zero] at hvalue
      have : value = 0 := by omega
      subst value
      rfl
  | cons w ws ih =>
      have hw : w ∉ ws := (List.nodup_cons.mp hnd).1
      have hws : ws.Nodup := (List.nodup_cons.mp hnd).2
      have hvalueTail : value / 2 < 2 ^ ws.length := by
        simpa only [List.length_cons, Nat.pow_succ] using
          (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mpr hvalue
      simp only [writeReg, regValue_cons]
      rw [writeReg_not_mem ws (value / 2) (s[w ↦ value.testBit 0]) hw]
      rw [upd_same]
      rw [ih (value := value / 2) (s := s[w ↦ value.testBit 0]) hws hvalueTail]
      rw [Nat.testBit_zero]
      have hmod : value % 2 < 2 := Nat.mod_lt _ (by omega)
      have hsplit := Nat.mod_add_div value 2
      by_cases hodd : value % 2 = 1
      · simp [hodd]
        omega
      · have heven : value % 2 = 0 := by omega
        simp [heven]
        omega

/-- Writing a canonical point code into an exact, duplicate-free point register reads back. -/
theorem regValue_write_encode
    (pointReg : List Wire) (P : Point) (s : BasisState)
    (hlen : pointReg.length = pointWidth)
    (hnd : pointReg.Nodup) :
    regValue pointReg (writeReg pointReg (encode P).val s) = encodeNat P := by
  apply regValue_writeReg_of_lt pointReg (encode P).val s hnd
  simpa only [hlen, encode_val] using encodeNat_lt P

/-- `writeReg` followed by public slicing recovers a finite point's tag and coordinates. -/
theorem slices_write_some
    (pointReg : List Wire) (s : BasisState)
    {xCoordinate yCoordinate : Fp}
    (hcurve : curve.toAffine.Nonsingular xCoordinate yCoordinate)
    (hlen : pointReg.length = pointWidth)
    (hnd : pointReg.Nodup) :
    let after := writeReg pointReg (encode (.some hcurve)).val s
    regValue (tag pointReg) after = 1 ∧
      regValue (x pointReg) after = xCoordinate.val ∧
      regValue (y pointReg) after = yCoordinate.val := by
  apply slices_of_regValue_some pointReg _ hcurve hlen
  exact regValue_write_encode pointReg (.some hcurve) s hlen hnd

/-- `writeReg` followed by public slicing recovers the all-zero infinity representation. -/
theorem slices_write_zero
    (pointReg : List Wire) (s : BasisState)
    (hlen : pointReg.length = pointWidth)
    (hnd : pointReg.Nodup) :
    let after := writeReg pointReg (encode (0 : Point)).val s
    regValue (tag pointReg) after = 0 ∧
      regValue (x pointReg) after = 0 ∧
      regValue (y pointReg) after = 0 := by
  apply slices_of_regValue_zero pointReg _ hlen
  exact regValue_write_encode pointReg 0 s hlen hnd

/-- A clean appended high wire changes the width from 256 to 257 without changing the value. -/
theorem regValue_padCoordinate_of_clean
    (coordinate : List Wire) (high : Wire) (s : BasisState)
    (hclean : Clean [high] s) :
    regValue (padCoordinate coordinate high) s = regValue coordinate s := by
  rw [padCoordinate, regValue_append]
  have hhigh : s high = false :=
    hclean high (List.mem_singleton_self high)
  simp only [regValue_cons, hhigh, Bool.false_eq_true, if_false, regValue_nil,
    mul_zero, add_zero]

/-- Freshness of the appended high wire preserves duplicate-freedom. -/
theorem padCoordinate_nodup
    (coordinate : List Wire) (high : Wire)
    (hnd : coordinate.Nodup)
    (hfresh : high ∉ coordinate) :
    (padCoordinate coordinate high).Nodup := by
  rw [padCoordinate, List.nodup_append]
  refine ⟨hnd, by simp, ?_⟩
  intro a ha b hb
  simp only [List.mem_singleton] at hb
  subst b
  intro hae
  subst a
  exact hfresh ha

end ShorECDLP.Secp256k1.PointRegister
