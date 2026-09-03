import ShorECDLP.Submission.Naive.EllipticCurve.Secp256k1
import ShorECDLP.Submission.Naive.OrderFinding.OracleSpec

/-
# Canonical secp256k1 point encoding (M2, representation layer)

This module gives the abstract secp256k1 point type one injective 513-bit representation. Registers
are little-endian throughout the submission, so bit 0 is the finite-point tag, bits 1--256 hold the
canonical representative of `x`, and bits 257--512 hold the canonical representative of `y`:

```text
O       ↦ 0
(x, y)  ↦ 1 + 2*x + 2^257*y.
```

The `ZMod p` representatives are already canonical in `[0, p)`, and `p < 2^256`, so every affine
point fits. Injectivity is the load-bearing property for order finding: two encoded basis labels
collide exactly when their mathematical points do.

`ValidCode` also characterizes that range directly from the raw fields: the all-zero word is the
unique infinity code, while a tagged affine word must contain coordinates strictly below `p` and
satisfy the curve's nonsingularity predicate. In particular, out-of-range coordinates are rejected,
not silently reduced modulo `p`.

This file deliberately defines no point-add circuit, decoder, or projective representation. The
later refinement layer must implement total translation on the valid-code subspace and remain
globally reversible on all basis states.
-/

namespace ShorECDLP
namespace Secp256k1

/-- One finite-point tag bit followed by two 256-bit affine coordinates. -/
def pointWidth : Nat := 513

private instance : NeZero p := ⟨by norm_num [p]⟩

private theorem p_lt_coordinateCapacity : p < 2 ^ 256 := by
  norm_num [p]

/-- The natural-number value of the canonical little-endian point representation. -/
def encodeNat : Point → Nat
  | .zero => 0
  | @WeierstrassCurve.Affine.Point.some _ _ _ x y _ =>
      1 + 2 * x.val + 2 ^ 257 * y.val

@[simp]
theorem encodeNat_zero : encodeNat (0 : Point) = 0 :=
  rfl

@[simp]
theorem encodeNat_some {x y : Fp} (h : curve.toAffine.Nonsingular x y) :
    encodeNat (.some h) = 1 + 2 * x.val + 2 ^ 257 * y.val :=
  rfl

/-- Every canonical point representation fits in exactly 513 bits. -/
theorem encodeNat_lt (P : Point) : encodeNat P < 2 ^ pointWidth := by
  cases P with
  | zero => norm_num [encodeNat, pointWidth]
  | @some x y h =>
      have hx : x.val < 2 ^ 256 := x.val_lt.trans p_lt_coordinateCapacity
      have hy : y.val < 2 ^ 256 := y.val_lt.trans p_lt_coordinateCapacity
      simp only [encodeNat, pointWidth]
      omega

/-- The canonical 513-bit encoding of a secp256k1 point. -/
def encode (P : Point) : Fin (2 ^ pointWidth) :=
  ⟨encodeNat P, encodeNat_lt P⟩

@[simp]
theorem encode_val (P : Point) : (encode P).val = encodeNat P :=
  rfl

/-- Read the least-significant finite-point tag from a raw point code. -/
def finiteFlag (c : Fin (2 ^ pointWidth)) : Nat :=
  c.val % 2

/-- Read the 256-bit `x` payload from a raw point code. -/
def xBits (c : Fin (2 ^ pointWidth)) : Nat :=
  (c.val / 2) % (2 ^ 256)

/-- Read the 256-bit `y` payload from a raw point code. -/
def yBits (c : Fin (2 ^ pointWidth)) : Nat :=
  (c.val / 2) / (2 ^ 256)

/-- A raw 513-bit word is canonical exactly when it is the all-zero infinity code, or it has a
finite tag, canonical field representatives, and valid affine coordinates. -/
def ValidCode (c : Fin (2 ^ pointWidth)) : Prop :=
  c.val = 0 ∨
    finiteFlag c = 1 ∧
    xBits c < p ∧
    yBits c < p ∧
    curve.toAffine.Nonsingular (xBits c : Fp) (yBits c : Fp)

@[simp]
theorem finiteFlag_encode_zero : finiteFlag (encode 0) = 0 :=
  rfl

@[simp]
theorem finiteFlag_encode_some {x y : Fp} (h : curve.toAffine.Nonsingular x y) :
    finiteFlag (encode (.some h)) = 1 := by
  simp only [finiteFlag, encode, encodeNat]
  omega

@[simp]
theorem xBits_encode_some {x y : Fp} (h : curve.toAffine.Nonsingular x y) :
    xBits (encode (.some h)) = x.val := by
  have hx : x.val < 2 ^ 256 := x.val_lt.trans p_lt_coordinateCapacity
  simp only [xBits, encode, encodeNat]
  omega

@[simp]
theorem yBits_encode_some {x y : Fp} (h : curve.toAffine.Nonsingular x y) :
    yBits (encode (.some h)) = y.val := by
  have hx : x.val < 2 ^ 256 := x.val_lt.trans p_lt_coordinateCapacity
  simp only [yBits, encode, encodeNat]
  omega

/-- Canonical affine coordinates and the infinity tag make the point encoding injective. -/
theorem encode_injective : Function.Injective encode := by
  intro P Q hPQ
  have hcode : encodeNat P = encodeNat Q := congrArg Fin.val hPQ
  cases P with
  | zero =>
      cases Q with
      | zero => rfl
      | @some x y h =>
          simp only [encodeNat] at hcode
          omega
  | @some x y hP =>
      cases Q with
      | zero =>
          simp only [encodeNat] at hcode
          omega
      | @some x' y' hQ =>
          have hx : x.val < 2 ^ 256 := x.val_lt.trans p_lt_coordinateCapacity
          have hy : y.val < 2 ^ 256 := y.val_lt.trans p_lt_coordinateCapacity
          have hx' : x'.val < 2 ^ 256 := x'.val_lt.trans p_lt_coordinateCapacity
          have hy' : y'.val < 2 ^ 256 := y'.val_lt.trans p_lt_coordinateCapacity
          simp only [encodeNat] at hcode
          have h_xval : x.val = x'.val := by omega
          have h_yval : y.val = y'.val := by omega
          have h_x : x = x' := ZMod.val_injective p h_xval
          have h_y : y = y' := ZMod.val_injective p h_yval
          subst x'
          subst y'
          rfl

@[simp]
theorem encode_inj (P Q : Point) : encode P = encode Q ↔ P = Q := by
  constructor
  · intro h
    exact encode_injective h
  · rintro rfl
    rfl

/-- The raw validity predicate is exactly the range of the canonical point encoding. -/
theorem validCode_iff_exists_point (c : Fin (2 ^ pointWidth)) :
    ValidCode c ↔ ∃ P : Point, encode P = c := by
  constructor
  · intro hc
    rcases hc with hzero | ⟨htag, hx, hy, hcurve⟩
    · refine ⟨0, Fin.ext ?_⟩
      simpa only [encode, encodeNat] using hzero.symm
    · let x : Fp := (xBits c : Nat)
      let y : Fp := (yBits c : Nat)
      have hxval : x.val = xBits c := ZMod.val_natCast_of_lt hx
      have hyval : y.val = yBits c := ZMod.val_natCast_of_lt hy
      have hxy : curve.toAffine.Nonsingular x y := by
        simpa only [x, y] using hcurve
      refine ⟨.some hxy, Fin.ext ?_⟩
      simp only [encode, encodeNat, hxval, hyval]
      have hsplit0 := Nat.mod_add_div c.val 2
      have hsplit1 := Nat.mod_add_div (c.val / 2) (2 ^ 256)
      simp only [finiteFlag] at htag
      simp only [xBits, yBits]
      omega
  · rintro ⟨P, rfl⟩
    cases P with
    | zero => exact Or.inl rfl
    | @some x y h =>
        refine Or.inr ⟨finiteFlag_encode_some h, ?_, ?_, ?_⟩
        · simpa using x.val_lt
        · simpa using y.val_lt
        · simpa using h

/-- The concrete encoding package consumed by the implementation-independent oracle contract. -/
def pointEncoding : PointEncoding Point pointWidth where
  encode := encode
  injective := encode_injective

@[simp]
theorem pointEncoding_encode_val (P : Point) :
    (pointEncoding.encode P).val = encodeNat P :=
  rfl

end Secp256k1
end ShorECDLP
