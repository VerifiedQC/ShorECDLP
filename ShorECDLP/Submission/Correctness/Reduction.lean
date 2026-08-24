import ShorECDLP.Submission.Field

/-
# Textbook hidden-subgroup reduction for secp256k1 ECDLP

This file isolates the pure number-theoretic core of the two-dimensional hidden-subgroup
reduction. Scalars live in the fixed Bitcoin group-order ring `ZMod order`. For a hidden shift
`k`, the textbook oracle exponent is `a + k * b`; translating `(a, b)` by a multiple of
`(-k, 1)` leaves that exponent unchanged. A frequency `(α, β)` annihilates this period exactly
when `β = k * α`, so a nonzero `α` recovers the shift as `β * α⁻¹` once the group order is
assumed prime.

This module deliberately does **not** claim ECDLP end-to-end correctness. It does not define
elliptic-curve point encodings or prove that a point-addition circuit implements
`[a]P + [b]Q = [a + k*b]P`; that bridge belongs to `ECDLPOracle` / `EndToEnd`. It also does not
claim that measurements from the implemented `2^m` QFT obey the exact annihilator equation;
the approximation and continued-fraction argument belongs to `SuccessBound`.
-/

namespace ShorECDLP
namespace Reduction

/-- Scalars modulo the fixed secp256k1 group order. -/
abbrev Scalar := ZMod order

/-- The exponent represented by the textbook ECDLP oracle input `(a, b)` for hidden shift
`k`: the eventual point oracle must justify `[a]P + [b]Q = [oracleExponent k (a,b)]P`. -/
def oracleExponent (k : Scalar) (input : Scalar × Scalar) : Scalar :=
  input.1 + k * input.2

/-- Generator `(-k, 1)` of the hidden period subgroup for shift `k`. -/
def periodGenerator (k : Scalar) : Scalar × Scalar := (-k, 1)

/-- Translate an oracle input by `t` times the hidden-period generator. -/
def shiftBy (k t : Scalar) (input : Scalar × Scalar) : Scalar × Scalar :=
  (input.1 + t * (periodGenerator k).1,
   input.2 + t * (periodGenerator k).2)

/-- Translating an input by any multiple of `(-k, 1)` leaves the oracle exponent unchanged. -/
theorem oracleExponent_shiftBy (k t : Scalar) (input : Scalar × Scalar) :
    oracleExponent k (shiftBy k t input) = oracleExponent k input := by
  simp [oracleExponent, shiftBy, periodGenerator]
  ring

/-- Bilinear pairing used to state membership in the annihilator of the hidden period. -/
def pairing (frequency period : Scalar × Scalar) : Scalar :=
  frequency.1 * period.1 + frequency.2 * period.2

/-- An ideal frequency annihilates the hidden-period generator. This is the exact algebraic
constraint; `SuccessBound` will later relate it to approximate `2^m`-QFT measurements. -/
def annihilatesPeriod (k : Scalar) (frequency : Scalar × Scalar) : Prop :=
  pairing frequency (periodGenerator k) = 0

/-- The annihilator equation for `(-k, 1)` is exactly `β = k * α`. No primality assumption is
needed: this is a ring identity in `ZMod order`. -/
theorem annihilatesPeriod_iff (k α β : Scalar) :
    annihilatesPeriod k (α, β) ↔ β = k * α := by
  simp only [annihilatesPeriod, pairing, periodGenerator, mul_one]
  constructor <;> intro h <;> linear_combination h

/-- Textbook recovery expression for a sampled frequency `(α, β)`. It is total as a ring
term; correctness requires `α ≠ 0`. -/
def recoverShift (α β : Scalar) : Scalar := β * α⁻¹

/-- A frequency annihilating `(-k, 1)` with nonzero `α` recovers the hidden shift `k`.
Primality of the fixed secp256k1 group order is carried as a visible instance hypothesis,
not introduced as an axiom. -/
theorem recoverShift_correct [Fact (Nat.Prime order)] (k α β : Scalar)
    (hfrequency : annihilatesPeriod k (α, β)) (hα : α ≠ 0) :
    recoverShift α β = k := by
  have hβ : β = k * α := (annihilatesPeriod_iff k α β).mp hfrequency
  calc
    recoverShift α β = (k * α) * α⁻¹ := by rw [recoverShift, hβ]
    _ = k * (α * α⁻¹) := by rw [mul_assoc]
    _ = k := by rw [mul_inv_cancel₀ hα, mul_one]

end Reduction
end ShorECDLP
