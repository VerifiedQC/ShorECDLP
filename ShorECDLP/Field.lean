import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic

/-
# secp256k1 base field and Fermat inversion (M1, spec layer)

This is the *mathematical* backbone of M1: the secp256k1 domain parameters and the
correctness statement for **Fermat inversion**, `a⁻¹ = a^(p-2) mod p`. The reversible
modular-exponentiation *circuit* built in the next M1 step implements this function, and
its correctness proof will discharge against `fermat_inv` here — so the circuit's
`correct` obligation and the mathematics it is judged against live in one place.

## Disclosure (validity condition, per the launch checklist)

Primality of the secp256k1 field prime `p` is a standard published fact carried here as a
hypothesis `[Fact (Nat.Prime p)]`, not machine-checked in this version (a Pratt/Lucas
certificate can discharge it later). It is a hypothesis, not an axiom — every theorem that
uses it says so in its signature, so the trusted surface stays visible.
-/

namespace ShorECDLP

/-- The secp256k1 base-field prime `p = 2^256 − 2^32 − 977`. -/
def p : ℕ := 2 ^ 256 - 2 ^ 32 - 977

/-- The secp256k1 group order `n` (number of points on the curve). -/
def order : ℕ :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- secp256k1 short-Weierstrass coefficient `a = 0` (curve `y² = x³ + 7`). -/
def curveA : ℕ := 0

/-- secp256k1 short-Weierstrass coefficient `b = 7`. -/
def curveB : ℕ := 7

/-- The secp256k1 base field `F_p`. It is a field exactly when `p` is prime, which we
carry as an instance hypothesis `[Fact (Nat.Prime p)]`. -/
abbrev Fp := ZMod p

/-- **Fermat inversion is correct.** For the prime field `F_p` and any nonzero `x`,
`x^(p-2)` is the field inverse `x⁻¹`. This is the correctness target the Fermat-inversion
circuit is judged against in the next M1 step. -/
theorem fermat_inv [Fact (Nat.Prime p)] (x : Fp) (hx : x ≠ 0) :
    x ^ (p - 2) = x⁻¹ := by
  have hp2 : 2 ≤ p := (Fact.out (p := Nat.Prime p)).two_le
  have h1 : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx
  have hmul : x * x ^ (p - 2) = 1 := by
    calc x * x ^ (p - 2)
        = x ^ (p - 2 + 1) := (pow_succ' x (p - 2)).symm
      _ = x ^ (p - 1)     := by rw [show p - 2 + 1 = p - 1 by omega]
      _ = 1               := h1
  exact (inv_eq_of_mul_eq_one_right hmul).symm

end ShorECDLP
