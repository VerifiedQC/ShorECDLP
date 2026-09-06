import ShorECDLP.Math.BitcoinCurve
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic

/-
# secp256k1 base field and Fermat inversion

This shared mathematical file states the correctness target for **Fermat inversion**,
`a⁻¹ = a^(p-2) mod p`, over Bitcoin's fixed base field. Submission-specific reversible
circuits can discharge their correctness obligations against `fermat_inv` without introducing
a dependency from the mathematical layer back to either implementation.

## Scope

  - **Constants are secp256k1-specific**: the shared problem specification fixes `p`,
    `a = 0`, `b = 7`, and
    `order` as part of the Bitcoin problem;
    **the modular reduction is the generic prime algorithm and does not exploit the
    pseudo-Mersenne structure of `p = 2^256 − 2^32 − 977`.** (Seeing the literal prime in
    the source must not be read as a pseudo-Mersenne speedup.)
  - **Primality of `p`** is machine-checked by the Lucas/Pratt-style certificate in
    `EllipticCurve/GeneratorOrder`.  This generic Fermat theorem keeps the minimal
    `[Fact (Nat.Prime p)]` hypothesis in its signature; concrete declarations instantiate it
    locally from that certificate, without exporting a global instance.

Algorithm and resource disclosures belong beside the submission-specific circuits that use this
shared theorem.
-/

namespace ShorECDLP

/-- **Fermat inversion is correct.** For the prime field `F_p` and any nonzero `x`,
`x^(p-2)` is the field inverse `x⁻¹`. This is the shared correctness target against which a
submission can verify its Fermat-inversion circuit. -/
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
