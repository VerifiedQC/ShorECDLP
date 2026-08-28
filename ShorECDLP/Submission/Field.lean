import ShorECDLP.Framework.BitcoinCurve
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic

/-
# secp256k1 base field and Fermat inversion (M1, spec layer)

This file states the submission's correctness target for **Fermat inversion**,
`a⁻¹ = a^(p-2) mod p`, over the Framework's fixed Bitcoin base field. The reversible
modular-exponentiation *circuit* built in the next M1 step implements this function, and
its correctness proof will discharge against `fermat_inv` here — so the circuit's
`correct` obligation and the mathematics it is judged against live in one place.

## Submission-side disclosure (how to read this submission's number)

Disclosures live here, beside the constants they describe — never in `framework/`, whose
cost model is construction-agnostic. They document algorithm choices (not machine-checked
theorems); a future optimized submission carries a different list against the same framework.

  - **Constants are secp256k1-specific**: the Framework fixes `p`, `a = 0`, `b = 7`, and
    `order` as part of the Bitcoin problem;
    **the modular reduction is the generic prime algorithm and does not exploit the
    pseudo-Mersenne structure of `p = 2^256 − 2^32 − 977`.** (Seeing the literal prime in
    the source must not be read as a pseudo-Mersenne speedup.)
  - **Primality of `p`** is machine-checked by the Lucas/Pratt-style certificate in
    `EllipticCurve/GeneratorOrder`.  This generic Fermat theorem keeps the minimal
    `[Fact (Nat.Prime p)]` hypothesis in its signature; concrete secp256k1 declarations
    instantiate it locally from that certificate, without exporting a global instance.

Further items attach to the modules they describe as those land (Fermat inversion →
`Arithmetic/ModExp`, un-windowed double-and-add → `Arithmetic/ScalarMul`, coherent-QFT
`+2n` qubits vs the semiclassical baseline → `Submission/QFT`), and are consolidated into the
submission's reading-guide at M5.
-/

namespace ShorECDLP

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
