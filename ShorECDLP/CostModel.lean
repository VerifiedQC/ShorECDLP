import ShorECDLP.InstructionSet

/-
# Cost model (M0 skeleton)

Primary unit = **Toffoli**; T-count is a derived quantity (the Toffoli→T conversion
constant is pinned in a later milestone). In the Toffoli-count metric the Clifford
gates (X, H, CNOT) are free and only Toffolis are charged — so `gateCount` below
counts exactly the Toffolis of a constructed circuit.

## Disclosure (this is the cost-model *statement* — read the number through it)

The end-to-end resource number this model reports is for the **simplest, un-optimized**
ShorECDLP construction over **secp256k1**, and specifically:

  - **generic modular reduction** — NOT specialized to the pseudo-Mersenne prime
    `p = 2^256 − 2^32 − 977`; the count is generic-prime grade;
  - **Fermat inversion** `a^(p−2) mod p` — reuses modular exponentiation, not the
    Toffoli-optimal inversion;
  - **un-windowed double-and-add** scalar multiplication (2n sequential point adds).

It is therefore a generic-prime-grade, end-to-end count and is not directly comparable
to pseudo-Mersenne-specialized or windowed estimates. Each such specialization is a
future submission, not a defect of this one.
-/

namespace ShorECDLP

/-- Toffoli-caliber cost of a single primitive gate: Cliffords are free, Toffoli costs 1. -/
def toffoliCost : Gate → Nat
  | .X _       => 0
  | .H _       => 0
  | .CX _ _    => 0
  | .CCX _ _ _ => 1

/-- Toffoli count of a circuit. This is the quantity every `gateCount ≤ bound`
theorem in M1–M5 is stated about — always about the *same* constructed circuit that
the correctness proof is about (the same-`prog`-term discipline). -/
def gateCount (c : Circuit) : Nat := (c.map toffoliCost).sum

@[simp] theorem gateCount_nil : gateCount [] = 0 := rfl

@[simp] theorem gateCount_cons (g : Gate) (c : Circuit) :
    gateCount (g :: c) = toffoliCost g + gateCount c := rfl

theorem gateCount_append (c₁ c₂ : Circuit) :
    gateCount (c₁ ++ c₂) = gateCount c₁ + gateCount c₂ := by
  induction c₁ with
  | nil => simp
  | cons g c ih => simp [ih, Nat.add_assoc]

end ShorECDLP
