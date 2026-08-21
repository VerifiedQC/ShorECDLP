import ShorECDLP.Framework.InstructionSet

/-
# Cost model — framework layer (curve- and construction-agnostic)

Primary unit = **Toffoli**; T-count is a derived quantity (the Toffoli→T conversion
constant is pinned in a later milestone). In the Toffoli-count metric the Clifford
gates (X, H, CNOT) are free and only Toffolis are charged — so `gateCount` below
counts exactly the Toffolis of a constructed circuit.

This model is deliberately **construction-agnostic**: it makes no claim about which
curve, reduction, inversion, or QFT a submission used. Those are the submission's
choices, and the note explaining how to read a particular number lives **submission-side**
beside the constants it describes (see `ShorECDLP/Submission/`). Keeping `framework/`
disclosure-free keeps this a small audited base that can judge any submission.
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
