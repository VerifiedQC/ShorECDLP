import ShorECDLP.Framework.InstructionSet

/-
# Cost model — framework layer (curve- and construction-agnostic)

A **naive, simple T-count**. Cliffords `{X, H, CX}` are free, a Toffoli `CCX` costs 7
(the standard unitary Toffoli), and either direction of a phase rotation `P` costs 1.
`tCount` sums this over a
circuit — the whole framework metric.

This is deliberately the *simple baseline*. A submission that wants a different or tighter
count (a 4-T Toffoli under measurement, an exact rotation-synthesis cost, a separate Toffoli
tally, …) proves that as its own theorem submission-side; the framework does not bake it in.

The model is **construction-agnostic**: it makes no claim about which curve, reduction,
inversion, or QFT a submission used. Those are submission choices, and the note explaining
how to read a particular number lives **submission-side** beside the constants it describes
(see `ShorECDLP/Submission/`). Keeping `framework/` disclosure-free keeps this a small audited
base that can judge any submission.
-/

namespace ShorECDLP

/-- Naive T-count of a single primitive gate: Cliffords free, Toffoli 7,
either direction of a phase rotation 1. -/
def tCost : Gate → Nat
  | .X _       => 0
  | .H _       => 0
  | .CX _ _    => 0
  | .CCX _ _ _ => 7
  | .P _ _ _   => 1

@[simp]
theorem tCost_adjoint (g : Gate) :
    tCost g.adjoint = tCost g := by
  cases g <;> rfl

/-- Naive T-count of a circuit. This is the quantity every `tCount ≤ bound` theorem in
M1–M5 is stated about — always about the *same* constructed circuit that the correctness
proof is about (the same-`program`-term discipline). -/
def tCount (c : Circuit) : Nat := (c.map tCost).sum

@[simp] theorem tCount_nil : tCount [] = 0 := rfl

@[simp] theorem tCount_cons (g : Gate) (c : Circuit) :
    tCount (g :: c) = tCost g + tCount c := rfl

theorem tCount_append (c₁ c₂ : Circuit) :
    tCount (c₁ ++ c₂) = tCount c₁ + tCount c₂ := by
  induction c₁ with
  | nil => simp
  | cons g c ih => simp [ih, Nat.add_assoc]

@[simp]
theorem tCount_adjoint (c : Circuit) :
    tCount (Circuit.adjoint c) = tCount c := by
  induction c with
  | nil => rfl
  | cons g c ih =>
      rw [circuit_adjoint_cons, tCount_append, ih]
      change tCount c + tCost g.adjoint = tCost g + tCount c
      rw [tCost_adjoint]
      exact Nat.add_comm _ _

end ShorECDLP
