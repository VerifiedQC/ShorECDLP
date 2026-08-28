import ShorECDLP.Framework.InstructionSet
import Mathlib.Data.List.Defs

/-
# Resource model — framework layer (curve- and construction-agnostic)

A circuit's static qubit count is the number of distinct wire labels touched by
its gates.  The time metric is a **naive, simple T-count**: Cliffords `{X, H, CX}`
are free, a Toffoli `CCX` costs 7
(the standard unitary Toffoli), and either direction of a phase rotation `P` costs 1.
`tCount` sums this over a circuit.

This is deliberately the *simple baseline*. A submission that wants a different or tighter
count (a 4-T Toffoli under measurement, an exact rotation-synthesis cost, a separate Toffoli
tally, …) proves that as its own theorem submission-side; the framework does not bake it in.

The measures are **construction-agnostic**: they make no claim about which curve, reduction,
inversion, or QFT a submission used. Those are submission choices, and the note explaining
how to read a particular number lives **submission-side** beside the constants it describes
(see `ShorECDLP/Submission/`). Keeping `framework/` disclosure-free keeps this a small audited
base that can judge any submission.
-/

namespace ShorECDLP

/-- All wires read or written by a primitive gate. -/
def gateWires : Gate → List Wire
  | .X t       => [t]
  | .H t       => [t]
  | .CX c t    => [c, t]
  | .CCX a b t => [a, b, t]
  | .P _ _ t   => [t]

/-- The (not necessarily duplicate-free) support of a circuit. -/
def circuitWires (c : Circuit) : List Wire := c.flatMap gateWires

/-- Number of distinct qubit wires touched by a static circuit. -/
def qubitCount (c : Circuit) : Nat := (circuitWires c).dedup.length

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
