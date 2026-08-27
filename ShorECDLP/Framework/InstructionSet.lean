/-
# Instruction set (M0 skeleton)

The primitive gate set over which every ShorECDLP circuit is built. M0 seeds only
the basic gates; the controlled modular-arithmetic building blocks (modular
multiplication, Fermat inversion, elliptic-curve point addition) are layered on top
in M1–M2 as *derived* circuits over this set, never as new primitives — so the cost
model has a single, small trusted surface to count against.
-/

namespace ShorECDLP

/-- A qubit / wire index. -/
abbrev Wire := Nat

/-- Direction of a dyadic phase rotation. The two constructors are mutual
adjoints, so the primitive gate set is closed under circuit adjoint. -/
inductive PhaseDir where
  | forward
  | inverse
  deriving Repr, DecidableEq

/-- Reverse the direction of a phase rotation. -/
@[simp]
def PhaseDir.adjoint : PhaseDir → PhaseDir
  | .forward => .inverse
  | .inverse => .forward

@[simp]
theorem PhaseDir.adjoint_adjoint (dir : PhaseDir) :
    dir.adjoint.adjoint = dir := by
  cases dir <;> rfl

/-- The primitive gate set. The Clifford/Toffoli gates `{X, H, CX, CCX}` express all
reversible arithmetic; `P` supplies the phases the QFT needs (none of the other four can
produce a non-trivial phase). Higher-level operations are expressed as `List Gate` circuits
over these, so the T-count cost model (see `CostModel`) counts exactly the constructed
circuit. -/
inductive Gate where
  /-- Pauli-X (logical NOT) on `target`. -/
  | X    (target : Wire)
  /-- Hadamard on `target`. -/
  | H    (target : Wire)
  /-- Controlled-NOT: flips `target` when `control` is set. -/
  | CX   (control target : Wire)
  /-- Toffoli (CCX): flips `target` when both `c1` and `c2` are set. -/
  | CCX  (c1 c2 target : Wire)
  /-- Phase rotation on `target` by the signed dyadic angle `±2π / 2^k`
  (`forward` uses `+`, `inverse` uses `-`; `k=1,2,3` give `Z`, `S`/`S†`,
  and `T`/`T†`). These are exactly the angles the QFT and inverse QFT use. -/
  | P    (dir : PhaseDir) (k : Nat) (target : Wire)
  deriving Repr, DecidableEq

/-- The primitive-gate adjoint. Classical gates and `H` are self-adjoint;
phase rotations reverse direction. -/
@[simp]
def Gate.adjoint : Gate → Gate
  | .X t       => .X t
  | .H t       => .H t
  | .CX c t    => .CX c t
  | .CCX a b t => .CCX a b t
  | .P dir k t => .P dir.adjoint k t

@[simp]
theorem Gate.adjoint_adjoint (g : Gate) :
    g.adjoint.adjoint = g := by
  cases g with
  | X t => rfl
  | H t => rfl
  | CX c t => rfl
  | CCX a b t => rfl
  | P dir k t => cases dir <;> rfl

/-- A circuit is a straight-line list of primitive gates. -/
abbrev Circuit := List Gate

/-! ## Step-by-step program syntax

`circuit! { ... }` is term syntax for composing circuits in execution order.  Each
ordinary step is already a `Circuit`, so a complete subprogram can be nested directly.  A
`gate!` step embeds one primitive gate.  The term macro emits only the existing list constructors
and left-associated appends; it introduces no second program representation.

```lean
circuit! {
  gate! Gate.X flag;
  prepare;
  body;
  prepare.reverse
}
```
-/

declare_syntax_cat circuitProgramStep
syntax "gate!" term : circuitProgramStep
syntax term : circuitProgramStep

syntax (name := circuitProgramSeq)
  "circuit!" "{" circuitProgramStep (";" circuitProgramStep)* "}" : term
syntax (name := circuitProgramNil) "circuit!" "{" "}" : term

namespace CircuitSyntax

open Lean

private abbrev ParsedStep := Bool × Term

private meta def parseStep : TSyntax `circuitProgramStep → MacroM ParsedStep
  | `(circuitProgramStep| gate! $g:term) => pure (true, g)
  | `(circuitProgramStep| $nested:term) => pure (false, nested)
  | _ => Macro.throwUnsupported

private def takeGates : List ParsedStep → List Term × List ParsedStep
  | (true, g) :: rest =>
      let (gates, tail) := takeGates rest
      (g :: gates, tail)
  | rest => ([], rest)

private meta def gatesTerm (gates : List Term) : MacroM Term := do
  let gates := gates.toArray
  `([$gates,*])

private meta def consGates (gates : List Term) (tail : Term) : MacroM Term :=
  match gates with
  | [] => pure tail
  | g :: gates => do
      let rest ← consGates gates tail
      `($g :: $rest)

private partial def appendSteps (acc : Term) : List ParsedStep → MacroM Term
  | [] => pure acc
  | (false, nested) :: rest => do
      let acc ← `($acc ++ $nested)
      appendSteps acc rest
  | steps@((true, _) :: _) => do
      let (gates, rest) := takeGates steps
      let gateBlock ← gatesTerm gates
      let acc ← `($acc ++ $gateBlock)
      appendSteps acc rest

private meta def lowerSteps : List ParsedStep → MacroM Term
  | [] => `([])
  | steps@((true, _) :: _) => do
      let (gates, rest) := takeGates steps
      match rest with
      | [] => gatesTerm gates
      | (false, nested) :: rest => do
          let acc ← consGates gates nested
          appendSteps acc rest
      | (true, _) :: _ => Macro.throwUnsupported
  | (false, nested) :: rest => appendSteps nested rest

end CircuitSyntax

macro_rules
  | `(circuit! { $head:circuitProgramStep $[; $tail:circuitProgramStep]* }) => do
      let mut steps := #[← CircuitSyntax.parseStep head]
      for step in tail do
        steps := steps.push (← CircuitSyntax.parseStep step)
      CircuitSyntax.lowerSteps steps.toList
  | `(circuit! { }) => `([])

example : (circuit! {}) = ([] : Circuit) := rfl

example (g h : Gate) : (circuit! { gate! g; gate! h }) = [g, h] := rfl

example (g : Gate) (nested : Circuit) :
    (circuit! { gate! g; nested }) = g :: nested := rfl

example (g h : Gate) :
    (circuit! { circuit! { gate! g }; gate! h }) = [g, h] := rfl

example (first middle last : Circuit) :
    (circuit! { first; middle; last }) = (first ++ middle) ++ last := rfl

/-- A primitive gate is physically well-formed when its distinct roles
are assigned to distinct wires. -/
def Gate.WellFormed : Gate → Prop
  | .X _       => True
  | .H _       => True
  | .CX c t    => c ≠ t
  | .CCX a b t => a ≠ b ∧ a ≠ t ∧ b ≠ t
  | .P _ _ _   => True

@[simp]
theorem Gate.wellFormed_adjoint (g : Gate) :
    g.adjoint.WellFormed ↔ g.WellFormed := by
  cases g <;> simp [Gate.WellFormed]

/-- Every primitive gate in the circuit is well-formed. -/
def CircuitWellFormed (c : Circuit) : Prop :=
  ∀ g ∈ c, g.WellFormed

@[simp]
theorem circuitWellFormed_nil :
    CircuitWellFormed [] := by
  simp [CircuitWellFormed]

@[simp]
theorem circuitWellFormed_cons (g : Gate) (c : Circuit) :
    CircuitWellFormed (g :: c) ↔
      g.WellFormed ∧ CircuitWellFormed c := by
  simp [CircuitWellFormed]

@[simp]
theorem circuitWellFormed_append (c₁ c₂ : Circuit) :
    CircuitWellFormed (c₁ ++ c₂) ↔
      CircuitWellFormed c₁ ∧ CircuitWellFormed c₂ := by
  simp [CircuitWellFormed]
  constructor
  · intro h
    constructor
    · intro g hg
      exact h g (Or.inl hg)
    · intro g hg
      exact h g (Or.inr hg)
  · intro h g hg
    cases hg with
    | inl hg₁ =>
        exact h.1 g hg₁
    | inr hg₂ =>
        exact h.2 g hg₂

/-- Reverse gate order and adjoint every primitive. -/
def Circuit.adjoint (c : Circuit) : Circuit :=
  c.reverse.map Gate.adjoint

@[simp]
theorem circuit_adjoint_nil :
    Circuit.adjoint [] = [] := rfl

@[simp]
theorem circuit_adjoint_cons (g : Gate) (c : Circuit) :
    Circuit.adjoint (g :: c) = Circuit.adjoint c ++ [g.adjoint] := by
  simp [Circuit.adjoint]

@[simp]
theorem circuit_adjoint_append (c₁ c₂ : Circuit) :
    Circuit.adjoint (c₁ ++ c₂) =
      Circuit.adjoint c₂ ++ Circuit.adjoint c₁ := by
  simp [Circuit.adjoint]

@[simp]
theorem circuit_adjoint_adjoint (c : Circuit) :
    Circuit.adjoint (Circuit.adjoint c) = c := by
  induction c with
  | nil => rfl
  | cons g c ih =>
      rw [circuit_adjoint_cons, circuit_adjoint_append,
        circuit_adjoint_cons, circuit_adjoint_nil,
        Gate.adjoint_adjoint, ih]
      rfl

@[simp]
theorem circuitWellFormed_adjoint (c : Circuit) :
    CircuitWellFormed (Circuit.adjoint c) ↔ CircuitWellFormed c := by
  induction c with
  | nil => simp
  | cons g c ih =>
      rw [circuit_adjoint_cons, circuitWellFormed_append, ih,
        circuitWellFormed_cons]
      simp only [circuitWellFormed_cons, circuitWellFormed_nil,
        and_true, Gate.wellFormed_adjoint]
      exact and_comm

end ShorECDLP
