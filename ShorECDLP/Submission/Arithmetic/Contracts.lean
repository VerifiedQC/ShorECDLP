import ShorECDLP.Framework.Classical.Semantics
import ShorECDLP.Framework.CostModel

/-
# Clean out-of-place arithmetic contracts

This module is the narrow interface between the sequential M1 arithmetic implementations.
It lets a downstream circuit use an upstream operation without importing that operation's
private carry, reduction, or workspace layout.

Every operation is out-of-place: `lhs` and `rhs` are preserved, `out` starts clean and receives
the result, and all `work` wires start and finish clean. `CleanBinaryContract` packages the four
obligations that travel together for one concrete circuit term: functional correctness,
T-count, H/P-freedom, and physical well-formedness. Addition, multiplication, and exponentiation
are thin specializations of this one structure rather than copied interfaces.
-/

namespace ShorECDLP

/-- Public input/output registers and private workspace for a binary arithmetic circuit.
Registers are lists of wires in least-significant-first order. -/
structure RegisterLayout where
  lhs : List Wire
  rhs : List Wire
  out : List Wire
  work : List Wire

namespace RegisterLayout

/-- Every wire visible to, or reserved for, the operation. -/
def allWires (layout : RegisterLayout) : List Wire :=
  layout.lhs ++ layout.rhs ++ layout.out ++ layout.work

/-- A usable layout has equally wide public registers and no aliased wires anywhere in its
public or workspace registers. Workspace width is deliberately implementation-specific. -/
def Valid (layout : RegisterLayout) : Prop :=
  layout.lhs.length = layout.rhs.length ∧
  layout.lhs.length = layout.out.length ∧
  layout.allWires.Nodup

end RegisterLayout

/-- All wires in `ws` hold `false` in the basis state `st`. -/
def Clean (ws : List Wire) (st : BasisState) : Prop :=
  ∀ w ∈ ws, st w = false

/-- Two basis states agree pointwise on every wire in `ws`. -/
def AgreesOn (ws : List Wire) (before after : BasisState) : Prop :=
  ∀ w ∈ ws, after w = before w

namespace Gate

/-- Every control and target of a gate belongs to `ws`. This is stronger than merely leaving
outside wires unchanged: it also rules out reading an undeclared outside wire as a control. -/
def UsesOnly (ws : List Wire) : Gate → Prop
  | .X t       => t ∈ ws
  | .H t       => t ∈ ws
  | .CX c t    => c ∈ ws ∧ t ∈ ws
  | .CCX a b t => a ∈ ws ∧ b ∈ ws ∧ t ∈ ws
  | .P _ t     => t ∈ ws

end Gate

/-- Every gate in `program` uses only controls and targets from `ws`. -/
def CircuitUsesOnly (ws : List Wire) (program : Circuit) : Prop :=
  ∀ g ∈ program, g.UsesOnly ws

/-- A circuit leaves every wire outside its declared register footprint unchanged.

This unconditional locality clause is what makes a contract composable inside a larger
arithmetic circuit: the caller may keep live controls and intermediate registers outside
`ws` without importing the callee's private implementation. -/
def PreservesOutside (ws : List Wire) (program : Circuit) : Prop :=
  ∀ (st : BasisState) (w : Wire), w ∉ ws → Classical.run program st w = st w

/-- A circuit confined to `ws` leaves every outside wire unchanged. -/
theorem CircuitUsesOnly.preservesOutside {ws : List Wire} {program : Circuit}
    (h : CircuitUsesOnly ws program) : PreservesOutside ws program := by
  intro st w hw
  induction program generalizing st with
  | nil => rfl
  | cons g program ih =>
      rw [Classical.run_cons, ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg'))]
      have hg := h g (List.mem_cons_self ..)
      cases g with
      | X t =>
          simp only [Gate.UsesOnly] at hg
          exact upd_other st t (!st t) (fun e => hw (e ▸ hg))
      | H _ => rfl
      | CX c t =>
          simp only [Gate.UsesOnly] at hg
          exact upd_other st t (Bool.xor (st t) (st c)) (fun e => hw (e ▸ hg.2))
      | CCX a b t =>
          simp only [Gate.UsesOnly] at hg
          exact upd_other st t (Bool.xor (st t) (st a && st b)) (fun e => hw (e ▸ hg.2.2))
      | P _ _ => rfl

/-- Complete clean out-of-place contract for one binary arithmetic circuit.

`op` is the mathematical operation before reduction. The circuit's output is `op lhs rhs`
reduced modulo `modulus`. The exact same `program` term appears in correctness, cost,
H/P-freedom, and well-formedness fields, preventing implementation/specification drift. -/
structure CleanBinaryContract (program : Circuit) (layout : RegisterLayout)
    (modulus : Nat) (op : Nat → Nat → Nat) (cost : Nat) : Prop where
  correct : ∀ st : BasisState,
    layout.Valid →
    regValue layout.lhs st < modulus →
    regValue layout.rhs st < modulus →
    Clean (layout.out ++ layout.work) st →
    let after := Classical.run program st
    AgreesOn layout.lhs st after ∧
      AgreesOn layout.rhs st after ∧
      regValue layout.out after = op (regValue layout.lhs st) (regValue layout.rhs st) % modulus ∧
      Clean layout.work after
  usesOnly : CircuitUsesOnly layout.allWires program
  counted : tCount program = cost
  hpFree : Classical.HPFree program
  wellFormed : layout.Valid → CircuitWellFormed program

/-- Contract for clean out-of-place modular addition. -/
abbrev ModAddContract (program : Circuit) (layout : RegisterLayout)
    (modulus cost : Nat) : Prop :=
  CleanBinaryContract program layout modulus Nat.add cost

/-- Contract for clean out-of-place modular multiplication. -/
abbrev ModMulContract (program : Circuit) (layout : RegisterLayout)
    (modulus cost : Nat) : Prop :=
  CleanBinaryContract program layout modulus Nat.mul cost

/-- Contract for clean out-of-place modular exponentiation (`lhs ^ rhs mod modulus`). -/
abbrev ModExpContract (program : Circuit) (layout : RegisterLayout)
    (modulus cost : Nat) : Prop :=
  CleanBinaryContract program layout modulus Nat.pow cost

end ShorECDLP
