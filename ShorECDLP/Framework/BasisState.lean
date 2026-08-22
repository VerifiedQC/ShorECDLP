import ShorECDLP.Framework.InstructionSet

/-
# Basis states (framework, layer-neutral)

A computational basis state assigns one bit to each wire. This type is **layer-neutral**: the
classical semantics acts on a basis state directly, and the M4 quantum layer indexes its
amplitudes over exactly this type (`BasisState →₀ ℂ`). So the name carries no "classical"
marker — that marker belongs on the *actions* (`Classical.run`, …), not on the shared basis
index. Keeping one basis type is what makes the classical→quantum agreement lemma a clean
restriction rather than a re-indexing.

`upd` (wire update) and `regValue` (the number a register holds) live here because both
layers use them: the quantum action of a classical gate on a basis ket is `|s⟩ ↦ |s[t ↦ …]⟩`,
and register values are read the same way in either layer's correctness statements.
-/

namespace ShorECDLP

/-- A computational basis state: one bit per wire. Layer-neutral (see the module comment). -/
abbrev BasisState := Nat → Bool

/-- Update wire `i` to `b`, leaving every other wire unchanged. -/
def upd (s : BasisState) (i : Nat) (b : Bool) : BasisState := fun j => if j = i then b else s j

@[inherit_doc] notation:max s:max "[" i " ↦ " b "]" => upd s i b

@[simp] theorem upd_same (s : BasisState) (i : Nat) (b : Bool) : s[i ↦ b] i = b := by
  simp [upd]

theorem upd_other (s : BasisState) (i : Nat) (b : Bool) {j : Nat} (h : j ≠ i) :
    s[i ↦ b] j = s j := by
  simp [upd, h]

/-- The natural number held by a register — a list of wires, least-significant first. -/
def regValue : List Nat → BasisState → Nat
  | [],      _ => 0
  | w :: ws, s => (if s w then 1 else 0) + 2 * regValue ws s

@[simp] theorem regValue_nil (s : BasisState) : regValue [] s = 0 := rfl

theorem regValue_cons (w : Nat) (ws : List Nat) (s : BasisState) :
    regValue (w :: ws) s = (if s w then 1 else 0) + 2 * regValue ws s := rfl

/-- Updating a wire outside a register leaves the register's value unchanged. -/
theorem regValue_upd_not_mem (ws : List Nat) (s : BasisState) (i : Nat) (b : Bool)
    (h : i ∉ ws) : regValue ws s[i ↦ b] = regValue ws s := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.mem_cons, not_or] at h
    rw [regValue_cons, regValue_cons, upd_other s i b (fun e => h.1 e.symm), ih h.2]

end ShorECDLP
