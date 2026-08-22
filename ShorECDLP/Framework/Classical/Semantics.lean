import ShorECDLP.Framework.InstructionSet

/-
# Fully classical basis-state semantics (framework)

This is the **classical** semantics: a state is a single computational basis state (one bit
per wire), and gates act as basis-state permutations. It is deliberately *not* a quantum
semantics — there is no amplitude or phase — so it can express and cheaply prove the
correctness of the reversible arithmetic (M1–M3, built from `{X, CX, CCX}`) and nothing more.

`H` (superposition) and `P` (phase) have no basis-state action and are identity placeholders
here; the classical semantics is faithful only on `H`/`P`-free circuits. The quantum
(Hilbert-space) semantics for the QFT is a *separate*, additive layer added at M4 over this
same basis index, bridged to this one by an agreement lemma — see `docs/PLAN.md`.

Everything lives in the `ShorECDLP.Classical` namespace so the naming makes the classical
scope unmistakable (`Classical.State`, `Classical.run`, …); the M4 quantum layer will be
`ShorECDLP.Quantum.*`.

## Notation (scoped to `Classical`)

  * `s[i ↦ b]` — the classical state `s` with wire `i` set to `b`.
  * `⟦g⟧`      — a gate's classical basis-state transformer (so `⟦g⟧ s`).
  * `⟪c⟫`      — a circuit's classical transformer, run left to right (`⟪c⟫ s`).
-/

namespace ShorECDLP.Classical

/-- A classical basis state: one bit per wire. -/
abbrev State := Nat → Bool

/-- Update wire `i` to `b`, leaving every other wire unchanged. -/
def upd (s : State) (i : Nat) (b : Bool) : State := fun j => if j = i then b else s j

@[inherit_doc] scoped notation:max s:max "[" i " ↦ " b "]" => upd s i b

@[simp] theorem upd_same (s : State) (i : Nat) (b : Bool) : s[i ↦ b] i = b := by
  simp [upd]

theorem upd_other (s : State) (i : Nat) (b : Bool) {j : Nat} (h : j ≠ i) :
    s[i ↦ b] j = s j := by
  simp [upd, h]

/-- Classical action of a single primitive gate on a basis state.

Only the reversible-classical gates `{X, CX, CCX}` have a genuine basis-state action. `H`
creates superposition and `P` adds a phase — neither is a basis-state permutation — so this
classical semantics is **faithful only on `H`- and `P`-free circuits** (all the reversible
arithmetic of M1–M3). `H` and `P` are set to the identity here solely to keep the transformer
total; no arithmetic correctness theorem is stated about a circuit that contains them, and
the QFT is handled by the separate quantum semantics at M4. -/
def applyGate : Gate → State → State
  | .X t,       s => s[t ↦ !s t]
  | .CX c t,    s => s[t ↦ Bool.xor (s t) (s c)]
  | .CCX a b t, s => s[t ↦ Bool.xor (s t) (s a && s b)]
  | .H _,       s => s
  | .P _ _,     s => s

@[inherit_doc] scoped notation:max "⟦" g "⟧" => applyGate g

/-- Run a circuit on a classical basis state, left to right. -/
def run (c : Circuit) (s : State) : State := c.foldl (fun s g => ⟦g⟧ s) s

@[inherit_doc] scoped notation:max "⟪" c "⟫" => run c

@[simp] theorem run_nil (s : State) : ⟪[]⟫ s = s := rfl

@[simp] theorem run_cons (g : Gate) (c : Circuit) (s : State) :
    ⟪g :: c⟫ s = ⟪c⟫ (⟦g⟧ s) := rfl

theorem run_append (c₁ c₂ : Circuit) (s : State) :
    ⟪c₁ ++ c₂⟫ s = ⟪c₂⟫ (⟪c₁⟫ s) := by
  simp [run, List.foldl_append]

/-- The natural number held by a register — a list of wires, least-significant first. -/
def regValue : List Nat → State → Nat
  | [],      _ => 0
  | w :: ws, s => (if s w then 1 else 0) + 2 * regValue ws s

@[simp] theorem regValue_nil (s : State) : regValue [] s = 0 := rfl

theorem regValue_cons (w : Nat) (ws : List Nat) (s : State) :
    regValue (w :: ws) s = (if s w then 1 else 0) + 2 * regValue ws s := rfl

/-- Updating a wire outside a register leaves the register's value unchanged. -/
theorem regValue_upd_not_mem (ws : List Nat) (s : State) (i : Nat) (b : Bool)
    (h : i ∉ ws) : regValue ws s[i ↦ b] = regValue ws s := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.mem_cons, not_or] at h
    rw [regValue_cons, regValue_cons, upd_other s i b (fun e => h.1 e.symm), ih h.2]

end ShorECDLP.Classical
