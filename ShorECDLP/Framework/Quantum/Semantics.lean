import ShorECDLP.Framework.InstructionSet

/-
# Classical basis-state semantics (framework)

The reversible gates `{X, CX, CCX}` act as permutations of computational basis states; this
is the semantics an arithmetic circuit's `correct` obligation is stated against. A basis
state assigns a bit to each wire. Phase gates `P` are diagonal — they carry a phase that is
invisible to this classical layer — so here they act as the identity; they appear only in
the QFT, whose correctness needs the full Hilbert-space semantics (a later layer).

This is enough to state and prove functional correctness of all the reversible modular
arithmetic (M1–M3), which never uses `P`.
-/

namespace ShorECDLP

/-- A classical basis state: one bit per wire. -/
abbrev State := Nat → Bool

/-- Update wire `i` to `b`, leaving every other wire unchanged. -/
def upd (s : State) (i : Nat) (b : Bool) : State := fun j => if j = i then b else s j

@[simp] theorem upd_same (s : State) (i : Nat) (b : Bool) : upd s i b i = b := by
  simp [upd]

theorem upd_other (s : State) (i : Nat) (b : Bool) {j : Nat} (h : j ≠ i) :
    upd s i b j = s j := by
  simp [upd, h]

/-- Action of a single primitive gate on a basis state.

Only the reversible-classical gates `{X, CX, CCX}` have a genuine basis-state action. `H`
creates superposition and `P` adds a phase — neither is a basis-state permutation — so this
classical semantics is **faithful only on `H`- and `P`-free circuits** (all the reversible
arithmetic of M1–M3). `H` and `P` are set to the identity here solely to keep `applyGate`
total; no arithmetic correctness theorem is stated about a circuit that contains them, and
the QFT is handled by the full Hilbert-space semantics in a later layer. -/
def applyGate : Gate → State → State
  | .X t,       s => upd s t (!s t)
  | .CX c t,    s => upd s t (Bool.xor (s t) (s c))
  | .CCX a b t, s => upd s t (Bool.xor (s t) (s a && s b))
  | .H _,       s => s
  | .P _ _,     s => s

/-- Run a circuit on a basis state, left to right. -/
def run (c : Circuit) (s : State) : State := c.foldl (fun s g => applyGate g s) s

@[simp] theorem run_nil (s : State) : run [] s = s := rfl

@[simp] theorem run_cons (g : Gate) (c : Circuit) (s : State) :
    run (g :: c) s = run c (applyGate g s) := rfl

theorem run_append (c₁ c₂ : Circuit) (s : State) :
    run (c₁ ++ c₂) s = run c₂ (run c₁ s) := by
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
    (h : i ∉ ws) : regValue ws (upd s i b) = regValue ws s := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.mem_cons, not_or] at h
    rw [regValue_cons, regValue_cons, upd_other s i b (fun e => h.1 e.symm), ih h.2]

end ShorECDLP
