import ShorECDLP.Framework.BasisState

/-
# Fully classical semantics (framework)

The **classical** action: gates act as basis-state permutations. There is no amplitude or
phase, so this expresses and cheaply proves the correctness of the reversible arithmetic
(M1–M3, built from `{X, CX, CCX}`) and nothing more. The classical marker is on the *actions*
here (`Classical.applyGate`, `Classical.run`); the basis-state *type* is the layer-neutral
`BasisState`, reused as the M4 quantum basis index.

`H` (superposition) and `P` (phase) have no basis-state action and are identity placeholders;
this semantics is faithful only on `H`/`P`-free circuits. The quantum (Hilbert-space)
semantics for the QFT is a *separate*, additive layer added at M4 over `BasisState →₀ ℂ`,
bridged to this one by an agreement lemma — see `docs/PLAN.md`.

## Notation (scoped to `Classical`)

  * `⟦g⟧` — a gate's classical basis-state transformer (so `⟦g⟧ s`).
  * `⟪c⟫` — a circuit's classical transformer, run left to right (`⟪c⟫ s`).
-/

namespace ShorECDLP.Classical

/-- Classical action of a single primitive gate on a basis state.

Only the reversible-classical gates `{X, CX, CCX}` have a genuine basis-state action. `H`
creates superposition and `P` adds a phase — neither is a basis-state permutation — so this
classical semantics is **faithful only on `H`- and `P`-free circuits** (all the reversible
arithmetic of M1–M3). `H` and `P` are set to the identity here solely to keep the transformer
total; no arithmetic correctness theorem is stated about a circuit that contains them, and
the QFT is handled by the separate quantum semantics at M4. -/
def applyGate : Gate → BasisState → BasisState
  | .X t,       s => s[t ↦ !s t]
  | .CX c t,    s => s[t ↦ Bool.xor (s t) (s c)]
  | .CCX a b t, s => s[t ↦ Bool.xor (s t) (s a && s b)]
  | .H _,       s => s
  | .P _ _,     s => s

@[inherit_doc] scoped notation:max "⟦" g "⟧" => applyGate g

/-- Run a circuit on a basis state, left to right (classical action). -/
def run (c : Circuit) (s : BasisState) : BasisState := c.foldl (fun s g => ⟦g⟧ s) s

@[inherit_doc] scoped notation:max "⟪" c "⟫" => run c

@[simp] theorem run_nil (s : BasisState) : ⟪[]⟫ s = s := rfl

@[simp] theorem run_cons (g : Gate) (c : Circuit) (s : BasisState) :
    ⟪g :: c⟫ s = ⟪c⟫ (⟦g⟧ s) := rfl

theorem run_append (c₁ c₂ : Circuit) (s : BasisState) :
    ⟪c₁ ++ c₂⟫ s = ⟪c₂⟫ (⟪c₁⟫ s) := by
  simp [run, List.foldl_append]

end ShorECDLP.Classical
