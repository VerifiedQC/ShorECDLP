import ShorECDLP.Framework.Classical.Semantics

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-
# Quantum semantics

The quantum state space is the free complex vector space over the shared
computational-basis type `BasisState`.

A state therefore has type

    BasisState →₀ ℂ

so every state has finite support. This is sufficient for the finite circuits
used in this development: a basis ket has support 1, and each Hadamard can at
most double the support.

Each primitive gate is first defined on computational-basis kets. We then
extend that action linearly to arbitrary quantum states using
`Finsupp.linearCombination`.

This keeps the basis indexing exactly the same as in the classical semantics,
which will later make the H/P-free classical→quantum agreement theorem direct.
-/

namespace ShorECDLP.Quantum

noncomputable section

/-- A finite-support quantum state over computational basis states. -/
abbrev State := BasisState →₀ ℂ

/-- The signed real angle represented by a dyadic phase gate. -/
def phaseAngle (dir : PhaseDir) (k : Nat) : ℝ :=
  match dir with
  | .forward => 2 * Real.pi / (2 : ℝ) ^ k
  | .inverse => -(2 * Real.pi / (2 : ℝ) ^ k)

/-- The unit complex scalar applied to `|1⟩` by a dyadic phase gate. -/
def phaseCoeff (dir : PhaseDir) (k : Nat) : ℂ :=
  Complex.exp (Complex.I * (phaseAngle dir k : ℂ))

@[simp]
theorem phaseAngle_adjoint (dir : PhaseDir) (k : Nat) :
    phaseAngle dir.adjoint k = -phaseAngle dir k := by
  cases dir <;> simp [phaseAngle]

@[simp]
theorem phaseCoeff_adjoint_mul (dir : PhaseDir) (k : Nat) :
    phaseCoeff dir.adjoint k * phaseCoeff dir k = 1 := by
  unfold phaseCoeff
  rw [← Complex.exp_add]
  have h :
      Complex.I * (phaseAngle dir.adjoint k : ℂ) +
          Complex.I * (phaseAngle dir k : ℂ) = 0 := by
    rw [phaseAngle_adjoint]
    push_cast
    ring
  rw [h, Complex.exp_zero]

@[simp]
theorem phaseCoeff_mul_adjoint (dir : PhaseDir) (k : Nat) :
    phaseCoeff dir k * phaseCoeff dir.adjoint k = 1 := by
  rw [mul_comm, phaseCoeff_adjoint_mul]


/-! ## Computational basis kets -/

/-- The computational basis ket `|s⟩`. -/
def ket (s : BasisState) : State :=
  Finsupp.single s 1 --If s, then 1, else 0

@[simp]
theorem ket_self (s : BasisState) :
    ket s s = 1 := by
  classical
  simp [ket]

theorem ket_ne {s t : BasisState} (h : s ≠ t) :
    ket s t = 0 := by
  classical
  simp [ket, h]

/-! ## Primitive gates on basis kets -/

/--
Action of a primitive gate on a computational-basis ket.
-/
def onKet : Gate → BasisState → State
  | .X t, s =>
      ket (s[t ↦ !s t])

  | .H t, s =>
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket (s[t ↦ false]) +
        ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (if (s t) then -1 else 1))
          • ket (s[t ↦ true])

  | .CX c t, s =>
      ket (s[t ↦ Bool.xor (s t) (s c)])

  | .CCX a b t, s =>
      ket (s[t ↦ Bool.xor (s t) (s a && s b)])

  | .P dir k t, s =>
      (if s t then phaseCoeff dir k else 1) • ket s


/-! ## Linear action of primitive gates -/

/--
Quantum action of a primitive gate.

`onKet g` specifies the action on basis kets; `linearCombination`
extends it uniquely by complex linearity to arbitrary finite-support states.
-/
def applyGate (g : Gate) : State →ₗ[ℂ] State :=
  Finsupp.linearCombination ℂ (onKet g)

/-- Applying a gate to a basis ket reduces to its `onKet` specification. -/
@[simp]
theorem applyGate_ket (g : Gate) (s : BasisState) :
    applyGate g (ket s) = onKet g s := by
  classical
  simp [applyGate, ket]


/-! Convenient basis-ket rules for the five primitives. -/

@[simp]
theorem applyGate_X_ket (t : Wire) (s : BasisState) :
    applyGate (.X t) (ket s) =
      ket (s[t ↦ !s t]) := by
  simp [onKet]

@[simp]
theorem applyGate_H_ket (t : Wire) (s : BasisState) :
    applyGate (.H t) (ket s) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket (s[t ↦ false]) +
        ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (if (s t) then -1 else 1)) • ket (s[t ↦ true]) := by
  simp [onKet]

@[simp]
theorem applyGate_CX_ket (c t : Wire) (s : BasisState) :
    applyGate (.CX c t) (ket s) =
      ket (s[t ↦ Bool.xor (s t) (s c)]) := by
  simp [onKet]

@[simp]
theorem applyGate_CCX_ket (a b t : Wire) (s : BasisState) :
    applyGate (.CCX a b t) (ket s) =
      ket (s[t ↦ Bool.xor (s t) (s a && s b)]) := by
  simp [onKet]

@[simp]
theorem applyGate_P_ket (dir : PhaseDir) (k : Nat) (t : Wire) (s : BasisState) :
    applyGate (.P dir k t) (ket s) =
      (if s t then phaseCoeff dir k else 1) • ket s := by
  simp [onKet]


/-! ## Agreement with the classical semantics on classical gates -/

@[simp]
theorem applyGate_X_agrees_classical (t : Wire) (s : BasisState) :
    applyGate (.X t) (ket s) =
      ket (Classical.applyGate (.X t) s) := by
  simp [Classical.applyGate, onKet]

@[simp]
theorem applyGate_CX_agrees_classical
    (c t : Wire) (s : BasisState) :
    applyGate (.CX c t) (ket s) =
      ket (Classical.applyGate (.CX c t) s) := by
  simp [Classical.applyGate, onKet]

@[simp]
theorem applyGate_CCX_agrees_classical
    (a b t : Wire) (s : BasisState) :
    applyGate (.CCX a b t) (ket s) =
      ket (Classical.applyGate (.CCX a b t) s) := by
  simp [Classical.applyGate, onKet]


/-! ## Circuit semantics -/

/--
Run a circuit from left to right.

The result is itself bundled as a complex-linear map. Consequently,
linearity of an entire circuit follows automatically from the type.
-/
def run : Circuit → State →ₗ[ℂ] State
  | [] =>
      LinearMap.id

  | g :: c =>
      (run c).comp (applyGate g)

@[simp]
theorem run_nil (ψ : State) :
    run [] ψ = ψ := rfl

@[simp]
theorem run_cons
    (g : Gate) (c : Circuit) (ψ : State) :
    run (g :: c) ψ =
      run c (applyGate g ψ) := rfl

@[simp]
theorem run_singleton
    (g : Gate) (ψ : State) :
    run [g] ψ = applyGate g ψ := by
  simp

/--
Running `c₁ ++ c₂` means first running `c₁`, then running `c₂`.
-/
theorem run_append
    (c₁ c₂ : Circuit) (ψ : State) :
    run (c₁ ++ c₂) ψ =
      run c₂ (run c₁ ψ) := by
  induction c₁ generalizing ψ with
  | nil =>
      simp
  | cons g c ih =>
      simp [ih]

/-- Linear-map form of `run_append`. -/
theorem run_append_map
    (c₁ c₂ : Circuit) :
    run (c₁ ++ c₂) =
      (run c₂).comp (run c₁) := by
  apply LinearMap.ext
  intro ψ
  exact run_append c₁ c₂ ψ


/-! ## Explicit linearity lemmas -/

@[simp]
theorem applyGate_add
    (g : Gate) (ψ φ : State) :
    applyGate g (ψ + φ) =
      applyGate g ψ + applyGate g φ :=
  (applyGate g).map_add ψ φ

@[simp]
theorem applyGate_smul
    (g : Gate) (a : ℂ) (ψ : State) :
    applyGate g (a • ψ) =
      a • applyGate g ψ :=
  (applyGate g).map_smul a ψ

@[simp]
theorem run_add
    (c : Circuit) (ψ φ : State) :
    run c (ψ + φ) =
      run c ψ + run c φ :=
  (run c).map_add ψ φ

@[simp]
theorem run_smul
    (c : Circuit) (a : ℂ) (ψ : State) :
    run c (a • ψ) =
      a • run c ψ :=
  (run c).map_smul a ψ

end

/--
On a classically faithful primitive gate, the quantum action on a
computational-basis ket agrees exactly with the classical basis-state action.
-/
theorem applyGate_ket_agrees_classical
    (g : Gate)
    (s : BasisState)
    (hg : Classical.IsClassicalGate g) :
    applyGate g (ket s) =
      ket (Classical.applyGate g s) := by
  cases g with
  | X t =>
      exact applyGate_X_agrees_classical t s

  | H t =>
      simp at hg

  | CX c t =>
      exact applyGate_CX_agrees_classical c t s

  | CCX a b t =>
      exact applyGate_CCX_agrees_classical a b t s

  | P dir k t =>
      simp at hg

/--
Classical-to-quantum agreement.

For an `H`/`P`-free circuit, running the quantum semantics on a
computational-basis ket gives exactly the ket corresponding to the result
of the classical semantics.

This is the bridge that lifts the M1–M3 arithmetic correctness proofs into
the quantum state space without re-proving the arithmetic in Hilbert space.
-/
theorem run_ket_agrees_classical
    (c : Circuit)
    (s : BasisState)
    (hc : Classical.HPFree c) :
    run c (ket s) =
      ket (Classical.run c s) := by
  induction c generalizing s with
  | nil =>
      simp

  | cons g c ih =>
      have hg : Classical.IsClassicalGate g :=
        ((Classical.hpFree_cons g c).mp hc).1

      have hc' : Classical.HPFree c :=
        ((Classical.hpFree_cons g c).mp hc).2

      calc
        run (g :: c) (ket s)
            = run c (applyGate g (ket s)) := rfl

        _ = run c (ket (Classical.applyGate g s)) := by
              rw [applyGate_ket_agrees_classical g s hg]

        _ = ket (Classical.run c (Classical.applyGate g s)) := by
              exact ih (Classical.applyGate g s) hc'

        _ = ket (Classical.run (g :: c) s) := by
              rfl


end ShorECDLP.Quantum
