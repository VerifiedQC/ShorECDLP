import ShorECDLP.Submission.QFT.Main

/-!
# Generic quantum phase estimation

This file defines the ideal semantics of textbook quantum phase estimation for
an abstract complex-linear operator `U`.  A `JointState precision` represents a
control/work state as one work-state component for every label of the
`precision`-qubit control register:

```text
  value ↦ work-state amplitude attached to |value⟩.
```

This finite direct-sum presentation is the concrete coefficient form of a
control⊗work state.  It lets the definition express controlled powers of an
arbitrary `U` without pretending that `U` is one of the repository's primitive
gates.  A later refinement theorem will connect these ideal semantics to a
supplied controlled-power circuit and the existing wire-level inverse QFT.

The Fourier sign and LSB-first label convention agree with
`ShorECDLP.Submission.QFT`: phase kickback uses the positive `qftPhase` kernel,
and `inverseFourier` uses its complex conjugate.
-/

namespace ShorECDLP.Quantum.PhaseEstimation

open scoped BigOperators

noncomputable section

/-- Labels of a `precision`-qubit phase register. -/
abbrev Label (precision : Nat) := Fin (2 ^ precision)

/--
An ideal joint control/work state.  The component at `value` is the work-state
amplitude multiplying the control ket `|value⟩`.
-/
abbrev JointState (precision : Nat) := Label precision → State

/-- The QFT normalization factor `1 / √(2ˡᵉᶜᶜʳᶦᵗⁿ)`. -/
def normalization (precision : Nat) : ℂ :=
  (((Real.sqrt (2 ^ precision))⁻¹ : ℝ) : ℂ)

/-- A joint state with control label `value` and work state `psi`. -/
def controlKet
    {precision : Nat}
    (value : Label precision)
    (psi : State) : JointState precision :=
  fun label => if label = value then psi else 0

/-- Uniform control-register preparation tensored with `psi`. -/
def uniform
    (precision : Nat)
    (psi : State) : JointState precision :=
  fun _ => normalization precision • psi

/--
Ideal controlled powers.  On control label `value`, apply `U ^ value` to that
branch's work state.
-/
def controlledPowers
    (precision : Nat)
    (U : State →ₗ[ℂ] State)
    (joint : JointState precision) : JointState precision :=
  fun value => (U ^ value.val) (joint value)

/--
Ideal inverse Fourier transform on the control register.  The work components
are spectators, and the conjugated `qftPhase` is the negative Fourier kernel.
-/
def inverseFourier
    (precision : Nat)
    (joint : JointState precision) : JointState precision :=
  fun outcome =>
    normalization precision •
      ∑ value : Label precision,
        (starRingEnd ℂ)
            (qftPhase (2 ^ precision) value.val outcome.val) •
          joint value

/--
Textbook ideal phase estimation: prepare the uniform control register, apply
controlled powers of `U`, then apply the inverse Fourier transform.
-/
def phaseEstimation
    (precision : Nat)
    (U : State →ₗ[ℂ] State)
    (psi : State) : JointState precision :=
  inverseFourier precision (controlledPowers precision U (uniform precision psi))

/-- The unit complex eigenvalue `exp(2πi·phase)`. -/
def eigenvalue (phase : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((2 * Real.pi * phase : ℝ) : ℂ))

/-- `psi` is an eigenstate of `U` with eigenphase `phase`. -/
def IsEigenstate
    (U : State →ₗ[ℂ] State)
    (psi : State)
    (phase : ℝ) : Prop :=
  U psi = eigenvalue phase • psi

/-- The exact phase fraction encoded by a control-register label. -/
def gridPhase
    (precision : Nat)
    (value : Label precision) : ℝ :=
  (value.val : ℝ) / (2 ^ precision : Nat)

/--
Born probability of a control-register outcome in the ideal joint-state
representation.  Each control label indexes an orthogonal work-state block.
-/
def outcomeProbability
    {precision : Nat}
    (joint : JointState precision)
    (outcome : Label precision) : ℝ :=
  normSq (joint outcome)

end

end ShorECDLP.Quantum.PhaseEstimation
