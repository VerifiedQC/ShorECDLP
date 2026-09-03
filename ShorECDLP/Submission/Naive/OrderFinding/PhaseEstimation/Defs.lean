import ShorECDLP.Framework.Quantum.InnerProduct
import ShorECDLP.Submission.Naive.QFT.Defs

/-!
# Generic quantum phase estimation

This file defines textbook phase estimation directly on the repository's
existing `Quantum.State`.  The phase register is a normal LSB-first wire list.
Since an arbitrary operator `U` is not a primitive gate, its controlled powers
are supplied as a complex-linear map and tied to `U` by
`ControlledPowersOn`.

The resulting `phaseEstimation` map has the standard three stages:

1. Hadamards prepare the phase register;
2. the supplied block applies `U ^ value` on register label `value`;
3. the existing inverse QFT converts the kicked-back phase to a basis label.

No elliptic-curve encoding or ECDLP-specific oracle appears in this generic
layer.
-/

namespace ShorECDLP.Quantum.PhaseEstimation

open scoped BigOperators

noncomputable section

/-- Apply one Hadamard to every wire of the phase register. -/
def hadamards (phaseReg : List Wire) : Circuit :=
  phaseReg.map Gate.H

/--
Overwrite the phase register with `value`, extended linearly from basis states
to arbitrary quantum states.
-/
def labelState
    (phaseReg : List Wire)
    (value : Nat) : State →ₗ[ℂ] State :=
  Finsupp.linearCombination ℂ
    (fun s => ket (writeReg phaseReg value s))

/-- The unit complex eigenvalue `exp(2πi·phase)`. -/
def eigenvalue (phase : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((2 * Real.pi * phase : ℝ) : ℂ))

/-- Circular distance between `phase` and the grid point encoded by `value`. -/
def circularDistance
    (precision : Nat)
    (phase : ℝ)
    (value : Fin (2 ^ precision)) : ℝ :=
  let delta := |phase - (value.val : ℝ) / (2 ^ precision : Nat)|
  min delta |1 - delta|

/--
Born probability that a computational-basis measurement of `phaseReg` returns
`value`.
-/
def registerProbability
    (phaseReg : List Wire)
    (value : Nat)
    (psi : State) : ℝ := by
  classical
  exact
    ∑ s ∈ psi.support,
      if regValue phaseReg s = value then Complex.normSq (psi s) else 0

/--
Semantic contract for the controlled-power block on the input eigenstate.
On phase-register label `value`, it preserves that label and applies
`U ^ value` to `psi`.
-/
def ControlledPowersOn
    (U controlledPowers : State →ₗ[ℂ] State)
    (phaseReg : List Wire)
    (psi : State) : Prop :=
  ∀ value : Fin (2 ^ phaseReg.length),
    controlledPowers (labelState phaseReg value.val psi) =
      labelState phaseReg value.val ((U ^ value.val) psi)

/--
Textbook phase estimation using a supplied controlled-power block and the
repository's existing inverse-QFT circuit.
-/
def phaseEstimation
    (phaseReg : List Wire)
    (qftAncilla : Wire)
    (controlledPowers : State →ₗ[ℂ] State) : State →ₗ[ℂ] State :=
  (run (iqft phaseReg qftAncilla)).comp
    (controlledPowers.comp (run (hadamards phaseReg)))

end

end ShorECDLP.Quantum.PhaseEstimation
