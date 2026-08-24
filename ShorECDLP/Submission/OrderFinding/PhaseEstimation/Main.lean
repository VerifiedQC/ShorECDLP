import ShorECDLP.Submission.OrderFinding.PhaseEstimation.Defs
import ShorECDLP.Submission.QFT.Main

/-!
# Correctness of generic quantum phase estimation

The theorem below is the exact-grid contract.  If `psi` is a normalized
eigenstate of an inner-product-preserving operator `U` with eigenphase
`value / 2^phaseReg.length`, the supplied block implements the controlled
powers of `U`, and the phase register plus QFT ancilla start clean, then phase
estimation writes `value` into the phase register and preserves `psi`.

The second theorem covers an arbitrary phase in `[0,1)`: a nearest grid label
is within half a grid cell in circular distance and occurs with the standard
phase-estimation probability lower bound `4/π²`.  The supplied
controlled-power map still needs a later refinement to an actual primitive-gate
circuit.
-/

namespace ShorECDLP.Quantum.PhaseEstimation

noncomputable section

/--
**Exact phase-estimation correctness.**  For an exactly representable
eigenphase, phase estimation returns the corresponding computational-basis
label with certainty while leaving the eigenstate unchanged.

This proof is the one deliberately deferred obligation in the initial
scaffold.
-/
theorem phaseEstimation_correct_exact
    (U controlledPowers : State →ₗ[ℂ] State)
    (psi : State)
    (phaseReg : List Wire)
    (qftAncilla : Wire)
    (value : Fin (2 ^ phaseReg.length))
    (hU : PreservesInner U)
    (hnorm : normSq psi = 1)
    (heigen :
      U psi =
        eigenvalue
            ((value.val : ℝ) / (2 ^ phaseReg.length : Nat)) • psi)
    (hcontrolled : ControlledPowersOn U controlledPowers phaseReg psi)
    (hphaseZero : ∀ s, psi s ≠ 0 → regValue phaseReg s = 0)
    (hancillaZero : ∀ s, psi s ≠ 0 → s qftAncilla = false)
    (hancilla : qftAncilla ∉ phaseReg)
    (hphaseReg : phaseReg.Nodup) :
    phaseEstimation phaseReg qftAncilla controlledPowers psi =
      labelState phaseReg value.val psi := by
  sorry

/--
**Approximate phase-estimation correctness.**  For an arbitrary eigenphase in
`[0,1)`, some nearest `phaseReg.length`-bit label is within half a grid cell in
circular distance and is observed with probability at least `4/π²`.
-/
theorem phaseEstimation_correct_approx
    (U controlledPowers : State →ₗ[ℂ] State)
    (psi : State)
    (phaseReg : List Wire)
    (qftAncilla : Wire)
    (phase : ℝ)
    (hU : PreservesInner U)
    (hnorm : normSq psi = 1)
    (heigen : U psi = eigenvalue phase • psi)
    (hphaseNonneg : 0 ≤ phase)
    (hphaseLtOne : phase < 1)
    (hcontrolled : ControlledPowersOn U controlledPowers phaseReg psi)
    (hphaseZero : ∀ s, psi s ≠ 0 → regValue phaseReg s = 0)
    (hancillaZero : ∀ s, psi s ≠ 0 → s qftAncilla = false)
    (hancilla : qftAncilla ∉ phaseReg)
    (hphaseReg : phaseReg.Nodup) :
    ∃ value : Fin (2 ^ phaseReg.length),
      circularDistance phaseReg.length phase value ≤
          (1 : ℝ) / (2 * (2 ^ phaseReg.length : Nat)) ∧
        (4 : ℝ) / Real.pi ^ 2 ≤
          registerProbability phaseReg value.val
            (phaseEstimation phaseReg qftAncilla controlledPowers psi) := by
  sorry

end

end ShorECDLP.Quantum.PhaseEstimation
