import ShorECDLP.Submission.Naive.OrderFinding.PhaseEstimation.Proofs.Hadamard
import ShorECDLP.Submission.Naive.OrderFinding.PhaseEstimation.Proofs.ControlledPowers
import ShorECDLP.Submission.Naive.OrderFinding.PhaseEstimation.Proofs.Fourier
import ShorECDLP.Submission.Naive.OrderFinding.PhaseEstimation.Proofs.Probability
import ShorECDLP.Submission.Naive.OrderFinding.PhaseEstimation.Proofs.Approximations

/-!
# Correctness of generic quantum phase estimation

The first theorem is the exact-grid contract.  If `psi` is an eigenvector of
`U` with eigenphase `value / 2^phaseReg.length`, the supplied block implements
the controlled powers of `U` on that eigenvector, and the phase register plus
QFT ancilla start clean, then phase estimation writes `value` into the phase
register and preserves `psi`.  This algebraic state equality is linear, so it
does not require `psi` to be normalized or `U` to preserve inner products
globally; for a normalized input it has the usual certainty interpretation.

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
label while leaving the eigenvector unchanged.  The equality holds without a
normalization hypothesis; when the input is normalized, it yields the usual
probability-one interpretation.
-/
theorem phaseEstimation_correct_exact
    (U controlledPowers : State →ₗ[ℂ] State)
    (psi : State)
    (phaseReg : List Wire)
    (qftAncilla : Wire)
    (value : Fin (2 ^ phaseReg.length))
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
  change
    run (iqft phaseReg qftAncilla)
      (controlledPowers (run (hadamards phaseReg) psi)) =
        labelState phaseReg value.val psi
  rw [run_hadamards_clean phaseReg psi hphaseZero hphaseReg]
  rw [controlledPowers_uniform_eigenstate
    U controlledPowers psi phaseReg
    (eigenvalue ((value.val : ℝ) / (2 ^ phaseReg.length : Nat)))
    heigen hcontrolled]
  rw [exact_phase_state_eq_run_qft phaseReg qftAncilla psi value
    hancillaZero hancilla hphaseReg]
  exact iqft_qft_cancel phaseReg qftAncilla
    (labelState phaseReg value.val psi) hancilla hphaseReg

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
  obtain ⟨value, hnear⟩ :=
    exists_nearest_phase_value
      phaseReg.length phase hphaseNonneg hphaseLtOne
  refine ⟨value, hnear, ?_⟩
  change
    (4 : ℝ) / Real.pi ^ 2 ≤
      registerProbability phaseReg value.val
        (run (iqft phaseReg qftAncilla)
          (controlledPowers
            (run (hadamards phaseReg) psi)))
  rw [run_hadamards_clean phaseReg psi hphaseZero hphaseReg]
  rw [controlledPowers_uniform_eigenstate
    U controlledPowers psi phaseReg
    (eigenvalue phase) heigen hcontrolled]
  rw [run_iqft_kicked_phase_state
    phaseReg qftAncilla psi phase
    hancillaZero hancilla hphaseReg]
  rw [registerProbability_label_superposition
    phaseReg psi
    (qpeAmplitude phaseReg.length phase)
    value hphaseZero hphaseReg]
  rw [hnorm, mul_one]
  unfold qpeAmplitude
  apply geometric_phase_average_lower_bound
  · positivity
  · simpa [circularDistance] using hnear

end

end ShorECDLP.Quantum.PhaseEstimation
