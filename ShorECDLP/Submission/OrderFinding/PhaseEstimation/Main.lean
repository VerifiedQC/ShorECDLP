import ShorECDLP.Submission.OrderFinding.PhaseEstimation.Defs

/-!
# Correctness of generic quantum phase estimation

The public theorem below fixes the exact-grid contract for phase estimation.
If `psi` is a normalized eigenstate of an inner-product-preserving `U` with
eigenphase `value / 2ˡᵉᶜᶜʳᶦᵗⁿ`, then ideal phase estimation returns the
control label `value` exactly while preserving `psi`.  Consequently a
computational-basis measurement of the control register returns `value` with
probability one and every other label with probability zero.

This theorem deliberately covers only phases exactly representable at the
chosen precision.  Approximate/off-grid phases and their tail bounds belong to
the later measurement/success-bound layer.  Likewise, this ideal result is not
yet a circuit-refinement theorem: a later module must connect controlled powers
of a concrete operator and the existing wire-level IQFT to these definitions.
-/

namespace ShorECDLP.Quantum.PhaseEstimation

noncomputable section

/--
**Exact phase-estimation correctness.**  If `psi` is a normalized eigenstate
of the physically valid operator `U` at the grid phase represented by `value`,
then phase estimation produces `|value⟩ ⊗ psi` exactly.

The proof is the one deliberately deferred obligation in this initial
scaffold.
-/
theorem phaseEstimation_correct_exact
    (precision : Nat)
    (U : State →ₗ[ℂ] State)
    (psi : State)
    (value : Label precision)
    (hU : PreservesInner U)
    (hnorm : normSq psi = 1)
    (heigen : IsEigenstate U psi (gridPhase precision value)) :
    phaseEstimation precision U psi = controlKet value psi := by
  sorry

/-- The exact phase label is observed with probability one. -/
theorem outcomeProbability_correct
    (precision : Nat)
    (U : State →ₗ[ℂ] State)
    (psi : State)
    (value : Label precision)
    (hU : PreservesInner U)
    (hnorm : normSq psi = 1)
    (heigen : IsEigenstate U psi (gridPhase precision value)) :
    outcomeProbability (phaseEstimation precision U psi) value = 1 := by
  rw [phaseEstimation_correct_exact precision U psi value hU hnorm heigen]
  simp [outcomeProbability, controlKet, hnorm]

/-- Every other phase label is observed with probability zero. -/
theorem outcomeProbability_incorrect
    (precision : Nat)
    (U : State →ₗ[ℂ] State)
    (psi : State)
    (value outcome : Label precision)
    (hU : PreservesInner U)
    (hnorm : normSq psi = 1)
    (heigen : IsEigenstate U psi (gridPhase precision value))
    (hne : outcome ≠ value) :
    outcomeProbability (phaseEstimation precision U psi) outcome = 0 := by
  rw [phaseEstimation_correct_exact precision U psi value hU hnorm heigen]
  simp [outcomeProbability, controlKet, hne]

/-- The complete measurement distribution is the point mass at `value`. -/
theorem outcomeProbability_eq_ite
    (precision : Nat)
    (U : State →ₗ[ℂ] State)
    (psi : State)
    (value outcome : Label precision)
    (hU : PreservesInner U)
    (hnorm : normSq psi = 1)
    (heigen : IsEigenstate U psi (gridPhase precision value)) :
    outcomeProbability (phaseEstimation precision U psi) outcome =
      if outcome = value then 1 else 0 := by
  by_cases h : outcome = value
  · subst outcome
    simp [outcomeProbability_correct precision U psi value hU hnorm heigen]
  · simp [h, outcomeProbability_incorrect precision U psi value outcome
      hU hnorm heigen h]

end

end ShorECDLP.Quantum.PhaseEstimation
