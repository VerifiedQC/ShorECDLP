import ShorECDLP.Submission.Naive.OrderFinding.PhaseEstimation.Proofs.Eigenphase

namespace ShorECDLP.Quantum.PhaseEstimation

theorem controlledPowers_uniform_eigenstate
    (U controlledPowers : State →ₗ[ℂ] State)
    (psi : State)
    (phaseReg : List Wire)
    (L : ℂ)
    (heigen : U psi = L • psi)
    (hcontrolled : ControlledPowersOn U controlledPowers phaseReg psi) :
    controlledPowers
        ((((Real.sqrt (2 ^ phaseReg.length))⁻¹ : ℝ) : ℂ) •
          ∑ y ∈ Finset.range (2 ^ phaseReg.length),
            labelState phaseReg y psi) =
      (((Real.sqrt (2 ^ phaseReg.length))⁻¹ : ℝ) : ℂ) •
        ∑ y ∈ Finset.range (2 ^ phaseReg.length),
          L ^ y • labelState phaseReg y psi := by
  rw [map_smul, map_sum]
  apply congrArg
    (fun φ : State =>
      (((Real.sqrt (2 ^ phaseReg.length))⁻¹ : ℝ) : ℂ) • φ)
  apply Finset.sum_congr rfl
  intro y hy
  have hylt : y < 2 ^ phaseReg.length := Finset.mem_range.mp hy
  rw [hcontrolled ⟨y, hylt⟩]
  rw [linearMap_pow_apply_eigenstate U psi L heigen y]
  rw [map_smul]

end ShorECDLP.Quantum.PhaseEstimation
