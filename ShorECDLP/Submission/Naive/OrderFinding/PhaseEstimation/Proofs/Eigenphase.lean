import ShorECDLP.Submission.Naive.OrderFinding.PhaseEstimation.Defs
import ShorECDLP.Submission.Naive.QFT.Proofs.Fourier

namespace ShorECDLP.Quantum.PhaseEstimation

noncomputable section

theorem linearMap_pow_apply_eigenstate
    (U : State →ₗ[ℂ] State)
    (psi : State)
    (L : ℂ)
    (h : U psi = L • psi) :
    ∀ n : Nat, (U ^ n) psi = L ^ n • psi := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, h, map_smul, ih]
      simp [pow_succ, smul_smul, mul_comm]

theorem eigenvalue_pow_eq_eigenvalue_mul
    (phase : ℝ)
    (n : Nat) :
    eigenvalue phase ^ n = eigenvalue (n * phase) := by
  unfold eigenvalue
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem eigenvalue_exact_pow_eq_qftPhase
    (precision x y : Nat) :
    eigenvalue ((x : ℝ) / (2 ^ precision : Nat)) ^ y =
      qftPhase (2 ^ precision) x y := by
  rw [eigenvalue_pow_eq_eigenvalue_mul]
  unfold eigenvalue qftPhase
  congr 1
  push_cast
  ring

end

end ShorECDLP.Quantum.PhaseEstimation
