import ShorECDLP.Submission.«2607_13816».Window.DirectOutcomes
import ShorECDLP.Submission.«2607_13816».Window.Success
import ShorECDLP.Submission.«2607_13816».OrderFinding.Normalization
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1 Quantum.PhaseEstimation Quantum.OrderFinding
open scoped BigOperators
noncomputable section
/-- Probability of the actual decoded finite Fourier-output pair. -/
def directWindowTrialFiniteOutputMass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (out : Fin (2^257) × Fin (2^257)) : ℝ :=
  directWindowTrialOutputMass P Q hP hQ hrP hrQ (paperOutcomeBits 257 out.1) (paperOutcomeBits 257 out.2)
theorem directWindowTrialFiniteOutputMass_eq {r : Nat} (hr : Nat.Prime r) (P Q : Point)
    (hP : P≠0) (hQ : Q≠0) (hrP : order • P=0) (hrQ : order • Q=0)
    (horder : addOrderOf P=r) (d : Nat) (hQd : Q=d • P) (out : Fin (2^257) × Fin (2^257)) :
    directWindowTrialFiniteOutputMass P Q hP hQ hrP hrQ out=paperPairMass r 257 d out := by
  unfold directWindowTrialFiniteOutputMass
  rw [directWindowTrialOutputMass_eq P Q hP hQ hrP hrQ _ _
    (paperOutcomeBits_length _ _) (paperOutcomeBits_length _ _)]
  exact windowTrialFiniteOutputMass_eq hr P Q hP hQ hrP hrQ horder d hQd out
theorem directWindowTrialFiniteOutputMass_total {r : Nat} (hr : Nat.Prime r) (P Q : Point)
    (hP : P≠0) (hQ : Q≠0) (hrP : order • P=0) (hrQ : order • Q=0)
    (horder : addOrderOf P=r) (d : Nat) (hQd : Q=d • P) :
    ∑ out : Fin (2^257) × Fin (2^257), directWindowTrialFiniteOutputMass P Q hP hQ hrP hrQ out=1 := by
  simp only [directWindowTrialFiniteOutputMass_eq hr P Q hP hQ hrP hrQ horder d hQd]
  exact paperPairMass_total r 257 d hr.pos
/-- Success mass of the actual windowed circuit followed by the canonical postprocessor. -/
def directWindowTrialSuccessMass (r : Nat) (hr : Nat.Prime r) (P Q : Point)
    (hP : P≠0) (hQ : Q≠0) (hrP : order • P=0) (hrQ : order • Q=0) (d : Nat) : ℝ :=
  ∑ out : Fin (2^257) × Fin (2^257),
    if orderFindingPostprocess r 257 hr out=some (d:ZMod r) then
      directWindowTrialFiniteOutputMass P Q hP hQ hrP hrQ out else 0
theorem directWindowTrialSuccessMass_eq {r : Nat} (hr : Nat.Prime r) (P Q : Point)
    (hP : P≠0) (hQ : Q≠0) (hrP : order • P=0) (hrQ : order • Q=0)
    (horder : addOrderOf P=r) (d : Nat) (hQd : Q=d • P) :
    directWindowTrialSuccessMass r hr P Q hP hQ hrP hrQ d=paperSuccessMass r 257 d hr := by
  unfold directWindowTrialSuccessMass paperSuccessMass
  simp only [directWindowTrialFiniteOutputMass_eq hr P Q hP hQ hrP hrQ horder d hQd]
theorem directWindowTrialSuccessMass_lower {r : Nat} (hr : Nat.Prime r) (P Q : Point)
    (hP : P≠0) (hQ : Q≠0) (hrP : order • P=0) (hrQ : order • Q=0)
    (horder : addOrderOf P=r) (d : Nat) (hQd : Q=d • P) (hprecision : r<2^257) :
    (((r-1:Nat):ℝ)/(r:ℝ))*((4:ℝ)/Real.pi^2)^2 ≤ directWindowTrialSuccessMass r hr P Q hP hQ hrP hrQ d := by
  rw [directWindowTrialSuccessMass_eq hr P Q hP hQ hrP hrQ horder d hQd]
  exact paperSuccessMass_lower r 257 d hr hprecision
/-- Same physical program: normalized output distribution, success bound and support bound. -/
theorem directWindowTrial_success_certificate {r : Nat} (hr : Nat.Prime r) (P Q : Point)
    (hP : P≠0) (hQ : Q≠0) (hrP : order • P=0) (hrQ : order • Q=0)
    (horder : addOrderOf P=r) (d : Nat) (hQd : Q=d • P) (hprecision : r<2^257) :
    (∑ out : Fin (2^257) × Fin (2^257), directWindowTrialFiniteOutputMass P Q hP hQ hrP hrQ out)=1 ∧
    (((r-1:Nat):ℝ)/(r:ℝ))*((4:ℝ)/Real.pi^2)^2 ≤ directWindowTrialSuccessMass r hr P Q hP hQ hrP hrQ d ∧
    (directWindowTrialProgram P Q hP hQ hrP hrQ).qubitCount≤1383 :=
  ⟨directWindowTrialFiniteOutputMass_total hr P Q hP hQ hrP hrQ horder d hQd,
   directWindowTrialSuccessMass_lower hr P Q hP hQ hrP hrQ horder d hQd hprecision,
   directWindowTrialProgram_qubitCount P Q hP hQ hrP hrQ⟩
end
end ShorECDLP.Paper2607_13816
