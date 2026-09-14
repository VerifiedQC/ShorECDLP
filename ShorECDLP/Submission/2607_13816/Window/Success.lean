import ShorECDLP.Submission.«2607_13816».Window.CharacterMixture
import ShorECDLP.Submission.«2607_13816».OrderFinding.Normalization
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1 Quantum.PhaseEstimation Quantum.OrderFinding
open scoped BigOperators
noncomputable section
/-- Probability of the actual decoded finite Fourier-output pair. -/
def windowTrialFiniteOutputMass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (out : Fin (2^257) × Fin (2^257)) : ℝ :=
  windowTrialOutputMass P Q hP hQ hrP hrQ (paperOutcomeBits 257 out.1) (paperOutcomeBits 257 out.2)
theorem windowTrialFiniteOutputMass_eq {r : Nat} (hr : Nat.Prime r) (P Q : Point)
    (hP : P≠0) (hQ : Q≠0) (hrP : order • P=0) (hrQ : order • Q=0)
    (horder : addOrderOf P=r) (d : Nat) (hQd : Q=d • P) (out : Fin (2^257) × Fin (2^257)) :
    windowTrialFiniteOutputMass P Q hP hQ hrP hrQ out=paperPairMass r 257 d out :=
  windowTrialOutputMass_character_mixture hr P Q hP hQ hrP hrQ horder d hQd _ _
    (paperOutcomeBits_length _ _) (paperOutcomeBits_length _ _) out
    (paperOutcomeBits_word _ _) (paperOutcomeBits_word _ _)
theorem windowTrialFiniteOutputMass_total {r : Nat} (hr : Nat.Prime r) (P Q : Point)
    (hP : P≠0) (hQ : Q≠0) (hrP : order • P=0) (hrQ : order • Q=0)
    (horder : addOrderOf P=r) (d : Nat) (hQd : Q=d • P) :
    ∑ out : Fin (2^257) × Fin (2^257), windowTrialFiniteOutputMass P Q hP hQ hrP hrQ out=1 := by
  simp only [windowTrialFiniteOutputMass_eq hr P Q hP hQ hrP hrQ horder d hQd]
  exact paperPairMass_total r 257 d hr.pos
/-- Success mass of the actual windowed circuit followed by the canonical postprocessor. -/
def windowTrialSuccessMass (r : Nat) (hr : Nat.Prime r) (P Q : Point)
    (hP : P≠0) (hQ : Q≠0) (hrP : order • P=0) (hrQ : order • Q=0) (d : Nat) : ℝ :=
  ∑ out : Fin (2^257) × Fin (2^257),
    if orderFindingPostprocess r 257 hr out=some (d:ZMod r) then
      windowTrialFiniteOutputMass P Q hP hQ hrP hrQ out else 0
theorem windowTrialSuccessMass_eq {r : Nat} (hr : Nat.Prime r) (P Q : Point)
    (hP : P≠0) (hQ : Q≠0) (hrP : order • P=0) (hrQ : order • Q=0)
    (horder : addOrderOf P=r) (d : Nat) (hQd : Q=d • P) :
    windowTrialSuccessMass r hr P Q hP hQ hrP hrQ d=paperSuccessMass r 257 d hr := by
  unfold windowTrialSuccessMass paperSuccessMass
  simp only [windowTrialFiniteOutputMass_eq hr P Q hP hQ hrP hrQ horder d hQd]
theorem windowTrialSuccessMass_lower {r : Nat} (hr : Nat.Prime r) (P Q : Point)
    (hP : P≠0) (hQ : Q≠0) (hrP : order • P=0) (hrQ : order • Q=0)
    (horder : addOrderOf P=r) (d : Nat) (hQd : Q=d • P) (hprecision : r<2^257) :
    (((r-1:Nat):ℝ)/(r:ℝ))*((4:ℝ)/Real.pi^2)^2 ≤ windowTrialSuccessMass r hr P Q hP hQ hrP hrQ d := by
  rw [windowTrialSuccessMass_eq hr P Q hP hQ hrP hrQ horder d hQd]
  exact paperSuccessMass_lower r 257 d hr hprecision
/-- Same physical program: normalized output distribution, success bound and support bound. -/
theorem windowTrial_success_certificate {r : Nat} (hr : Nat.Prime r) (P Q : Point)
    (hP : P≠0) (hQ : Q≠0) (hrP : order • P=0) (hrQ : order • Q=0)
    (horder : addOrderOf P=r) (d : Nat) (hQd : Q=d • P) (hprecision : r<2^257) :
    (∑ out : Fin (2^257) × Fin (2^257), windowTrialFiniteOutputMass P Q hP hQ hrP hrQ out)=1 ∧
    (((r-1:Nat):ℝ)/(r:ℝ))*((4:ℝ)/Real.pi^2)^2 ≤ windowTrialSuccessMass r hr P Q hP hQ hrP hrQ d ∧
    (windowTrialProgram P Q hP hQ hrP hrQ).qubitCount≤1383 :=
  ⟨windowTrialFiniteOutputMass_total hr P Q hP hQ hrP hrQ horder d hQd,
   windowTrialSuccessMass_lower hr P Q hP hQ hrP hrQ horder d hQd hprecision,
   windowTrialProgram_qubitCount P Q hP hQ hrP hrQ⟩
end
end ShorECDLP.Paper2607_13816
