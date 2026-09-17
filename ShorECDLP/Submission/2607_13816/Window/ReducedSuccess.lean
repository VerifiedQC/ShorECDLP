import ShorECDLP.Submission.«2607_13816».Window.ReducedMixture
import ShorECDLP.Submission.«2607_13816».OrderFinding.ReducedVerified
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1 Quantum.PhaseEstimation Quantum.OrderFinding
open scoped BigOperators
noncomputable section
/-- Probability of the actual decoded finite Fourier-output pair. -/
def reducedWindowTrialFiniteOutputMass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (out : Fin (2^256) × Fin (2^208)) : ℝ :=
  reducedWindowTrialOutputMass P Q hP hQ hrP hrQ (paperOutcomeBits 256 out.1) (paperOutcomeBits 208 out.2)
theorem reducedWindowTrialFiniteOutputMass_eq {r : Nat} (hr : Nat.Prime r) (P Q : Point)
    (hP : P≠0) (hQ : Q≠0) (hrP : order • P=0) (hrQ : order • Q=0)
    (horder : addOrderOf P=r) (d : Nat) (hQd : Q=d • P) (out : Fin (2^256) × Fin (2^208)) :
    reducedWindowTrialFiniteOutputMass P Q hP hQ hrP hrQ out=asymmetricPairMass r 256 208 d out :=
  reducedWindowTrialOutputMass_character_mixture hr P Q hP hQ hrP hrQ horder d hQd _ _
    (paperOutcomeBits_length _ _) (paperOutcomeBits_length _ _) out
    (paperOutcomeBits_word _ _) (paperOutcomeBits_word _ _)
theorem reducedWindowTrialFiniteOutputMass_total {r : Nat} (hr : Nat.Prime r) (P Q : Point)
    (hP : P≠0) (hQ : Q≠0) (hrP : order • P=0) (hrQ : order • Q=0)
    (horder : addOrderOf P=r) (d : Nat) (hQd : Q=d • P) :
    ∑ out : Fin (2^256) × Fin (2^208), reducedWindowTrialFiniteOutputMass P Q hP hQ hrP hrQ out=1 := by
  simp only [reducedWindowTrialFiniteOutputMass_eq hr P Q hP hQ hrP hrQ horder d hQd]
  exact asymmetricPairMass_total r 256 208 d hr.pos

/-- Success mass from the physical decoded distribution and public-point verification. -/
def reducedPhysicalVerifiedMass (Q : Point) (hG : G≠0) (hQ : Q≠0)
    (hrQ : order • Q=0) (d : Nat) : ℝ :=
  ∑ out : Fin (2^256) × Fin (2^208),
    if reducedVerifiedCandidate Q out=some (d:ZMod order) then
      reducedWindowTrialFiniteOutputMass G Q hG hQ generator_nsmul_eq_zero hrQ out else 0

theorem reducedPhysicalVerifiedMass_eq (Q : Point) (hG : G≠0) (hQ : Q≠0)
    (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    reducedPhysicalVerifiedMass Q hG hQ hrQ d=reducedVerifiedMass Q d := by
  unfold reducedPhysicalVerifiedMass reducedVerifiedMass
  simp only [reducedWindowTrialFiniteOutputMass_eq order_prime G Q hG hQ
    generator_nsmul_eq_zero hrQ generator_order d hQd]

theorem reducedPhysicalVerifiedMass_lower (Q : Point) (hG : G≠0) (hQ : Q≠0)
    (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    (((order-1:Nat):ℝ)/(order:ℝ))*((4:ℝ)/Real.pi^2)^2 ≤
      reducedPhysicalVerifiedMass Q hG hQ hrQ d := by
  rw [reducedPhysicalVerifiedMass_eq Q hG hQ hrQ d hQd]
  exact reducedVerifiedMass_lower Q d hQd

/-- One nonzero-public-point circuit has normalized observations, verified success, and bounded support. -/
theorem reducedPhysical_success_certificate (Q : Point) (hG : G≠0) (hQ : Q≠0)
    (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    (∑ out : Fin (2^256) × Fin (2^208),
      reducedWindowTrialFiniteOutputMass G Q hG hQ generator_nsmul_eq_zero hrQ out)=1 ∧
    (((order-1:Nat):ℝ)/(order:ℝ))*((4:ℝ)/Real.pi^2)^2 ≤
      reducedPhysicalVerifiedMass Q hG hQ hrQ d ∧
    (reducedWindowTrialProgram G Q hG hQ generator_nsmul_eq_zero hrQ).qubitCount≤1303 :=
  ⟨reducedWindowTrialFiniteOutputMass_total order_prime G Q hG hQ
    generator_nsmul_eq_zero hrQ generator_order d hQd,
   reducedPhysicalVerifiedMass_lower Q hG hQ hrQ d hQd,
   reducedWindowTrialProgram_qubitCount G Q hG hQ generator_nsmul_eq_zero hrQ⟩
end
end ShorECDLP.Paper2607_13816
