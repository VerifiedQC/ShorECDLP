import ShorECDLP.Submission.«2607_13816».Window.ReducedKernel
import ShorECDLP.Submission.«2607_13816».Window.CharacterMixture
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1 Quantum.PhaseEstimation Quantum.OrderFinding
open scoped BigOperators
noncomputable section
/-- The actual windowed circuit's observed pair has the character-mixture probability. -/
theorem reducedWindowTrialOutputMass_character_mixture {r : Nat} (hr : Nat.Prime r)
    (P Q : Point) (hP : P≠0) (hQ : Q≠0) (hrP : order • P=0) (hrQ : order • Q=0)
    (horder : addOrderOf P=r) (d : Nat) (hQd : Q=d • P)
    (x y : List Bool) (hx : x.length=256) (hy : y.length=208)
    (out : Fin (2^256) × Fin (2^208)) (hox : fourierWordLSB x=out.1.val)
    (hoy : fourierWordLSB y=out.2.val) :
    reducedWindowTrialOutputMass P Q hP hQ hrP hrQ x y=asymmetricPairMass r 256 208 d out := by
  rw [reducedWindowTrialOutputMass_point_sum P Q hP hQ hrP hrQ x y hx hy]
  rw [pointDoubleSum_normalize _ _ _ _ _ P Q d hQd zeroBasisState]
  have hp : ((((Real.sqrt 2)⁻¹:ℝ):ℂ)^464)=
      ((((Real.sqrt 2)⁻¹:ℝ):ℂ)^256)*((((Real.sqrt 2)⁻¹:ℝ):ℂ)^208) := by
    rw [←pow_add]
  rw [hp]
  exact asymmetric_point_character_mass hr P horder zeroBasisState 256 208 d x y hx hy out hox hoy

end
end ShorECDLP.Paper2607_13816
