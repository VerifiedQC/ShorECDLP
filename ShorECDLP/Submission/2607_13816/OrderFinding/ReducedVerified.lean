import ShorECDLP.Submission.«2607_13816».OrderFinding.ReducedCoverage
import ShorECDLP.Submission.«2607_13816».Window.Total
namespace ShorECDLP.Paper2607_13816
open Classical ShorECDLP.Secp256k1
noncomputable section
/-- Search only the finite reduced-precision list and check the public point. -/
def reducedVerifiedCandidate (Q : Point) (out : Fin (2^256) × Fin (2^208)) : Option (ZMod order) := by
  classical
  exact if h : ∃ c ∈ reducedShiftCandidates order 256 208 out, c.val • G=Q then some h.choose else none

theorem reducedVerifiedCandidate_sound (Q : Point) (d : Nat) (hQd : Q=d • G)
    (out : Fin (2^256) × Fin (2^208)) (c : ZMod order)
    (hc : reducedVerifiedCandidate Q out=some c) : c=(d:ZMod order) := by
  unfold reducedVerifiedCandidate at hc
  split_ifs at hc with h
  · have he := Option.some.inj hc
    exact he ▸ (secpCandidate_correct Q d hQd h.choose).mp h.choose_spec.2

theorem reducedVerifiedCandidate_complete (Q : Point) (d : Nat) (hQd : Q=d • G)
    (out : Fin (2^256) × Fin (2^208)) :
    reducedVerifiedCandidate Q out=some (d:ZMod order) ↔
      (d:ZMod order) ∈ reducedShiftCandidates order 256 208 out := by
  constructor
  · intro hc
    unfold reducedVerifiedCandidate at hc
    split_ifs at hc with h
    · exact Option.some.inj hc ▸ h.choose_spec.1
  · intro hm
    have h : ∃ c ∈ reducedShiftCandidates order 256 208 out, c.val • G=Q :=
      ⟨(d:ZMod order), hm, (secpCandidate_correct Q d hQd _).mpr rfl⟩
    unfold reducedVerifiedCandidate
    rw [dif_pos h]
    congr 1
    exact (secpCandidate_correct Q d hQd _).mp h.choose_spec.2

open scoped BigOperators
/-- Mathematical success mass after checking every candidate against the public point. -/
def reducedVerifiedMass (Q : Point) (d : Nat) : ℝ :=
  ∑ out : Fin (2^256) × Fin (2^208),
    if reducedVerifiedCandidate Q out=some (d:ZMod order) then asymmetricPairMass order 256 208 d out else 0

theorem reducedVerifiedMass_eq (Q : Point) (d : Nat) (hQd : Q=d • G) :
    reducedVerifiedMass Q d = reducedCoverageMass order 256 208 d := by
  unfold reducedVerifiedMass reducedCoverageMass
  simp_rw [reducedVerifiedCandidate_complete Q d hQd]

theorem reducedVerifiedMass_lower (Q : Point) (d : Nat) (hQd : Q=d • G) :
    ((order-1:Nat):ℝ)/(order:ℝ) * ((4:ℝ)/Real.pi^2)^2 ≤ reducedVerifiedMass Q d := by
  letI : Fact (Nat.Prime order) := ⟨order_prime⟩
  rw [reducedVerifiedMass_eq Q d hQd]
  exact reducedCoverageMass_lower order 256 208 d reducedLeftPrecision_order
end
end ShorECDLP.Paper2607_13816
