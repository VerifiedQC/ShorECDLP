import ShorECDLP.Submission.«2607_13816».OrderFinding.AsymmetricPair
import ShorECDLP.Submission.«2607_13816».OrderFinding.WrappedCandidates
namespace ShorECDLP.Paper2607_13816
open scoped BigOperators
noncomputable section

theorem asymmetricPairMass_nonneg (r n m d : Nat) (out : Fin (2^n) × Fin (2^m)) :
    0 ≤ asymmetricPairMass r n m d out := by
  unfold asymmetricPairMass
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))

/-- Probability that the bounded list contains the true logarithm, before point verification. -/
def reducedCoverageMass (r n m d : Nat) : ℝ :=
  ∑ out : Fin (2^n) × Fin (2^m),
    if (d:ZMod r) ∈ reducedShiftCandidates r n m out then asymmetricPairMass r n m d out else 0
/-- Success mass of the mathematical character mixture; the physical-oracle refinement is separate. -/
theorem reducedCoverageMass_lower (r n m d : Nat) [Fact (Nat.Prime r)]
    (hprecision : r<2^n) :
    ((r-1:Nat):ℝ)/(r:ℝ) * ((4:ℝ)/Real.pi^2)^2 ≤ reducedCoverageMass r n m d := by
  classical
  have hr := Fact.out (p := Nat.Prime r)
  let S : Finset (Fin r) := Finset.univ.filter (fun k => k.val ≠ 0)
  let peak := asymmetricPairPeak r n m d hprecision
  let f : (Fin (2^n) × Fin (2^m)) → ℝ := fun out =>
    if (d:ZMod r) ∈ reducedShiftCandidates r n m out
      then asymmetricPairMass r n m d out else 0
  have hf : ∀ out, 0 ≤ f out := by
    intro out
    dsimp [f]
    split
    · exact asymmetricPairMass_nonneg _ _ _ _ _
    · rfl
  have hp : ∀ k ∈ S, (1/(r:ℝ))*((4:ℝ)/Real.pi^2)^2 ≤ f (peak k) := by
    intro k hk
    have hn : k.val ≠ 0 := (Finset.mem_filter.mp hk).2
    dsimp [f, peak]
    have hkz : (k.val : ZMod r) ≠ 0 := by
      intro hz
      have hv := congrArg ZMod.val hz
      simp only [ZMod.val_natCast_of_lt k.isLt, ZMod.val_zero] at hv
      exact hn hv
    have hm : (d:ZMod r) ∈ reducedShiftCandidates r n m (asymmetricPairPeak r n m d hprecision k) :=
      reducedShiftCandidates_correct r n m d hprecision k hkz
    rw [if_pos hm]
    exact asymmetricPairPeak_mass _ _ _ _ _ _
  have hcard : S.card=r-1 := by
    have he : S=Finset.univ.erase (⟨0,hr.pos⟩ : Fin r) := by
      ext k
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      constructor
      · intro hn he; exact hn (congrArg Fin.val he)
      · intro hn he; exact hn (Fin.ext he)
    rw [he]
    simp
  calc
    ((r-1:Nat):ℝ)/(r:ℝ) * ((4:ℝ)/Real.pi^2)^2 =
        ∑ k ∈ S, (1/(r:ℝ))*((4:ℝ)/Real.pi^2)^2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, hcard]
      ring
    _ ≤ ∑ k ∈ S, f (peak k) := Finset.sum_le_sum hp
    _ = ∑ out ∈ S.image peak, f out := by
      rw [Finset.sum_image]
      intro k _ l _ he
      exact asymmetricPairPeak_injective r n m d hprecision he
    _ ≤ ∑ out, f out := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun out _ _ => hf out)
    _ = reducedCoverageMass r n m d := rfl
/-- The 256-bit left register still resolves every secp256k1 character. -/
theorem reducedLeftPrecision_order : ShorECDLP.order < 2^256 := by
  decide +kernel
end
end ShorECDLP.Paper2607_13816
