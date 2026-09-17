import ShorECDLP.Submission.«2607_13816».OrderFinding.ReducedPeak
import ShorECDLP.Submission.«2607_13816».OrderFinding.Normalization
namespace ShorECDLP.Paper2607_13816
open scoped BigOperators
noncomputable section
/-- Character mixture with independent Fourier precisions. -/
def asymmetricPairMass (r n m d : Nat) (out : Fin (2^n) × Fin (2^m)) : ℝ :=
  (1/(r:ℝ)) * ∑ k : Fin r,
    Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) out.1.val) *
      Complex.normSq (paperPhaseAmplitude m ((((d*k.val)%r:Nat):ℝ)/r) out.2.val)

def asymmetricPairPeak (r n m d : Nat) (hn : r<2^n) (k : Fin r) :
    Fin (2^n) × Fin (2^m) :=
  (paperPeak r n hn k, reducedPeak r m (paperCharacterProduct d k))

theorem asymmetricPairPeak_injective (r n m d : Nat) (hn : r<2^n) :
    Function.Injective (asymmetricPairPeak r n m d hn) := by
  intro k l h
  exact paperPeak_injective r n hn (congrArg Prod.fst h)

theorem asymmetricPairPeak_mass (r n m d : Nat) (hn : r<2^n) (k : Fin r) :
    (1/(r:ℝ))*((4:ℝ)/Real.pi^2)^2 ≤
      asymmetricPairMass r n m d (asymmetricPairPeak r n m d hn k) := by
  unfold asymmetricPairMass
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have ha := paperPhasePeak_mass r n hn k
  have hb := reducedPeak_mass r m (paperCharacterProduct d k)
  apply le_trans _ (Finset.single_le_sum
    (fun i _ => mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)) (Finset.mem_univ k))
  change ((4:ℝ)/Real.pi^2)^2 ≤ _
  rw [pow_two]
  exact mul_le_mul ha hb (by positivity) (Complex.normSq_nonneg _)

theorem asymmetricPairMass_total (r n m d : Nat) (hr : 0<r) :
    ∑ out : Fin (2^n) × Fin (2^m), asymmetricPairMass r n m d out = 1 := by
  unfold asymmetricPairMass
  rw [← Finset.mul_sum,Finset.sum_comm]
  have h (k : Fin r) :
      ∑ out : Fin (2^n) × Fin (2^m),
        Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) out.1.val) *
        Complex.normSq (paperPhaseAmplitude m ((((d*k.val)%r:Nat):ℝ)/r) out.2.val)=1 := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum,paperPhaseAmplitude_totalMass,mul_one]
  simp_rw [h]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have hr' : (r:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hr
  exact one_div_mul_cancel hr'
end
end ShorECDLP.Paper2607_13816
