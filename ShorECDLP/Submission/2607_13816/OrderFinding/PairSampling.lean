import ShorECDLP.Submission.«2607_13816».OrderFinding.PeakMass
namespace ShorECDLP.Paper2607_13816
open ShorECDLP Quantum.OrderFinding
open scoped BigOperators
noncomputable section
def paperCharacterProduct {r : Nat} (d : Nat) (k : Fin r) : Fin r :=
  ⟨(d*k.val)%r, Nat.mod_lt _ (by have := k.isLt; omega)⟩
def paperPairPeak (r precision d : Nat) (hprecision : r<2^precision) (k : Fin r) :
    Fin (2^precision) × Fin (2^precision) :=
  (paperPeak r precision hprecision k, paperPeak r precision hprecision (paperCharacterProduct d k))
/-- Uniform character mixture; connection to the physical oracle is a separate theorem. -/
def paperPairMass (r precision d : Nat) (out : Fin (2^precision) × Fin (2^precision)) : ℝ :=
  (1/(r:ℝ)) * ∑ k : Fin r,
    Complex.normSq (paperPhaseAmplitude precision ((k.val:ℝ)/(r:ℝ)) out.1.val) *
      Complex.normSq (paperPhaseAmplitude precision ((((d*k.val)%r:Nat):ℝ)/(r:ℝ)) out.2.val)

theorem paperPairMass_nonneg (r precision d : Nat) (out : Fin (2^precision) × Fin (2^precision)) :
    0 ≤ paperPairMass r precision d out := by
  unfold paperPairMass
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))

theorem paperPairPeak_injective (r precision d : Nat) (hprecision : r<2^precision) :
    Function.Injective (paperPairPeak r precision d hprecision) := by
  intro k l h
  exact paperPeak_injective r precision hprecision (congrArg Prod.fst h)

theorem paperPairPeak_postprocess (r precision d : Nat) (hr : Nat.Prime r)
    (hprecision : r<2^precision) (k : Fin r) (hk : k.val ≠ 0) :
    orderFindingPostprocess r precision hr (paperPairPeak r precision d hprecision k)=some (d:ZMod r) := by
  apply paperPostprocess_correct r precision d k.val hr hprecision
  · intro hz
    have hv := congrArg ZMod.val hz
    simp only [ZMod.val_natCast_of_lt k.isLt, ZMod.val_zero] at hv
    exact hk hv
  · exact paperPeak_near r precision hprecision k
  · exact paperPeak_near r precision hprecision (paperCharacterProduct d k)

theorem paperPairPeak_mass (r precision d : Nat) (hprecision : r<2^precision) (k : Fin r) :
    (1/(r:ℝ))*((4:ℝ)/Real.pi^2)^2 ≤
      paperPairMass r precision d (paperPairPeak r precision d hprecision k) := by
  unfold paperPairMass
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have ha := paperPhasePeak_mass r precision hprecision k
  have hb := paperPhasePeak_mass r precision hprecision (paperCharacterProduct d k)
  apply le_trans _ (Finset.single_le_sum (fun i _ => mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)) (Finset.mem_univ k))
  change ((4:ℝ)/Real.pi^2)^2 ≤ _
  rw [pow_two]
  exact mul_le_mul ha hb (by positivity) (Complex.normSq_nonneg _)

def paperSuccessMass (r precision d : Nat) (hr : Nat.Prime r) : ℝ :=
  ∑ out : Fin (2^precision) × Fin (2^precision),
    if orderFindingPostprocess r precision hr out=some (d:ZMod r) then paperPairMass r precision d out else 0

/-- Success mass of the mathematical character mixture; the physical-oracle refinement is separate. -/
theorem paperSuccessMass_lower (r precision d : Nat) (hr : Nat.Prime r)
    (hprecision : r<2^precision) :
    ((r-1:Nat):ℝ)/(r:ℝ) * ((4:ℝ)/Real.pi^2)^2 ≤ paperSuccessMass r precision d hr := by
  classical
  let S : Finset (Fin r) := Finset.univ.filter (fun k => k.val ≠ 0)
  let peak := paperPairPeak r precision d hprecision
  let f : (Fin (2^precision) × Fin (2^precision)) → ℝ := fun out =>
    if orderFindingPostprocess r precision hr out=some (d:ZMod r)
      then paperPairMass r precision d out else 0
  have hf : ∀ out, 0 ≤ f out := by
    intro out
    dsimp [f]
    split
    · exact paperPairMass_nonneg _ _ _ _
    · rfl
  have hp : ∀ k ∈ S, (1/(r:ℝ))*((4:ℝ)/Real.pi^2)^2 ≤ f (peak k) := by
    intro k hk
    have hn : k.val ≠ 0 := (Finset.mem_filter.mp hk).2
    dsimp [f, peak]
    rw [paperPairPeak_postprocess r precision d hr hprecision k hn, if_pos rfl]
    exact paperPairPeak_mass _ _ _ _ _
  have hcard : S.card=r-1 := by
    have he : S=Finset.univ.erase (⟨0,hr.pos⟩ : Fin r) := by
      ext k
      simp [S, Fin.ext_iff]
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
      exact paperPairPeak_injective r precision d hprecision he
    _ ≤ ∑ out, f out := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun out _ _ => hf out)
    _ = paperSuccessMass r precision d hr := rfl
end
end ShorECDLP.Paper2607_13816
