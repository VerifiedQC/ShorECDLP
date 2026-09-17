import ShorECDLP.Submission.«2607_13816».OrderFinding.PeakMass
namespace ShorECDLP.Paper2607_13816
/-- A rounded sample before wrapping the endpoint back to zero. -/
def reducedPeakRaw (r precision : Nat) (k : Fin r) : Nat :=
  (2*2^precision*k.val+r)/(2*r)

theorem reducedPeakRaw_near (r precision : Nat) (k : Fin r) :
    NearNumerator r precision k.val (reducedPeakRaw r precision k) := by
  have hr : 0<2*r := by have := k.isLt; omega
  have h₁ := Nat.div_mul_le_self (2*2^precision*k.val+r) (2*r)
  have h₂ := Nat.lt_mul_div_succ (2*2^precision*k.val+r) hr
  unfold NearNumerator reducedPeakRaw
  constructor <;> nlinarith

theorem reducedPeakRaw_le (r precision : Nat) (k : Fin r) :
    reducedPeakRaw r precision k ≤ 2^precision := by
  have hr : 0<2*r := by have := k.isLt; omega
  have hk := k.isLt
  have hn : 0<2^precision := by positivity
  unfold reducedPeakRaw
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hr).mpr
  nlinarith

open ShorECDLP.Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section

def reducedPeak (r precision : Nat) (k : Fin r) : Fin (2^precision) :=
  ⟨reducedPeakRaw r precision k % 2^precision, Nat.mod_lt _ (by positivity)⟩

private theorem eigenvalue_period (phase : ℝ) : eigenvalue (phase-1)=eigenvalue phase := by
  unfold eigenvalue
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-1, ?_⟩
  push_cast
  ring

private theorem amplitude_endpoint (precision : Nat) (phase : ℝ) :
    paperPhaseAmplitude precision phase (2^precision) = paperPhaseAmplitude precision phase 0 := by
  unfold paperPhaseAmplitude
  simp only [Nat.cast_zero, zero_div, sub_zero]
  have hN : ((2^precision:Nat):ℝ) ≠ 0 := by positivity
  simp only [div_self hN, eigenvalue_period]

theorem reducedPeak_mass (r precision : Nat) (k : Fin r) :
    (4:ℝ)/Real.pi^2 ≤ Complex.normSq
      (paperPhaseAmplitude precision ((k.val:ℝ)/(r:ℝ)) (reducedPeak r precision k).val) := by
  have hraw : (4:ℝ)/Real.pi^2 ≤ Complex.normSq
      (paperPhaseAmplitude precision ((k.val:ℝ)/(r:ℝ)) (reducedPeakRaw r precision k)) := by
    apply geometric_phase_average_lower_bound
    · positivity
    · exact le_trans (min_le_left _ _) (nearNumerator_abs _ _ _ _
        (by have := k.isLt; omega) (reducedPeakRaw_near _ _ _))
  have hle := reducedPeakRaw_le r precision k
  by_cases heq : reducedPeakRaw r precision k = 2^precision
  · simpa [reducedPeak, heq, amplitude_endpoint] using hraw
  · simpa [reducedPeak, Nat.mod_eq_of_lt (by omega : reducedPeakRaw r precision k < 2^precision)] using hraw
end
end ShorECDLP.Paper2607_13816
