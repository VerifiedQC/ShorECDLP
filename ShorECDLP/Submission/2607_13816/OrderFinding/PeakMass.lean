import ShorECDLP.Submission.«2607_13816».OrderFinding.Postprocess
import ShorECDLP.Math.PhaseApproximation
namespace ShorECDLP.Paper2607_13816
open ShorECDLP Quantum.OrderFinding Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section
theorem nearNumerator_abs (r precision k value : Nat) (hr : 0<r)
    (h : NearNumerator r precision k value) :
    |(k:ℝ)/(r:ℝ)-(value:ℝ)/(2^precision:Nat)| ≤ (1:ℝ)/(2*(2^precision:Nat)) := by
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have hNR : (0:ℝ)<(2^precision:Nat) := by positivity
  have h₁ : (2:ℝ)*(2^precision:Nat)*k ≤ 2*r*value+r := by exact_mod_cast h.1
  have h₂ : (2:ℝ)*r*value ≤ 2*(2^precision:Nat)*k+r := by exact_mod_cast h.2
  have hb : |(k:ℝ)*(2^precision:Nat)-(r:ℝ)*value| ≤ (r:ℝ)/2 := by
    rw [abs_le]; constructor <;> nlinarith
  calc
    |(k:ℝ)/(r:ℝ)-(value:ℝ)/(2^precision:Nat)| =
        |(k:ℝ)*(2^precision:Nat)-(r:ℝ)*value|/((r:ℝ)*(2^precision:Nat)) := by
      rw [div_sub_div _ _ (ne_of_gt hrR) (ne_of_gt hNR), abs_div, abs_of_pos (mul_pos hrR hNR)]
    _ ≤ ((r:ℝ)/2)/((r:ℝ)*(2^precision:Nat)) :=
      div_le_div_of_nonneg_right hb (le_of_lt (mul_pos hrR hNR))
    _ = (1:ℝ)/(2*(2^precision:Nat)) := by field_simp
/-- The mathematical phase-sampling amplitude, with inverse Fourier sign. -/
def paperPhaseAmplitude (precision : Nat) (phase : ℝ) (value : Nat) : ℂ :=
  ((2^precision:Nat):ℂ)⁻¹ * ∑ x ∈ Finset.range (2^precision),
    eigenvalue (phase-(value:ℝ)/(2^precision:Nat))^x

theorem paperPhasePeak_mass (r precision : Nat) (hprecision : r<2^precision) (k : Fin r) :
    (4:ℝ)/Real.pi^2 ≤ Complex.normSq
      (paperPhaseAmplitude precision ((k.val:ℝ)/(r:ℝ)) (paperPeak r precision hprecision k).val) := by
  apply geometric_phase_average_lower_bound
  · positivity
  · exact le_trans (min_le_left _ _) (nearNumerator_abs _ _ _ _ (by have := k.isLt; omega)
      (paperPeak_near _ _ _ _))
end
end ShorECDLP.Paper2607_13816
