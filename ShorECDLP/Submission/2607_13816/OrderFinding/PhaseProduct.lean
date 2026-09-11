import ShorECDLP.Submission.«2607_13816».Fourier.Kernel
import ShorECDLP.Submission.«2607_13816».OrderFinding.PhaseStep
import ShorECDLP.Submission.«2607_13816».OrderFinding.PeakMass
namespace ShorECDLP.Paper2607_13816
open ShorECDLP Quantum Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section
/-- The scalar produced by successive recycled-control outcomes, largest power first. -/
def phaseProduct (phase : ℝ) : List Bool → List Bool → ℂ
  | _, [] => 1
  | prior, b::bs =>
      (((Real.sqrt 2)⁻¹:ℝ):ℂ) *
        (xResetCoeff b false + eigenvalue (phase * (2:ℝ)^bs.length) *
          Complex.exp (Complex.I * (fourierHistoryAngle .inverse prior 2:ℂ)) * xResetCoeff b true) *
        phaseProduct phase (b::prior) bs

def dyadicPhaseAverage (n : Nat) (z : ℂ) : ℂ :=
  ((2^n:Nat):ℂ)⁻¹ * ∑ x ∈ Finset.range (2^n), z^x

theorem dyadicPhaseAverage_succ (n : Nat) (z : ℂ) :
    dyadicPhaseAverage (n+1) z = (1/2:ℂ) * (1+z^(2^n)) * dyadicPhaseAverage n z := by
  unfold dyadicPhaseAverage
  rw [show 2^(n+1)=2^n+2^n by omega, Finset.sum_range_add]
  simp_rw [pow_add]
  rw [← Finset.mul_sum]
  push_cast
  have h : (2:ℂ)^n≠0 := pow_ne_zero _ (by norm_num)
  field_simp
  ring

def phaseProductRoot (phase : ℝ) (prior bs : List Bool) : ℂ :=
  eigenvalue phase * phaseCoeff .inverse bs.length ^ fourierWordLSB bs *
    Complex.exp (Complex.I * (fourierHistoryAngle .inverse prior (bs.length+1):ℂ))

theorem phaseProductRoot_cons (phase : ℝ) (prior : List Bool) (b : Bool) (bs : List Bool) :
    phaseProductRoot phase prior (b::bs) = phaseProductRoot phase (b::prior) bs := by
  unfold phaseProductRoot
  simp only [List.length_cons,fourierWordLSB,pow_add,pow_mul,dyadicPhase_square]
  cases b <;> simp only [fourierHistoryAngle,Bool.false_eq_true,if_false,if_true,
    Bool.toNat_false,Bool.toNat_true,pow_zero,pow_one,one_mul,zero_add]
  rw [phaseCoeff]
  push_cast
  rw [mul_add,Complex.exp_add]
  ring
theorem phaseProductRoot_power (phase : ℝ) (prior : List Bool) (b : Bool) (bs : List Bool) :
    phaseProductRoot phase prior (b::bs) ^ (2^bs.length) =
      eigenvalue (phase * (2:ℝ)^bs.length) * (-1:ℂ)^b.toNat *
        Complex.exp (Complex.I * (fourierHistoryAngle .inverse prior 2:ℂ)) := by
  unfold phaseProductRoot
  simp only [List.length_cons,mul_pow,fourierWordLSB,pow_add]
  rw [pow_mul,dyadicPhase_square]
  have swap (a : ℂ) (x y : Nat) : (a^x)^y=(a^y)^x := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
  rw [swap (phaseCoeff .inverse bs.length),dyadicPhase_period,one_pow,mul_one,
    swap (phaseCoeff .inverse (bs.length+1)),dyadicPhase_half_period]
  rw [eigenvalue_pow_eq_eigenvalue_mul,← Complex.exp_nat_mul]
  have h := fourierHistoryAngle_scale .inverse prior 2 bs.length
  rw [Nat.add_comm 2 bs.length] at h
  have hc := congrArg (fun r : ℝ => (r:ℂ)) h
  push_cast at hc ⊢
  rw [mul_comm ((2:ℝ)^bs.length) phase]
  congr 1
  congr 1
  linear_combination Complex.I * hc
private theorem phaseProduct_factor (phase : ℝ) (prior : List Bool) (b : Bool) (n : Nat) :
    (((Real.sqrt 2)⁻¹:ℝ):ℂ) *
      (xResetCoeff b false + eigenvalue (phase*(2:ℝ)^n) *
        Complex.exp (Complex.I*(fourierHistoryAngle .inverse prior 2:ℂ)) * xResetCoeff b true) =
      (1/2:ℂ) * (1+eigenvalue (phase*(2:ℝ)^n) * (-1:ℂ)^b.toNat *
        Complex.exp (Complex.I*(fourierHistoryAngle .inverse prior 2:ℂ))) := by
  have h : ((((Real.sqrt 2)⁻¹:ℝ):ℂ))^2=(1/2:ℂ) := by
    rw [← Complex.ofReal_pow,inv_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  push_cast at h
  cases b <;> simp [xResetCoeff]
  · linear_combination h * (1+eigenvalue (phase*(2:ℝ)^n) *
      Complex.exp (Complex.I*(fourierHistoryAngle .inverse prior 2:ℂ)))
  · linear_combination h * (1-eigenvalue (phase*(2:ℝ)^n) *
      Complex.exp (Complex.I*(fourierHistoryAngle .inverse prior 2:ℂ)))

theorem phaseProduct_average (phase : ℝ) (prior bs : List Bool) :
    phaseProduct phase prior bs = dyadicPhaseAverage bs.length (phaseProductRoot phase prior bs) := by
  induction bs generalizing prior with
  | nil => simp [phaseProduct,dyadicPhaseAverage]
  | cons b bs ih =>
    rw [phaseProduct,phaseProduct_factor,ih,List.length_cons,dyadicPhaseAverage_succ,
      phaseProductRoot_power,phaseProductRoot_cons]
theorem phaseProductRoot_nil (phase : ℝ) (bs : List Bool) :
    phaseProductRoot phase List.nil bs =
      eigenvalue (phase-(fourierWordLSB bs:ℝ)/(2^bs.length:Nat)) := by
  simp only [phaseProductRoot,fourierHistoryAngle,Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one]
  rw [phaseCoeff,← Complex.exp_nat_mul]
  unfold eigenvalue
  rw [← Complex.exp_add]
  congr 1
  simp only [phaseAngle]
  push_cast
  ring

theorem phaseProduct_eq_amplitude (phase : ℝ) (bs : List Bool) :
    phaseProduct phase List.nil bs=paperPhaseAmplitude bs.length phase (fourierWordLSB bs) := by
  rw [phaseProduct_average,phaseProductRoot_nil]
  rfl
/-- The scalar recurrence uses exactly the coefficient of the physical point-oracle step. -/
theorem phaseProduct_cons_point (r k : Nat) (prior bs : List Bool) (b : Bool) :
    phaseProduct ((k:ℝ)/(r:ℝ)) prior (b::bs) =
      pointPhaseStepCoeff r k (2^bs.length) prior b *
        phaseProduct ((k:ℝ)/(r:ℝ)) (b::prior) bs := by
  rw [phaseProduct,pointPhaseStepCoeff]
  have h : (k:ℝ)/(r:ℝ)*(2:ℝ)^bs.length=((k*2^bs.length:Nat):ℝ)/(r:ℝ) := by
    push_cast
    ring
  rw [h]
/-- The physical scalar recurrence inherits the nearest-peak lower bound. -/
theorem phaseProduct_peak_mass (r precision : Nat) (hprecision : r<2^precision) (k : Fin r)
    (bs : List Bool) (hlen : bs.length=precision)
    (hword : fourierWordLSB bs=(paperPeak r precision hprecision k).val) :
    (4:ℝ)/Real.pi^2 ≤ Complex.normSq (phaseProduct ((k.val:ℝ)/(r:ℝ)) List.nil bs) := by
  rw [phaseProduct_eq_amplitude,hlen,hword]
  exact paperPhasePeak_mass r precision hprecision k
end
end ShorECDLP.Paper2607_13816
