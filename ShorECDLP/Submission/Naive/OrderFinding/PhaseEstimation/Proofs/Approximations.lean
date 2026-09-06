import ShorECDLP.Submission.Naive.OrderFinding.PhaseEstimation.Proofs.Fourier
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace ShorECDLP.Quantum.PhaseEstimation

open scoped BigOperators

noncomputable section

theorem exists_nearest_phase_value
    (precision : Nat)
    (phase : ℝ)
    (hphaseNonneg : 0 ≤ phase)
    (hphaseLtOne : phase < 1) :
    ∃ value : Fin (2 ^ precision),
      circularDistance precision phase value ≤
        (1 : ℝ) / (2 * (2 ^ precision : Nat)) := by
  let N : Nat := 2 ^ precision
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hNR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN
  let a : ℝ := (N : ℝ) * phase + 1 / 2
  have ha0 : 0 ≤ a := by
    dsimp [a]
    have h := mul_nonneg (le_of_lt hNR) hphaseNonneg
    linarith
  let k : Nat := ⌊a⌋₊
  have hk_le_a : (k : ℝ) ≤ a := by
    dsimp [k]
    exact Nat.floor_le ha0
  have ha_lt_k1 : a < (k : ℝ) + 1 := by
    dsimp [k]
    exact Nat.lt_floor_add_one a
  have ha_lt_N1 : a < (N : ℝ) + 1 := by
    dsimp [a]
    have hmul : (N : ℝ) * phase < (N : ℝ) := by
      simpa using mul_lt_mul_of_pos_left hphaseLtOne hNR
    linarith
  have hk_lt_succ : k < N + 1 := by
    dsimp [k]
    apply (Nat.floor_lt ha0).2
    simpa using ha_lt_N1
  have hk_le : k ≤ N := by omega
  by_cases hkN : k = N
  · refine ⟨⟨0, by simp [N, hN]⟩, ?_⟩
    unfold circularDistance
    simp
    rw [abs_of_nonneg hphaseNonneg]
    have hone : 0 ≤ 1 - phase := by linarith
    rw [abs_of_nonneg hone]
    refine Or.inr ?_
    have hunit :
        (N : ℝ) * (1 - phase) ≤ (1 : ℝ) / 2 := by
      rw [hkN] at hk_le_a
      dsimp [a] at hk_le_a
      nlinarith
    dsimp [N] at hunit hNR
    calc
      1 - phase =
          (((2 ^ precision : Nat) : ℝ) * (1 - phase)) /
            ((2 ^ precision : Nat) : ℝ) := by
          field_simp [ne_of_gt hNR]
      _ ≤ ((1 : ℝ) / 2) / ((2 ^ precision : Nat) : ℝ) := by
          exact (div_le_div_iff_of_pos_right hNR).2 hunit
      _ = ((2 ^ precision : Nat) : ℝ)⁻¹ * (2 : ℝ)⁻¹ := by
          field_simp [ne_of_gt hNR]
      _ = ((2 : ℝ) ^ precision)⁻¹ * (2 : ℝ)⁻¹ := by
          norm_cast
  · have hklt : k < N := by omega
    refine ⟨⟨k, by simpa [N] using hklt⟩, ?_⟩
    unfold circularDistance
    apply le_trans (min_le_left _ _)
    change
      |phase - (k : ℝ) / (N : ℝ)| ≤
        (1 : ℝ) / (2 * (N : ℝ))
    have hscaled :
        |(N : ℝ) * phase - (k : ℝ)| ≤ (1 : ℝ) / 2 := by
      rw [abs_le]
      constructor
      · dsimp [a] at hk_le_a
        linarith
      · dsimp [a] at ha_lt_k1
        linarith
    have hid :
        phase - (k : ℝ) / (N : ℝ) =
          ((N : ℝ) * phase - (k : ℝ)) / (N : ℝ) := by
      field_simp [ne_of_gt hNR]
    rw [hid, abs_div, abs_of_pos hNR]
    calc
      |(N : ℝ) * phase - (k : ℝ)| / (N : ℝ)
          ≤ ((1 : ℝ) / 2) / (N : ℝ) := by
            exact (div_le_div_iff_of_pos_right hNR).2 hscaled
      _ = (1 : ℝ) / (2 * (N : ℝ)) := by
        field_simp [ne_of_gt hNR]

private theorem eigenvalue_add_one (delta : ℝ) :
    eigenvalue (delta + 1) = eigenvalue delta := by
  unfold eigenvalue
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨1, ?_⟩
  push_cast
  ring

private theorem eigenvalue_sub_one (delta : ℝ) :
    eigenvalue (delta - 1) = eigenvalue delta := by
  unfold eigenvalue
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-1, ?_⟩
  push_cast
  ring

private theorem norm_eigenvalue_sub_one (delta : ℝ) :
    ‖eigenvalue delta - 1‖ =
      ‖2 * Real.sin (Real.pi * delta)‖ := by
  unfold eigenvalue
  convert
    Complex.norm_exp_I_mul_ofReal_sub_one
      (2 * Real.pi * delta) using 1 ; ring_nf

private theorem norm_eigenvalue_pow_sub_one
    (N : Nat) (delta : ℝ) :
    ‖eigenvalue delta ^ N - 1‖ =
      ‖2 * Real.sin (Real.pi * (N : ℝ) * delta)‖ := by
  rw [eigenvalue_pow_eq_eigenvalue_mul]
  convert
    norm_eigenvalue_sub_one ((N : ℝ) * delta) using 1 ; ring_nf

private theorem norm_eigenvalue_sub_one_le
    (delta : ℝ) :
    ‖eigenvalue delta - 1‖ ≤
      2 * Real.pi * |delta| := by
  rw [norm_eigenvalue_sub_one, Real.norm_eq_abs]
  calc
    |2 * Real.sin (Real.pi * delta)|
        = 2 * |Real.sin (Real.pi * delta)| := by
            rw [abs_mul]
            norm_num
    _ ≤ 2 * |Real.pi * delta| := by
          exact mul_le_mul_of_nonneg_left
            (Real.abs_sin_le_abs (x := Real.pi * delta))
            (by norm_num)
    _ = 2 * Real.pi * |delta| := by
          rw [abs_mul, abs_of_pos Real.pi_pos]
          ring

private theorem four_mul_abs_le_norm_eigenvalue_pow_sub_one
    (N : Nat)
    (hN : 0 < N)
    (delta : ℝ)
    (hsmall : |delta| ≤ (1 : ℝ) / (2 * N)) :
    4 * (N : ℝ) * |delta| ≤
      ‖eigenvalue delta ^ N - 1‖ := by
  have hNR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN
  have hNdelta :
      (N : ℝ) * |delta| ≤ (1 : ℝ) / 2 := by
    calc
      (N : ℝ) * |delta|
          ≤ (N : ℝ) * ((1 : ℝ) / (2 * N)) :=
            mul_le_mul_of_nonneg_left hsmall (le_of_lt hNR)
      _ = (1 : ℝ) / 2 := by
            field_simp [ne_of_gt hNR]
  have hx :
      |Real.pi * (N : ℝ) * delta| ≤ Real.pi / 2 := by
    calc
      |Real.pi * (N : ℝ) * delta|
          = Real.pi * (N : ℝ) * |delta| := by
              rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos,
                abs_of_pos hNR]
      _ = Real.pi * ((N : ℝ) * |delta|) := by ring
      _ ≤ Real.pi * ((1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hNdelta
              (le_of_lt Real.pi_pos)
      _ = Real.pi / 2 := by ring
  have hsin :
      2 * (N : ℝ) * |delta| ≤
        |Real.sin (Real.pi * (N : ℝ) * delta)| := by
    calc
      2 * (N : ℝ) * |delta|
          = (2 / Real.pi) *
              |Real.pi * (N : ℝ) * delta| := by
              rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos,
                abs_of_pos hNR]
              field_simp [ne_of_gt Real.pi_pos]
      _ ≤ |Real.sin (Real.pi * (N : ℝ) * delta)| :=
        Real.mul_abs_le_abs_sin hx
  rw [norm_eigenvalue_pow_sub_one, Real.norm_eq_abs]
  calc
    4 * (N : ℝ) * |delta|
        = 2 * (2 * (N : ℝ) * |delta|) := by ring
    _ ≤ 2 *
        |Real.sin (Real.pi * (N : ℝ) * delta)| :=
          mul_le_mul_of_nonneg_left hsin (by norm_num)
    _ = |2 * Real.sin (Real.pi * (N : ℝ) * delta)| := by
          rw [abs_mul]
          norm_num

private theorem geometric_phase_average_lower_bound_of_abs
    (N : Nat)
    (hN : 0 < N)
    (delta : ℝ)
    (hsmall : |delta| ≤ (1 : ℝ) / (2 * N)) :
    (4 : ℝ) / Real.pi ^ 2 ≤
      Complex.normSq
        (((N : ℂ)⁻¹) *
          ∑ y ∈ Finset.range N,
            eigenvalue delta ^ y) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN
  by_cases hdelta : delta = 0
  · subst delta
    have hsum :
        (∑ y ∈ Finset.range N,
          eigenvalue 0 ^ y) = (N : ℂ) := by
      simp [eigenvalue]
    have havg :
        ((N : ℂ)⁻¹) *
            ∑ y ∈ Finset.range N, eigenvalue 0 ^ y = 1 := by
      rw [hsum]
      simp [Nat.ne_of_gt hN]
    rw [havg]
    simp only [Complex.normSq_one]
    rw [div_le_iff₀ (sq_pos_of_pos Real.pi_pos)]
    nlinarith [Real.two_le_pi]
  · let r : ℂ := eigenvalue delta
    let S : ℂ := ∑ y ∈ Finset.range N, r ^ y
    have hgeom :
        S * (r - 1) = r ^ N - 1 := by
      dsimp [S]
      exact geom_sum_mul r N
    have hnormgeom :
        ‖S‖ * ‖r - 1‖ = ‖r ^ N - 1‖ := by
      calc
        ‖S‖ * ‖r - 1‖ = ‖S * (r - 1)‖ :=
          (norm_mul _ _).symm
        _ = ‖r ^ N - 1‖ := by rw [hgeom]
    have hden :
        ‖r - 1‖ ≤ 2 * Real.pi * |delta| := by
      simpa [r] using norm_eigenvalue_sub_one_le delta
    have hnum :
        4 * (N : ℝ) * |delta| ≤ ‖r ^ N - 1‖ := by
      simpa [r] using
        four_mul_abs_le_norm_eigenvalue_pow_sub_one
          N hN delta hsmall
    have hchain :
        4 * (N : ℝ) * |delta| ≤
          ‖S‖ * (2 * Real.pi * |delta|) := by
      calc
        4 * (N : ℝ) * |delta|
            ≤ ‖r ^ N - 1‖ := hnum
        _ = ‖S‖ * ‖r - 1‖ := hnormgeom.symm
        _ ≤ ‖S‖ * (2 * Real.pi * |delta|) :=
          mul_le_mul_of_nonneg_left hden (norm_nonneg S)
    have habs : 0 < |delta| := abs_pos.mpr hdelta
    have hchain' :
        (4 * (N : ℝ)) * |delta| ≤
          (2 * Real.pi * ‖S‖) * |delta| := by
      calc
        (4 * (N : ℝ)) * |delta|
            = 4 * (N : ℝ) * |delta| := by ring
        _ ≤ ‖S‖ * (2 * Real.pi * |delta|) := hchain
        _ = (2 * Real.pi * ‖S‖) * |delta| := by ring
    have hcancel :
        4 * (N : ℝ) ≤ 2 * Real.pi * ‖S‖ :=
      (mul_le_mul_iff_of_pos_right habs).mp hchain'
    have hcore :
        2 * (N : ℝ) ≤ Real.pi * ‖S‖ := by
      nlinarith
    have hS :
        2 / Real.pi ≤ ‖S‖ / (N : ℝ) := by
      apply (div_le_div_iff₀ Real.pi_pos hNR).2
      simpa [mul_comm] using hcore
    have havgnorm :
        ‖((N : ℂ)⁻¹) * S‖ = ‖S‖ / (N : ℝ) := by
      calc
        ‖((N : ℂ)⁻¹) * S‖
            = ‖(N : ℂ)⁻¹‖ * ‖S‖ := norm_mul _ _
        _ = ((N : ℝ)⁻¹) * ‖S‖ := by
              rw [norm_inv]
              simp
        _ = ‖S‖ / (N : ℝ) := by
              rw [div_eq_mul_inv]
              ring
    have havg :
        2 / Real.pi ≤ ‖((N : ℂ)⁻¹) * S‖ := by
      rw [havgnorm]
      exact hS
    change
      (4 : ℝ) / Real.pi ^ 2 ≤
        Complex.normSq (((N : ℂ)⁻¹) * S)
    rw [Complex.normSq_eq_norm_sq]
    have hsquare :
        (2 / Real.pi) * (2 / Real.pi) ≤
          ‖((N : ℂ)⁻¹) * S‖ *
            ‖((N : ℂ)⁻¹) * S‖ :=
      mul_self_le_mul_self
        (by positivity : 0 ≤ (2 : ℝ) / Real.pi) havg
    calc
      (4 : ℝ) / Real.pi ^ 2
          = (2 / Real.pi) * (2 / Real.pi) := by
              field_simp [ne_of_gt Real.pi_pos]
              ring
      _ ≤ ‖((N : ℂ)⁻¹) * S‖ *
            ‖((N : ℂ)⁻¹) * S‖ := hsquare
      _ = ‖((N : ℂ)⁻¹) * S‖ ^ 2 := by ring

theorem geometric_phase_average_lower_bound
    (N : Nat)
    (hN : 0 < N)
    (delta : ℝ)
    (hdelta :
      min |delta| |(1 - |delta|)| ≤ (1 : ℝ) / (2 * N)) :
    (4 : ℝ) / Real.pi ^ 2 ≤
      Complex.normSq
        (((N : ℂ)⁻¹) *
          ∑ y ∈ Finset.range N,
            eigenvalue delta ^ y) := by
  have hsmall_or :
      |delta| ≤ (1 : ℝ) / (2 * N) ∨
        |(1 - |delta|)| ≤ (1 : ℝ) / (2 * N) := by
    by_cases hle : |delta| ≤ |(1 - |delta|)|
    · left
      simpa [min_eq_left hle] using hdelta
    · right
      have hle' : |(1 - |delta|)| ≤ |delta| := le_of_not_ge hle
      simpa [min_eq_right hle'] using hdelta
  rcases hsmall_or with hsmall | hwrap
  · exact geometric_phase_average_lower_bound_of_abs N hN delta hsmall
  · by_cases hdelta_nonneg : 0 ≤ delta
    · have hsmall' : |delta - 1| ≤ (1 : ℝ) / (2 * N) := by
        have habs : |delta| = delta := abs_of_nonneg hdelta_nonneg
        simpa [habs, abs_sub_comm] using hwrap
      simpa [eigenvalue_sub_one] using
        geometric_phase_average_lower_bound_of_abs N hN (delta - 1) hsmall'
    · have hdelta_le : delta ≤ 0 := le_of_not_ge hdelta_nonneg
      have hsmall' : |delta + 1| ≤ (1 : ℝ) / (2 * N) := by
        have habs : |delta| = -delta := abs_of_nonpos hdelta_le
        simpa [habs, add_comm] using hwrap
      simpa [eigenvalue_add_one] using
        geometric_phase_average_lower_bound_of_abs N hN (delta + 1) hsmall'

end

end ShorECDLP.Quantum.PhaseEstimation
