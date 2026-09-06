import ShorECDLP.Submission.Naive.OrderFinding.PhaseEstimation.Main
import ShorECDLP.Submission.Naive.OrderFinding.Defs

namespace ShorECDLP.Quantum.OrderFinding

open PhaseEstimation

private theorem circular_near_rational_abs
    {r N n v : ℕ}
    (hr : 0 < r)
    (hN : 0 < N)
    (hrN : r ≤ N)
    (hn : n < r)
    (hv : v < N)
    (hnear :
      min
          |(n : ℝ) / (r : ℝ) - (v : ℝ) / (N : ℝ)|
          |(1 - |(n : ℝ) / (r : ℝ) - (v : ℝ) / (N : ℝ)|)| ≤
        (1 : ℝ) / (2 * (N : ℝ))) :
    |(n : ℝ) / (r : ℝ) - (v : ℝ) / (N : ℝ)| ≤
      (1 : ℝ) / (2 * (N : ℝ)) := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hn1 : n + 1 ≤ r := Nat.succ_le_iff.mpr hn
  have hv1 : v + 1 ≤ N := Nat.succ_le_iff.mpr hv

  have hxNat : n * N + r ≤ r * N := by
    calc
      n * N + r ≤ n * N + N := Nat.add_le_add_left hrN _
      _ = (n + 1) * N := by ring
      _ ≤ r * N := Nat.mul_le_mul_right N hn1

  have hxCross :
      (n : ℝ) * (N : ℝ) ≤
        ((N : ℝ) - 1) * (r : ℝ) := by
    have h :
        (n : ℝ) * (N : ℝ) + (r : ℝ) ≤
          (r : ℝ) * (N : ℝ) := by
      exact_mod_cast hxNat
    nlinarith

  have hx :
      (n : ℝ) / (r : ℝ) ≤
        1 - 1 / (N : ℝ) := by
    calc
      (n : ℝ) / (r : ℝ) ≤
          ((N : ℝ) - 1) / (N : ℝ) :=
        (div_le_div_iff₀ hrR hNR).2 hxCross
      _ = 1 - 1 / (N : ℝ) := by
        field_simp [ne_of_gt hNR]

  have hvR :
      (v : ℝ) ≤ (N : ℝ) - 1 := by
    have h : (v : ℝ) + 1 ≤ (N : ℝ) := by
      exact_mod_cast hv1
    linarith

  have hy :
      (v : ℝ) / (N : ℝ) ≤
        1 - 1 / (N : ℝ) := by
    calc
      (v : ℝ) / (N : ℝ) ≤
          ((N : ℝ) - 1) / (N : ℝ) :=
        (div_le_div_iff_of_pos_right hNR).2 hvR
      _ = 1 - 1 / (N : ℝ) := by
        field_simp [ne_of_gt hNR]

  have hx0 : 0 ≤ (n : ℝ) / (r : ℝ) := by positivity
  have hy0 : 0 ≤ (v : ℝ) / (N : ℝ) := by positivity

  have hdelta :
      |(n : ℝ) / (r : ℝ) - (v : ℝ) / (N : ℝ)| ≤
        1 - 1 / (N : ℝ) := by
    rw [abs_le]
    constructor <;> linarith

  rcases (min_le_iff.mp hnear) with h | h
  · exact h
  · have hgap :
        1 / (N : ℝ) ≤
          1 -
            |(n : ℝ) / (r : ℝ) -
              (v : ℝ) / (N : ℝ)| := by
      linarith
    have hnonneg :
        0 ≤
          1 -
            |(n : ℝ) / (r : ℝ) -
              (v : ℝ) / (N : ℝ)| := by
      exact le_trans (by positivity) hgap
    rw [abs_of_nonneg hnonneg] at h
    have heps :
        (1 : ℝ) / (2 * (N : ℝ)) <
          1 / (N : ℝ) := by
      rw [div_lt_div_iff₀ (by positivity) hNR]
      nlinarith
    linarith

theorem nearestNumerator_eq_of_near_phase
    {r precision n : ℕ}
    (hr : 0 < r)
    (hprecision : r ≤ 2 ^ precision)
    (hn : n < r)
    (value : Fin (2 ^ precision))
    (hnear :
      circularDistance precision ((n : ℝ) / (r : ℝ)) value ≤
        (1 : ℝ) / (2 * (2 ^ precision : Nat))) :
    nearestNumerator r precision value.val = n := by
  let N : ℕ := 2 ^ precision
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hrN : r ≤ N := by
    simpa [N] using hprecision
  have hv : value.val < N := by
    simp [N]
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN

  have habs :
      |(n : ℝ) / (r : ℝ) -
          (value.val : ℝ) / (N : ℝ)| ≤
        (1 : ℝ) / (2 * (N : ℝ)) := by
    apply circular_near_rational_abs hr hN hrN hn hv
    simpa [circularDistance, N] using hnear

  rw [abs_le] at habs

  have hscale :
      0 ≤ (2 : ℝ) * (r : ℝ) * (N : ℝ) := by
    positivity

  have hlo0 :=
    mul_le_mul_of_nonneg_left habs.1 hscale
  have hhi0 :=
    mul_le_mul_of_nonneg_left habs.2 hscale

  have hlo :
      -(r : ℝ) ≤
        2 * (n : ℝ) * (N : ℝ) -
          2 * (r : ℝ) * (value.val : ℝ) := by
    convert hlo0 using 1 <;>
      field_simp [ne_of_gt hrR, ne_of_gt hNR]

  have hhi :
      2 * (n : ℝ) * (N : ℝ) -
          2 * (r : ℝ) * (value.val : ℝ) ≤
        (r : ℝ) := by
    convert hhi0 using 1 <;>
      field_simp [ne_of_gt hrR, ne_of_gt hNR]

  have hrNR : (r : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hrN

  have hlowerR :
      (n : ℝ) * (2 * (N : ℝ)) ≤
        2 * (r : ℝ) * (value.val : ℝ) + (N : ℝ) := by
    nlinarith

  have hlower :
      n * (2 * N) ≤
        2 * r * value.val + N := by
    exact_mod_cast hlowerR

  rcases lt_or_eq_of_le hrN with hrlt | hre
  · have hrltR : (r : ℝ) < (N : ℝ) := by
      exact_mod_cast hrlt
    have hupperR :
        2 * (r : ℝ) * (value.val : ℝ) + (N : ℝ) <
          ((n + 1 : ℕ) : ℝ) * (2 * (N : ℝ)) := by
      have hrv :
          2 * (r : ℝ) * (value.val : ℝ) ≤
            2 * (n : ℝ) * (N : ℝ) + (r : ℝ) := by
        nlinarith [hlo]
      calc
        2 * (r : ℝ) * (value.val : ℝ) + (N : ℝ)
            ≤ 2 * (n : ℝ) * (N : ℝ) + (r : ℝ) + (N : ℝ) := by
              linarith
        _ < 2 * (n : ℝ) * (N : ℝ) + (N : ℝ) + (N : ℝ) := by
              linarith
        _ = ((n + 1 : ℕ) : ℝ) * (2 * (N : ℝ)) := by
              push_cast
              ring
    have hupper :
        2 * r * value.val + N <
          (n + 1) * (2 * N) := by
      exact_mod_cast hupperR
    unfold nearestNumerator
    change
      (2 * r * value.val + N) / (2 * N) = n
    exact Nat.div_eq_of_lt_le hlower hupper

  · have hloN := hlo
    have hhiN := hhi
    rw [hre] at hloN hhiN

    have hvn : value.val = n := by
      rcases lt_trichotomy value.val n with hvn | hvn | hvn
      · have hgap :
            ((value.val + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast Nat.succ_le_iff.mpr hvn
        exfalso
        have hstep :
            2 * (N : ℝ) ≤
              2 * (n : ℝ) * (N : ℝ) -
                2 * (N : ℝ) * (value.val : ℝ) := by
          have hmul :=
            mul_le_mul_of_nonneg_right hgap
              (show 0 ≤ (2 : ℝ) * (N : ℝ) by positivity)
          ring_nf at hmul ⊢
          nlinarith [hmul, hNR]
        nlinarith [hhiN, hstep, hNR]
      · exact hvn
      · have hgap :
            ((n + 1 : ℕ) : ℝ) ≤ (value.val : ℝ) := by
          exact_mod_cast Nat.succ_le_iff.mpr hvn
        exfalso
        have hstep :
            2 * (N : ℝ) ≤
              2 * (N : ℝ) * (value.val : ℝ) -
                2 * (n : ℝ) * (N : ℝ) := by
          have hgapNat : n + 1 ≤ value.val :=
            Nat.succ_le_iff.mpr hvn
          have hmulNat :
              (n + 1) * (2 * N) ≤ value.val * (2 * N) :=
            Nat.mul_le_mul_right (2 * N) hgapNat
          have hmulR :
              (((n + 1) * (2 * N) : ℕ) : ℝ) ≤
                ((value.val * (2 * N) : ℕ) : ℝ) := by
            exact_mod_cast hmulNat
          push_cast at hmulR
          ring_nf at hmulR ⊢
          linarith
        nlinarith [hloN, hstep, hNR]

    unfold nearestNumerator
    change
      (2 * r * value.val + N) / (2 * N) = n
    rw [hre, hvn]

    have hden : 0 < 2 * N := by omega
    have hNlt : N < 2 * N := by omega

    calc
      (2 * N * n + N) / (2 * N) =
          (N + (2 * N) * n) / (2 * N) := by
            congr 1
            ring
      _ = N / (2 * N) + n := by
            exact Nat.add_mul_div_left N n hden
      _ = n := by
            rw [Nat.div_eq_of_lt hNlt]
            simp

theorem orderFindingPostprocess_of_character_peak
    {r precision d : ℕ}
    (hr : Nat.Prime r)
    (hprecision : r ≤ 2 ^ precision)
    (k : Fin r)
    (hk : k.val ≠ 0)
    (a b : Fin (2 ^ precision))
    (ha :
      circularDistance precision ((k.val : ℝ) / (r : ℝ)) a ≤
        (1 : ℝ) / (2 * (2 ^ precision : Nat)))
    (hb :
      circularDistance precision
          ((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ)) b ≤
        (1 : ℝ) / (2 * (2 ^ precision : Nat))) :
    orderFindingPostprocess r precision hr (a, b) =
      some (d : ZMod r) := by
  letI : Fact (Nat.Prime r) := ⟨hr⟩

  have hka :
      nearestNumerator r precision a.val = k.val :=
    nearestNumerator_eq_of_near_phase
      hr.pos hprecision k.isLt a ha

  have hmodlt :
      (k.val * d) % r < r :=
    Nat.mod_lt _ hr.pos

  have hkb :
      nearestNumerator r precision b.val =
        (k.val * d) % r :=
    nearestNumerator_eq_of_near_phase
      hr.pos hprecision hmodlt b hb

  have hkZ : (k.val : ZMod r) ≠ 0 := by
    intro h
    apply hk
    have hval := congrArg ZMod.val h
    have hkval :
        (k.val : ZMod r).val = k.val :=
      ZMod.val_natCast_of_lt k.isLt
    rw [hkval, ZMod.val_zero] at hval
    exact hval

  have hmod :
      (((k.val * d) % r : ℕ) : ZMod r) =
        (k.val : ZMod r) * (d : ZMod r) := by
    rw [ZMod.natCast_mod]
    push_cast
    rfl

  have hdiv :
      (((k.val * d) % r : ℕ) : ZMod r) /
          (k.val : ZMod r) =
        (d : ZMod r) := by
    rw [hmod]
    exact mul_div_cancel_left₀ (d : ZMod r) hkZ

  simp [orderFindingPostprocess, hka, hkb, hkZ]

theorem exists_character_peak_family
    (r precision d : ℕ)
    (hr : Nat.Prime r) :
    ∃ aPeak bPeak : Fin r → Fin (2 ^ precision),
      (∀ k,
        circularDistance precision
            ((k.val : ℝ) / (r : ℝ)) (aPeak k) ≤
          (1 : ℝ) / (2 * (2 ^ precision : Nat))) ∧
      (∀ k,
        circularDistance precision
            ((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ))
            (bPeak k) ≤
          (1 : ℝ) / (2 * (2 ^ precision : Nat))) := by
  classical
  have hrR : (0 : ℝ) < (r : ℝ) := by
    exact_mod_cast hr.pos

  have haExists :
      ∀ k : Fin r,
        ∃ a : Fin (2 ^ precision),
          circularDistance precision
              ((k.val : ℝ) / (r : ℝ)) a ≤
            (1 : ℝ) / (2 * (2 ^ precision : Nat)) := by
    intro k
    apply exists_nearest_phase_value
    · positivity
    · rw [div_lt_iff₀ hrR]
      have hkR : (k.val : ℝ) < (r : ℝ) := by
        exact_mod_cast k.isLt
      simp

  have hbExists :
      ∀ k : Fin r,
        ∃ b : Fin (2 ^ precision),
          circularDistance precision
              ((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ)) b ≤
            (1 : ℝ) / (2 * (2 ^ precision : Nat)) := by
    intro k
    apply exists_nearest_phase_value
    · positivity
    · rw [div_lt_iff₀ hrR]
      have hm :
          (k.val * d) % r < r :=
        Nat.mod_lt _ hr.pos
      have hmR :
          (((k.val * d) % r : ℕ) : ℝ) < (r : ℝ) := by
        exact_mod_cast hm
      simpa using hmR

  choose aPeak haPeak using haExists
  choose bPeak hbPeak using hbExists
  exact ⟨aPeak, bPeak, haPeak, hbPeak⟩

theorem character_peak_first_injective
    {r precision : ℕ}
    (hr : Nat.Prime r)
    (hprecision : r ≤ 2 ^ precision)
    (aPeak : Fin r → Fin (2 ^ precision))
    (hnear :
      ∀ k,
        circularDistance precision
            ((k.val : ℝ) / (r : ℝ)) (aPeak k) ≤
          (1 : ℝ) / (2 * (2 ^ precision : Nat))) :
    Function.Injective aPeak := by
  intro k l hkl

  have hk :
      nearestNumerator r precision (aPeak k).val = k.val :=
    nearestNumerator_eq_of_near_phase
      hr.pos hprecision k.isLt (aPeak k) (hnear k)

  have hl :
      nearestNumerator r precision (aPeak l).val = l.val :=
    nearestNumerator_eq_of_near_phase
      hr.pos hprecision l.isLt (aPeak l) (hnear l)

  have hv :
      (aPeak k).val = (aPeak l).val :=
    congrArg Fin.val hkl

  apply Fin.ext
  calc
    k.val =
        nearestNumerator r precision (aPeak k).val := hk.symm
    _ =
        nearestNumerator r precision (aPeak l).val := by rw [hv]
    _ = l.val := hl

end ShorECDLP.Quantum.OrderFinding
