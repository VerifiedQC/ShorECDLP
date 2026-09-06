import ShorECDLP.Submission.Naive.OrderFinding.Proofs.Probability
import ShorECDLP.Submission.Naive.OrderFinding.Proofs.Postprocess

namespace ShorECDLP.Quantum.OrderFinding

open scoped BigOperators

theorem nonzero_character_peak_sum_le_success
    {r precision d : ℕ}
    (hr : Nat.Prime r)
    (aReg bReg : List Wire)
    (ψ : State)
    (aPeak bPeak : Fin r → Fin (2 ^ precision))
    (haInj : Function.Injective aPeak)
    (hgood :
      ∀ k : Fin r, k.val ≠ 0 →
        orderFindingPostprocess r precision hr
            (aPeak k, bPeak k) =
          some (d : ZMod r)) :
    (∑ k : Fin r,
        if k.val = 0 then 0
        else
          jointRegisterProbability
            aReg bReg (aPeak k).val (bPeak k).val ψ) ≤
      orderFindingSuccessProbability
        r precision d hr aReg bReg ψ := by
  classical
  let S : Fin (2 ^ precision) → ℝ :=
    fun a =>
      ∑ b : Fin (2 ^ precision),
        if orderFindingPostprocess r precision hr (a, b) =
            some (d : ZMod r)
        then jointRegisterProbability aReg bReg a.val b.val ψ
        else 0

  have hS : ∀ a, 0 ≤ S a := by
    intro a
    dsimp [S]
    apply Finset.sum_nonneg
    intro b _
    by_cases h :
        orderFindingPostprocess r precision hr (a, b) =
          some (d : ZMod r)
    · simp [h, jointRegisterProbability_nonneg]
    · simp [h]

  have hk : ∀ k : Fin r,
      (if k.val = 0 then 0
       else
         jointRegisterProbability
           aReg bReg (aPeak k).val (bPeak k).val ψ) ≤
        S (aPeak k) := by
    intro k
    by_cases hk0 : k.val = 0
    · simp [hk0, hS]
    · rw [if_neg hk0]
      dsimp [S]
      have hg := hgood k hk0
      calc
        jointRegisterProbability
            aReg bReg (aPeak k).val (bPeak k).val ψ =
          (if orderFindingPostprocess r precision hr
                (aPeak k, bPeak k) = some (d : ZMod r)
           then
             jointRegisterProbability
               aReg bReg (aPeak k).val (bPeak k).val ψ
           else 0) := by
          simp [hg]
        _ ≤
          ∑ b : Fin (2 ^ precision),
            if orderFindingPostprocess r precision hr
                  (aPeak k, b) = some (d : ZMod r)
            then
              jointRegisterProbability
                aReg bReg (aPeak k).val b.val ψ
            else 0 := by
          exact
            Finset.single_le_sum
              (s := (Finset.univ : Finset (Fin (2 ^ precision))))
              (a := bPeak k)
              (f := fun b : Fin (2 ^ precision) =>
                if orderFindingPostprocess r precision hr
                    (aPeak k, b) = some (d : ZMod r)
                then
                  jointRegisterProbability
                    aReg bReg (aPeak k).val b.val ψ
                else 0)
              (by
                intro b _
                by_cases h :
                    orderFindingPostprocess r precision hr
                        (aPeak k, b) = some (d : ZMod r)
                · simp [h, jointRegisterProbability_nonneg]
                · simp [h])
              (by simp)

  calc
    (∑ k : Fin r,
        if k.val = 0 then 0
        else
          jointRegisterProbability
            aReg bReg (aPeak k).val (bPeak k).val ψ)
        ≤ ∑ k : Fin r, S (aPeak k) := by
          apply Finset.sum_le_sum
          intro k _
          exact hk k
    _ =
        ∑ a ∈ Finset.univ.image aPeak, S a := by
          symm
          apply Finset.sum_image
          intro x _ y _ hxy
          exact haInj hxy
    _ ≤ ∑ a : Fin (2 ^ precision), S a := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro a _
            simp
          · intro a _ _
            exact hS a
    _ =
        orderFindingSuccessProbability
          r precision d hr aReg bReg ψ := by
          rfl

theorem nonzero_character_baseline_sum
    {r : ℕ}
    (hr : Nat.Prime r)
    (c : ℝ) :
    (∑ k : Fin r,
        if k.val = 0 then 0
        else (r : ℝ)⁻¹ * c) =
      ((r - 1 : ℝ) / r) * c := by
  classical
  let z : Fin r := ⟨0, hr.pos⟩
  let q : ℝ := (r : ℝ)⁻¹ * c

  have hkz (k : Fin r) : k.val = 0 ↔ k = z := by
    constructor
    · intro h
      apply Fin.ext
      simpa [z] using h
    · intro h
      subst k
      rfl

  simp_rw [hkz]

  calc
    (∑ k : Fin r, if k = z then 0 else q) =
        ∑ k ∈ Finset.univ.filter (fun k : Fin r => k ≠ z), q := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro k _
          by_cases h : k = z <;> simp [h]
    _ = ∑ k ∈ Finset.univ.erase z, q := by
          rw [Finset.filter_ne']
    _ = ((Finset.univ.erase z).card : ℝ) * q := by
          simp [nsmul_eq_mul]
    _ = (((r - 1 : ℕ) : ℝ)) * q := by
          congr 1
          simp [z]
    _ = ((r - 1 : ℝ) / r) * c := by
          dsimp [q]
          rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hr.ne_zero)]
          simp [div_eq_mul_inv, mul_assoc]
end ShorECDLP.Quantum.OrderFinding
