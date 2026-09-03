import ShorECDLP.Submission.Naive.OrderFinding.Proofs.SuccessProbability

/-!
# Abstract two-register ECDLP order finding

This module proves a single-run lower bound for recovering the hidden shift `d` from a supplied
`ECDLPOracleSpec`. It does not instantiate secp256k1 arithmetic, implement measurement/discard,
or provide the final same-program resource theorem.
-/

namespace ShorECDLP.Quantum.OrderFinding

open PhaseEstimation

theorem orderFinding_correct
    {G : Type*} [AddCommGroup G]
    {w r d precision : ℕ}
    (enc : PointEncoding G w)
    (oracle : State →ₗ[ℂ] State)
    (P Q : G)
    (aReg bReg pointReg oracleWork : List Wire)
    (qftAncilla : Wire)
    (s : BasisState)
    (hsetting : ECDLPSetting P Q r d)
    (hspec :
      ECDLPOracleSpec enc oracle P Q
        aReg bReg pointReg oracleWork)
    (hsetup :
      OrderFindingSetup enc aReg bReg pointReg oracleWork
        qftAncilla precision s)
    (hprecision : r ≤ 2 ^ precision) :
    ((r - 1 : ℝ) / r) *
        ((4 : ℝ) / Real.pi ^ 2) ^ 2 ≤
      orderFindingSuccessProbability
        r precision d hsetting.prime_order aReg bReg
        (orderFinding aReg bReg qftAncilla oracle (ket s)) := by
  obtain ⟨aPeak, bPeak, hnearA, hnearB⟩ :=
    exists_character_peak_family r precision d hsetting.prime_order

  have haInj : Function.Injective aPeak :=
    character_peak_first_injective
      hsetting.prime_order hprecision aPeak hnearA

  have hgood :
      ∀ k : Fin r, k.val ≠ 0 →
        orderFindingPostprocess r precision hsetting.prime_order
            (aPeak k, bPeak k) =
          some (d : ZMod r) := by
    intro k hk
    exact orderFindingPostprocess_of_character_peak
      hsetting.prime_order hprecision k hk
      (aPeak k) (bPeak k) (hnearA k) (hnearB k)

  calc
    ((r - 1 : ℝ) / r) *
        ((4 : ℝ) / Real.pi ^ 2) ^ 2 =
        ∑ k : Fin r,
          if k.val = 0 then 0
          else
            (r : ℝ)⁻¹ *
              ((4 : ℝ) / Real.pi ^ 2) ^ 2 := by
      symm
      exact nonzero_character_baseline_sum
        hsetting.prime_order
        (((4 : ℝ) / Real.pi ^ 2) ^ 2)
    _ ≤
        ∑ k : Fin r,
          if k.val = 0 then 0
          else
            jointRegisterProbability
              aReg bReg
              (aPeak k).val (bPeak k).val
              (orderFinding
                aReg bReg qftAncilla oracle (ket s)) := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : k.val = 0
      · simp [hk]
      · simp only [hk, if_false]
        exact jointRegisterProbability_character_peak_lower_bound
          enc oracle P Q
          aReg bReg pointReg oracleWork
          qftAncilla s
          hsetting hspec hsetup
          k (aPeak k) (bPeak k)
          (hnearA k) (hnearB k)
    _ ≤
        orderFindingSuccessProbability
          r precision d hsetting.prime_order aReg bReg
          (orderFinding
            aReg bReg qftAncilla oracle (ket s)) := by
      exact nonzero_character_peak_sum_le_success
        hsetting.prime_order
        aReg bReg
        (orderFinding
          aReg bReg qftAncilla oracle (ket s))
        aPeak bPeak haInj hgood

end ShorECDLP.Quantum.OrderFinding
