import ShorECDLP.Submission.OrderFinding.Proofs.OracleKickback

namespace ShorECDLP.Quantum.OrderFinding

open PhaseEstimation
open scoped BigOperators

noncomputable def orderFindingFourierState
    {G : Type*} [AddCommGroup G]
    {w r d precision : ℕ}
    (enc : PointEncoding G w)
    (P : G)
    (aReg bReg pointReg : List Wire)
    (s : BasisState) : State :=
  (((Real.sqrt r)⁻¹ : ℝ) : ℂ) •
    ∑ k : Fin r,
      ∑ a : Fin (2 ^ precision),
        ∑ b : Fin (2 ^ precision),
          (qpeAmplitude precision
              ((k.val : ℝ) / (r : ℝ)) a.val *
            qpeAmplitude precision
              ((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ))
              b.val) •
            labelState bReg b.val
              (labelState aReg a.val
                (pointEigenstate enc P pointReg s k))

theorem orderFinding_eq_fourierState
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
        qftAncilla precision s) :
    orderFinding aReg bReg qftAncilla oracle (ket s) =
      orderFindingFourierState
        (r := r) (d := d) (precision := precision)
        enc P aReg bReg pointReg s := by
  sorry

end ShorECDLP.Quantum.OrderFinding
