import ShorECDLP.Submission.OrderFinding.Defs

namespace ShorECDLP.Quantum.OrderFinding

structure OrderFindingSetup
    {G : Type*} [AddCommGroup G]
    {w : ℕ}
    (enc : PointEncoding G w)
    (aReg bReg pointReg oracleWork : List Wire)
    (qftAncilla : Wire)
    (precision : ℕ)
    (s : BasisState) : Prop where
  a_width : aReg.length = precision
  b_width : bReg.length = precision
  a_zero : regValue aReg s = 0
  b_zero : regValue bReg s = 0
  point_zero : regValue pointReg s = (enc.encode (0 : G)).val
  oracleWork_zero : Clean oracleWork s
  ancilla_zero : s qftAncilla = false
  ancilla_fresh :
    qftAncilla ∉ aReg ++ bReg ++ pointReg ++ oracleWork

theorem orderFinding_correct
    {G : Type*} [AddCommGroup G]
    {w r d precision : ℕ}
    (enc : PointEncoding G w)
    (oracle : State →ₗ[ℂ] State)
    (P Q : G)
    (aReg bReg pointReg oracleWork: List Wire)
    (qftAncilla : Wire)
    (s : BasisState)
    (hsetting : ECDLPSetting P Q r d)
    (hspec : ECDLPOracleSpec enc oracle P Q aReg bReg pointReg oracleWork)
    (hsetup : OrderFindingSetup enc aReg bReg pointReg oracleWork qftAncilla precision s)
    (hprecision : r ≤ 2 ^ precision) :
    ((r - 1 : ℝ) / r) * ((4 : ℝ) / Real.pi ^ 2) ^ 2 ≤
      orderFindingSuccessProbability
        r precision d hsetting.prime_order aReg bReg
        (orderFinding aReg bReg qftAncilla oracle (ket s)) := by
  sorry
